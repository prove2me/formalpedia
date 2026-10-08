-- Prove2me | solution 1 for KingmanSubadditive.Ulam.beta_infimum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:17:34.029984+00:00
-- url     : https://prove2.me/submissions/e4770eab-fe01-4d8d-82b1-702ffd512fd8

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations



namespace KingmanSubadditive.Ulam

open Set Real

/-- the auxiliary function whose positive zero is `δ` -/
noncomputable def phi (δ : ℝ) : ℝ := Real.log (1 + δ) - 2 * δ / (1 + δ)

lemma phi_hasDerivAt {δ : ℝ} (hδ : 0 < 1 + δ) :
    HasDerivAt phi ((δ - 1) / (1 + δ) ^ 2) δ := by
  have h1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + δ)) δ := by
    have := ((hasDerivAt_id δ).const_add 1).log hδ.ne'
    simpa using this
  have h2 : HasDerivAt (fun x : ℝ => 2 * x / (1 + x)) ((2 * (1 + δ) - 2 * δ * 1) / (1 + δ) ^ 2) δ := by
    have hc : HasDerivAt (fun x : ℝ => 2 * x) 2 δ := by simpa using (hasDerivAt_id δ).const_mul 2
    have hd : HasDerivAt (fun x : ℝ => 1 + x) 1 δ := by simpa using (hasDerivAt_id δ).const_add 1
    exact hc.div hd hδ.ne'
  have := h1.sub h2
  refine this.congr_deriv ?_
  field_simp
  ring

lemma phi_continuous : ContinuousOn phi (Ici 0) := by
  intro x hx
  have hx' : (0 : ℝ) ≤ x := hx
  have : (0 : ℝ) < 1 + x := by linarith
  exact (phi_hasDerivAt this).continuousAt.continuousWithinAt

lemma phi_zero : phi 0 = 0 := by simp [phi]

lemma phi_strictAnti : StrictAntiOn phi (Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1) (phi_continuous.mono Icc_subset_Ici_self)
  intro x hx
  rw [interior_Icc] at hx
  have h0 : (0 : ℝ) < 1 + x := by linarith [hx.1]
  rw [(phi_hasDerivAt h0).deriv]
  apply div_neg_of_neg_of_pos
  · linarith [hx.2]
  · positivity

lemma phi_strictMono : StrictMonoOn phi (Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    (phi_continuous.mono (fun x hx => mem_Ici.2 (le_trans zero_le_one (mem_Ici.1 hx))))
  intro x hx
  rw [interior_Ici] at hx
  have h1 : (1 : ℝ) < x := hx
  have h0 : (0 : ℝ) < 1 + x := by linarith
  rw [(phi_hasDerivAt h0).deriv]
  apply div_pos
  · linarith
  · positivity

lemma phi_neg_of_le_one {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) : phi δ < 0 := by
  have := phi_strictAnti (a := 0) (b := δ) ⟨le_refl 0, zero_le_one⟩ ⟨h0.le, h1⟩ h0
  rwa [phi_zero] at this

lemma phi_one_neg : phi 1 < 0 := phi_neg_of_le_one one_pos le_rfl

lemma phi_seven_pos : 0 < phi 7 := by
  unfold phi
  have h8 : Real.log (1 + 7) = 3 * Real.log 2 := by
    rw [show (1 : ℝ) + 7 = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  rw [h8]
  have := Real.log_two_gt_d9
  norm_num at this ⊢
  linarith

lemma root_gt_one {δ : ℝ} (h0 : 0 < δ) (hroot : Real.log (1 + δ) = 2 * δ / (1 + δ)) : 1 < δ := by
  by_contra h
  push_neg at h
  have := phi_neg_of_le_one h0 h
  unfold phi at this
  linarith

/-- existence and uniqueness of the positive root -/
lemma delta_exists_unique : ∃! δ : ℝ, 0 < δ ∧ Real.log (1 + δ) = 2 * δ / (1 + δ) := by
  have hiv := intermediate_value_Icc (a := 1) (b := 7) (by norm_num) (f := phi)
    (phi_continuous.mono (fun x hx => mem_Ici.2 (le_trans zero_le_one hx.1)))
  have h0mem : (0 : ℝ) ∈ Icc (phi 1) (phi 7) := ⟨phi_one_neg.le, phi_seven_pos.le⟩
  obtain ⟨δ, hδ, hphi⟩ := hiv h0mem
  refine ⟨δ, ⟨by linarith [hδ.1], ?_⟩, ?_⟩
  · unfold phi at hphi; linarith
  · rintro δ' ⟨h0', hroot'⟩
    have h1' := root_gt_one h0' hroot'
    have h1 : 1 ≤ δ := hδ.1
    apply phi_strictMono.injOn (mem_Ici.2 h1'.le) (mem_Ici.2 h1)
    show phi δ' = phi δ
    rw [hphi]; unfold phi; rw [hroot']; ring

/-! ### the exponent `E(α, b)` -/

lemma stirlingExponent_eq (α b : ℝ) :
    stirlingExponent α b = 2 * α + (b - α) * Real.log (b - α) - α * Real.log α - b * Real.log b :=
  rfl

/-- continuity in `α` -/
lemma continuous_E_alpha (b : ℝ) : Continuous (fun α => stirlingExponent α b) := by
  simp only [stirlingExponent]
  have h1 : Continuous (fun α : ℝ => (b - α) * Real.log (b - α)) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  have h2 : Continuous (fun α : ℝ => α * Real.log α) := Real.continuous_mul_log
  fun_prop

/-- continuity in `b` -/
lemma continuous_E_b (α : ℝ) : Continuous (fun b => stirlingExponent α b) := by
  simp only [stirlingExponent]
  have h1 : Continuous (fun b : ℝ => (b - α) * Real.log (b - α)) :=
    Real.continuous_mul_log.comp (continuous_id.sub continuous_const)
  have h2 : Continuous (fun b : ℝ => b * Real.log b) := Real.continuous_mul_log
  fun_prop

/-- derivative in `α` -/
lemma hasDerivAt_E_alpha {α b : ℝ} (hα : α ≠ 0) (hαb : b - α ≠ 0) :
    HasDerivAt (fun α => stirlingExponent α b) (-Real.log (α * (b - α))) α := by
  simp only [stirlingExponent]
  have h1 : HasDerivAt (fun α : ℝ => (b - α) * Real.log (b - α))
      ((Real.log (b - α) + 1) * (-1)) α := by
    have := (Real.hasDerivAt_mul_log hαb).comp α ((hasDerivAt_id α).const_sub b)
    exact this
  have h2 : HasDerivAt (fun α : ℝ => α * Real.log α) (Real.log α + 1) α :=
    Real.hasDerivAt_mul_log hα
  have h3 : HasDerivAt (fun α : ℝ => 2 * α) 2 α := by
    simpa using (hasDerivAt_id α).const_mul 2
  have := ((h3.add h1).sub h2).sub_const (b * Real.log b)
  refine this.congr_deriv ?_
  rw [Real.log_mul hα hαb]; ring

/-- derivative in `b` -/
lemma hasDerivAt_E_b {α b : ℝ} (hb : b ≠ 0) (hαb : b - α ≠ 0) :
    HasDerivAt (fun b => stirlingExponent α b) (Real.log (b - α) - Real.log b) b := by
  simp only [stirlingExponent]
  have h1 : HasDerivAt (fun b : ℝ => (b - α) * Real.log (b - α))
      ((Real.log (b - α) + 1) * 1) b := by
    have := (Real.hasDerivAt_mul_log hαb).comp b ((hasDerivAt_id b).sub_const α)
    exact this
  have h2 : HasDerivAt (fun b : ℝ => b * Real.log b) (Real.log b + 1) b :=
    Real.hasDerivAt_mul_log hb
  have := ((h1.const_add (2 * α)).sub_const (α * Real.log α)).sub h2
  refine this.congr_deriv ?_
  ring

/-- `E(α, ·)` is strictly decreasing on `[α, ∞)` -/
lemma E_strictAnti_b {α : ℝ} (hα : 0 < α) : StrictAntiOn (fun b => stirlingExponent α b) (Ici α) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici α) (continuous_E_b α).continuousOn
  intro b hb
  rw [interior_Ici] at hb
  have hb' : α < b := hb
  rw [(hasDerivAt_E_b (by linarith : b ≠ 0) (by linarith : b - α ≠ 0)).deriv]
  have := Real.log_lt_log (by linarith : 0 < b - α) (by linarith : b - α < b)
  linarith

lemma E_zero_left (b : ℝ) : stirlingExponent 0 b = 0 := by
  simp [stirlingExponent]

/-- the monotonicity pieces of `α ↦ E(α, β)` where `β = a + 1/a`, `a ≥ 1` -/
lemma E_mono_low {a : ℝ} (ha : 1 ≤ a) :
    MonotoneOn (fun α => stirlingExponent α (a + 1 / a)) (Icc 0 (1 / a)) := by
  have ha0 : 0 < a := by linarith
  have hia : 0 < 1 / a := by positivity
  have hia1 : 1 / a ≤ a := by rw [div_le_iff₀ ha0]; nlinarith
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (continuous_E_alpha _).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx1 : 0 < x := hx.1
    have hx2 : x < 1 / a := hx.2
    exact (hasDerivAt_E_alpha hx1.ne' (by linarith : a + 1 / a - x ≠ 0)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx1 : 0 < x := hx.1
    have hx2 : x < 1 / a := hx.2
    rw [(hasDerivAt_E_alpha hx1.ne' (by linarith : a + 1 / a - x ≠ 0)).deriv]
    rw [neg_nonneg, Real.log_nonpos_iff (by nlinarith)]
    have hkey : (x - 1 / a) * (x - a) ≥ 0 := by nlinarith
    have : a * (1 / a) = 1 := by field_simp
    nlinarith

lemma E_anti_mid {a : ℝ} (ha : 1 ≤ a) :
    AntitoneOn (fun α => stirlingExponent α (a + 1 / a)) (Icc (1 / a) a) := by
  have ha0 : 0 < a := by linarith
  have hia : 0 < 1 / a := by positivity
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (continuous_E_alpha _).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx1 : 1 / a < x := hx.1
    have hx2 : x < a := hx.2
    exact (hasDerivAt_E_alpha (by linarith) (by linarith : a + 1 / a - x ≠ 0)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx1 : 1 / a < x := hx.1
    have hx2 : x < a := hx.2
    rw [(hasDerivAt_E_alpha (by linarith) (by linarith : a + 1 / a - x ≠ 0)).deriv]
    rw [neg_nonpos, Real.log_nonneg_iff (by nlinarith)]
    have hkey : (x - 1 / a) * (x - a) ≤ 0 := by nlinarith
    have : a * (1 / a) = 1 := by field_simp
    nlinarith

lemma E_mono_high {a : ℝ} (ha : 1 ≤ a) :
    MonotoneOn (fun α => stirlingExponent α (a + 1 / a)) (Icc a (a + 1 / a)) := by
  have ha0 : 0 < a := by linarith
  have hia : 0 < 1 / a := by positivity
  have hia1 : 1 / a ≤ a := by rw [div_le_iff₀ ha0]; nlinarith
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (continuous_E_alpha _).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx1 : a < x := hx.1
    have hx2 : x < a + 1 / a := hx.2
    exact (hasDerivAt_E_alpha (by linarith) (by linarith : a + 1 / a - x ≠ 0)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx1 : a < x := hx.1
    have hx2 : x < a + 1 / a := hx.2
    rw [(hasDerivAt_E_alpha (by linarith) (by linarith : a + 1 / a - x ≠ 0)).deriv]
    rw [neg_nonneg, Real.log_nonpos_iff (by nlinarith)]
    have hkey : (x - 1 / a) * (x - a) ≥ 0 := by nlinarith
    have : a * (1 / a) = 1 := by field_simp
    nlinarith

/-- the value at the critical point `α = a = √δ`, `β = a + 1/a` -/
lemma E_at_crit {δ : ℝ} (h0 : 0 < δ) (hroot : Real.log (1 + δ) = 2 * δ / (1 + δ)) :
    stirlingExponent (Real.sqrt δ) (Real.sqrt δ + 1 / Real.sqrt δ) = 0 := by
  set a := Real.sqrt δ with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 h0
  have ha2 : a ^ 2 = δ := Real.sq_sqrt h0.le
  simp only [stirlingExponent]
  have e1 : a + 1 / a - a = 1 / a := by ring
  have e2 : Real.log (1 / a) = -Real.log a := by rw [one_div, Real.log_inv]
  have e3 : a + 1 / a = (1 + δ) / a := by rw [← ha2]; field_simp; ring
  have e4 : Real.log ((1 + δ) / a) = Real.log (1 + δ) - Real.log a :=
    Real.log_div (by linarith) ha0.ne'
  rw [e1, e2, e3, e4, hroot]
  field_simp
  rw [← ha2]
  ring

/-- `E(α, β) ≥ 0` for all `α ∈ (0, β)` -/
lemma E_nonneg_at_beta {δ : ℝ} (h0 : 0 < δ) (h1 : 1 < δ)
    (hroot : Real.log (1 + δ) = 2 * δ / (1 + δ)) {α : ℝ} (hα : 0 < α)
    (hαβ : α < Real.sqrt δ + 1 / Real.sqrt δ) :
    0 ≤ stirlingExponent α (Real.sqrt δ + 1 / Real.sqrt δ) := by
  have hcrit := E_at_crit h0 hroot
  set a := Real.sqrt δ with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 h0
  have ha1 : 1 ≤ a := by
    rw [ha, Real.le_sqrt zero_le_one h0.le]; linarith
  have hia : 0 < 1 / a := by positivity
  have hia1 : 1 / a ≤ a := by rw [div_le_iff₀ ha0]; nlinarith
  rcases le_or_gt α (1 / a) with hc | hc
  · have := E_mono_low ha1 (⟨le_rfl, hia.le⟩ : (0 : ℝ) ∈ Icc 0 (1 / a))
      (⟨hα.le, hc⟩ : α ∈ Icc 0 (1 / a)) hα.le
    simp only [E_zero_left] at this
    exact this
  rcases le_or_gt α a with hc2 | hc2
  · have := E_anti_mid ha1 (⟨hc.le, hc2⟩ : α ∈ Icc (1 / a) a)
      (⟨hia1, le_rfl⟩ : a ∈ Icc (1 / a) a) hc2
    simp only at this
    rw [hcrit] at this
    exact this
  · have := E_mono_high ha1 (⟨le_rfl, by linarith⟩ : a ∈ Icc a (a + 1 / a))
      (⟨hc2.le, hαβ.le⟩ : α ∈ Icc a (a + 1 / a)) hc2.le
    simp only at this
    rw [hcrit] at this
    exact this

/-- the admissible set is exactly `(β, ∞)` -/
lemma admissible_eq {δ : ℝ} (h0 : 0 < δ) (h1 : 1 < δ)
    (hroot : Real.log (1 + δ) = 2 * δ / (1 + δ)) :
    {b : ℝ | 0 < b ∧ ∃ α : ℝ, 0 < α ∧ α < b ∧ stirlingExponent α b < 0} =
      Ioi (Real.sqrt δ + 1 / Real.sqrt δ) := by
  set a := Real.sqrt δ with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 h0
  have hia : 0 < 1 / a := by positivity
  have hcrit := E_at_crit h0 hroot
  ext b
  simp only [mem_setOf_eq, mem_Ioi]
  constructor
  · rintro ⟨hb, α, hα, hαb, hE⟩
    by_contra hle
    push_neg at hle
    have hanti := E_strictAnti_b hα
    have : stirlingExponent α (a + 1 / a) ≤ stirlingExponent α b :=
      hanti.antitoneOn (mem_Ici.2 hαb.le) (mem_Ici.2 (by linarith)) hle
    have hnn := E_nonneg_at_beta h0 h1 hroot hα (by linarith)
    linarith
  · intro hb
    refine ⟨by linarith, a, ha0, by linarith, ?_⟩
    have hanti := E_strictAnti_b ha0
    have : stirlingExponent a b < stirlingExponent a (a + 1 / a) :=
      hanti (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) hb
    rw [hcrit] at this
    exact this

theorem beta_infimum_core :
    (∃! δ : ℝ, 0 < δ ∧ Real.log (1 + δ) = 2 * δ / (1 + δ)) ∧
    ∀ δ : ℝ, 0 < δ → Real.log (1 + δ) = 2 * δ / (1 + δ) →
      sInf {b : ℝ | 0 < b ∧ ∃ α : ℝ, 0 < α ∧ α < b ∧ stirlingExponent α b < 0} =
        Real.sqrt δ + 1 / Real.sqrt δ := by
  refine ⟨delta_exists_unique, ?_⟩
  intro δ h0 hroot
  rw [admissible_eq h0 (root_gt_one h0 hroot) hroot]
  exact csInf_Ioi

end KingmanSubadditive.Ulam

open KingmanSubadditive.Ulam


theorem solution :
    (∃! δ : ℝ, 0 < δ ∧ Real.log (1 + δ) = 2 * δ / (1 + δ)) ∧
    ∀ δ : ℝ, 0 < δ → Real.log (1 + δ) = 2 * δ / (1 + δ) →
      sInf {b : ℝ | 0 < b ∧ ∃ α : ℝ, 0 < α ∧ α < b ∧ stirlingExponent α b < 0} =
        Real.sqrt δ + 1 / Real.sqrt δ := by
  exact beta_infimum_core

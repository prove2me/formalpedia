-- Prove2me | solution 1 for LuoSunLiu.PLBLower.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:35:00.129466+00:00
-- url     : https://prove2.me/submissions/7d0a0849-5439-4468-8a63-737b60948d59

import Mathlib
import Definitions.Def_LuoSunLiu_PLBLower_Model

open MeasureTheory

namespace RRAux_LuoSunLiu_PLBLower_proposition_2

open LuoSunLiu.PLBLower

theorem snoc_meas {Ω : Type*} [MeasurableSpace Ω] {X : Type*} [MeasurableSpace X] {n : ℕ}
    (f : Ω → Fin n → X) (g : Ω → X) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => Fin.snoc (α := fun _ => X) (f ω) (g ω)) := by
  rw [measurable_pi_iff]
  intro i
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using hg
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp hf

theorem hist_meas {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (alg : Algorithm d Ω)
    (ξ : ℕ → Fin d → ℝ) (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ)
    (hη : ∀ t, Measurable (η t)) : ∀ n, Measurable (history alg ξ 𝒜 η n)
  | 0 => measurable_of_subsingleton_codomain _
  | n + 1 => by
    have ih := hist_meas alg ξ 𝒜 η hη n
    have hdec : Measurable (fun ω => alg.decide n ω (history alg ξ 𝒜 η n ω) (𝒜 (n + 1))) :=
      (alg.measurable_decide n (𝒜 (n + 1))).comp (measurable_id.prodMk ih)
    have hdot : Measurable (fun ω => ξ (n + 1) ⬝ᵥ
        alg.decide n ω (history alg ξ 𝒜 η n ω) (𝒜 (n + 1)) + η (n + 1) ω) := by
      have hc : Measurable (fun w : Fin d → ℝ => ξ (n + 1) ⬝ᵥ w) := by fun_prop
      exact (hc.comp hdec).add (hη (n + 1))
    exact snoc_meas _ _ ih (hdec.prodMk hdot)

theorem action_meas {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (alg : Algorithm d Ω)
    (ξ : ℕ → Fin d → ℝ) (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ)
    (hη : ∀ t, Measurable (η t)) (t : ℕ) : Measurable (action alg ξ 𝒜 η t) :=
  (alg.measurable_decide (t - 1) (𝒜 t)).comp
    (measurable_id.prodMk (hist_meas alg ξ 𝒜 η hη (t - 1)))

theorem hist_congr {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (alg : Algorithm d Ω)
    (ξ ξ' : ℕ → Fin d → ℝ) (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ) :
    ∀ n, (∀ s, s ≤ n → ξ s = ξ' s) → history alg ξ 𝒜 η n = history alg ξ' 𝒜 η n
  | 0, _ => rfl
  | n + 1, h => by
    have ih := hist_congr alg ξ ξ' 𝒜 η n (fun s hs => h s (by omega))
    funext ω
    simp only [history, ih, h (n + 1) le_rfl]

theorem action_congr {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (alg : Algorithm d Ω)
    (ξ ξ' : ℕ → Fin d → ℝ) (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ) (t : ℕ)
    (h : ∀ s, s ≤ t - 1 → ξ s = ξ' s) : action alg ξ 𝒜 η t = action alg ξ' 𝒜 η t := by
  funext ω
  unfold action
  rw [hist_congr alg ξ ξ' 𝒜 η (t - 1) h]

noncomputable def Xi {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (alg : Algorithm d Ω)
    (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ) (P : Measure Ω) (a0 θ0 θ1 : Fin d → ℝ) :
    ℕ → ℕ → Fin d → ℝ
  | 0 => fun _ => θ0
  | n + 1 => Function.update (Xi alg 𝒜 η P a0 θ0 θ1 n) (n + 1)
      (if (2⁻¹ : ENNReal) ≤ P {ω | action alg (Xi alg 𝒜 η P a0 θ0 θ1 n) 𝒜 η (n + 1) ω = a0}
        then θ1 else θ0)

theorem Xi_stable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (alg : Algorithm d Ω)
    (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ) (P : Measure Ω) (a0 θ0 θ1 : Fin d → ℝ)
    (s : ℕ) : ∀ k, Xi alg 𝒜 η P a0 θ0 θ1 (s + k) s = Xi alg 𝒜 η P a0 θ0 θ1 s s
  | 0 => rfl
  | k + 1 => by
    rw [show s + (k + 1) = (s + k) + 1 by ring]
    simp only [Xi]
    rw [Function.update_of_ne (by omega)]
    exact Xi_stable alg 𝒜 η P a0 θ0 θ1 s k

theorem Xi_diag_succ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (alg : Algorithm d Ω)
    (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ) (P : Measure Ω) (a0 θ0 θ1 : Fin d → ℝ)
    (n : ℕ) : Xi alg 𝒜 η P a0 θ0 θ1 (n + 1) (n + 1) =
      (if (2⁻¹ : ENNReal) ≤ P {ω | action alg (Xi alg 𝒜 η P a0 θ0 θ1 n) 𝒜 η (n + 1) ω = a0}
        then θ1 else θ0) := by
  simp only [Xi, Function.update_self]

theorem Xi_mem {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (alg : Algorithm d Ω)
    (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ) (P : Measure Ω) (a0 θ0 θ1 : Fin d → ℝ)
    (t : ℕ) : Xi alg 𝒜 η P a0 θ0 θ1 t t = θ0 ∨ Xi alg 𝒜 η P a0 θ0 θ1 t t = θ1 := by
  cases t with
  | zero => left; rfl
  | succ n => rw [Xi_diag_succ]; split_ifs <;> simp

theorem lintegral_sum_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*}
    (s : Finset ι) (f : ι → Ω → ENNReal) :
    ∑ i ∈ s, ∫⁻ ω, f i ω ∂P ≤ ∫⁻ ω, ∑ i ∈ s, f i ω ∂P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have e : (fun ω => ∑ i ∈ insert a s, f i ω) = fun ω => f a ω + ∑ i ∈ s, f i ω := by
      funext ω; rw [Finset.sum_insert ha]
    rw [e]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

theorem step_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : Set Ω)
    (hW : MeasurableSet W) (hPW : (2⁻¹ : ENNReal) ≤ P W) (g : Ω → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (hgW : ∀ ω ∈ W, G ≤ g ω) :
    ENNReal.ofReal (G * 2⁻¹) ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂P := by
  have h1 : ∫⁻ ω, W.indicator (fun _ => ENNReal.ofReal G) ω ∂P ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂P := by
    apply lintegral_mono
    intro ω
    by_cases hω : ω ∈ W
    · rw [Set.indicator_of_mem hω]; exact ENNReal.ofReal_le_ofReal (hgW ω hω)
    · rw [Set.indicator_of_notMem hω]; exact bot_le
  rw [lintegral_indicator_const hW] at h1
  refine le_trans ?_ h1
  rw [ENNReal.ofReal_mul hG, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  exact mul_le_mul_of_nonneg_left hPW bot_le


theorem val_one (x : ℝ) (hx : 0 < x) : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'

theorem val_frac (x h : ℝ) (hh : 0 ≤ h) (hlt : h < x) :
    0 ≤ (x - h) * (x + h)⁻¹ ∧ (x - h) * (x + h)⁻¹ ≤ 1 := by
  have hp : 0 < x + h := by linarith
  constructor
  · exact mul_nonneg (by linarith) (inv_nonneg.mpr hp.le)
  · rw [← div_eq_mul_inv, div_le_one hp]; linarith

theorem gap_ge (x y Cp : ℝ) (hx : 0 < x) (hy : 0 < y) (hC : 0 ≤ Cp) (hlt : Cp / 2 < x) :
    1 / (4 * (x + y)) * Cp ≤ (1 - (x - Cp / 2) * (x + Cp / 2)⁻¹) * 2⁻¹ := by
  have hp : 0 < x + Cp / 2 := by linarith
  have e1 : (1 - (x - Cp / 2) * (x + Cp / 2)⁻¹) * 2⁻¹ = Cp / (2 * (x + Cp / 2)) := by
    field_simp; ring
  have e2 : 1 / (4 * (x + y)) * Cp = Cp / (4 * (x + y)) := by ring
  rw [e1, e2]
  apply div_le_div_of_nonneg_left hC (by linarith)
  linarith

theorem gap_nonneg (x Cp : ℝ) (hC : 0 ≤ Cp) (hlt : Cp / 2 < x) :
    0 ≤ 1 - (x - Cp / 2) * (x + Cp / 2)⁻¹ := by
  have := (val_frac x (Cp / 2) (by linarith) hlt).2; linarith

theorem half_of_not {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S T : Set Ω) (hcov : ∀ ω, ω ∈ S ∨ ω ∈ T) (hS : ¬ (2⁻¹ : ENNReal) ≤ P S) :
    (2⁻¹ : ENNReal) ≤ P T := by
  by_contra hT
  push Not at hS hT
  have h1 : P Set.univ ≤ P S + P T := by
    refine (measure_mono ?_).trans (measure_union_le S T)
    intro ω _; exact hcov ω
  rw [measure_univ] at h1
  have h2 : P S + P T < 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add hS hT
  rw [ENNReal.inv_two_add_inv_two] at h2
  exact absurd (h1.trans_lt h2) (lt_irrefl _)

end RRAux_LuoSunLiu_PLBLower_proposition_2

open LuoSunLiu.PLBLower in
open RRAux_LuoSunLiu_PLBLower_proposition_2 in
-- Proposition 2 (p. 22; restated p. 44)
theorem solution (d : ℕ) (hd : 2 ≤ d) (ξc : Fin d → ℝ) (hξc : ∀ i, 0 < ξc i) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ Cp : ℝ, 0 ≤ Cp → (∀ i, Cp / 2 < ξc i) →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : ℕ → Ω → ℝ), (∀ t, Measurable (η t)) →
      ∀ alg : Algorithm d Ω,
      ∃ (ξ : ℕ → Fin d → ℝ) (𝒜 : ℕ → Finset (Fin d → ℝ)),
        (∀ t, ξ t ∈ PB ξc Cp) ∧ IsPerturbed ξ Cp ∧
        (∀ t, (𝒜 t).Nonempty) ∧
        (∀ t, ∀ a ∈ 𝒜 t,
          (∃ j : Fin d, ∃ c : ℝ, c ≠ 0 ∧ a = Pi.single j c) ∧ |ξ t ⬝ᵥ a| ≤ 1) ∧
        ∀ T0 : ℕ, 1 ≤ T0 →
          ENNReal.ofReal (C0 * Cp * T0) ≤
            ∫⁻ ω, ENNReal.ofReal (regret alg ξ 𝒜 η T0 ω) ∂P := by
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have hne : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have hx0 := hξc i0
  have hx1 := hξc i1
  refine ⟨1 / (4 * (ξc i0 + ξc i1)), by positivity, ?_⟩
  intro Cp hC hlt Ω _ P _ η hη alg
  have hl0 := hlt i0
  have hl1 := hlt i1
  have hh : 0 ≤ Cp / 2 := by linarith
  set D : Fin d → ℝ := Pi.single i0 (Cp / 2) - Pi.single i1 (Cp / 2) with hD
  set θ0 : Fin d → ℝ := ξc + D with hθ0
  set θ1 : Fin d → ℝ := ξc - D with hθ1
  set a0 : Fin d → ℝ := Pi.single i0 (ξc i0 + Cp / 2)⁻¹ with ha0
  set a1 : Fin d → ℝ := Pi.single i1 (ξc i1 + Cp / 2)⁻¹ with ha1
  have hD0 : D i0 = Cp / 2 := by simp [hD, hne]
  have hD1 : D i1 = -(Cp / 2) := by simp [hD, hne.symm]
  have hDn : ‖D‖ ≤ Cp / 2 := by
    rw [pi_norm_le_iff_of_nonneg hh]
    intro k
    rw [Real.norm_eq_abs]
    by_cases k0 : k = i0
    · subst k0; rw [hD0, abs_of_nonneg hh]
    · by_cases k1 : k = i1
      · subst k1; rw [hD1, abs_neg, abs_of_nonneg hh]
      · simp [hD, k0, k1, hh]
  -- dot products
  have v00 : θ0 ⬝ᵥ a0 = 1 := by
    rw [ha0, dotProduct_single, hθ0, Pi.add_apply, hD0]; exact val_one _ (by linarith)
  have v01 : θ0 ⬝ᵥ a1 = (ξc i1 - Cp / 2) * (ξc i1 + Cp / 2)⁻¹ := by
    rw [ha1, dotProduct_single, hθ0, Pi.add_apply, hD1]; ring
  have v10 : θ1 ⬝ᵥ a0 = (ξc i0 - Cp / 2) * (ξc i0 + Cp / 2)⁻¹ := by
    rw [ha0, dotProduct_single, hθ1, Pi.sub_apply, hD0]
  have v11 : θ1 ⬝ᵥ a1 = 1 := by
    rw [ha1, dotProduct_single, hθ1, Pi.sub_apply, hD1, sub_neg_eq_add]
    exact val_one _ (by linarith)
  have f0 := val_frac (ξc i0) (Cp / 2) hh hl0
  have f1 := val_frac (ξc i1) (Cp / 2) hh hl1
  set 𝒜 : ℕ → Finset (Fin d → ℝ) := fun _ => {a0, a1} with h𝒜
  have hAne : ∀ t, (𝒜 t).Nonempty := fun t => ⟨a0, by simp [h𝒜]⟩
  set Ξ := Xi alg 𝒜 η P a0 θ0 θ1 with hΞ
  set ξ : ℕ → Fin d → ℝ := fun t => Ξ t t with hξ
  have hξmem : ∀ t, ξ t = θ0 ∨ ξ t = θ1 := fun t => Xi_mem alg 𝒜 η P a0 θ0 θ1 t
  have hPB : ∀ t, ξ t ∈ PB ξc Cp := by
    intro t
    show ‖ξ t - ξc‖ ≤ Cp / 2
    rcases hξmem t with h | h <;> rw [h]
    · rw [hθ0, add_sub_cancel_left]; exact hDn
    · rw [hθ1, sub_sub_cancel_left, norm_neg]; exact hDn
  have hval : ∀ t, ∀ a ∈ 𝒜 t, 0 ≤ ξ t ⬝ᵥ a ∧ ξ t ⬝ᵥ a ≤ 1 := by
    intro t a ha
    simp only [h𝒜, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases hξmem t with h | h <;> rcases ha with ha | ha <;> rw [h, ha]
    · rw [v00]; norm_num
    · rw [v01]; exact f1
    · rw [v10]; exact f0
    · rw [v11]; norm_num
  have hbest : ∀ t, bestValue ξ 𝒜 t = 1 := by
    intro t
    unfold bestValue
    rw [dif_pos (hAne t)]
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun a ha => (hval t a ha).2
    · rcases hξmem t with h | h
      · have := Finset.le_sup' (fun a => ξ t ⬝ᵥ a) (show a0 ∈ 𝒜 t by simp [h𝒜])
        refine le_trans (le_of_eq ?_) this
        show 1 = ξ t ⬝ᵥ a0
        rw [h, v00]
      · have := Finset.le_sup' (fun a => ξ t ⬝ᵥ a) (show a1 ∈ 𝒜 t by simp [h𝒜])
        refine le_trans (le_of_eq ?_) this
        show 1 = ξ t ⬝ᵥ a1
        rw [h, v11]
  have hact : ∀ t ω, action alg ξ 𝒜 η t ω = a0 ∨ action alg ξ 𝒜 η t ω = a1 := by
    intro t ω
    have := alg.decide_mem (t - 1) ω (history alg ξ 𝒜 η (t - 1) ω) (𝒜 t) (hAne t)
    unfold action
    simpa [h𝒜] using this
  -- per-step lower bound
  have hstep : ∀ t, 1 ≤ t → ENNReal.ofReal (1 / (4 * (ξc i0 + ξc i1)) * Cp) ≤
      ∫⁻ ω, ENNReal.ofReal (bestValue ξ 𝒜 t - ξ t ⬝ᵥ action alg ξ 𝒜 η t ω) ∂P := by
    intro t ht
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    have hsame : action alg ξ 𝒜 η (n + 1) = action alg (Ξ n) 𝒜 η (n + 1) := by
      apply action_congr
      intro s hs
      simp only [hξ, hΞ]
      have := Xi_stable alg 𝒜 η P a0 θ0 θ1 s (n - s)
      rw [show s + (n - s) = n by omega] at this
      exact this.symm
    have hξt : ξ (n + 1) = if (2⁻¹ : ENNReal) ≤
        P {ω | action alg (Ξ n) 𝒜 η (n + 1) ω = a0} then θ1 else θ0 :=
      Xi_diag_succ alg 𝒜 η P a0 θ0 θ1 n
    rw [← hsame] at hξt
    have hmeas := action_meas alg ξ 𝒜 η hη (n + 1)
    simp only [hbest]
    split_ifs at hξt with hP
    · -- a0 is the worse arm
      refine le_trans (ENNReal.ofReal_le_ofReal
        (gap_ge (ξc i0) (ξc i1) Cp hx0 hx1 hC hl0)) ?_
      apply step_ge P _ (hmeas (measurableSet_singleton a0)) hP _ _
        (gap_nonneg _ Cp hC hl0)
      intro ω hω
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
      rw [hω, hξt, v10]
    · have hT := half_of_not P {ω | action alg ξ 𝒜 η (n + 1) ω = a0}
        {ω | action alg ξ 𝒜 η (n + 1) ω = a1} (fun ω => hact (n + 1) ω) hP
      have hg := gap_ge (ξc i1) (ξc i0) Cp hx1 hx0 hC hl1
      rw [add_comm (ξc i1)] at hg
      refine le_trans (ENNReal.ofReal_le_ofReal hg) ?_
      apply step_ge P _ (hmeas (measurableSet_singleton a1)) hT _ _
        (gap_nonneg _ Cp hC hl1)
      intro ω hω
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
      rw [hω, hξt, v01]
  refine ⟨ξ, 𝒜, hPB, ?_, hAne, ?_, ?_⟩
  · intro s t
    have e : ξ s - ξ t = (ξ s - ξc) - (ξ t - ξc) := by abel
    rw [e]
    have h1 : ‖ξ s - ξc‖ ≤ Cp / 2 := hPB s
    have h2 : ‖ξ t - ξc‖ ≤ Cp / 2 := hPB t
    have := norm_sub_le (ξ s - ξc) (ξ t - ξc)
    linarith
  · intro t a ha
    refine ⟨?_, ?_⟩
    · simp only [h𝒜, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha
      · exact ⟨i0, _, inv_ne_zero (by linarith), ha⟩
      · exact ⟨i1, _, inv_ne_zero (by linarith), ha⟩
    · obtain ⟨h1, h2⟩ := hval t a ha
      rw [abs_le]; constructor <;> linarith
  · intro T0 hT0
    have hreg : ∀ ω, ENNReal.ofReal (regret alg ξ 𝒜 η T0 ω) =
        ∑ t ∈ Finset.Icc 1 T0,
          ENNReal.ofReal (bestValue ξ 𝒜 t - ξ t ⬝ᵥ action alg ξ 𝒜 η t ω) := by
      intro ω
      unfold regret
      apply ENNReal.ofReal_sum_of_nonneg
      intro t _
      rw [hbest]
      rcases hact t ω with h | h
      · have := (hval t a0 (by simp [h𝒜])).2; rw [h]; linarith
      · have := (hval t a1 (by simp [h𝒜])).2; rw [h]; linarith
    simp only [hreg]
    refine le_trans ?_ (lintegral_sum_ge P _ _)
    have hsum := Finset.sum_le_sum (fun t (ht : t ∈ Finset.Icc 1 T0) =>
      hstep t (Finset.mem_Icc.mp ht).1)
    refine le_trans (le_of_eq ?_) hsum
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast, mul_comm, Nat.add_sub_cancel]

#print axioms solution

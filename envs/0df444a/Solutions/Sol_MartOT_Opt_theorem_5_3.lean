-- Prove2me | solution 1 for MartOT.Opt.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T08:00:48.069026+00:00
-- url     : https://prove2.me/submissions/a407a853-e39b-4b6c-81aa-ad45a3fff9ba

import Mathlib
import Definitions.Def_MartOT_Var_Setting

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace MartOT.T53
theorem cxo_partC (v : ℕ → ℝ) : ∀ M k, k ≤ M →
    v k ≤ v 0 + ∑ i ∈ Finset.range M, max (v (i+1) - v i) 0 := by
  intro M
  induction M with
  | zero => intro k hk; rw [Nat.le_zero.1 hk]; simp
  | succ M ih =>
    intro k hk
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge k (M+1) with h | h
    · have h1 := ih k (by omega)
      have h2 := le_max_right (v (M+1) - v M) 0
      linarith
    · have hk' : k = M + 1 := by omega
      subst hk'
      have h1 := ih M le_rfl
      have h2 := le_max_left (v (M+1) - v M) 0
      linarith

theorem cxo_partA (v : ℕ → ℝ) : ∀ M, (∀ k < M, 0 ≤ v (k+1) - v k) →
    v 0 + ∑ i ∈ Finset.range M, max (v (i+1) - v i) 0 = v M := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro h
    rw [Finset.sum_range_succ, ← add_assoc, ih (fun k hk => h k (by omega)),
      max_eq_left (h M (by omega))]
    ring

theorem cxo_partB (v : ℕ → ℝ)
    (hP : ∀ k k', k < k' → v (k+1) - v k < 0 → v (k'+1) - v k' ≤ 0) : ∀ M, ∃ k ≤ M,
    v 0 + ∑ i ∈ Finset.range M, max (v (i+1) - v i) 0 = v k := by
  intro M
  induction M with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ M ih =>
    obtain ⟨k, hk, hS⟩ := ih
    rw [Finset.sum_range_succ, ← add_assoc]
    rcases le_or_gt (v (M+1) - v M) 0 with h | h
    · refine ⟨k, by omega, ?_⟩
      rw [hS, max_eq_right h, add_zero]
    · have hall : ∀ k < M, 0 ≤ v (k+1) - v k := by
        intro k' hk'
        by_contra hneg
        push Not at hneg
        have := hP k' M hk' hneg
        linarith
      refine ⟨M+1, le_rfl, ?_⟩
      rw [cxo_partA v M hall, max_eq_left h.le]
      ring


noncomputable def cxoD (φ : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin φ (Set.Ioi x) x

noncomputable def cxoT (N k : ℕ) : ℝ := ((k : ℝ) - ((N : ℝ) + 1) ^ 2) / ((N : ℝ) + 1)

noncomputable def cxoL (φ : ℝ → ℝ) (N k : ℕ) (x : ℝ) : ℝ :=
  φ (cxoT N k) + cxoD φ (cxoT N k) * (x - cxoT N k)

noncomputable def cxoPsi (φ : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  cxoL φ N 0 x + ∑ i ∈ Finset.range (2 * (N + 1) ^ 2), max (cxoL φ N (i+1) x - cxoL φ N i x) 0

theorem cxo_Dmono {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) : Monotone (cxoD φ) := by
  intro a b hab
  have h := hφ.monotoneOn_rightDeriv (by simp : a ∈ interior Set.univ)
    (by simp : b ∈ interior Set.univ) hab
  simpa [cxoD] using h

theorem cxo_sg {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (x y : ℝ) :
    φ x + cxoD φ x * (y - x) ≤ φ y := by
  rcases lt_trichotomy x y with h | h | h
  · have h1 := hφ.rightDeriv_le_slope_of_mem_interior (x := x) (y := y) (by simp)
      (Set.mem_univ _) h
    rw [slope_def_field] at h1
    have h2 : 0 < y - x := sub_pos.2 h
    rw [le_div_iff₀ h2] at h1
    simp only [cxoD]
    linarith
  · subst h; simp
  · have h1 := hφ.slope_le_leftDeriv_of_mem_interior (x := y) (y := x) (Set.mem_univ _)
      (by simp) h
    have h3 := hφ.leftDeriv_le_rightDeriv_of_mem_interior (x := x) (by simp)
    rw [slope_def_field] at h1
    have h2 : 0 < x - y := sub_pos.2 h
    rw [div_le_iff₀ h2] at h1
    have h4 := mul_le_mul_of_nonneg_right h3 h2.le
    simp only [cxoD]
    nlinarith

theorem cxo_T_mono (N : ℕ) {k k' : ℕ} (h : k ≤ k') : cxoT N k ≤ cxoT N k' := by
  unfold cxoT
  have : (k : ℝ) ≤ k' := by exact_mod_cast h
  gcongr

theorem cxo_T_zero (N : ℕ) : cxoT N ((N + 1) ^ 2) = 0 := by
  unfold cxoT
  push_cast
  simp

theorem cxo_e_nonneg {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {a b x : ℝ} (hab : a ≤ b)
    (hbx : b ≤ x) :
    0 ≤ (φ b + cxoD φ b * (x - b)) - (φ a + cxoD φ a * (x - a)) := by
  have h1 := cxo_sg hφ a b
  have h2 := mul_nonneg (sub_nonneg.2 (cxo_Dmono hφ hab)) (sub_nonneg.2 hbx)
  nlinarith

theorem cxo_e_nonpos {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {a b x : ℝ} (hab : a ≤ b)
    (hxa : x ≤ a) :
    (φ b + cxoD φ b * (x - b)) - (φ a + cxoD φ a * (x - a)) ≤ 0 := by
  have h1 := cxo_sg hφ b a
  have h2 := mul_nonneg (sub_nonneg.2 (cxo_Dmono hφ hab)) (sub_nonneg.2 hxa)
  nlinarith

theorem cxo_psi_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (N : ℕ) (x : ℝ) :
    cxoPsi φ N x ≤ φ x := by
  have hP : ∀ k k', k < k' → cxoL φ N (k+1) x - cxoL φ N k x < 0 →
      cxoL φ N (k'+1) x - cxoL φ N k' x ≤ 0 := by
    intro k k' hkk' hneg
    have hlt : x < cxoT N (k+1) := by
      by_contra hc
      push Not at hc
      have := cxo_e_nonneg hφ (cxo_T_mono N (Nat.le_succ k)) hc
      unfold cxoL at hneg
      linarith
    have hle : x ≤ cxoT N k' := hlt.le.trans (cxo_T_mono N (by omega))
    have := cxo_e_nonpos hφ (cxo_T_mono N (Nat.le_succ k')) hle
    unfold cxoL
    linarith
  obtain ⟨k, _, hk⟩ := cxo_partB (fun k => cxoL φ N k x) hP (2 * (N + 1) ^ 2)
  unfold cxoPsi
  rw [hk]
  exact cxo_sg hφ _ _

theorem cxo_psi_ge {φ : ℝ → ℝ} (N : ℕ) (x : ℝ) :
    φ 0 + cxoD φ 0 * x ≤ cxoPsi φ N x := by
  have h := cxo_partC (fun k => cxoL φ N k x) (2 * (N + 1) ^ 2) ((N + 1) ^ 2) (by nlinarith)
  unfold cxoPsi
  refine le_trans (le_of_eq ?_) h
  simp only [cxoL, cxo_T_zero, sub_zero]

theorem cxo_psi_cont (φ : ℝ → ℝ) (N : ℕ) : Continuous (cxoPsi φ N) := by
  unfold cxoPsi cxoL
  fun_prop

theorem cxo_psi_form (φ : ℝ → ℝ) (N : ℕ) (z : ℝ) :
    cxoPsi φ N z = (φ (cxoT N 0) - cxoD φ (cxoT N 0) * cxoT N 0) + cxoD φ (cxoT N 0) * z +
      ∑ k ∈ Finset.range (2 * (N + 1) ^ 2),
        max ((cxoD φ (cxoT N (k+1)) - cxoD φ (cxoT N k)) * z +
          (φ (cxoT N (k+1)) - cxoD φ (cxoT N (k+1)) * cxoT N (k+1) - φ (cxoT N k) +
            cxoD φ (cxoT N k) * cxoT N k)) 0 := by
  unfold cxoPsi cxoL
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    ring

theorem cxo_psi_tendsto {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (x : ℝ) :
    Tendsto (fun N => cxoPsi φ N x) atTop (𝓝 (φ x)) := by
  have hc : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  set j : ℕ → ℕ := fun N => ⌊x * ((N : ℝ) + 1) + ((N : ℝ) + 1) ^ 2⌋₊ with hj
  have hev : ∀ᶠ N : ℕ in atTop, |x| < (N : ℝ) + 1 := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop |x|] with N hN
    linarith
  have hpos : ∀ N : ℕ, (0 : ℝ) < (N : ℝ) + 1 := fun N => by positivity
  -- basic floor facts
  have hfacts : ∀ᶠ N : ℕ in atTop, cxoT N (j N) ≤ x ∧ x - 1 / ((N : ℝ) + 1) < cxoT N (j N) ∧
      j N ≤ 2 * (N + 1) ^ 2 := by
    filter_upwards [hev] with N hN
    have hx1 : -((N : ℝ) + 1) < x := by linarith [neg_abs_le x]
    have hx2 : x < (N : ℝ) + 1 := by linarith [le_abs_self x]
    have ha : 0 ≤ x * ((N : ℝ) + 1) + ((N : ℝ) + 1) ^ 2 := by nlinarith [hpos N]
    have hfl := Nat.floor_le ha
    have hfl2 := Nat.lt_floor_add_one (x * ((N : ℝ) + 1) + ((N : ℝ) + 1) ^ 2)
    refine ⟨?_, ?_, ?_⟩
    · simp only [cxoT, hj]
      rw [div_le_iff₀ (hpos N)]
      linarith
    · simp only [cxoT, hj]
      rw [lt_div_iff₀ (hpos N), sub_mul, div_mul_cancel₀ _ (hpos N).ne']
      linarith
    · have : ((j N : ℕ) : ℝ) ≤ ((2 * (N + 1) ^ 2 : ℕ) : ℝ) := by
        push_cast
        simp only [hj]
        nlinarith [hpos N]
      exact_mod_cast this
  have hτ : Tendsto (fun N => cxoT N (j N)) atTop (𝓝 x) := by
    have hlow : Tendsto (fun N : ℕ => x - 1 / ((N : ℝ) + 1)) atTop (𝓝 x) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub x
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hfacts] with N hN
      exact hN.2.1.le
    · filter_upwards [hfacts] with N hN
      exact hN.1
  have hglow : Tendsto (fun N => φ (cxoT N (j N)) + cxoD φ (x - 1) * (x - cxoT N (j N)))
      atTop (𝓝 (φ x)) := by
    have h1 := (hc.tendsto x).comp hτ
    have h2 : Tendsto (fun N => cxoD φ (x - 1) * (x - cxoT N (j N))) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := x)).sub hτ
      simpa using this.const_mul (cxoD φ (x - 1))
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hglow tendsto_const_nhds ?_ ?_
  · filter_upwards [hfacts] with N hN
    obtain ⟨h1, h2, h3⟩ := hN
    have hC := cxo_partC (fun k => cxoL φ N k x) (2 * (N + 1) ^ 2) (j N) h3
    have hin : x - 1 ≤ cxoT N (j N) := by
      have : 1 / ((N : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (hpos N)]
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith
      linarith
    have hD := cxo_Dmono hφ hin
    have hm := mul_le_mul_of_nonneg_right hD (sub_nonneg.2 h1)
    have : cxoL φ N (j N) x ≥ φ (cxoT N (j N)) + cxoD φ (x - 1) * (x - cxoT N (j N)) := by
      unfold cxoL
      linarith
    unfold cxoPsi
    linarith
  · exact Eventually.of_forall fun N => cxo_psi_le hφ N x


lemma integralE_eq_coe {X : Type*} [MeasurableSpace X] (m : Measure X) (f : X → ℝ)
    (hf : Integrable f m) : MartOT.Var.integralE m f = ((∫ x, f x ∂m : ℝ) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have e1 : ∀ x, ((f x : ℝ) : EReal).toENNReal = ENNReal.ofReal (max (f x) 0) := fun x => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  have e2 : ∀ x, (-((f x : ℝ) : EReal)).toENNReal = ENNReal.ofReal (max (-f x) 0) := fun x => by
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rcases le_total 0 (-f x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  simp_rw [e1, e2]
  rw [← ofReal_integral_eq_lintegral_ofReal hf.pos_part (Filter.Eventually.of_forall
      (fun x => le_max_right _ _)),
    ← ofReal_integral_eq_lintegral_ofReal (show Integrable (fun x => max (-f x) 0) m from hf.neg.pos_part) (Filter.Eventually.of_forall
      (fun x => le_max_right _ _)),
    EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
    max_eq_left (integral_nonneg (fun x => le_max_right (f x) 0)),
    max_eq_left (integral_nonneg (fun x => le_max_right (-f x) 0)), ← EReal.coe_sub]
  congr 1
  rw [← integral_sub hf.pos_part (show Integrable (fun x => max (-f x) 0) m from hf.neg.pos_part)]
  congr 1
  ext x
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

theorem hinge_fin (m1 m2 : Measure ℝ) (hmass : m1.real Set.univ = m2.real Set.univ)
    (hsl : ∀ a : ℝ, ∫ x, max (x - a) 0 ∂m1 ≤ ∫ x, max (x - a) 0 ∂m2)
    (γ δ : ℝ) (hγ : 0 ≤ γ) :
    ∫ x, max (γ * x + δ) 0 ∂m1 ≤ ∫ x, max (γ * x + δ) 0 ∂m2 := by
  rcases hγ.eq_or_lt with h | h
  · subst h
    simp only [zero_mul, zero_add, integral_const, smul_eq_mul, hmass, le_refl]
  · have key : ∀ z : ℝ, max (γ * z + δ) 0 = γ * max (z - (-δ / γ)) 0 := by
      intro z
      rw [mul_max_of_nonneg _ _ h.le, mul_zero]
      congr 1
      field_simp
      ring
    simp_rw [key]
    rw [integral_const_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hsl _) h.le

theorem gen_fin (m1 m2 : Measure ℝ) [IsFiniteMeasure m1] [IsFiniteMeasure m2]
    (hmass : m1.real Set.univ = m2.real Set.univ)
    (hX : Integrable (fun x : ℝ => x) m1) (hY : Integrable (fun x : ℝ => x) m2)
    (hmean : ∫ x, x ∂m1 = ∫ x, x ∂m2)
    (hsl : ∀ a : ℝ, ∫ x, max (x - a) 0 ∂m1 ≤ ∫ x, max (x - a) 0 ∂m2)
    (ψ : ℝ → ℝ) (A B : ℝ) (s : Finset ℕ) (γ δ : ℕ → ℝ) (hγ : ∀ k, 0 ≤ γ k)
    (hψ : ∀ z, ψ z = A + B * z + ∑ k ∈ s, max (γ k * z + δ k) 0) :
    ∫ x, ψ x ∂m1 ≤ ∫ x, ψ x ∂m2 := by
  simp_rw [hψ]
  have iX : ∀ k, Integrable (fun x : ℝ => max (γ k * x + δ k) 0) m1 := fun k =>
    ((hX.const_mul (γ k)).add (integrable_const (δ k))).pos_part
  have iY : ∀ k, Integrable (fun x : ℝ => max (γ k * x + δ k) 0) m2 := fun k =>
    ((hY.const_mul (γ k)).add (integrable_const (δ k))).pos_part
  have iAX : Integrable (fun x : ℝ => A + B * x) m1 := (integrable_const A).add (hX.const_mul B)
  have iAY : Integrable (fun x : ℝ => A + B * x) m2 := (integrable_const A).add (hY.const_mul B)
  have iSX : Integrable (fun x : ℝ => ∑ k ∈ s, max (γ k * x + δ k) 0) m1 :=
    integrable_finsetSum s fun k _ => iX k
  have iSY : Integrable (fun x : ℝ => ∑ k ∈ s, max (γ k * x + δ k) 0) m2 :=
    integrable_finsetSum s fun k _ => iY k
  have iBX : Integrable (fun x : ℝ => B * x) m1 := hX.const_mul B
  have iBY : Integrable (fun x : ℝ => B * x) m2 := hY.const_mul B
  rw [integral_add iAX iSX, integral_add iAY iSY,
    integral_add (integrable_const A) iBX, integral_add (integrable_const A) iBY,
    integral_const_mul, integral_const_mul, integral_finsetSum s fun k _ => iX k,
    integral_finsetSum s fun k _ => iY k, hmean]
  simp only [integral_const, smul_eq_mul, hmass]
  exact add_le_add le_rfl (Finset.sum_le_sum fun k _ => hinge_fin m1 m2 hmass hsl (γ k) (δ k) (hγ k))

noncomputable def lin (φ : ℝ → ℝ) (x : ℝ) : ℝ := φ 0 + cxoD φ 0 * x

theorem lin_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (x : ℝ) : lin φ x ≤ φ x := by
  have := cxo_sg hφ 0 x
  simp only [sub_zero] at this
  exact this

theorem lin_cont (φ : ℝ → ℝ) : Continuous (lin φ) := by
  unfold lin; fun_prop

theorem lin_int (φ : ℝ → ℝ) (m : Measure ℝ) [IsFiniteMeasure m]
    (h : Integrable (fun x : ℝ => x) m) : Integrable (lin φ) m :=
  (integrable_const _).add (h.const_mul _)

theorem psi_int (φ : ℝ → ℝ) (N : ℕ) (m : Measure ℝ) [IsFiniteMeasure m]
    (h : Integrable (fun x : ℝ => x) m) : Integrable (cxoPsi φ N) m := by
  have e : cxoPsi φ N = fun z => (φ (cxoT N 0) - cxoD φ (cxoT N 0) * cxoT N 0) +
      cxoD φ (cxoT N 0) * z + ∑ k ∈ Finset.range (2 * (N + 1) ^ 2),
        max ((cxoD φ (cxoT N (k+1)) - cxoD φ (cxoT N k)) * z +
          (φ (cxoT N (k+1)) - cxoD φ (cxoT N (k+1)) * cxoT N (k+1) - φ (cxoT N k) +
            cxoD φ (cxoT N k) * cxoT N k)) 0 := funext (cxo_psi_form φ N)
  rw [e]
  exact ((integrable_const _).add (h.const_mul _)).add
    (integrable_finsetSum _ fun k _ => ((h.const_mul _).add (integrable_const _)).pos_part)

theorem lint_le (m1 m2 : Measure ℝ) [IsFiniteMeasure m1] [IsFiniteMeasure m2]
    (hmass : m1.real Set.univ = m2.real Set.univ)
    (h1 : Integrable (fun x : ℝ => x) m1) (h2 : Integrable (fun x : ℝ => x) m2)
    (hmean : ∫ x, x ∂m1 = ∫ x, x ∂m2)
    (hsl : ∀ a : ℝ, ∫ x, max (x - a) 0 ∂m1 ≤ ∫ x, max (x - a) 0 ∂m2)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) :
    ∫⁻ x, ENNReal.ofReal (φ x - lin φ x) ∂m1 ≤ ∫⁻ x, ENNReal.ofReal (φ x - lin φ x) ∂m2 := by
  have hlin : ∫ x, lin φ x ∂m1 = ∫ x, lin φ x ∂m2 := by
    unfold lin
    rw [integral_add (integrable_const _) (h1.const_mul _),
      integral_add (integrable_const _) (h2.const_mul _), integral_const, integral_const,
      integral_const_mul, integral_const_mul, hmass, hmean]
  have key : ∀ N, ∫⁻ x, ENNReal.ofReal (cxoPsi φ N x - lin φ x) ∂m1 ≤
      ∫⁻ x, ENNReal.ofReal (cxoPsi φ N x - lin φ x) ∂m2 := by
    intro N
    have i1 : Integrable (fun x => cxoPsi φ N x - lin φ x) m1 :=
      (psi_int φ N m1 h1).sub (lin_int φ m1 h1)
    have i2 : Integrable (fun x => cxoPsi φ N x - lin φ x) m2 :=
      (psi_int φ N m2 h2).sub (lin_int φ m2 h2)
    rw [← ofReal_integral_eq_lintegral_ofReal i1
        (Eventually.of_forall fun x => sub_nonneg.2 (cxo_psi_ge N x)),
      ← ofReal_integral_eq_lintegral_ofReal i2
        (Eventually.of_forall fun x => sub_nonneg.2 (cxo_psi_ge N x))]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sub (psi_int φ N m1 h1) (lin_int φ m1 h1),
      integral_sub (psi_int φ N m2 h2) (lin_int φ m2 h2), hlin]
    have := gen_fin m1 m2 hmass h1 h2 hmean hsl (cxoPsi φ N) _ _ _ _ _
      (fun k => sub_nonneg.2 (cxo_Dmono hφ (cxo_T_mono N (Nat.le_succ k)))) (cxo_psi_form φ N)
    linarith
  calc ∫⁻ x, ENNReal.ofReal (φ x - lin φ x) ∂m1
      = ∫⁻ x, liminf (fun N => ENNReal.ofReal (cxoPsi φ N x - lin φ x)) atTop ∂m1 := by
        refine lintegral_congr fun x => ?_
        exact (((ENNReal.continuous_ofReal.tendsto _).comp
          ((cxo_psi_tendsto hφ x).sub_const (lin φ x))).liminf_eq).symm
    _ ≤ liminf (fun N => ∫⁻ x, ENNReal.ofReal (cxoPsi φ N x - lin φ x) ∂m1) atTop :=
        lintegral_liminf_le fun N =>
          ((cxo_psi_cont φ N).measurable.sub (lin_cont φ).measurable).ennreal_ofReal
    _ ≤ liminf (fun N => ∫⁻ x, ENNReal.ofReal (cxoPsi φ N x - lin φ x) ∂m2) atTop :=
        liminf_le_liminf (Eventually.of_forall key)
    _ ≤ ∫⁻ x, ENNReal.ofReal (φ x - lin φ x) ∂m2 := by
        refine liminf_le_of_frequently_le' (Eventually.of_forall fun N => ?_).frequently
        exact lintegral_mono fun x =>
          ENNReal.ofReal_le_ofReal (by linarith [cxo_psi_le hφ N x])

theorem integralE_top (m : Measure ℝ) [IsFiniteMeasure m]
    (h : Integrable (fun x : ℝ => x) m) {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (hn : ¬ Integrable φ m) : MartOT.Var.integralE m φ = ⊤ := by
  have hc : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have e1 : ∀ x, ((φ x : ℝ) : EReal).toENNReal = ENNReal.ofReal (max (φ x) 0) := fun x => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rcases le_total 0 (φ x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  have e2 : ∀ x, (-((φ x : ℝ) : EReal)).toENNReal = ENNReal.ofReal (max (-φ x) 0) := fun x => by
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rcases le_total 0 (-φ x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  simp_rw [e1, e2]
  have hli := (lin_int φ m h).abs
  have hQ : ∫⁻ x, ENNReal.ofReal (max (-φ x) 0) ∂m ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_)
      hli.lintegral_lt_top)
    have := lin_le hφ x
    exact max_le (by linarith [le_abs_self (lin φ x), neg_abs_le (lin φ x)]) (abs_nonneg _)
  have hP : ∫⁻ x, ENNReal.ofReal (max (φ x) 0) ∂m = ⊤ := by
    by_contra hP
    apply hn
    have ip : Integrable (fun x => max (φ x) 0) m :=
      ⟨(hc.max continuous_const).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => le_max_right _ _)).2
          (lt_top_iff_ne_top.2 hP)⟩
    refine (ip.add hli).mono' hc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have := lin_le hφ x
    show ‖φ x‖ ≤ max (φ x) 0 + |lin φ x|
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [le_max_right (φ x) 0, neg_abs_le (lin φ x)]
    · linarith [le_max_left (φ x) 0, abs_nonneg (lin φ x)]
  rw [hP, ← EReal.coe_ennreal_toReal hQ, EReal.coe_ennreal_top, EReal.top_sub_coe]

/-- Stop-loss order with equal mass and mean gives the convex order in the `integralE` sense. -/
theorem cx_of_stoploss (m1 m2 : Measure ℝ) [IsFiniteMeasure m1] [IsFiniteMeasure m2]
    (hmass : m1.real Set.univ = m2.real Set.univ)
    (h1 : Integrable (fun x : ℝ => x) m1) (h2 : Integrable (fun x : ℝ => x) m2)
    (hmean : ∫ x, x ∂m1 = ∫ x, x ∂m2)
    (hsl : ∀ a : ℝ, ∫ x, max (x - a) 0 ∂m1 ≤ ∫ x, max (x - a) 0 ∂m2)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    MartOT.Var.integralE m1 φ ≤ MartOT.Var.integralE m2 φ := by
  have hc : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  by_cases hi2 : Integrable φ m2
  swap
  · rw [integralE_top m2 h2 hφ hi2]; exact le_top
  have hL := lint_le m1 m2 hmass h1 h2 hmean hsl hφ
  have hd2 : Integrable (fun x => φ x - lin φ x) m2 := hi2.sub (lin_int φ m2 h2)
  have hnn : ∀ x, 0 ≤ φ x - lin φ x := fun x => sub_nonneg.2 (lin_le hφ x)
  have hF2 := (hasFiniteIntegral_iff_ofReal (ae_of_all m2 hnn)).1 hd2.2
  have hd1 : Integrable (fun x => φ x - lin φ x) m1 :=
    ⟨(hc.sub (lin_cont φ)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all m1 hnn)).2 (lt_of_le_of_lt hL hF2)⟩
  have hi1 : Integrable φ m1 := by
    exact (hd1.add (lin_int φ m1 h1)).congr
      (ae_of_all _ fun x => by simp only [Pi.add_apply, sub_add_cancel])
  rw [integralE_eq_coe m1 φ hi1, integralE_eq_coe m2 φ hi2, EReal.coe_le_coe_iff]
  have hlin : ∫ x, lin φ x ∂m1 = ∫ x, lin φ x ∂m2 := by
    unfold lin
    rw [integral_add (integrable_const _) (h1.const_mul _),
      integral_add (integrable_const _) (h2.const_mul _), integral_const, integral_const,
      integral_const_mul, integral_const_mul, hmass, hmean]
  have s1 : ∫ x, φ x ∂m1 = ∫ x, (φ x - lin φ x) ∂m1 + ∫ x, lin φ x ∂m1 := by
    rw [← integral_add hd1 (lin_int φ m1 h1)]; simp
  have s2 : ∫ x, φ x ∂m2 = ∫ x, (φ x - lin φ x) ∂m2 + ∫ x, lin φ x ∂m2 := by
    rw [← integral_add hd2 (lin_int φ m2 h2)]; simp
  rw [s1, s2, hlin, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn)
      (hc.sub (lin_cont φ)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) (hc.sub (lin_cont φ)).aestronglyMeasurable]
  gcongr
  exact hF2.ne


/-- Call-price (stop-loss) function `k ↦ ∫ (y - k)⁺ dρ`. -/
noncomputable def sl (ρ : Measure ℝ) (k : ℝ) : ℝ := ∫ y, max (y - k) 0 ∂ρ

/-- Put-price function `k ↦ ∫ (k - y)⁺ dρ`. -/
noncomputable def pl (ρ : Measure ℝ) (k : ℝ) : ℝ := ∫ y, max (k - y) 0 ∂ρ

theorem hinge_int (ρ : Measure ℝ) [IsFiniteMeasure ρ] (h : Integrable (fun x : ℝ => x) ρ) (k : ℝ) :
    Integrable (fun y : ℝ => max (y - k) 0) ρ :=
  (h.sub (integrable_const k)).pos_part

theorem put_int (ρ : Measure ℝ) [IsFiniteMeasure ρ] (h : Integrable (fun x : ℝ => x) ρ) (k : ℝ) :
    Integrable (fun y : ℝ => max (k - y) 0) ρ :=
  ((integrable_const k).sub h).pos_part

theorem sl_eq_pl (ρ : Measure ℝ) [IsFiniteMeasure ρ] (h : Integrable (fun x : ℝ => x) ρ) (k : ℝ) :
    sl ρ k = pl ρ k + (∫ y, y ∂ρ - ρ.real Set.univ * k) := by
  unfold sl pl
  have e : ∀ y : ℝ, max (y - k) 0 = max (k - y) 0 + (y - k) := fun y => by
    rcases le_total y k with hy | hy
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  simp_rw [e]
  rw [integral_add (put_int ρ h k) (show Integrable (fun y : ℝ => y - k) ρ from h.sub (integrable_const k)),
    integral_sub h (integrable_const k),
    integral_const, smul_eq_mul]

theorem sl_lip (ρ : Measure ℝ) [IsFiniteMeasure ρ] (h : Integrable (fun x : ℝ => x) ρ) (k k' : ℝ) :
    |sl ρ k - sl ρ k'| ≤ ρ.real Set.univ * |k - k'| := by
  unfold sl
  rw [← integral_sub (hinge_int ρ h k) (hinge_int ρ h k')]
  have := norm_integral_le_of_norm_le_const (μ := ρ)
    (f := fun y : ℝ => max (y - k) 0 - max (y - k') 0) (C := |k - k'|)
    (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      calc |max (y - k) 0 - max (y - k') 0| ≤ |(y - k) - (y - k')| := abs_max_sub_max_le_abs _ _ _
        _ = |k - k'| := by rw [show (y - k) - (y - k') = -(k - k') by ring, abs_neg])
  rw [Real.norm_eq_abs] at this
  linarith

theorem sl_cont (ρ : Measure ℝ) [IsFiniteMeasure ρ] (h : Integrable (fun x : ℝ => x) ρ) :
    Continuous (sl ρ) := by
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (ρ.real Set.univ)) fun k k' => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ measureReal_nonneg]
  exact sl_lip ρ h k k'

theorem sl_tendsto (ρ : Measure ℝ) [IsFiniteMeasure ρ] (h : Integrable (fun x : ℝ => x) ρ) :
    Tendsto (sl ρ) atTop (𝓝 0) := by
  have : Tendsto (fun k => ∫ y, max (y - k) 0 ∂ρ) atTop (𝓝 (∫ y, (0 : ℝ) ∂ρ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => |y|)
      (Eventually.of_forall fun k => (hinge_int ρ h k).aestronglyMeasurable) ?_ h.abs ?_
    · filter_upwards [eventually_ge_atTop 0] with k hk
      refine ae_of_all _ fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self y]) (abs_nonneg y)
    · refine ae_of_all _ fun y => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop y] with k hk
      rw [max_eq_right (by linarith)]
  rw [integral_zero] at this
  exact this

theorem pl_tendsto (ρ : Measure ℝ) [IsFiniteMeasure ρ] (h : Integrable (fun x : ℝ => x) ρ) :
    Tendsto (pl ρ) atBot (𝓝 0) := by
  have : Tendsto (fun k => ∫ y, max (k - y) 0 ∂ρ) atBot (𝓝 (∫ y, (0 : ℝ) ∂ρ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => |y|)
      (Eventually.of_forall fun k => (put_int ρ h k).aestronglyMeasurable) ?_ h.abs ?_
    · filter_upwards [eventually_le_atBot 0] with k hk
      refine ae_of_all _ fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [neg_abs_le y]) (abs_nonneg y)
    · refine ae_of_all _ fun y => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_le_atBot y] with k hk
      rw [max_eq_right (by linarith)]
  rw [integral_zero] at this
  exact this

/-- Maximum principle for call-price differences. If `η1 + θ = η2 + ζ`, `η1, η2` have equal mass and
mean, `θ` vanishes on open intervals inside the open set `O`, and `sl η1 ≤ sl η2` off `O`, then
`sl η1 ≤ sl η2` everywhere. -/
theorem maxprinciple (η1 η2 ζ θ : Measure ℝ) [IsFiniteMeasure η1] [IsFiniteMeasure η2]
    [IsFiniteMeasure ζ] [IsFiniteMeasure θ]
    (h1 : Integrable (fun x : ℝ => x) η1) (h2 : Integrable (fun x : ℝ => x) η2)
    (hz : Integrable (fun x : ℝ => x) ζ) (ht : Integrable (fun x : ℝ => x) θ)
    (hmass : η1.real Set.univ = η2.real Set.univ) (hmean : ∫ y, y ∂η1 = ∫ y, y ∂η2)
    (hsum : η1 + θ = η2 + ζ) (O : Set ℝ) (hO : IsOpen O)
    (hθO : ∀ a b, Set.Ioo a b ⊆ O → θ (Set.Ioo a b) = 0)
    (hoff : ∀ k, k ∉ O → sl η1 k ≤ sl η2 k) : ∀ k, sl η1 k ≤ sl η2 k := by
  set f : ℝ → ℝ := fun k => sl η1 k - sl η2 k with hf
  have hfc : Continuous f := (sl_cont η1 h1).sub (sl_cont η2 h2)
  have hfeq : ∀ k, f k = sl ζ k - sl θ k := by
    intro k
    have e : ∫ y, max (y - k) 0 ∂(η1 + θ) = ∫ y, max (y - k) 0 ∂(η2 + ζ) := by rw [hsum]
    rw [integral_add_measure (hinge_int η1 h1 k) (hinge_int θ ht k),
      integral_add_measure (hinge_int η2 h2 k) (hinge_int ζ hz k)] at e
    show sl η1 k - sl η2 k = sl ζ k - sl θ k
    unfold sl
    linarith
  have htop : Tendsto f atTop (𝓝 0) := by
    simpa using (sl_tendsto η1 h1).sub (sl_tendsto η2 h2)
  have hbot : Tendsto f atBot (𝓝 0) := by
    have e : ∀ k, f k = pl η1 k - pl η2 k := fun k => by
      show sl η1 k - sl η2 k = _; rw [sl_eq_pl η1 h1, sl_eq_pl η2 h2, hmass, hmean]; ring
    have := (pl_tendsto η1 h1).sub (pl_tendsto η2 h2)
    rw [sub_zero] at this
    exact this.congr fun k => (e k).symm
  intro k0
  by_contra hk0
  have hpos : 0 < f k0 := by show 0 < sl η1 k0 - sl η2 k0; linarith [not_le.1 hk0]
  obtain ⟨R1, hR1⟩ := eventually_atTop.1 ((tendsto_order.1 htop).2 _ hpos)
  obtain ⟨R2, hR2⟩ := eventually_atBot.1 ((tendsto_order.1 hbot).2 _ hpos)
  set a := min R2 k0
  set b := max R1 k0
  have hk0ab : k0 ∈ Set.Icc a b := ⟨min_le_right _ _, le_max_right _ _⟩
  obtain ⟨c, hcab, hcmax⟩ := isCompact_Icc.exists_isMaxOn ⟨k0, hk0ab⟩ hfc.continuousOn
  set M := f c
  have hM0 : f k0 ≤ M := hcmax hk0ab
  have hout : ∀ k, k ∉ Set.Icc a b → f k < f k0 := by
    intro k hk
    rcases not_and_or.1 hk with h | h
    · exact hR2 k (le_trans (le_of_lt (not_le.1 h)) (min_le_left _ _))
    · exact hR1 k (le_trans (le_max_left _ _) (le_of_lt (not_le.1 h)))
  have hglob : ∀ k, f k ≤ M := by
    intro k
    by_cases hk : k ∈ Set.Icc a b
    · exact hcmax hk
    · exact le_trans (le_of_lt (hout k hk)) hM0
  set K := Set.Icc a b ∩ f ⁻¹' {M}
  have hKc : IsCompact K := isCompact_Icc.inter_right (isClosed_singleton.preimage hfc)
  have hKne : K.Nonempty := ⟨c, hcab, rfl⟩
  set ks := sSup K
  have hks : ks ∈ K := hKc.sSup_mem hKne
  have hfks : f ks = M := hks.2
  have hksO : ks ∈ O := by
    by_contra hn
    have := hoff ks hn
    have : f ks ≤ 0 := by show sl η1 ks - sl η2 ks ≤ 0; linarith
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO ks hksO
  rw [Real.ball_eq_Ioo] at hball
  obtain ⟨hh, hh0, hhε⟩ : ∃ hh : ℝ, 0 < hh ∧ hh < ε := ⟨ε / 2, by positivity, by linarith⟩
  have hnull : θ (Set.Ioo (ks - hh) (ks + hh)) = 0 :=
    measure_mono_null (Set.Ioo_subset_Ioo (by linarith) (by linarith)) (hθO _ _ hball)
  have hae : ∀ᵐ y ∂θ, y ∉ Set.Ioo (ks - hh) (ks + hh) := by
    have e : {a | ¬ a ∉ Set.Ioo (ks - hh) (ks + hh)} = Set.Ioo (ks - hh) (ks + hh) := by
      ext; simp
    rw [ae_iff, e]; exact hnull
  -- θ: midpoint affine
  have hθmid : sl θ (ks - hh) + sl θ (ks + hh) = 2 * sl θ ks := by
    unfold sl
    rw [← integral_add (hinge_int θ ht _) (hinge_int θ ht _), ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rcases le_or_gt y (ks - hh) with h | h
    · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; ring
    · have : ks + hh ≤ y := by
        by_contra hc
        exact hy ⟨h, not_le.1 hc⟩
      rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  have hζmid : 2 * sl ζ ks ≤ sl ζ (ks - hh) + sl ζ (ks + hh) := by
    unfold sl
    rw [← integral_add (hinge_int ζ hz _) (hinge_int ζ hz _), ← integral_const_mul]
    refine integral_mono ((hinge_int ζ hz _).const_mul 2)
      ((hinge_int ζ hz _).add (hinge_int ζ hz _)) fun y => ?_
    have a1 := le_max_left (y - (ks - hh)) 0
    have a2 := le_max_right (y - (ks - hh)) 0
    have a3 := le_max_left (y - (ks + hh)) 0
    have a4 := le_max_right (y - (ks + hh)) 0
    show 2 * max (y - ks) 0 ≤ max (y - (ks - hh)) 0 + max (y - (ks + hh)) 0
    rcases le_total (y - ks) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hmid : 2 * f ks ≤ f (ks - hh) + f (ks + hh) := by
    rw [hfeq, hfeq, hfeq]; linarith
  have hright : f (ks + hh) < M := by
    rcases lt_or_eq_of_le (hglob (ks + hh)) with h | h
    · exact h
    · exfalso
      have hin : ks + hh ∈ Set.Icc a b := by
        by_contra hn
        have := hout _ hn
        linarith
      have hK : ks + hh ∈ K := ⟨hin, h⟩
      have := le_csSup hKc.bddAbove hK
      linarith
  linarith [hglob (ks - hh)]


theorem mart_set (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hmart : ∀ ρ : ℝ → ℝ, Measurable ρ → (∃ C, ∀ x, |ρ x| ≤ C) →
      ∫ p, ρ p.1 * (p.2 - p.1) ∂π = 0)
    (S : Set ℝ) (hS : MeasurableSet S) : ∫ p in S ×ˢ Set.univ, (p.2 - p.1) ∂π = 0 := by
  have h := hmart (S.indicator fun _ => (1 : ℝ)) (measurable_const.indicator hS) ⟨1, fun x => by
    by_cases hx : x ∈ S <;> simp [hx]⟩
  rw [← integral_indicator (hS.prod MeasurableSet.univ), ← h]
  congr 1
  ext p
  by_cases hp : p.1 ∈ S <;> simp [Set.indicator, hp, Set.mem_prod]

theorem ind_zero (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hmart : ∀ ρ : ℝ → ℝ, Measurable ρ → (∃ C, ∀ x, |ρ x| ≤ C) →
      ∫ p, ρ p.1 * (p.2 - p.1) ∂π = 0) (t k : ℝ) :
    ∫ p, (Set.Ioi k ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => p.2 - p.1) p
      ∂(π.restrict (Set.Iic t ×ˢ Set.univ)) = 0 := by
  rw [integral_indicator (measurableSet_Ioi.prod MeasurableSet.univ),
    Measure.restrict_restrict (measurableSet_Ioi.prod MeasurableSet.univ), Set.prod_inter_prod,
    Set.univ_inter]
  exact mart_set π hmart _ (measurableSet_Ioi.inter measurableSet_Iic)

theorem hinge_ineq (p : ℝ × ℝ) (a : ℝ) :
    max (p.1 - a) 0 + (Set.Ioi a ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => p.2 - p.1) p ≤
      max (p.2 - a) 0 := by
  rw [Set.indicator_apply]
  by_cases hp : a < p.1
  · rw [if_pos (show p ∈ Set.Ioi a ×ˢ Set.univ from ⟨hp, trivial⟩), max_eq_left (by linarith)]
    linarith [le_max_left (p.2 - a) 0]
  · rw [if_neg (show p ∉ Set.Ioi a ×ˢ Set.univ from fun h => hp h.1),
      max_eq_right (by linarith [not_lt.1 hp])]
    linarith [le_max_right (p.2 - a) 0]

theorem stoploss_M (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hint : Integrable (fun p : ℝ × ℝ => p.2 - p.1) π)
    (hmart : ∀ ρ : ℝ → ℝ, Measurable ρ → (∃ C, ∀ x, |ρ x| ≤ C) →
      ∫ p, ρ p.1 * (p.2 - p.1) ∂π = 0)
    (h1 : Integrable (fun p : ℝ × ℝ => p.1) π) (h2 : Integrable (fun p : ℝ × ℝ => p.2) π)
    (t a : ℝ) :
    ∫ p, max (p.1 - a) 0 ∂(π.restrict (Set.Iic t ×ˢ Set.univ)) ≤
      ∫ p, max (p.2 - a) 0 ∂(π.restrict (Set.Iic t ×ˢ Set.univ)) := by
  have i1 : Integrable (fun p : ℝ × ℝ => max (p.1 - a) 0) (π.restrict (Set.Iic t ×ˢ Set.univ)) :=
    (h1.sub (integrable_const a)).pos_part.restrict
  have i2 : Integrable (fun p : ℝ × ℝ => max (p.2 - a) 0) (π.restrict (Set.Iic t ×ˢ Set.univ)) :=
    (h2.sub (integrable_const a)).pos_part.restrict
  have i3 : Integrable (fun p => (Set.Ioi a ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => p.2 - p.1) p)
      (π.restrict (Set.Iic t ×ˢ Set.univ)) :=
    hint.restrict.indicator (measurableSet_Ioi.prod MeasurableSet.univ)
  have this : ∫ p, (max (p.1 - a) 0 +
      (Set.Ioi a ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => p.2 - p.1) p)
      ∂(π.restrict (Set.Iic t ×ˢ Set.univ)) ≤
      ∫ p, max (p.2 - a) 0 ∂(π.restrict (Set.Iic t ×ˢ Set.univ)) :=
    integral_mono (i1.add i3) i2 fun p => hinge_ineq p a
  rw [integral_add i1 i3, ind_zero π hmart t a, add_zero] at this
  exact this

theorem key_eq (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hint : Integrable (fun p : ℝ × ℝ => p.2 - p.1) π)
    (hmart : ∀ ρ : ℝ → ℝ, Measurable ρ → (∃ C, ∀ x, |ρ x| ≤ C) →
      ∫ p, ρ p.1 * (p.2 - p.1) ∂π = 0)
    (h1 : Integrable (fun p : ℝ × ℝ => p.1) π) (h2 : Integrable (fun p : ℝ × ℝ => p.2) π)
    (Γ : Set (ℝ × ℝ)) (hΓm : MeasurableSet Γ) (hΓ0 : π Γᶜ = 0)
    (hΓ : ∀ x x' ym yp y' : ℝ, (x, ym) ∈ Γ → (x, yp) ∈ Γ → (x', y') ∈ Γ →
      ¬ (x < x' ∧ ym < y' ∧ y' < yp))
    (t k x' : ℝ) (hx' : t < x') (hk : (x', k) ∈ Γ) :
    ∫ p, max (p.2 - k) 0 ∂(π.restrict (Set.Iic t ×ˢ Set.univ)) =
      ∫ p, max (p.1 - k) 0 ∂(π.restrict (Set.Iic t ×ˢ Set.univ)) := by
  have hΓae : ∀ᵐ p ∂π, p ∈ Γ := by
    rw [ae_iff]; exact hΓ0
  have mS : ∀ (A B C : Set ℝ), MeasurableSet A → MeasurableSet B → MeasurableSet C →
      MeasurableSet (Γ ∩ {p : ℝ × ℝ | p.1 ∈ A ∧ p.1 ∈ B ∧ p.2 ∈ C}) := by
    intro A B C hA hB hC
    exact hΓm.inter ((measurable_fst hA).inter ((measurable_fst hB).inter (measurable_snd hC)))
  have an : ∀ (A B C : Set ℝ), MeasurableSet A → MeasurableSet B → MeasurableSet C →
      MeasureTheory.AnalyticSet (Prod.fst '' (Γ ∩ {p : ℝ × ℝ | p.1 ∈ A ∧ p.1 ∈ B ∧ p.2 ∈ C})) :=
    fun A B C hA hB hC => (mS A B C hA hB hC).analyticSet.image_of_continuous continuous_fst
  -- part 1: no mass on {k < x ≤ t, y < k}
  have hE1 : ∀ᵐ p ∂π, p.1 ≤ t → ¬ (k < p.1 ∧ p.2 < k) := by
    obtain ⟨U, hU1, hU2, hUm⟩ := (an (Set.Ioi k) (Set.Iic t) (Set.Iio k) measurableSet_Ioi
      measurableSet_Iic measurableSet_Iio).measurablySeparable
      (an (Set.Ioi k) (Set.Iic t) (Set.Ioi k) measurableSet_Ioi measurableSet_Iic measurableSet_Ioi) (by
        rw [Set.disjoint_left]
        rintro x ⟨⟨x1, y1⟩, ⟨hΓ1, hk1, ht1, hy1⟩, rfl⟩ ⟨⟨x2, y2⟩, ⟨hΓ2, hk2, ht2, hy2⟩, hx2⟩
        simp only at hx2
        exact hΓ x1 x' y1 y2 k hΓ1 (hx2 ▸ hΓ2) hk ⟨lt_of_le_of_lt ht1 hx', hy1, hy2⟩)
    set S := U ∩ Set.Ioc k t
    have hS : MeasurableSet S := hUm.inter measurableSet_Ioc
    have hz := mart_set π hmart S hS
    have hnn : ∀ᵐ p ∂(π.restrict (S ×ˢ Set.univ)), 0 < p.1 - p.2 := by
      rw [ae_restrict_iff' (hS.prod MeasurableSet.univ)]
      filter_upwards [hΓae] with p hpΓ hpS
      obtain ⟨⟨hpU, hk1, ht1⟩, -⟩ := hpS
      by_contra hc
      have hk2 : k < p.2 := by linarith [not_lt.1 hc, show k < p.1 from hk1]
      exact Set.disjoint_left.1 hU2 ⟨p, ⟨hpΓ, hk1, ht1, hk2⟩, rfl⟩ hpU
    have hint' : Integrable (fun p : ℝ × ℝ => p.1 - p.2) (π.restrict (S ×ˢ Set.univ)) :=
      (h1.sub h2).restrict
    have h0 : ∫ p in S ×ˢ Set.univ, (p.1 - p.2) ∂π = 0 := by
      have e : ∫ p in S ×ˢ Set.univ, (p.1 - p.2) ∂π = -∫ p in S ×ˢ Set.univ, (p.2 - p.1) ∂π := by
        rw [← integral_neg]; congr 1; ext p; ring
      rw [e, hz, neg_zero]
    have hae0 := (integral_eq_zero_iff_of_nonneg_ae (hnn.mono fun p hp => le_of_lt hp) hint').1 h0
    have hf : ∀ᵐ p ∂(π.restrict (S ×ˢ Set.univ)), False := by
      filter_upwards [hae0, hnn] with p hp1 hp2
      simp only [Pi.zero_apply] at hp1
      linarith
    have hzero : π.restrict (S ×ˢ Set.univ) = 0 :=
      ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hf)
    have hSnull : π (S ×ˢ Set.univ) = 0 := by
      rw [← Measure.restrict_apply_univ, hzero, Measure.coe_zero, Pi.zero_apply]
    filter_upwards [hΓae, measure_eq_zero_iff_ae_notMem.1 hSnull] with p hpΓ hpS hpt hkk
    exact hpS ⟨⟨hU1 ⟨p, ⟨hpΓ, hkk.1, hpt, hkk.2⟩, rfl⟩, hkk.1, hpt⟩, trivial⟩
  -- part 2: no mass on {x ≤ k, x ≤ t, y > k}
  have hE2 : ∀ᵐ p ∂π, p.1 ≤ t → ¬ (p.1 ≤ k ∧ k < p.2) := by
    obtain ⟨V, hV1, hV2, hVm⟩ := (an (Set.Iic k) (Set.Iic t) (Set.Ioi k) measurableSet_Iic
      measurableSet_Iic measurableSet_Ioi).measurablySeparable
      (an (Set.Iic k) (Set.Iic t) (Set.Iio k) measurableSet_Iic measurableSet_Iic measurableSet_Iio) (by
        rw [Set.disjoint_left]
        rintro x ⟨⟨x1, y1⟩, ⟨hΓ1, hk1, ht1, hy1⟩, rfl⟩ ⟨⟨x2, y2⟩, ⟨hΓ2, hk2, ht2, hy2⟩, hx2⟩
        simp only at hx2
        exact hΓ x1 x' y2 y1 k (hx2 ▸ hΓ2) hΓ1 hk ⟨lt_of_le_of_lt ht1 hx', hy2, hy1⟩)
    set S := V ∩ (Set.Iic k ∩ Set.Iic t)
    have hS : MeasurableSet S := hVm.inter (measurableSet_Iic.inter measurableSet_Iic)
    have hz := mart_set π hmart S hS
    have hnn : ∀ᵐ p ∂(π.restrict (S ×ˢ Set.univ)), 0 ≤ p.2 - p.1 := by
      rw [ae_restrict_iff' (hS.prod MeasurableSet.univ)]
      filter_upwards [hΓae] with p hpΓ hpS
      obtain ⟨⟨hpV, hk1, ht1⟩, -⟩ := hpS
      by_contra hc
      have hk2 : p.2 < k := by linarith [not_le.1 hc, show p.1 ≤ k from hk1]
      exact Set.disjoint_left.1 hV2 ⟨p, ⟨hpΓ, hk1, ht1, hk2⟩, rfl⟩ hpV
    have hint' : Integrable (fun p : ℝ × ℝ => p.2 - p.1) (π.restrict (S ×ˢ Set.univ)) :=
      hint.restrict
    have hae0 := (integral_eq_zero_iff_of_nonneg_ae hnn hint').1 hz
    have hq : ∀ᵐ p ∂π, p ∈ S ×ˢ Set.univ → p.2 - p.1 = 0 :=
      (ae_restrict_iff' (hS.prod MeasurableSet.univ)).1 hae0
    filter_upwards [hΓae, hq] with p hpΓ hpq hpt hkk
    have hmem : p ∈ S ×ˢ Set.univ := ⟨⟨hV1 ⟨p, ⟨hpΓ, hkk.1, hpt, hkk.2⟩, rfl⟩, hkk.1, hpt⟩, trivial⟩
    have := hpq hmem
    linarith [hkk.1, hkk.2]
  -- conclude
  have hM : ∀ᵐ p ∂(π.restrict (Set.Iic t ×ˢ Set.univ)),
      max (p.2 - k) 0 =
        max (p.1 - k) 0 + (Set.Ioi k ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => p.2 - p.1) p := by
    rw [ae_restrict_iff' (measurableSet_Iic.prod MeasurableSet.univ)]
    filter_upwards [hE1, hE2] with p hp1 hp2 hpt
    have hpt' : p.1 ≤ t := hpt.1
    rw [Set.indicator_apply]
    by_cases hp : k < p.1
    · rw [if_pos (show p ∈ Set.Ioi k ×ˢ Set.univ from ⟨hp, trivial⟩)]
      have : k ≤ p.2 := by
        by_contra hc
        exact hp1 hpt' ⟨hp, not_le.1 hc⟩
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    · rw [if_neg (show p ∉ Set.Ioi k ×ˢ Set.univ from fun h => hp h.1)]
      have : p.2 ≤ k := by
        by_contra hc
        exact hp2 hpt' ⟨not_lt.1 hp, not_le.1 hc⟩
      rw [max_eq_right (by linarith), max_eq_right (by linarith [not_lt.1 hp])]
      ring
  have i1 : Integrable (fun p : ℝ × ℝ => max (p.1 - k) 0) (π.restrict (Set.Iic t ×ˢ Set.univ)) :=
    (h1.sub (integrable_const k)).pos_part.restrict
  have i3 : Integrable (fun p => (Set.Ioi k ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => p.2 - p.1) p)
      (π.restrict (Set.Iic t ×ˢ Set.univ)) :=
    hint.restrict.indicator (measurableSet_Ioi.prod MeasurableSet.univ)
  rw [integral_congr_ae hM, integral_add i1 i3, ind_zero π hmart t k, add_zero]


theorem hinge_convex' (k : ℝ) : ConvexOn ℝ Set.univ (fun y : ℝ => max (y - k) 0) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h1 : a * x + b * y - k = a * (x - k) + b * (y - k) := by
    have : k = a * k + b * k := by rw [← add_mul, hab, one_mul]
    linarith
  apply max_le
  · rw [h1]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
  · positivity

theorem affine_convex (a b : ℝ) : ConvexOn ℝ Set.univ (fun x : ℝ => a * x + b) := by
  refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  have h : p * (a * x + b) + q * (a * y + b) - (a * (p * x + q * y) + b) = b * (p + q - 1) := by
    ring
  rw [hpq, sub_self, mul_zero] at h
  linarith

theorem cx_mass_mean (m1 m2 : Measure ℝ) [IsFiniteMeasure m1] [IsFiniteMeasure m2]
    (h1 : Integrable (fun x : ℝ => x) m1) (h2 : Integrable (fun x : ℝ => x) m2)
    (hcx : ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ →
      MartOT.Var.integralE m1 φ ≤ MartOT.Var.integralE m2 φ) :
    m1.real Set.univ = m2.real Set.univ ∧ ∫ x, x ∂m1 = ∫ x, x ∂m2 := by
  have key : ∀ a b : ℝ, a * ∫ x, x ∂m1 + m1.real Set.univ * b ≤
      a * ∫ x, x ∂m2 + m2.real Set.univ * b := by
    intro a b
    have h := hcx _ (affine_convex a b)
    rw [integralE_eq_coe m1 _ (show Integrable (fun x : ℝ => a * x + b) m1 from
        (h1.const_mul a).add (integrable_const b)),
      integralE_eq_coe m2 _ (show Integrable (fun x : ℝ => a * x + b) m2 from
        (h2.const_mul a).add (integrable_const b)), EReal.coe_le_coe_iff,
      integral_add (h1.const_mul a) (integrable_const b),
      integral_add (h2.const_mul a) (integrable_const b), integral_const_mul, integral_const_mul,
      integral_const, integral_const, smul_eq_mul, smul_eq_mul] at h
    exact h
  have k1 := key 0 1
  have k2 := key 0 (-1)
  have k3 := key 1 0
  have k4 := key (-1) 0
  constructor <;> nlinarith

theorem sl_map (M : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) (hf : Measurable f) (k : ℝ) :
    sl (M.map f) k = ∫ p, max (f p - k) 0 ∂M := by
  unfold sl
  rw [integral_map hf.aemeasurable
    (by fun_prop : Continuous fun y : ℝ => max (y - k) 0).aestronglyMeasurable]

theorem id_map (M : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    ∫ y, y ∂(M.map f) = ∫ p, f p ∂M := by
  exact integral_map hf.aemeasurable aestronglyMeasurable_id

theorem real_map (M : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    (M.map f).real Set.univ = M.real Set.univ := by
  rw [measureReal_def, measureReal_def, Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]

theorem int_map (M : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (h : Integrable f M) : Integrable (fun y : ℝ => y) (M.map f) :=
  (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).2 h

theorem sl_cx (m1 m2 : Measure ℝ) [IsFiniteMeasure m1] [IsFiniteMeasure m2]
    (h1 : Integrable (fun x : ℝ => x) m1) (h2 : Integrable (fun x : ℝ => x) m2)
    (hcx : ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ →
      MartOT.Var.integralE m1 φ ≤ MartOT.Var.integralE m2 φ) (k : ℝ) : sl m1 k ≤ sl m2 k := by
  have h := hcx _ (hinge_convex' k)
  rw [integralE_eq_coe m1 _ (hinge_int m1 h1 k), integralE_eq_coe m2 _ (hinge_int m2 h2 k),
    EReal.coe_le_coe_iff] at h
  exact h

theorem main (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hμ : MartOT.Var.InM (π.map Prod.fst)) (hν : MartOT.Var.InM (π.map Prod.snd))
    (hπ : MartOT.Var.IsMartingalePlan (π.map Prod.fst) (π.map Prod.snd) π)
    (hmono : MartOT.Var.IsLeftMonotone π) :
    MartOT.Var.IsLeftCurtain (π.map Prod.fst) (π.map Prod.snd) π := by
  obtain ⟨-, hint, hmart⟩ := hπ
  obtain ⟨Γ, hΓm, hΓ0, hΓ⟩ := hmono
  have h1 : Integrable (fun p : ℝ × ℝ => p.1) π :=
    (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).1 hμ.2
  have h2 : Integrable (fun p : ℝ × ℝ => p.2) π :=
    (integrable_map_measure aestronglyMeasurable_id measurable_snd.aemeasurable).1 hν.2
  refine ⟨inferInstance, fun t => ?_⟩
  have hmarg : (π.restrict (Set.Iic t ×ˢ Set.univ)).map Prod.fst =
      (π.map Prod.fst).restrict (Set.Iic t) := by
    rw [Measure.restrict_map measurable_fst measurableSet_Iic, ← Set.prod_univ]
  refine ⟨hmarg, ?_⟩
  unfold MartOT.Var.targetUpTo
  rw [← hmarg]
  set M := π.restrict (Set.Iic t ×ˢ Set.univ) with hMdef
  set μt := M.map Prod.fst with hμt
  set ηt := M.map Prod.snd with hηt
  set ν := π.map Prod.snd with hνdef
  have iμ : Integrable (fun y : ℝ => y) μt := int_map M _ measurable_fst h1.restrict
  have iη : Integrable (fun y : ℝ => y) ηt := int_map M _ measurable_snd h2.restrict
  have inμ : MartOT.Var.InM μt := ⟨inferInstance, iμ⟩
  have inη : MartOT.Var.InM ηt := ⟨inferInstance, iη⟩
  have hmass : μt.real Set.univ = ηt.real Set.univ := by
    rw [real_map M _ measurable_fst, real_map M _ measurable_snd]
  have hmean : ∫ y, y ∂μt = ∫ y, y ∂ηt := by
    rw [id_map M _ measurable_fst, id_map M _ measurable_snd]
    have hz := mart_set π hmart (Set.Iic t) measurableSet_Iic
    rw [integral_sub h2.restrict h1.restrict] at hz
    linarith
  have hsl : ∀ a, sl μt a ≤ sl ηt a := fun a => by
    rw [sl_map M _ measurable_fst, sl_map M _ measurable_snd]
    exact stoploss_M π hint hmart h1 h2 t a
  have hcxt : MartOT.Var.ConvexLE μt ηt :=
    ⟨inμ, inη, cx_of_stoploss μt ηt hmass iμ iη hmean hsl⟩
  have hle : ηt ≤ ν := Measure.map_mono Measure.restrict_le_self measurable_snd
  refine ⟨hle, hcxt, fun η' hη' hcx' => ?_⟩
  obtain ⟨-, inη', hcx⟩ := hcx'
  have : IsFiniteMeasure η' := inη'.1
  have iη' : Integrable (fun y : ℝ => y) η' := inη'.2
  obtain ⟨hm', hmean'⟩ := cx_mass_mean μt η' iμ iη' hcx
  have : IsFiniteMeasure ν := hν.1
  have : IsFiniteMeasure (ν - η') := isFiniteMeasure_of_le ν Measure.sub_le
  have iζ : Integrable (fun y : ℝ => y) (ν - η') := hν.2.mono_measure Measure.sub_le
  set θ := (π.restrict (Set.Iic t ×ˢ Set.univ)ᶜ).map Prod.snd with hθ
  have iθ : Integrable (fun y : ℝ => y) θ := int_map _ _ measurable_snd h2.restrict
  have hsum : ηt + θ = η' + (ν - η') := by
    rw [add_comm η', Measure.sub_add_cancel_of_le hη', hηt, hθ, hMdef,
      ← Measure.map_add _ _ measurable_snd,
      Measure.restrict_add_restrict_compl (measurableSet_Iic.prod MeasurableSet.univ)]
  have hO : IsOpen {k : ℝ | sl μt k < sl ηt k} := isOpen_lt (sl_cont μt iμ) (sl_cont ηt iη)
  have hθO : ∀ a b, Set.Ioo a b ⊆ {k : ℝ | sl μt k < sl ηt k} → θ (Set.Ioo a b) = 0 := by
    intro a b hab
    rw [hθ, Measure.map_apply measurable_snd measurableSet_Ioo,
      Measure.restrict_apply (measurable_snd measurableSet_Ioo)]
    refine measure_mono_null (fun p hp => ?_) hΓ0
    intro hpΓ
    obtain ⟨hp1, hp2⟩ := hp
    have hpt : t < p.1 := by
      by_contra hc
      exact hp2 ⟨not_lt.1 hc, trivial⟩
    have hk := key_eq π hint hmart h1 h2 Γ hΓm hΓ0 hΓ t p.2 p.1 hpt (by simpa using hpΓ)
    have hin := hab hp1
    simp only [Set.mem_setOf_eq] at hin
    rw [sl_map M _ measurable_fst, sl_map M _ measurable_snd] at hin
    linarith
  have hoff : ∀ k, k ∉ {k : ℝ | sl μt k < sl ηt k} → sl ηt k ≤ sl η' k := by
    intro k hk
    simp only [Set.mem_setOf_eq, not_lt] at hk
    exact le_trans hk (sl_cx μt η' iμ iη' hcx k)
  have hall := maxprinciple ηt η' (ν - η') θ iη iη' iζ iθ (by rw [← hmass, hm'])
    (by rw [← hmean, hmean']) hsum _ hO hθO hoff
  exact ⟨inη, inη', cx_of_stoploss ηt η' (by rw [← hmass, hm']) iη iη' (by rw [← hmean, hmean'])
    hall⟩

end MartOT.T53

open MeasureTheory in
theorem solution (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hμ : MartOT.Var.InM (π.map Prod.fst)) (hν : MartOT.Var.InM (π.map Prod.snd))
    (hπ : MartOT.Var.IsMartingalePlan (π.map Prod.fst) (π.map Prod.snd) π) (hmono : MartOT.Var.IsLeftMonotone π) :
    MartOT.Var.IsLeftCurtain (π.map Prod.fst) (π.map Prod.snd) π := by
  exact MartOT.T53.main π hμ hν hπ hmono

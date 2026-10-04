-- Prove2me | solution 1 for MDPFinance.TerminalWealth.one_period_optimal_existence
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:10:23.71114+00:00
-- url     : https://prove2.me/submissions/7fe2bf69-4bd3-4d2c-a4f0-f5f11c04710e

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_OnePeriod

open MeasureTheory ProbabilityTheory MDPFinance.TerminalWealth

namespace OPCex

theorem eI_dirac_coe (t : ℝ) : erealIntegral (Measure.dirac ()) (fun _ : Unit => (t : EReal)) = t := by
  unfold erealIntegral
  rw [lintegral_dirac, lintegral_dirac]
  rw [← EReal.coe_neg]
  have h1 : (((t : EReal) ⊔ 0).toENNReal : EReal) = ((max t 0 : ℝ) : EReal) := by
    rcases le_total t 0 with h | h
    · rw [sup_eq_right.mpr (by exact_mod_cast h), max_eq_right h]; simp
    · rw [sup_eq_left.mpr (by exact_mod_cast h), max_eq_left h]
      simp [EReal.coe_ennreal_ofReal, h]
  have h2 : ((((-t : ℝ) : EReal) ⊔ 0).toENNReal : EReal) = ((max (-t) 0 : ℝ) : EReal) := by
    rcases le_total (-t) 0 with h | h
    · rw [sup_eq_right.mpr (by exact_mod_cast h), max_eq_right h]; simp
    · rw [sup_eq_left.mpr (by exact_mod_cast h), max_eq_left h]
      simp [EReal.coe_ennreal_ofReal, h]
  rw [h1, h2, ← EReal.coe_neg, ← EReal.coe_add]
  congr 1
  rcases le_total t 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

theorem sqrt_ge (x M : ℝ) (hx : 0 ≤ x) : M ≤ Real.sqrt (x + M ^ 2) := by
  calc M ≤ |M| := le_abs_self M
    _ = Real.sqrt (M ^ 2) := (Real.sqrt_sq_eq_abs M).symm
    _ ≤ Real.sqrt (x + M ^ 2) := Real.sqrt_le_sqrt (by linarith)

def RR : Unit → Fin 1 → ℝ := fun _ _ => 1

theorem V_top (x : ℝ) (hx : 0 ≤ x) :
    OnePeriodV (Measure.dirac ()) (Set.Ici 0) Real.sqrt 0 RR x = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  have ha : (fun _ : Fin 1 => (M + 1) ^ 2) ∈ OnePeriodD (Measure.dirac ()) (Set.Ici 0) 0 RR x := by
    refine (show ∀ᵐ ω ∂(Measure.dirac ()), _ from Filter.Eventually.of_forall fun ω => ?_)
    simp only [RR, Set.mem_Ici]
    simp; positivity
  refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun a (_ : a ∈ OnePeriodD (Measure.dirac ())
    (Set.Ici 0) 0 RR x) => OnePeriodU (Measure.dirac ()) Real.sqrt 0 RR x a) _ ha)
  unfold OnePeriodU
  simp only [RR, Finset.univ_unique, Finset.sum_singleton, mul_one, add_zero, one_mul]
  rw [eI_dirac_coe]
  have := sqrt_ge x (M + 1) hx
  exact_mod_cast (by linarith : M < Real.sqrt (x + (M + 1) ^ 2))

end OPCex

open OPCex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    (measIP : Measure Ω) [IsProbabilityMeasure measIP] (domU : Set ℝ)
    (hdomU : domU = Set.Ici (0 : ℝ) ∨ domU = Set.Ioi (0 : ℝ)) (U : ℝ → ℝ)
    (hU : StrictMonoOn U domU ∧ StrictConcaveOn ℝ domU U ∧ ContinuousOn U domU)
    (i : ℝ) (hi : 0 < 1 + i) (R : Ω → Fin d → ℝ) (hR_meas : Measurable R)
    (hR_integrable : Integrable (fun ω => ∑ k, |R ω k|) measIP),
    (NoArbitrageOnePeriod measIP R ↔
      ∃ fstar : ℝ → (Fin d → ℝ), Measurable fstar ∧
        ∀ x ∈ domU, OnePeriodU measIP U i R x (fstar x) = OnePeriodV measIP domU U i R x) ∧
      StrictMonoOn (OnePeriodV measIP domU U i R) domU ∧
      StrictConcaveOnEReal domU (OnePeriodV measIP domU U i R) ∧
      ContinuousOn (OnePeriodV measIP domU U i R) domU) := by
  intro h
  have hU : StrictMonoOn Real.sqrt (Set.Ici (0 : ℝ)) ∧ StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) Real.sqrt ∧
      ContinuousOn Real.sqrt (Set.Ici (0 : ℝ)) :=
    ⟨fun x hx y _ hxy => Real.sqrt_lt_sqrt hx hxy, Real.strictConcaveOn_sqrt,
      Real.continuous_sqrt.continuousOn⟩
  have H := (h (Measure.dirac ()) (Set.Ici 0) (Or.inl rfl) Real.sqrt hU 0 (by norm_num) RR
    measurable_const Integrable.of_finite).2.1
  have := H (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one) zero_lt_one
  rw [V_top 0 le_rfl, V_top 1 zero_le_one] at this
  exact lt_irrefl _ this

#print axioms solution

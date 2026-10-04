-- Prove2me | solution 1 for MDPFinance.ConsumptionInvestment.one_period_ci_existence
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:10:24.392138+00:00
-- url     : https://prove2.me/submissions/9472c666-b051-4526-8cc1-78757501c7eb

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_OnePeriod

open MeasureTheory ProbabilityTheory MDPFinance.ConsumptionInvestment

namespace OPCICex

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
    OnePeriodCIV (Measure.dirac ()) (Set.Ici 0) Real.sqrt Real.sqrt 0 RR x = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  have ha : ((0 : ℝ), fun _ : Fin 1 => (M + 1) ^ 2) ∈
      OnePeriodCID (Measure.dirac ()) (Set.Ici 0) 0 RR x := by
    refine ⟨le_rfl, hx, Set.mem_Ici.mpr le_rfl,
      (show ∀ᵐ ω ∂(Measure.dirac ()), _ from Filter.Eventually.of_forall fun ω => ?_)⟩
    simp only [RR, Set.mem_Ici]
    simp; positivity
  refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun ca (_ : ca ∈ OnePeriodCID (Measure.dirac ())
    (Set.Ici 0) 0 RR x) => OnePeriodCIU (Measure.dirac ()) Real.sqrt Real.sqrt 0 RR x ca) _ ha)
  unfold OnePeriodCIU
  simp only [RR, Finset.univ_unique, Finset.sum_singleton, mul_one, add_zero, one_mul,
    Real.sqrt_zero, sub_zero, EReal.coe_zero, zero_add]
  rw [eI_dirac_coe]
  have := sqrt_ge x (M + 1) hx
  exact_mod_cast (by linarith : M < Real.sqrt (x + (M + 1) ^ 2))

end OPCICex

open OPCICex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    (measIP : Measure Ω) [IsProbabilityMeasure measIP] (domUp : Set ℝ)
    (hdomUp : domUp = Set.Ici (0 : ℝ)) (Uc Up : ℝ → ℝ)
    (hUc : StrictMonoOn Uc domUp ∧ StrictConcaveOn ℝ domUp Uc ∧ ContinuousOn Uc domUp)
    (hUp : StrictMonoOn Up domUp ∧ StrictConcaveOn ℝ domUp Up ∧ ContinuousOn Up domUp)
    (i : ℝ) (hi : 0 < 1 + i) (R : Ω → Fin d → ℝ) (hR_meas : Measurable R)
    (hR_integrable : Integrable (fun ω => ∑ k, |R ω k|) measIP),
    (NoArbitrageOnePeriodCI measIP R ↔
      ∃ fstar : ℝ → ℝ × (Fin d → ℝ), Measurable fstar ∧
        ∀ x ∈ domUp, OnePeriodCIU measIP Uc Up i R x (fstar x) =
          OnePeriodCIV measIP domUp Uc Up i R x) ∧
      StrictMonoOn (OnePeriodCIV measIP domUp Uc Up i R) domUp ∧
      StrictConcaveOnEReal domUp (OnePeriodCIV measIP domUp Uc Up i R) ∧
      ContinuousOn (OnePeriodCIV measIP domUp Uc Up i R) domUp) := by
  intro h
  have hU : StrictMonoOn Real.sqrt (Set.Ici (0 : ℝ)) ∧ StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) Real.sqrt ∧
      ContinuousOn Real.sqrt (Set.Ici (0 : ℝ)) :=
    ⟨fun x hx y _ hxy => Real.sqrt_lt_sqrt hx hxy, Real.strictConcaveOn_sqrt,
      Real.continuous_sqrt.continuousOn⟩
  have H := (h (Measure.dirac ()) (Set.Ici 0) rfl Real.sqrt Real.sqrt hU hU 0 (by norm_num) RR
    measurable_const Integrable.of_finite).2.1
  have := H (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one) zero_lt_one
  rw [V_top 0 le_rfl, V_top 1 zero_le_one] at this
  exact lt_irrefl _ this

#print axioms solution

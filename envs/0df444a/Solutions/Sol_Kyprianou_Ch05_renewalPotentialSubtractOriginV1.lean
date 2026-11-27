-- Prove2me | solution 1 for Kyprianou.Ch05.renewalPotentialSubtractOriginV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:23:49.397975+00:00
-- url     : https://prove2.me/submissions/34e1b133-707e-407e-89b1-d8a0574c813c

import Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheoremV2
import Theorems.Thm_Kyprianou_Ch05_renewalLocalFiniteFromGrowth
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Apply the classical renewal theorem and remove the single Dirac mass at zero using local finiteness. -/
theorem solution
    (F V : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F)
    (hRenewal : renewalMeasure F = Measure.dirac (0 : Real) + V)
    (hNonLattice : NonLatticeMeasure V → NonLatticeMeasure F) :
    let mu := ∫ x : Real, x ∂F
    ((NonLatticeMeasure V → ∀ y : Real, 0 < y →
      Tendsto (fun x : Real => (V (Set.Ioc x (x+y))).toReal)
        atTop (nhds (y / mu))) ∧
      Tendsto (fun x : Real => (V (Set.Icc 0 x)).toReal / x)
        atTop (nhds (1 / mu))) := by
  dsimp only
  have ht := classicalRenewalTheoremV2 F hSupport hFiniteMean hPositiveMean
  have hfin (x : Real) : V (Set.Icc 0 x) ≠ ⊤ := by
    have hf := renewalLocalFiniteFromGrowth F hSupport hFiniteMean hPositiveMean x
    rw [hRenewal, Measure.add_apply] at hf
    exact fun h => hf (by simp [h])
  constructor
  · intro hn y hy
    apply (ht.1 (hNonLattice hn) y hy).congr'
    filter_upwards [eventually_ge_atTop (0 : Real)] with x hx
    rw [hRenewal, Measure.add_apply]
    have hz : (0 : Real) ∉ Set.Ioc x (x+y) := fun h => (not_lt_of_ge hx) h.1
    simp [Measure.dirac_apply' _ measurableSet_Ioc, hz]
  · have hi : Tendsto (fun x : Real => 1 / x) atTop (nhds 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : Real => x⁻¹) atTop (nhds 0))
    have h := ht.2.2.sub hi
    apply (show Tendsto _ atTop (nhds (1 / (∫ x : Real, x ∂F))) from by simpa using h).congr'
    filter_upwards [eventually_ge_atTop (0 : Real)] with x hx
    have hz : (0 : Real) ∈ Set.Icc 0 x := ⟨le_rfl, hx⟩
    have he : renewalMeasure F (Set.Icc 0 x) = 1 + V (Set.Icc 0 x) := by
      rw [hRenewal, Measure.add_apply]
      simp [Measure.dirac_apply' _ measurableSet_Icc, hz]
    rw [he, ENNReal.toReal_add (by simp) (hfin x), ENNReal.toReal_one]
    ring

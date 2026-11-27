-- Prove2me | solution 1 for Kyprianou.Ch05.unkilledPotentialUnitMeanV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:13:41.708805+00:00
-- url     : https://prove2.me/submissions/223e1d95-11e6-45bb-a22d-42531ba27b3e

import Theorems.Thm_Kyprianou_Ch05_unkilledPotentialUnitFirstMomentV1
import Theorems.Thm_Kyprianou_Ch05_unkilledPotentialUnitSupportV1
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Recover integrability and the real mean from the finite nonnegative moment. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P) :
    Integrable (fun x : Real => x) (U 1) ∧
      (∫ x : Real, x ∂(U 1)) = (∫ w, Y 1 w ∂P) := by
  have hs := (unkilledPotentialUnitSupportV1 P Y death hKilled U hPotential).1
  have hn : 0 ≤ᵐ[U 1] (fun x : Real => x) := by
    change ∀ᵐ x : Real ∂(U 1), 0 ≤ x
    rw [ae_iff]
    have hset : {x : Real | ¬ 0 ≤ x} = Set.Iio 0 := by
      ext x
      simp [not_le]
    rw [hset]
    exact hs
  have hm := unkilledPotentialUnitFirstMomentV1 P Y death hKilled U hPotential hFiniteMean
  have hi : Integrable (fun x : Real => x) (U 1) :=
    ⟨measurable_id.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hn).mpr
      (by rw [hm]; exact ENNReal.ofReal_lt_top)⟩
  have hpos : 0 ≤ ∫ w, Y 1 w ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [hKilled.1.2] with w hw
    simpa [hKilled.1.1.start_zero] using hw (show (0 : NNReal) ≤ 1 from bot_le)
  exact ⟨hi, by rw [integral_eq_lintegral_of_nonneg_ae hn measurable_id.aestronglyMeasurable,
    hm, ENNReal.toReal_ofReal hpos]⟩

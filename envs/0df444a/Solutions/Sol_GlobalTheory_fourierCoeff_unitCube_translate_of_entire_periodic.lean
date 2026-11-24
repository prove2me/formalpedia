-- Prove2me | solution 1 for GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:40.755963+00:00
-- url     : https://prove2.me/submissions/24952f63-5dde-4f7b-9a51-f7f8477f2017

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ShiftSingleInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Theorems.Thm_GlobalTheory_setIntegral_unitCube_add_of_entire_periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (g : ℕ) (f : (Fin g → ℂ) → ℂ)
    (hf : Differentiable ℂ f) (hper : ∀ (i : Fin g) z, f (z + Pi.single i 1) = f z)
    (m : Fin g → ℤ) (w : Fin g → ℂ) :
    (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w) *
        cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) =
      cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * w i) *
        (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) *
          cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) := by
  have h := setIntegral_unitCube_add_of_entire_periodic
    (f := fun z => f z * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * z i))
    (by fun_prop) (fun i z => by
      rw [hper]
      congr 1
      have e : ∑ j, (m j : ℂ) * (z + (Pi.single i 1 : Fin g → ℂ)) j
          = ∑ j, (m j : ℂ) * z j + m i := by
        simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
      rw [e, mul_add, Complex.exp_add]
      have : cexp (-(2 * Real.pi * I) * (m i : ℂ)) = 1 := by
        have := Complex.exp_int_mul_two_pi_mul_I (-m i)
        rw [← this]
        congr 1
        push_cast
        ring
      rw [this, mul_one]) w
  rw [← h, ← integral_const_mul]
  congr 1
  funext x
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring
end GlobalTheory

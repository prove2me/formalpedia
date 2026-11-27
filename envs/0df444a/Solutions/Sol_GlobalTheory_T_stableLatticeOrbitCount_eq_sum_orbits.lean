-- Prove2me | solution 1 for GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:27.311168+00:00
-- url     : https://prove2.me/submissions/b953b656-1959-4525-8cb8-3488b53e2023

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableLatticeOrbitCountEqSumOrbits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableLatticeOrbitCountEqSumOrbitsStatement
import Theorems.Thm_GlobalTheory_UnitLemma_countGL_eq_sum_orbits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A), countGL O E g = ∑ᶠ o : MulAction.orbitRel.Quotient Aˣ (stLat O E g), ((MulAction.stabilizer Aˣ (Quotient.out o)).relIndex (intUnits O A) : ℚ) := by
  first | exact @GlobalTheory.UnitLemma.countGL_eq_sum_orbits | exact GlobalTheory.UnitLemma.countGL_eq_sum_orbits | (intros; apply GlobalTheory.UnitLemma.countGL_eq_sum_orbits <;> assumption)
end _root_.GlobalTheory.T

-- Prove2me | solution 1 for GlobalTheory.integralClosure_restrictScalars_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:24.846449+00:00
-- url     : https://prove2.me/submissions/425f7e9c-51b5-4dca-b82f-25508ce7c096

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries TensorProduct
open GlobalTheory
open scoped PowerSeries TensorProduct
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    [Algebra.IsIntegral A A'] :
    (integralClosure A' B).restrictScalars A = integralClosure A B := by
  ext x
  simp only [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩
end _root_.GlobalTheory
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.QCoh.fibreEval_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:23.207462+00:00
-- url     : https://prove2.me/submissions/dbdda0c7-e5fd-4d13-af6c-766503746bb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution (h : V ≤ U) (x : V) (s : Γ(F, U)) :
    fibreEval F x (F.presheaf.map (homOfLE h).op s) = fibreEval F (⟨x, h x.2⟩ : U) s := by
  rw [fibreEval_apply, fibreEval_apply, F.presheaf.germ_res_apply]
end GlobalTheory.QCoh

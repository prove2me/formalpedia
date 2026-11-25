-- Prove2me | solution 1 for GlobalTheory.QCoh.fibreEval_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:25.404885+00:00
-- url     : https://prove2.me/submissions/bbe414a5-02be-4e09-81d0-cba64e0acc6e

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
theorem _root_.solution (x : U) (f : Γ(X, U)) (s : Γ(F, U)) :
    fibreEval F x (f • s) = X.evaluation U x x.2 f • fibreEval F x s := by
  rw [map_smul, ← algebraMap_smul (X.residueField (x : X))]; rfl
end GlobalTheory.QCoh

-- Prove2me | solution 1 for GlobalTheory.QCoh.app_injective_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:02:56.305201+00:00
-- url     : https://prove2.me/submissions/1f6419ae-e874-48ef-802e-1f58dd8639b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X Y : Scheme.{u}} {F F' : X.Modules}
namespace GlobalTheory.QCoh
theorem _root_.solution (φ : F ⟶ F') [Mono φ] (U : X.Opens) :
    Function.Injective (φ.app U) := by
  have : Mono ((Scheme.Modules.toPresheaf X).map φ) := inferInstance
  have : Mono (((Scheme.Modules.toPresheaf X).map φ).app (op U)) :=
    (NatTrans.mono_iff_mono_app _).mp this _
  exact (AddCommGrpCat.mono_iff_injective _).mp this
end GlobalTheory.QCoh

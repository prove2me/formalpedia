-- Prove2me | solution 1 for GlobalTheory.presheafCubeLowerFaceIso_hom_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:40:38.307321+00:00
-- url     : https://prove2.me/submissions/08f490b3-d6cf-458e-8746-aad9aa73a6b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : Type w} [TopologicalSpace T] {ι κ : Type} {R : Type u} [Ring R]
variable (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{v} R) {Q Q' : (Opens T)ᵒᵖ ⥤ ModuleCat.{v} R}
variable (V : Opens T) (U : ι → Opens T)
variable [LinearOrder ι]
variable [LinearOrder κ] (e : κ ↪o ι) (i : ι)
namespace GlobalTheory
theorem _root_.solution (s : Finset κ) :
    ((presheafCubeLowerFaceIso P V U e).hom.app s).hom =
      presheafRes P (cechOpen_map V U e.toEmbedding s).ge := rfl
end GlobalTheory

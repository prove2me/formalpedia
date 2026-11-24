-- Prove2me | solution 1 for GlobalTheory.cechAbHMap_toCechAbH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:24.738772+00:00
-- url     : https://prove2.me/submissions/30ae08db-0572-40d1-93c2-9ee25cb15076

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Theorems.Thm_GlobalTheory_homologyMap_presheafToCechH

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
variable {T : Type w} [TopologicalSpace T] {ι : Type}
  (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) {Q Q' : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}}
  (V : Opens T) (U : ι → Opens T)
variable [LinearOrder ι]
variable {P}
namespace GlobalTheory
theorem _root_.solution (φ : P ⟶ Q) (x : P.obj (op V)) :
    (cechAbHMap V U φ 0).hom (toCechAbH P V U x) = toCechAbH Q V U (φ.app (op V) x) :=
  homologyMap_presheafToCechH V U (Functor.whiskerRight φ abToIntModule) x
end GlobalTheory

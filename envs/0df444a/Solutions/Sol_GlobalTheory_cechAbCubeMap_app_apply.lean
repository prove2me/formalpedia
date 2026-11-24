-- Prove2me | solution 1 for GlobalTheory.cechAbCubeMap_app_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:26.755581+00:00
-- url     : https://prove2.me/submissions/fa307825-9a61-4756-91ce-646dce5b9ef8

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
variable {T : Type w} [TopologicalSpace T] {ι : Type}
  (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) {Q Q' : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}}
  (V : Opens T) (U : ι → Opens T)
variable {P}
namespace GlobalTheory
theorem _root_.solution (φ : P ⟶ Q) (s : Finset ι) (x : P.obj (op (cechOpen V U s))) :
    ((cechAbCubeMap V U φ).app s).hom x = φ.app (op (cechOpen V U s)) x := rfl
end GlobalTheory

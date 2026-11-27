-- Prove2me | solution 1 for GlobalTheory.res_cechAbCube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:42:44.491184+00:00
-- url     : https://prove2.me/submissions/6790c2ef-cc43-4a63-8290-3e2ff0adaeac

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
namespace GlobalTheory
theorem _root_.solution {s t : Finset ι} (h : s ⊆ t) (x : P.obj (op (cechOpen V U s))) :
    Cube.res (cechAbCube P V U) h x = P.map (homOfLE (cechOpen_anti V U h)).op x := rfl
end GlobalTheory

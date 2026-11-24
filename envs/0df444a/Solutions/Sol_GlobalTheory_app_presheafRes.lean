-- Prove2me | solution 1 for GlobalTheory.app_presheafRes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:15.104545+00:00
-- url     : https://prove2.me/submissions/e1c5c868-4edb-446c-81d5-bcd26b0cd7e3

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
variable {P}
namespace GlobalTheory
theorem _root_.solution (φ : P ⟶ Q) {W W' : Opens T} (h : W' ≤ W) (x : P.obj (op W)) :
    (φ.app (op W')).hom (presheafRes P h x) = presheafRes Q h ((φ.app (op W)).hom x) :=
  congr(($(φ.naturality (homOfLE h).op)).hom x)
end GlobalTheory

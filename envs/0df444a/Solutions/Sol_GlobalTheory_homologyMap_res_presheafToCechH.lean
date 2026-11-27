-- Prove2me | solution 1 for GlobalTheory.homologyMap_res_presheafToCechH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:40:38.299402+00:00
-- url     : https://prove2.me/submissions/5a859c94-e819-4491-83f8-0bda5f9b6d8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Theorems.Thm_GlobalTheory_homologyMap_cechClass


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
variable {V U}
namespace GlobalTheory
theorem _root_.solution {V' : Opens T} {U' : ι → Opens T}
    (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) (hV : V' ≤ V) (x : P.obj (op V)) :
    (HomologicalComplex.homologyMap (cechComplexMap (presheafCubeRes P h)) 0).hom
      (presheafToCechH P V U x) = presheafToCechH P V' U' (presheafRes P hV x) := by
  rw [presheafToCechH_apply, presheafToCechH_apply]
  exact homologyMap_cechClass _ 0 _ _ (funext fun s =>
    (presheafRes_presheafRes P _ _ x).trans
      (presheafRes_presheafRes P hV (cechOpen_le V' U' s.1) x).symm)
end GlobalTheory

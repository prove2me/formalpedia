-- Prove2me | solution 1 for GlobalTheory.homologyMap_presheafToCechH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:31.044262+00:00
-- url     : https://prove2.me/submissions/1dcd2783-9603-408e-9d4d-01d99dfa4b22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Theorems.Thm_GlobalTheory_app_presheafRes
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
variable {P}
namespace GlobalTheory
theorem _root_.solution (φ : P ⟶ Q) (x : P.obj (op V)) :
    (HomologicalComplex.homologyMap (cechComplexMap (presheafCubeMap V U φ)) 0).hom
      (presheafToCechH P V U x) = presheafToCechH Q V U ((φ.app (op V)).hom x) := by
  rw [presheafToCechH_apply, presheafToCechH_apply]
  exact homologyMap_cechClass _ 0 _ _ (funext fun _ => app_presheafRes φ _ x)
end GlobalTheory

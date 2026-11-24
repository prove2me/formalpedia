-- Prove2me | solution 1 for GlobalTheory.CechDR.oneFormsMapOfFunctorMorphism_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:38:57.823295+00:00
-- url     : https://prove2.me/submissions/4595dc7d-cddc-423a-ab18-cfa67f1c7ac8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_eq_self_of_id


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
open CatCoh
universe v u v' u' v'' u''
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'')
namespace GlobalTheory.CechDR
theorem _root_.solution (ω : Ω[F.obj T⁄R]) : p1 F (𝟙 T) ω = ω := by
  unfold p1
  exact (semiHom_mp F (𝟙 T)).oneFormMap_eq_self_of_id (fun b ↦ mp_id F T b) ω
end GlobalTheory.CechDR

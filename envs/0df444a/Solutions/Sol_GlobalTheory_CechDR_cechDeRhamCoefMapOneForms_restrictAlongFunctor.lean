-- Prove2me | solution 1 for GlobalTheory.CechDR.cechDeRhamCoefMapOneForms_restrictAlongFunctor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:47:27.5959+00:00
-- url     : https://prove2.me/submissions/e07adc27-1050-4ca7-8a37-3bc0a86852cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
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
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''} (m : CoefMap σ F F')
namespace GlobalTheory.CechDR
theorem _root_.solution (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (T : C') (ω : Ω[F.obj (G.obj T)⁄R]) :
    q1 (CoefMap.restrict F G) T ω = ω := SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) ω
end GlobalTheory.CechDR

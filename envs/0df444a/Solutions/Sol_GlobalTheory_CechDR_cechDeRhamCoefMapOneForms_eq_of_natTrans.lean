-- Prove2me | solution 1 for GlobalTheory.CechDR.cechDeRhamCoefMapOneForms_eq_of_natTrans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:35:38.907107+00:00
-- url     : https://prove2.me/submissions/3b8d8e32-49c7-4e38-9d9f-5d5bb1524106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_comp_oneFormMap


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
variable {σ' : R →+* R'} (m' : CoefMap σ' F F') (θ : m.G ⟶ m'.G)
  (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b)
include h
namespace GlobalTheory.CechDR
theorem _root_.solution (T : C') (ω : Ω[F.obj (m.G.obj T)⁄R]) : q1 m' T (p1 F (θ.app T) ω) = q1 m T ω :=
  SemiHom.oneFormMap_comp_oneFormMap _ _ _ (h T) ω
end GlobalTheory.CechDR

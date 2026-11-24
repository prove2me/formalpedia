-- Prove2me | solution 1 for GlobalTheory.CechDR.qOm_pOm_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:38:27.422521+00:00
-- url     : https://prove2.me/submissions/a6d59215-c73e-41df-9e98-b7b1d499e4b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_mOm


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
theorem _root_.solution {j : ℕ} (T : C') (x : Om R (F.obj (m.G.obj T)) j) :
    qOm m' j T (pOm F j (θ.app T) x) = qOm m j T x := SemiHom.mOm_mOm _ _ _ (h T) x
end GlobalTheory.CechDR

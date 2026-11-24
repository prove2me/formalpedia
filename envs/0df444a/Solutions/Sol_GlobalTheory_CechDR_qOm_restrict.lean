-- Prove2me | solution 1 for GlobalTheory.CechDR.qOm_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:35:40.836557+00:00
-- url     : https://prove2.me/submissions/74d88329-3ad3-4983-aece-406e429fda47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_id


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
theorem _root_.solution (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) {j : ℕ} (T : C')
    (x : Om R (F.obj (G.obj T)) j) : qOm (CoefMap.restrict F G) j T x = x :=
  SemiHom.mOm_id _ (fun _ ↦ rfl) x
end GlobalTheory.CechDR

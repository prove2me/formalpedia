-- Prove2me | solution 1 for GlobalTheory.CechDR.pOm_dTwo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:42:48.598155+00:00
-- url     : https://prove2.me/submissions/be391f6c-3726-4a5f-89c3-b21f293c4d97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_dTwo


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
theorem _root_.solution (x : Om R (F.obj T) 2) : pOm F 3 φ (dTwo R _ x) = dTwo R _ (pOm F 2 φ x) := by
  unfold pOm
  exact (semiHom_mp F φ).mOm_dTwo x
end GlobalTheory.CechDR

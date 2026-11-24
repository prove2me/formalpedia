-- Prove2me | solution 1 for GlobalTheory.CechDR.FormExtJ.mp_omjExt_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:15:46.907445+00:00
-- url     : https://prove2.me/submissions/68016a6d-7a15-47aa-b43b-f5e8702edc51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExtJ
open GlobalTheory.CatCoh
attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)
namespace GlobalTheory.CechDR.FormExtJ
theorem _root_.solution {T T' : C} (φ : T ⟶ T') (x : Om R (F.obj T) j) :
    mp (omjExt F j) φ (TrivSqZeroExt.inr x : (omjExt F j).obj T) =
      (TrivSqZeroExt.inr (pOm F j φ x) : (omjExt F j).obj T') := by
  change extMapJ F j φ (TrivSqZeroExt.inr x) = _
  exact TrivSqZeroExt.ext ((fst_extMapJ F j φ _).trans (by simp)) ((snd_extMapJ F j φ _).trans (by simp))
end GlobalTheory.CechDR.FormExtJ

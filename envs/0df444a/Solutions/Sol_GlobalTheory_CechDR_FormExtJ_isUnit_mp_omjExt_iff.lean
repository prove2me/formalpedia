-- Prove2me | solution 1 for GlobalTheory.CechDR.FormExtJ.isUnit_mp_omjExt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:17:16.014697+00:00
-- url     : https://prove2.me/submissions/0f36379c-eafd-45ec-aa91-8519f447063e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff

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
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExtJ
open GlobalTheory.CatCoh
attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)
namespace GlobalTheory.CechDR.FormExtJ
theorem _root_.solution {T S : C} (u : T ⟶ S) (c : (omjExt F j).obj T) :
    IsUnit (mp (omjExt F j) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_extMapJ F j u c)))
end GlobalTheory.CechDR.FormExtJ

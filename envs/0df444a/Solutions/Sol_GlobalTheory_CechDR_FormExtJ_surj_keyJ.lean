-- Prove2me | solution 1 for GlobalTheory.CechDR.FormExtJ.surj_keyJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:50.214797+00:00
-- url     : https://prove2.me/submissions/9a218641-7381-4181-98d2-1080634dea2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocalisationAtElementsTrivSqZeroExtForms
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_pOm_smul
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExtJ
attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)
namespace GlobalTheory.CechDR.FormExtJ
theorem _root_.solution {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j))
    (y : TrivSqZeroExt (F.obj T') (Om R (F.obj T') j)) (a₀ : F.obj T) (η₀ : Om R (F.obj T) j)
    (k₁ k₂ : ℕ) (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀)
    (hη : mp F l (c.fst ^ k₂) • y.snd = pOm F j l η₀) :
    y * extMapJ F j l c ^ (k₁ + k₂ + 1) = extMapJ F j l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_extMapJ, fst_extMapJ]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_extMapJ, fst_extMapJ, snd_extMapJ]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      pOm_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module
end GlobalTheory.CechDR.FormExtJ

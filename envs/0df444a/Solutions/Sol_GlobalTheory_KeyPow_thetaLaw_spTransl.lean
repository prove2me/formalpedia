-- Prove2me | solution 1 for GlobalTheory.KeyPow.thetaLaw_spTransl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:51.584098+00:00
-- url     : https://prove2.me/submissions/39df9685-2472-42c8-bd29-050cf1b6f127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaSqCongrModTwo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_cMat_spTransl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eC_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_spTransl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_mulVec_halfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofIntVec_dot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofRealVec_halfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_spTransl
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero
import Theorems.Thm_ReciprocityTheory_PTheta_ofIntVec_mulVec
import Theorems.Thm_ReciprocityTheory_PTheta_thetaTranslTau_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open GlobalTheory GlobalTheory.KeyPow
namespace GlobalTheory.KeyPow
theorem _root_.solution {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (hS : S.IsSymm) (n n' : Fin g → ℤ) :
    ThetaLaw g (spTransl S) n n' n (n' - S *ᵥ n - fun i => S i i) := by
  set X : ℂ := -(ofRealVec (halfVec n) ⬝ᵥ (S.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n))) / 2 -
      ofRealVec (halfVec n) ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ) / 2) with hX
  refine ⟨eC X ^ 2, ?_, fun τ _ z => ?_⟩
  · rw [← pow_mul, eC_pow]
    have h8 : ((2 * 4 : ℕ) : ℂ) * X = ((-(n ⬝ᵥ (S *ᵥ n)) - 2 * (n ⬝ᵥ fun i => S i i) : ℤ) : ℂ) := by
      have hd : ofIntVec n ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ)) = ((n ⬝ᵥ fun i => S i i : ℤ) : ℂ) := by
        simp [dotProduct, ofIntVec]
      have hd2 : (fun i => ((S i i : ℤ) : ℂ) / 2) = (1 / 2 : ℂ) • fun i => ((S i i : ℤ) : ℂ) := by
        ext i; simp; ring
      rw [hX, ofRealVec_halfVec, Matrix.mulVec_smul, ← ofIntVec_mulVec, smul_dotProduct,
        dotProduct_smul, ofIntVec_dot, hd2, smul_dotProduct, dotProduct_smul, hd]
      simp only [smul_eq_mul]
      push_cast; ring
    rw [h8, eC_int]
  · have hb : halfVec (n' - S *ᵥ n - fun i => S i i) + S.map (fun x : ℤ => (x : ℝ)) *ᵥ halfVec n +
        (fun i => ((S i i : ℤ) : ℝ) / 2) = halfVec n' := by
      rw [mulVec_halfVec]
      ext i; simp only [halfVec, Pi.add_apply, Pi.sub_apply]; push_cast; ring
    have hz : zAct (spTransl S) τ z = z := by simp [zAct, jAut_spTransl]
    have he : expArg (spTransl S) τ z = 0 := by simp [expArg, jAut_spTransl, cMat_spTransl]
    rw [hz, he, spAct_spTransl, jAut_spTransl, thetaTranslTau_holds (Fin g) _ _ _ _ S hS, hb,
      mul_pow, det_one, eC_zero]
    ring
end GlobalTheory.KeyPow

-- Prove2me | solution 1 for GlobalTheory.KeyPow.thetaLaw_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:26.465736+00:00
-- url     : https://prove2.me/submissions/7d1bebaa-2d12-4378-8d19-d3b10028297d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaSqCongrModTwo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_cMat_J
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eC_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_J
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_nAut_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofIntVec_dot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofRealVec_halfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_eq
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int


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
theorem _root_.solution {g : ℕ} (hInv : InversionStatement) (n n' : Fin g → ℤ) :
    ThetaLaw g (Matrix.J (Fin g) ℤ) n n' (-n') n := by
  set F : ℂ := 2 * (ofRealVec (halfVec (-n')) ⬝ᵥ ofRealVec (halfVec n))
  refine ⟨(-I) ^ g * eC F, ?_, fun τ hτ z => ?_⟩
  · rw [mul_pow, ← pow_mul, mul_comm g 4, pow_mul, eC_pow]
    have hI : (-I : ℂ) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp
    have hF : ((4 : ℕ) : ℂ) * F = ((-(2 * (n' ⬝ᵥ n)) : ℤ) : ℂ) := by
      simp only [F, ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot, smul_eq_mul]
      simp [dotProduct]; ring
    rw [hI, one_pow, one_mul, hF, eC_int]
  · have hsym : τ.IsSymm := hτ.1
    have hs : spAct (Matrix.J (Fin g) ℤ) τ = -τ⁻¹ := by
      rw [spAct_eq, jAut_J, nAut_eq, cMat_J]; simp [Matrix.J]
    have htinv : (τ⁻¹)ᵀ = τ⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym.eq]
    have hz : zAct (Matrix.J (Fin g) ℤ) τ z = τ⁻¹ *ᵥ z := by rw [zAct, jAut_J, htinv]
    have he : expArg (Matrix.J (Fin g) ℤ) τ z = z ⬝ᵥ (τ⁻¹ *ᵥ z) := by
      rw [expArg, jAut_J, cMat_J]; simp [Matrix.J]
    have hneg : -halfVec (-n') = halfVec n' := by ext i; simp [halfVec]; ring
    rw [hs, hz, he, jAut_J, hInv g _ _ τ hτ z, hneg]
    ring
end GlobalTheory.KeyPow

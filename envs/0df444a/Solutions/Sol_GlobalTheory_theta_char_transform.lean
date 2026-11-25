-- Prove2me | solution 1 for GlobalTheory.theta_char_transform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:29:58.446261+00:00
-- url     : https://prove2.me/submissions/ee741ad8-d522-4e15-b14d-5cee44c68825

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_symplectic_fromBlocks_relations
import Theorems.Thm_GlobalTheory_fromBlocks_map_intCast_mem_symplecticGroup
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_mem_siegelUpperCoords
import Theorems.Thm_GlobalTheory_riemannThetaJointForm_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_isUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_nAut_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_isSymm
import Theorems.Thm_ReciprocityTheory_PTheta_dot_mulVec_symm
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_ofRealVec_add
import Theorems.Thm_ReciprocityTheory_PTheta_ofRealVec_mulVec
import Theorems.Thm_ReciprocityTheory_PTheta_thetaCharShift_holds
import Theorems.Thm_ReciprocityTheory_PTheta_thetaRealTransl_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.mem_siegelUpperCoords
attribute [local simp] GlobalTheory.riemannThetaJointForm_apply



set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
namespace GlobalTheory
theorem _root_.solution (hγ : γ ∈ symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) {l : ℂ}
    (hl : ∀ z, theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l * theta 0 0 z τ)
    {p q p' q' : Fin g → ℝ}
    (hp : p = γ.toBlocks₁₁ᵀ.map ((↑) : ℤ → ℝ) *ᵥ p' + γ.toBlocks₂₁ᵀ.map ((↑) : ℤ → ℝ) *ᵥ q')
    (hq : q = γ.toBlocks₁₂ᵀ.map ((↑) : ℤ → ℝ) *ᵥ p' + γ.toBlocks₂₂ᵀ.map ((↑) : ℤ → ℝ) *ᵥ q')
    (z : Fin g → ℂ) :
    theta p' q' (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) =
      l * eC ((ofRealVec p' ⬝ᵥ ofRealVec q' - ofRealVec p ⬝ᵥ ofRealVec q) / 2) * theta p q z τ := by
  have hj := jAut_isUnit hγ hτ
  have hs := spAct_isSymm hγ hτ.1 hj
  have hP : ofRealVec p = (cMat γ).toBlocks₁₁ᵀ *ᵥ ofRealVec p' +
      (cMat γ).toBlocks₂₁ᵀ *ᵥ ofRealVec q' := by
    rw [hp, ofRealVec_add, ofRealVec_mulVec, ofRealVec_mulVec]
    rfl
  have hQ : ofRealVec q = (cMat γ).toBlocks₁₂ᵀ *ᵥ ofRealVec p' +
      (cMat γ).toBlocks₂₂ᵀ *ᵥ ofRealVec q' := by
    rw [hq, ofRealVec_add, ofRealVec_mulVec, ofRealVec_mulVec]
    rfl
  obtain ⟨-, -, -, r4, r5⟩ : _ ∧ _ ∧ _ ∧
      (cMat γ).toBlocks₂₁ * (cMat γ).toBlocks₂₂ᵀ = (cMat γ).toBlocks₂₂ * (cMat γ).toBlocks₂₁ᵀ ∧
      (cMat γ).toBlocks₂₂ * (cMat γ).toBlocks₁₁ᵀ - (cMat γ).toBlocks₂₁ * (cMat γ).toBlocks₁₂ᵀ = 1 :=
    symplectic_fromBlocks_relations (fromBlocks_map_intCast_mem_symplecticGroup ℂ
      (by rwa [fromBlocks_toBlocks] : fromBlocks γ.toBlocks₁₁ γ.toBlocks₁₂ γ.toBlocks₂₁
        γ.toBlocks₂₂ ∈ symplecticGroup (Fin g) ℤ))
  set u := τ *ᵥ ofRealVec p + ofRealVec q with hu
  have e1 : (jAut γ τ)⁻¹ᵀ *ᵥ u = spAct γ τ *ᵥ ofRealVec p' + ofRealVec q' := by
    have : u = (nAut γ τ)ᵀ *ᵥ ofRealVec p' + (jAut γ τ)ᵀ *ᵥ ofRealVec q' := by
      rw [hu, hP, hQ, nAut_eq, jAut_eq]
      simp only [transpose_add, transpose_mul, hτ.1.eq, add_mulVec, mulVec_add, mulVec_mulVec]
      abel
    rw [this, mulVec_add, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, ← transpose_mul,
      mul_nonsing_inv _ hj, transpose_one, one_mulVec, ← spAct_eq, hs.eq]
  have e2 : ((jAut γ τ)⁻¹ * (cMat γ).toBlocks₂₁) *ᵥ u =
      ofRealVec p - (jAut γ τ)⁻¹ *ᵥ ofRealVec p' := by
    have : (cMat γ).toBlocks₂₁ *ᵥ u = jAut γ τ *ᵥ ofRealVec p - ofRealVec p' := by
      have h : (cMat γ).toBlocks₂₂ *ᵥ ofRealVec p - (cMat γ).toBlocks₂₁ *ᵥ ofRealVec q =
          ofRealVec p' := by
        rw [hP, hQ]
        simp only [mulVec_add, mulVec_mulVec]
        rw [r4, add_sub_add_right_eq_sub, ← sub_mulVec, r5, one_mulVec]
      rw [← h, hu, jAut_eq, mulVec_add, add_mulVec, mulVec_mulVec]
      abel
    rw [← mulVec_mulVec, this, mulVec_sub, mulVec_mulVec, nonsing_inv_mul _ hj, one_mulVec]
  have hK : ((jAut γ τ)⁻¹ * (cMat γ).toBlocks₂₁).IsSymm := by
    have : (cMat γ).toBlocks₂₁ * (jAut γ τ)ᵀ = jAut γ τ * (cMat γ).toBlocks₂₁ᵀ := by
      rw [jAut_eq, transpose_add, transpose_mul, hτ.1.eq, Matrix.mul_add, Matrix.add_mul, r4,
        Matrix.mul_assoc]
    rw [Matrix.IsSymm, transpose_mul, transpose_nonsing_inv,
      ← nonsing_inv_mul_cancel_left (jAut γ τ) (cMat γ).toBlocks₂₁ᵀ hj, ← this, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_right _ _ (isUnit_det_transpose _ hj)]
  have e3 : zAct γ τ (z + u) = zAct γ τ z + spAct γ τ *ᵥ ofRealVec p' + ofRealVec q' := by
    rw [zAct, mulVec_add, e1, ← add_assoc, zAct]
  have e4 (v : Fin g → ℂ) : v ⬝ᵥ (jAut γ τ)⁻¹ *ᵥ ofRealVec p' =
      ofRealVec p' ⬝ᵥ (jAut γ τ)⁻¹ᵀ *ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  have e5 : expArg γ τ (z + u) = expArg γ τ z +
      2 * (ofRealVec p ⬝ᵥ z - ofRealVec p' ⬝ᵥ zAct γ τ z) + (ofRealVec p ⬝ᵥ u -
        ofRealVec p' ⬝ᵥ (spAct γ τ *ᵥ ofRealVec p' + ofRealVec q')) := by
    rw [expArg, expArg, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      dot_mulVec_symm hK z u, e2, dotProduct_sub, dotProduct_sub, e4, e4, e1, zAct,
      dotProduct_comm z (ofRealVec p), dotProduct_comm u (ofRealVec p)]
    ring
  have h0 : ofRealVec (0 : Fin g → ℝ) = 0 := by
    ext
    simp [ofRealVec]
  have key := hl (z + u)
  have t1 := thetaCharShift_holds (Fin g) p' q' 0 0 (zAct γ τ z) (spAct γ τ) hs
  have t2 := thetaRealTransl_holds (Fin g) 0 0 p q z τ hτ.1
  rw [zero_add, zero_add, h0, add_zero] at t1 t2
  rw [e3, e5, hu, ← add_assoc z, t2] at key
  have aux {X Y Z V W A B : ℂ} (h : A * eC X = l * (eC Y * B)) (hV : V + Z + Y = W + X) :
      eC V * A * eC Z = l * eC W * B := by
    have hY : eC Y ≠ 0 := Complex.exp_ne_zero _
    have := congrArg eC hV
    rw [eC_add, eC_add, eC_add] at this
    apply mul_right_cancel₀ hY
    linear_combination A * this + eC W * h
  rw [t1]
  refine aux key ?_
  simp only [dotProduct_add]
  ring
end GlobalTheory

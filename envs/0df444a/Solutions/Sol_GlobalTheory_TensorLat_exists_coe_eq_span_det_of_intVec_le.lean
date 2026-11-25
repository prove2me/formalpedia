-- Prove2me | solution 1 for GlobalTheory.TensorLat.exists_coe_eq_span_det_of_intVec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:25:38.262589+00:00
-- url     : https://prove2.me/submissions/dfa32b54-96dd-45e9-889f-7032eaa0bd10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_absNorm_mul_relIndex_one
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coe_prod_frac
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_det_mem_prod_sub
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_det_rowMat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_lattice_split
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_prod_eq_span_prod
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_smul_mem_of_split
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors
open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx ReciprocityTheory.PGsh
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution (X : Submodule (𝓞 K) (Fin n → K)) (hfg : X.FG)
    (hstd : intVec K n ≤ X) :
    ∃ J : FractionalIdeal (𝓞 K)⁰ K, (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ X) ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J * ((intVec K n).toAddSubgroup.relIndex X.toAddSubgroup : ℚ) = 1 := by
  obtain ⟨C, z, hfgC, h1, htri, hdiag, hin, hdec, hidx⟩ := lattice_split K n X hfg hstd
  let CF : Fin n → FractionalIdeal (𝓞 K)⁰ K := fun i =>
    ⟨C i, FractionalIdeal.isFractional_of_fg (hfgC i)⟩
  refine ⟨∏ i, CF i, ?_, ?_⟩
  · rw [coe_prod_frac]
    change ∏ i, C i = _
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rw [prod_eq_span_prod]
      refine Submodule.span_mono fun x hx => ?_
      obtain ⟨t, ht, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
      refine ⟨fun i => t i • z i, fun i => smul_mem_of_split hin i (ht i), ?_⟩
      have : (Matrix.of fun i => t i • z i) = Matrix.diagonal t * rowMat z := by
        ext i j
        simp [rowMat, Matrix.diagonal_mul]
      rw [this, Matrix.det_mul, det_rowMat z htri hdiag, Matrix.det_diagonal, mul_one]
    · rintro _ ⟨v, hv, rfl⟩
      choose T hT hTv using fun i => hdec (v i) (hv i)
      have : Matrix.of v = Matrix.of T * rowMat z := by
        ext i j
        rw [Matrix.of_apply, hTv i]
        simp [rowMat, Matrix.mul_apply, Finset.sum_apply]
      rw [this, Matrix.det_mul, det_rowMat z htri hdiag, mul_one, ← Matrix.det_transpose]
      exact det_mem_prod_sub C _ fun i j => hT j i
  · rw [hidx, map_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => absNorm_mul_relIndex_one (C i) (hfgC i) (h1 i)
end GlobalTheory.TensorLat

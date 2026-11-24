-- Prove2me | solution 1 for GlobalTheory.symplectic_fromBlocks_relations
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:30.457849+00:00
-- url     : https://prove2.me/submissions/a7468174-2901-4a4a-9519-dda3e7b131e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_mem_siegelUpperCoords
import Theorems.Thm_GlobalTheory_riemannThetaJointForm_apply
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c d : Matrix ι ι ℤ}
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] {a b c d : Matrix ι ι R}
    (h : fromBlocks a b c d ∈ symplecticGroup ι R) :
    aᵀ * c = cᵀ * a ∧ aᵀ * d - cᵀ * b = 1 ∧ dᵀ * b = bᵀ * d ∧ c * dᵀ = d * cᵀ ∧
      d * aᵀ - c * bᵀ = 1 := by
  have h' := h
  rw [SymplecticGroup.mem_iff', J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h
  rw [SymplecticGroup.mem_iff, J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h'
  obtain ⟨h1, h2, -, h3⟩ := h
  obtain ⟨-, -, h4, h5⟩ := h'
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul] at h1 h2 h3 h4 h5
  refine ⟨(add_neg_eq_zero.1 h1).symm, ?_, add_neg_eq_zero.1 h3, (add_neg_eq_zero.1 h5).symm, ?_⟩
  · rw [← neg_inj, ← h2]
    abel
  · rw [← h4]
    abel
end GlobalTheory

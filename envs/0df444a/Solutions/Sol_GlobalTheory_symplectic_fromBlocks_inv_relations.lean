-- Prove2me | solution 1 for GlobalTheory.symplectic_fromBlocks_inv_relations
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:25.78985+00:00
-- url     : https://prove2.me/submissions/87d6a682-e28a-4dd1-9c78-1c0deeac6781

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

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c d : Matrix ι ι ℤ}
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] {a b c d : Matrix ι ι R}
    (h : fromBlocks a b c d ∈ symplecticGroup ι R) (hd : IsUnit d.det) :
    (b * d⁻¹).IsSymm ∧ (d⁻¹ * c).IsSymm ∧ cᵀ * (b * d⁻¹) = aᵀ - d⁻¹ := by
  obtain ⟨-, h2, h3, h4, -⟩ := symplectic_fromBlocks_relations h
  have hd' := isUnit_det_transpose _ hd
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.IsSymm, transpose_mul, transpose_nonsing_inv, ← mul_nonsing_inv_cancel_right d bᵀ hd,
      ← h3, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hd']
  · rw [Matrix.IsSymm, transpose_mul, transpose_nonsing_inv, ← nonsing_inv_mul_cancel_left d cᵀ hd,
      ← h4, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hd']
  · rw [← Matrix.mul_assoc, show cᵀ * b = aᵀ * d - 1 by rw [← h2]; abel, Matrix.sub_mul,
      mul_nonsing_inv_cancel_right _ _ hd, Matrix.one_mul]
end GlobalTheory

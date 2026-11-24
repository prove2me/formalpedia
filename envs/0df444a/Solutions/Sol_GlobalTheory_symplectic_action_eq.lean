-- Prove2me | solution 1 for GlobalTheory.symplectic_action_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:46.427462+00:00
-- url     : https://prove2.me/submissions/0f253216-52bc-4c9e-b68a-412973f4caf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_symplectic_fromBlocks_inv_relations

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
theorem _root_.solution {R : Type*} [CommRing R] {a b c d τ : Matrix ι ι R}
    (h : fromBlocks a b c d ∈ symplecticGroup ι R) (hd : IsUnit d.det) (hτ : IsUnit τ.det)
    (hN : IsUnit (τ⁻¹ + d⁻¹ * c).det) :
    c * τ + d = d * (τ⁻¹ + d⁻¹ * c) * τ ∧
    (a * τ + b) * (c * τ + d)⁻¹ = d⁻¹ᵀ * (τ⁻¹ + d⁻¹ * c)⁻¹ * d⁻¹ + b * d⁻¹ := by
  obtain ⟨h1, -, h3⟩ := symplectic_fromBlocks_inv_relations h hd
  have e1 : c * τ + d = d * (τ⁻¹ + d⁻¹ * c) * τ := by
    rw [Matrix.mul_add, mul_nonsing_inv_cancel_left _ _ hd, Matrix.add_mul,
      nonsing_inv_mul_cancel_right _ _ hτ, add_comm]
  have hj : IsUnit (c * τ + d).det := by
    rw [e1, det_mul, det_mul]
    exact (hd.mul hN).mul hτ
  have e2 : a = d⁻¹ᵀ + b * d⁻¹ * c := by
    have := congrArg transpose h3
    rw [transpose_mul, h1.eq, transpose_transpose, transpose_sub, transpose_transpose] at this
    rw [this]
    abel
  have e3 : a * τ + b = d⁻¹ᵀ * τ + b * d⁻¹ * (c * τ + d) := by
    rw [Matrix.mul_add, nonsing_inv_mul_cancel_right _ _ hd, ← add_assoc, ← Matrix.mul_assoc,
      ← Matrix.add_mul, ← e2]
  refine ⟨e1, ?_⟩
  rw [e3, Matrix.add_mul, mul_nonsing_inv_cancel_right _ _ hj, e1, Matrix.mul_inv_rev,
    Matrix.mul_inv_rev, ← Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hτ, Matrix.mul_assoc]
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.fromBlocks_map_intCast_mem_symplecticGroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:27.714857+00:00
-- url     : https://prove2.me/submissions/b1d04675-974d-4652-8d1a-a8ee344b2c4b

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
theorem _root_.solution (R : Type*) [CommRing R]
    (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) :
    fromBlocks (a.map ((↑) : ℤ → R)) (b.map (↑)) (c.map (↑)) (d.map (↑)) ∈
      symplecticGroup ι R := by
  rw [SymplecticGroup.mem_iff] at h ⊢
  have := congrArg (Int.castRingHom R).mapMatrix h
  rw [map_mul, map_mul] at this
  simp only [RingHom.mapMatrix_apply, Matrix.map_J, transpose_map, fromBlocks_map] at this
  exact this
end GlobalTheory

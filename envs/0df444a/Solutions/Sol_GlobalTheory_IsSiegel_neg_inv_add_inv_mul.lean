-- Prove2me | solution 1 for GlobalTheory.IsSiegel.neg_inv_add_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:43.112186+00:00
-- url     : https://prove2.me/submissions/0ec5ec6f-26c9-4261-808b-20491cf1138c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_fromBlocks_map_intCast_mem_symplecticGroup
import Theorems.Thm_GlobalTheory_symplectic_fromBlocks_inv_relations
import Theorems.Thm_GlobalTheory_isUnit_det_map_intCast
import Theorems.Thm_GlobalTheory_IsSiegel_add_map_ofReal
import Theorems.Thm_GlobalTheory_IsSiegel_neg_inv
import Theorems.Thm_GlobalTheory_inv_map_ofReal
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
namespace IsSiegel
theorem _root_.solution {τ : Matrix ι ι ℂ} (hτ : IsSiegel τ)
    (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) (hd : d.det ≠ 0) :
    IsSiegel (-(τ⁻¹ + (d.map ((↑) : ℤ → ℂ))⁻¹ * c.map ((↑) : ℤ → ℂ))) := by
  have hu := isUnit_det_map_intCast ℝ hd
  obtain ⟨-, h2, -⟩ := symplectic_fromBlocks_inv_relations
    (fromBlocks_map_intCast_mem_symplecticGroup ℝ h) hu
  have e (M : Matrix ι ι ℤ) : M.map ((↑) : ℤ → ℂ) = (M.map ((↑) : ℤ → ℝ)).map ofReal := by
    ext
    simp
  convert hτ.neg_inv.add_map_ofReal h2.neg using 1
  rw [e c, e d, inv_map_ofReal hu.ne_zero, neg_add]
  ext i j
  simp [mul_apply]
end IsSiegel
end GlobalTheory

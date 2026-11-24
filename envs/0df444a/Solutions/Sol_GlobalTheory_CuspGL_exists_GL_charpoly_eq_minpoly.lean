-- Prove2me | solution 1 for GlobalTheory.CuspGL.exists_GL_charpoly_eq_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:06:55.799965+00:00
-- url     : https://prove2.me/submissions/161083e9-ad0f-4cb6-976d-03049cc2d4ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (F K : Type) [Field F] [Field K] [Algebra F K]
    (α : K) (hx : IsIntegral F α) (h0 : α ≠ 0) (n : ℕ) (hn : (minpoly F α).natDegree = n) :
    ∃ x : GL (Fin n) F, Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = minpoly F α := by
  subst hn
  have hdim : (IntermediateField.adjoin.powerBasis hx).dim = (minpoly F α).natDegree :=
    IntermediateField.adjoin.powerBasis_dim hx
  have hg : (IntermediateField.adjoin.powerBasis hx).gen ≠ 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen hx]
    intro h
    apply h0
    have := congrArg (algebraMap (IntermediateField.adjoin F {α}) K) h
    simpa using this
  let f : (IntermediateField.adjoin F {α}) →ₐ[F] Matrix (Fin (minpoly F α).natDegree) (Fin (minpoly F α).natDegree) F :=
    (Matrix.reindexAlgEquiv F F (finCongr hdim)).toAlgHom.comp
      (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hx).basis)
  refine ⟨Units.map (f : (IntermediateField.adjoin F {α}) →* Matrix _ _ F) (Units.mk0 _ hg), ?_⟩
  rw [Units.coe_map, Units.val_mk0]
  change (Matrix.reindexAlgEquiv F F (finCongr hdim)
      (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hx).basis
        (IntermediateField.adjoin.powerBasis hx).gen)).charpoly = _
  rw [Matrix.coe_reindexAlgEquiv, Matrix.charpoly_reindex, charpoly_leftMulMatrix,
    IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
end GlobalTheory.CuspGL

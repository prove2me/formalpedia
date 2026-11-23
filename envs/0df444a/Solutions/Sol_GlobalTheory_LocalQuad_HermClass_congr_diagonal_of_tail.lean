-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.congr_diagonal_of_tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:22.944696+00:00
-- url     : https://prove2.me/submissions/eee1de8e-0afb-4573-84a3-26ce51b90841

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_trans
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_submatrix
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_fromBlocks
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.HermClass
variable {E : Type*} [Field E] {c : E →+* E} {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]
namespace GlobalTheory.LocalQuad.HermClass
theorem _root_.solution {r : ℕ} {g g' : Fin (r + 1) → E} (h0 : g 0 = g' 0)
    (h : Congr c (Matrix.diagonal fun i : Fin r => g i.succ)
      (Matrix.diagonal fun i : Fin r => g' i.succ)) :
    Congr c (Matrix.diagonal g) (Matrix.diagonal g') := by
  let e : Fin (r + 1) ≃ Fin r ⊕ PUnit.{1} := (finSuccEquiv r).trans (Equiv.optionEquivSumPUnit _)
  have key : ∀ k : Fin (r + 1) → E, Matrix.diagonal k =
      (Matrix.fromBlocks (Matrix.diagonal fun i : Fin r => k i.succ) 0 0
        (Matrix.diagonal fun _ : PUnit.{1} => k 0)).submatrix e e := by
    intro k
    rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [e]
  rw [key g, key g', h0]
  exact (h.fromBlocks _).submatrix e
end GlobalTheory.LocalQuad.HermClass

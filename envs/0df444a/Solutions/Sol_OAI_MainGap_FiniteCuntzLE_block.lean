-- Prove2me | solution 1 for OAI.MainGap.FiniteCuntzLE.block
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:16:03.301672+00:00
-- url     : https://prove2.me/submissions/9e8a24f4-d4e8-4fdf-9c2f-9a6855b6f552

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Comparison.lean:L240-L255
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.FiniteCuntzLE.block. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Comparison ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

attribute [local instance] OAI.MainGap.positivityOrder
attribute [local instance] OAI.MainGap.positivityStarOrder
lemma matrixBlock_mul {m n p q r s : ℕ}
    (x : CStarMatrix (Fin m) (Fin n) A) (y : CStarMatrix (Fin p) (Fin q) A)
    (u : CStarMatrix (Fin n) (Fin r) A) (v : CStarMatrix (Fin q) (Fin s) A) :
    matrixBlock x y * matrixBlock u v = matrixBlock (x * u) (y * v) := by
  apply CStarMatrix.ofMatrix.symm.injective
  change (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm x) 0 0 (CStarMatrix.ofMatrix.symm y)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm *
    (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm u) 0 0 (CStarMatrix.ofMatrix.symm v)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm =
    (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm x * CStarMatrix.ofMatrix.symm u) 0 0
      (CStarMatrix.ofMatrix.symm y * CStarMatrix.ofMatrix.symm v)).submatrix _ _
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

lemma matrixBlock_star {m n p q : ℕ}
    (x : CStarMatrix (Fin m) (Fin n) A) (y : CStarMatrix (Fin p) (Fin q) A) :
    (matrixBlock x y).conjTranspose = matrixBlock x.conjTranspose y.conjTranspose := by
  apply CStarMatrix.ext
  intro i j
  change star (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm x) 0 0 (CStarMatrix.ofMatrix.symm y) (finSumFinEquiv.symm j) (finSumFinEquiv.symm i)) = _
  generalize hi : finSumFinEquiv.symm i = i'
  generalize hj : finSumFinEquiv.symm j = j'
  cases i' <;> cases j' <;> simp [matrixBlock, Matrix.fromBlocks, Matrix.submatrix, hi, hj]

lemma tendsto_matrixBlock {X : Type*} {f : Filter X} {m n p q : ℕ}
    {x : X → CStarMatrix (Fin m) (Fin n) A} {y : X → CStarMatrix (Fin p) (Fin q) A}
    {u : CStarMatrix (Fin m) (Fin n) A} {v : CStarMatrix (Fin p) (Fin q) A}
    (hx : Tendsto x f (𝓝 u)) (hy : Tendsto y f (𝓝 v)) :
    Tendsto (fun t => matrixBlock (x t) (y t)) f (𝓝 (matrixBlock u v)) := by
  change Tendsto (fun t => CStarMatrix.ofMatrix.symm (matrixBlock (x t) (y t))) f
    (𝓝 (CStarMatrix.ofMatrix.symm (matrixBlock u v)))
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  change Tendsto (fun t => Matrix.fromBlocks (CStarMatrix.ofMatrix.symm (x t)) 0 0
      (CStarMatrix.ofMatrix.symm (y t)) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) f
    (𝓝 (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm u) 0 0
      (CStarMatrix.ofMatrix.symm v) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)))
  cases finSumFinEquiv.symm i with
  | inl i' =>
    cases finSumFinEquiv.symm j with
    | inl j' => exact (hx.apply_nhds i').apply_nhds j'
    | inr j' => exact tendsto_const_nhds
  | inr i' =>
    cases finSumFinEquiv.symm j with
    | inl j' => exact tendsto_const_nhds
    | inr j' => exact (hy.apply_nhds i').apply_nhds j'

lemma matrixBlock_conjugate {m n p q : ℕ}
    (r : CStarMatrix (Fin m) (Fin n) A) (s : CStarMatrix (Fin p) (Fin q) A)
    (v : CStarMatrix (Fin m) (Fin m) A) (w : CStarMatrix (Fin p) (Fin p) A) :
    (matrixBlock r s).conjTranspose * matrixBlock v w * matrixBlock r s =
      matrixBlock (r.conjTranspose * v * r) (s.conjTranspose * w * s) := by
  rw [matrixBlock_star, matrixBlock_mul, matrixBlock_mul]

lemma FiniteCuntzLE.block {m n p q : ℕ}
    {d : CStarMatrix (Fin n) (Fin n) A} {v : CStarMatrix (Fin m) (Fin m) A}
    {d' : CStarMatrix (Fin q) (Fin q) A} {v' : CStarMatrix (Fin p) (Fin p) A}
    (h : FiniteCuntzLE d v) (h' : FiniteCuntzLE d' v') :
    FiniteCuntzLE (matrixBlock d d') (matrixBlock v v') := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨s, hs⟩ := h'
  refine ⟨fun j => matrixBlock (r j) (s j), ?_⟩
  have heq : (fun j => (matrixBlock (r j) (s j)).conjTranspose *
      matrixBlock v v' * matrixBlock (r j) (s j)) =
      (fun j => matrixBlock ((r j).conjTranspose * v * r j)
        ((s j).conjTranspose * v' * s j)) := by
    funext j
    exact matrixBlock_conjugate (r j) (s j) v v'
  rw [heq]
  exact tendsto_matrixBlock hr hs

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.positivityOrder
attribute [local instance] OAI.MainGap.positivityStarOrder


theorem solution : type_of% @_root_.OAI.MainGap.FiniteCuntzLE.block := @_root_.OAI.MainGap.FiniteCuntzLE.block

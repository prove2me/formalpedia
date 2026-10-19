-- Prove2me | solution 1 for OAI.MainGap.ProperlyInfinite.finite_copies
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:17:37.784787+00:00
-- url     : https://prove2.me/submissions/c1d6d0d8-8e85-4606-ae7a-6974c80d2960

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Comparison.lean:L279-L295
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.ProperlyInfinite.finite_copies. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Theorems.Thm_OAI_MainGap_FiniteCuntzLE_block

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Comparison ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

attribute [local instance] OAI.MainGap.positivityOrder
attribute [local instance] OAI.MainGap.positivityStarOrder
lemma matrix_mul_assoc {l m n k : ℕ} (x : CStarMatrix (Fin l) (Fin m) A)
    (y : CStarMatrix (Fin m) (Fin n) A) (z : CStarMatrix (Fin n) (Fin k) A) :
    (x * y) * z = x * (y * z) := Matrix.mul_assoc x y z

lemma matrix_star_mul {l m n : ℕ} (x : CStarMatrix (Fin l) (Fin m) A)
    (y : CStarMatrix (Fin m) (Fin n) A) :
    (x * y).conjTranspose = y.conjTranspose * x.conjTranspose :=
  Matrix.conjTranspose_mul x y

lemma continuous_matrix_mul {X : Type*} [TopologicalSpace X] {l m n : ℕ}
    {x : X → CStarMatrix (Fin l) (Fin m) A} {y : X → CStarMatrix (Fin m) (Fin n) A}
    (hx : Continuous x) (hy : Continuous y) : Continuous (fun t => x t * y t) :=
  hx.matrix_mul hy

lemma finiteCuntzLE_iff_closure {m n : ℕ} (d : CStarMatrix (Fin n) (Fin n) A)
    (v : CStarMatrix (Fin m) (Fin m) A) :
    FiniteCuntzLE d v ↔ d ∈ closure (Set.range
      (fun r : CStarMatrix (Fin m) (Fin n) A => r.conjTranspose * v * r)) := by
  rw [mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨_, fun j => ⟨r j, rfl⟩, hr⟩
  · rintro ⟨x, hx, ht⟩
    choose r hr using hx
    exact ⟨r, by simpa only [hr] using ht⟩

lemma finiteCuntzLE_of_forall_approx {m n : ℕ} {d : CStarMatrix (Fin n) (Fin n) A}
    {v : CStarMatrix (Fin m) (Fin m) A}
    (h : ∀ ε > 0, ∃ r : CStarMatrix (Fin m) (Fin n) A,
      ‖d - r.conjTranspose * v * r‖ < ε) : FiniteCuntzLE d v := by
  rw [finiteCuntzLE_iff_closure, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr⟩ := h ε hε
  exact ⟨_, ⟨r, rfl⟩, by simpa only [dist_eq_norm] using hr⟩

lemma FiniteCuntzLE.conjugate {l m n : ℕ} {d : CStarMatrix (Fin n) (Fin n) A}
    {v : CStarMatrix (Fin m) (Fin m) A} (hdv : FiniteCuntzLE d v)
    (x : CStarMatrix (Fin n) (Fin l) A) :
    FiniteCuntzLE (x.conjTranspose * d * x) v := by
  obtain ⟨r, hr⟩ := hdv
  refine ⟨fun j => r j * x, ?_⟩
  have hc : Continuous (fun d : CStarMatrix (Fin n) (Fin n) A =>
      x.conjTranspose * d * x) :=
    continuous_matrix_mul (continuous_matrix_mul continuous_const continuous_id) continuous_const
  convert hc.continuousAt.tendsto.comp hr using 1
  ext j
  rw [matrix_star_mul]
  simp only [Function.comp_apply, matrix_mul_assoc]

lemma FiniteCuntzLE.trans {l m n : ℕ} {d : CStarMatrix (Fin n) (Fin n) A}
    {v : CStarMatrix (Fin m) (Fin m) A} {w : CStarMatrix (Fin l) (Fin l) A}
    (hdv : FiniteCuntzLE d v) (hvw : FiniteCuntzLE v w) : FiniteCuntzLE d w := by
  rw [finiteCuntzLE_iff_closure] at hdv ⊢
  apply closure_minimal _ isClosed_closure hdv
  rintro _ ⟨x, rfl⟩
  exact (finiteCuntzLE_iff_closure _ _).mp (hvw.conjugate x)

lemma FiniteCuntzLE.refl {n : ℕ} (v : CStarMatrix (Fin n) (Fin n) A) :
    FiniteCuntzLE v v := by
  let M := CStarMatrix (Fin n) (Fin n) A
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  have hu := CStarAlgebra.increasingApproximateUnit M
  apply finiteCuntzLE_of_forall_approx
  intro ε hε
  have hl : ∀ᶠ e : M in CStarAlgebra.approximateUnit M, ‖v - v * e‖ < ε / 2 := by
    have ht := ((tendsto_const_nhds (x := v)).sub (hu.tendsto_mul_left v)).norm
    simpa only [sub_self, norm_zero] using ht.eventually (Iio_mem_nhds (by simpa only [sub_self, norm_zero] using half_pos hε))
  have hr : ∀ᶠ e : M in CStarAlgebra.approximateUnit M, ‖v - e * v‖ < ε / 2 := by
    have ht := ((tendsto_const_nhds (x := v)).sub (hu.tendsto_mul_right v)).norm
    simpa only [sub_self, norm_zero] using ht.eventually (Iio_mem_nhds (by simpa only [sub_self, norm_zero] using half_pos hε))
  obtain ⟨e, hesa, hen, hel, her⟩ :=
    (hu.eventually_star_eq.and (hu.eventually_norm.and (hl.and hr))).exists
  refine ⟨e, ?_⟩
  change ‖v - star e * v * e‖ < ε
  rw [hesa]
  calc
    ‖v - e * v * e‖ = ‖(v - e * v) + e * (v - v * e)‖ := by rw [mul_sub, ← mul_assoc]; congr 1; abel
    _ ≤ ‖v - e * v‖ + ‖e‖ * ‖v - v * e‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_mul_le _ _) _)
    _ ≤ ‖v - e * v‖ + ‖v - v * e‖ := by nlinarith [norm_nonneg (v - v * e)]
    _ < ε := by linarith

lemma matrixBlock_diagonal (n m : ℕ) (h : A) :
    matrixBlock (diagonalCorner n h) (diagonalCorner m h) = diagonalCorner (n+m) h := by
  apply CStarMatrix.ext
  intro i j
  change (Matrix.fromBlocks (Matrix.diagonal (fun _ => h)) 0 0
    (Matrix.diagonal (fun _ => h))).submatrix _ _ i j = _
  rw [Matrix.fromBlocks_diagonal]
  simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, diagonalCorner,
    CStarMatrix.ofMatrix_apply, Equiv.apply_eq_iff_eq]
  split_ifs with hij
  · cases finSumFinEquiv.symm i <;> rfl
  · rfl

lemma diagonalCorner_one (h : A) : diagonalCorner 1 h = scalarCorner h := by
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  change Matrix.diagonal (fun _ => h) i j = h
  simp [Matrix.diagonal, hij]

lemma ProperlyInfinite.finite_copies {h : A} (hh : ProperlyInfinite h) (n : ℕ) :
    FiniteCuntzLE (diagonalCorner n h) (scalarCorner h) := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, ?_⟩
    have heq : (fun _ : ℕ => (0 : CStarMatrix (Fin 1) (Fin 0) A).conjTranspose *
        scalarCorner h * (0 : CStarMatrix (Fin 1) (Fin 0) A)) = fun _ => diagonalCorner 0 h := by
      funext j
      apply CStarMatrix.ext
      intro i
      exact Fin.elim0 i
    rw [heq]
    exact tendsto_const_nhds
  | succ n hn =>
    have hblock := hn.block (FiniteCuntzLE.refl (scalarCorner h))
    rw [← diagonalCorner_one h, matrixBlock_diagonal, matrixBlock_diagonal] at hblock
    exact hblock.trans hh

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.positivityOrder
attribute [local instance] OAI.MainGap.positivityStarOrder


theorem solution : type_of% @_root_.OAI.MainGap.ProperlyInfinite.finite_copies := @_root_.OAI.MainGap.ProperlyInfinite.finite_copies

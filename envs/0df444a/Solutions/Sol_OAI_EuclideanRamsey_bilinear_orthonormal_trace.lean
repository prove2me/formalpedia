-- Prove2me | solution 1 for OAI.EuclideanRamsey.bilinear_orthonormal_trace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:02:11.943985+00:00
-- url     : https://prove2.me/submissions/2898d4a7-09e0-4c85-91cb-5cc0f7b8dd19

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean:L126-L152
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.bilinear_orthonormal_trace. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian

-- ---- from OAI.Combinatorics.EuclideanRamsey.Hessian ----
namespace OAI

universe uDomain uCodomain uIndex uColor uAction

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial

open scoped BigOperators
open Matrix MeasureTheory
namespace EuclideanRamsey

section Hessian
variable {E : Type uDomain} {F : Type uCodomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end Hessian

section Trace
variable {E : Type uDomain} {ι : Type uIndex} {κ : Type uColor} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

lemma bilinear_orthonormal_trace (B : E →L[ℝ] E →L[ℝ] ℝ)
    (e : OrthonormalBasis ι ℝ E) (f : OrthonormalBasis κ ℝ E) :
    ∑ i, B (e i) (e i) = ∑ j, B (f j) (f j) := by
  classical
  have hex (x y : E) : B x y = ∑ j, ∑ l,
      (inner ℝ (f j) x * inner ℝ (f l) y) * B (f j) (f l) := by
    conv_lhs => rw [← f.sum_repr x, ← f.sum_repr y]
    simp only [map_sum, map_smul, _root_.sum_apply,
      _root_.smul_apply, OrthonormalBasis.repr_apply_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  conv_lhs => arg 2; intro i; rw [hex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hsum (l : κ) : ∑ i, inner ℝ (f j) (e i) * inner ℝ (f l) (e i) =
      if j=l then 1 else 0 := by
    simpa only [real_inner_comm (f l), f.inner_eq_ite, eq_comm] using e.sum_inner_mul_inner (f j) (f l)
  simp_rw [hsum]
  simp

end Trace

section MatrixContraction

end MatrixContraction

section Split
variable {E : Type uDomain} {H : Type uAction} [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]

end Split

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open scoped BigOperators
open Matrix MeasureTheory


theorem solution.{uDomain,uIndex,uColor} : type_of% @_root_.OAI.EuclideanRamsey.bilinear_orthonormal_trace.{uDomain,uIndex,uColor} := @_root_.OAI.EuclideanRamsey.bilinear_orthonormal_trace.{uDomain,uIndex,uColor}

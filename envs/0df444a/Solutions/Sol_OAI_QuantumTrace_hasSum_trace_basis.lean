-- Prove2me | solution 1 for OAI.QuantumTrace.hasSum_trace_basis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:10:29.513179+00:00
-- url     : https://prove2.me/submissions/c00c53a3-dcc2-4e00-bdaf-6c08684971d0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L372-L392
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.hasSum_trace_basis. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

-- ---- from OAI.Analysis.QuantumTrace.Basic ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

omit [CompleteSpace E] in
theorem basis_tsum_enorm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    (∑' i, ENNReal.ofReal (‖inner ℂ (b i) x‖ ^ 2)) =
      ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (basis_hasSum_norm_sq b x).summable,
    (basis_hasSum_norm_sq b x).tsum_eq]

theorem diagonalTrace_eq_sqrt (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) :
    diagonalTrace b T = ∑' i, ENNReal.ofReal (‖CFC.sqrt T (b i)‖ ^ 2) := by
  simp only [diagonalTrace, sqrt_inner_eq hT]

omit [CompleteSpace E] in
theorem sum_norm_sq_basis_independent (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    (T : E →L[ℂ] E) (hT : T.IsSymmetric) :
    (∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2)) =
      ∑' j, ENNReal.ofReal (‖T (c j)‖ ^ 2) := by
  calc
    _ = ∑' i, ∑' j, ENNReal.ofReal (‖inner ℂ (c j) (T (b i))‖ ^ 2) := by
      simp only [basis_tsum_enorm_sq]
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (c j) (T (b i))‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (b i) (T (c j))‖ ^ 2) := by
      congr 1; ext j
      congr 1; ext i
      have he : inner ℂ (c j) (T (b i)) = inner ℂ (T (c j)) (b i) :=
        (hT (c j) (b i)).symm
      rw [he, norm_inner_symm]
    _ = _ := by simp only [basis_tsum_enorm_sq]

theorem diagonalTrace_basis_independent (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ E) {T : E →L[ℂ] E} (hT : T.IsPositive) :
    diagonalTrace b T = diagonalTrace c T := by
  rw [diagonalTrace_eq_sqrt b hT, diagonalTrace_eq_sqrt c hT]
  apply sum_norm_sq_basis_independent
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg T)).isSymmetric

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open Filter

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

theorem hasSum_trace_basis (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
    HasSum (fun i => (inner ℂ (c i) (T (c i))).re) τ := by
  have hnB (i : ι) : 0 ≤ (inner ℂ (b i) (T (b i))).re := hp.re_inner_nonneg_right _
  have hnC (i : κ) : 0 ≤ (inner ℂ (c i) (T (c i))).re := hp.re_inner_nonneg_right _
  have hb : diagonalTrace b T = ENNReal.ofReal τ := by
    rw [diagonalTrace, ← ENNReal.ofReal_tsum_of_nonneg hnB ht.summable, ht.tsum_eq]
  have hc : diagonalTrace c T = ENNReal.ofReal τ :=
    (diagonalTrace_basis_independent b c hp).symm.trans hb
  have hn : τ ≥ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Filter.Eventually.of_forall (fun s => Finset.sum_nonneg (fun i _ => hp.re_inner_nonneg_right (b i))))
  have hfin : (∑' i, ENNReal.ofReal (inner ℂ (c i) (T (c i))).re) ≠ ⊤ := by
    rw [← diagonalTrace, hc]
    exact ENNReal.ofReal_ne_top
  have hh := ENNReal.hasSum_toReal hfin
  simp only [ENNReal.toReal_ofReal (hnC _)] at hh
  have he : (∑' i, (inner ℂ (c i) (T (c i))).re) = τ := by
    rw [← ENNReal.toReal_ofReal hn, ← hc, diagonalTrace, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (hnC _)]
  exact he ▸ hh

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section

open Filter Topology
open scoped Classical
variable {ι : Type*}
end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

end

section
open Filter Topology
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe v
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open Filter Topology
variable {ι : Type*}

end

section
open Filter Topology

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

end

section
variable {ι J : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end

open scoped BigOperators ComplexConjugate
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end QuantumTrace

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace QuantumTrace
variable {ι J : Type*}

end QuantumTrace

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory


theorem solution.{u,u_1,u_2} : type_of% @_root_.OAI.QuantumTrace.hasSum_trace_basis.{u,u_1,u_2} := @_root_.OAI.QuantumTrace.hasSum_trace_basis.{u,u_1,u_2}

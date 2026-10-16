-- Prove2me | solution 1 for OAI.QuantumTrace.exists_positive_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:12:35.527724+00:00
-- url     : https://prove2.me/submissions/9ac99791-1393-4452-b78c-dd81f6d5c202

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L394-L419
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.exists_positive_eigenbasis. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Theorems.Thm_OAI_QuantumTrace_basisApprox_norm_sub_le
import Theorems.Thm_OAI_QuantumTrace_exists_eigenbasis
import Theorems.Thm_OAI_QuantumTrace_hasSum_trace_basis

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

omit [CompleteSpace E] [CompleteSpace F] in
theorem basisApprox_isCompactOperator (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    (s : Finset ι) : IsCompactOperator (basisApprox b T s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [basisApprox] using (isCompactOperator_zero : IsCompactOperator (0 : E →L[ℂ] F))
  | @insert j s hj hs =>
    rw [basisApprox, Finset.sum_insert hj]
    apply IsCompactOperator.add _ hs
    rw [rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_rng (toSpanSingleton ℂ (T (b j)))).comp_clm (innerSL ℂ (b j))

omit [CompleteSpace E] in
theorem compact_of_summable_basis_norm_sq (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    (ht : Summable (fun i => ‖T (b i)‖ ^ 2)) : IsCompactOperator T := by
  have hlim : Tendsto (fun s : Finset ι => basisApprox b T s) atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hzero : Tendsto (fun s : Finset ι =>
        Real.sqrt ((∑' i, ‖T (b i)‖ ^ 2) - ∑ i ∈ s, ‖T (b i)‖ ^ 2)) atTop (𝓝 0) := by
      convert! Real.continuous_sqrt.continuousAt.tendsto.comp
        (tendsto_const_nhds.sub ht.hasSum) using 1
      simp
    apply squeeze_zero (fun _ => norm_nonneg _) ?_ hzero
    intro s
    rw [norm_sub_rev]
    exact basisApprox_norm_sub_le b T ht.hasSum s
  exact isCompactOperator_of_tendsto hlim
    (Eventually.of_forall (fun s => basisApprox_isCompactOperator b T s))

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

theorem compact_of_positive_finite_trace (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive)
    (ht : Summable (fun i => (inner ℂ (b i) (T (b i))).re)) : IsCompactOperator T := by
  have hs : IsCompactOperator (CFC.sqrt T : E →L[ℂ] E) := compact_of_summable_basis_norm_sq b _
    (by simpa only [sqrt_inner_eq hT] using ht)
  have he : (CFC.sqrt T) ∘L CFC.sqrt T = T := by
    simpa only [pow_two, ContinuousLinearMap.mul_def] using CFC.sq_sqrt T
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hT)
  rw [← he]
  exact hs.comp_clm _

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

theorem exists_positive_eigenbasis (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
    ∃ (J : Type u) (c : HilbertBasis J ℂ E) (p : J → ℝ),
      (∀ j, 0 ≤ p j) ∧ HasSum p τ ∧ ∀ j, T (c j) = (p j : ℂ) • c j := by
  obtain ⟨J, c, e, he⟩ := exists_eigenbasis
    (compact_of_positive_finite_trace b hp ht.summable) hp.isSymmetric
  have hie (j : J) : inner ℂ (c j) (T (c j)) = e j := by
    rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, c.orthonormal.norm_eq_one]
    simp
  have her (j : J) : (e j).re ≥ 0 := by
    rw [← hie]
    exact hp.re_inner_nonneg_right _
  have hec (j : J) : (e j).re = e j := by
    have hr := hp.isSymmetric.conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (he j), c.orthonormal.ne_zero j⟩)
    apply Complex.ext
    · rfl
    · have := congrArg Complex.im hr
      simp only [Complex.conj_im] at this
      simpa using (show (0 : ℝ) = (e j).im by linarith)
  refine ⟨J, c, fun j => (e j).re, her, ?_, ?_⟩
  · simpa only [hie] using hasSum_trace_basis b c hp ht
  · intro j
    rw [hec, he]

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


theorem solution.{u,u_1} : type_of% @_root_.OAI.QuantumTrace.exists_positive_eigenbasis.{u,u_1} := @_root_.OAI.QuantumTrace.exists_positive_eigenbasis.{u,u_1}

-- Prove2me | solution 1 for OAI.QuantumTrace.basisApprox_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:05:28.259211+00:00
-- url     : https://prove2.me/submissions/ad989ce9-b299-496e-99a2-8fa4a7b16d02

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L214-L228
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.basisApprox_norm_sub_le. The node keeps its source
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

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_apply_sq_le_basis_sum (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    {τ : ℝ} (ht : HasSum (fun i => ‖T (b i)‖ ^ 2) τ) (x : E) :
    ‖T x‖ ^ 2 ≤ τ * ‖x‖ ^ 2 := by
  have hlim := ((T.hasSum (b.hasSum_repr x)).norm).pow 2
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro s
  simp only [map_smul]
  calc
    ‖∑ i ∈ s, b.repr x i • T (b i)‖ ^ 2 ≤
        (∑ i ∈ s, ‖b.repr x i‖ * ‖T (b i)‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_smul] using norm_sum_le s (fun i => b.repr x i • T (b i))
    _ ≤ (∑ i ∈ s, ‖b.repr x i‖ ^ 2) * (∑ i ∈ s, ‖T (b i)‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ ≤ ‖x‖ ^ 2 * τ := by
      apply mul_le_mul
      · simpa only [b.repr_apply_apply] using b.orthonormal.sum_inner_products_le x (s := s)
      · simpa only [ht.tsum_eq] using ht.summable.sum_le_tsum s (fun _ _ => sq_nonneg _)
      · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      · exact sq_nonneg _
    _ = _ := mul_comm _ _

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_le_sqrt_basis_sum (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    {τ : ℝ} (ht : HasSum (fun i => ‖T (b i)‖ ^ 2) τ) :
    ‖T‖ ≤ Real.sqrt τ := by
  have hn : 0 ≤ τ := ht.nonneg (fun i => sq_nonneg _)
  apply T.opNorm_le_bound (Real.sqrt_nonneg _)
  intro x
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [← pow_two, ← pow_two, mul_pow, Real.sq_sqrt hn]
  exact norm_apply_sq_le_basis_sum b T ht x

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

omit [CompleteSpace E] [CompleteSpace F] in
theorem basisApprox_norm_sub_le (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    {τ : ℝ} (ht : HasSum (fun i => ‖T (b i)‖ ^ 2) τ) (s : Finset ι) :
    ‖T - basisApprox b T s‖ ≤ Real.sqrt (τ - ∑ i ∈ s, ‖T (b i)‖ ^ 2) := by
  classical
  apply norm_le_sqrt_basis_sum b
  have hfin : HasSum (fun i => if i ∈ s then ‖T (b i)‖ ^ 2 else 0)
      (∑ i ∈ s, ‖T (b i)‖ ^ 2) := by
    have hh := (hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ι) (f := fun i => if i ∈ s then ‖T (b i)‖ ^ 2 else 0)
      (s := s) (by intro i hi; simp [hi]))
    simpa using hh
  convert! ht.sub hfin using 1
  ext i
  simp only [sub_apply, basisApprox_apply_basis]
  split_ifs <;> simp

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
open Filter ContinuousLinearMap InnerProductSpace


theorem solution : type_of% @_root_.OAI.QuantumTrace.basisApprox_norm_sub_le := @_root_.OAI.QuantumTrace.basisApprox_norm_sub_le

-- Prove2me | solution 1 for OAI.QuantumTrace.weighted_number_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:25:24.222537+00:00
-- url     : https://prove2.me/submissions/679f0dde-a8e6-4ff9-bf15-c24dbf427125

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L1508-L1535
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.weighted_number_moment. The node keeps its source
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

theorem weighted_number_moment (b : HilbertBasis J ℂ (SequenceHilbert ι))
    (T : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (he : ∀ j, T (b j) = (p j : ℂ) • b j)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ν : J → ℝ)
    (hrow : ∀ j, HasSum (fun i => w i*‖b j i‖^2) (ν j))
    (hs : Summable (fun j => p j*ν j)) :
    Summable (fun i => w i*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re) := by
  let f : J × ι → ℝ := fun a => p a.1*(w a.2*‖b a.1 a.2‖^2)
  have hf : Summable f := by
    apply (summable_prod_of_nonneg (fun a => mul_nonneg (hp a.1) (mul_nonneg (hw a.2) (sq_nonneg _)))).mpr
    refine ⟨fun j => ((hrow j).mul_left (p j)).summable, ?_⟩
    convert hs using 1
    funext j
    exact ((hrow j).mul_left (p j)).tsum_eq
  have hcol (i : ι) : HasSum (fun j => f (j,i))
      (w i*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re) := by
    have hh := (hasSum_quadratic_eigenbasis b T p he (sequenceBasis ι i)).mul_left (w i)
    have heq : (fun j => w i*(p j*‖inner ℂ (b j) (sequenceBasis ι i)‖^2)) =
        (fun j => f (j,i)) := by
      funext j
      rw [norm_inner_symm, sequenceBasis_inner]
      dsimp [f]
      ring
    rw [heq] at hh
    exact hh
  apply hf.prod_symm.prod.congr
  intro i
  exact (hcol i).tsum_eq

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


theorem solution : type_of% @_root_.OAI.QuantumTrace.weighted_number_moment := @_root_.OAI.QuantumTrace.weighted_number_moment

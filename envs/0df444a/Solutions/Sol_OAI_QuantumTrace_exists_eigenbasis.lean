-- Prove2me | solution 1 for OAI.QuantumTrace.exists_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:06:48.441097+00:00
-- url     : https://prove2.me/submissions/26f45b39-970c-482e-86c9-715c207bba55

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L266-L297
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.exists_eigenbasis. The node keeps its source
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

theorem exists_eigenbasis {T : E →L[ℂ] E} (hc : IsCompactOperator T)
    (hs : T.IsSymmetric) :
    ∃ (J : Type u) (b : HilbertBasis J ℂ E) (e : J → ℂ),
      ∀ j, T (b j) = e j • b j := by
  classical
  let S (μ : ℂ) := eigenspace T.toLinearMap μ
  let α (μ : ℂ) := Classical.choose (exists_hilbertBasis ℂ (S μ))
  let b (μ : ℂ) : HilbertBasis (α μ) ℂ (S μ) :=
    Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ (S μ)))
  let v : (Σ μ, α μ) → E := fun a => (b a.1 a.2 : E)
  have hv : Orthonormal ℂ v :=
    hs.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal (fun μ => (b μ).orthonormal)
  have hsp : (span ℂ (Set.range v))ᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hzero (μ : ℂ) (y : S μ) : inner ℂ x (y : E) = 0 := by
      have hi (i : α μ) : inner ℂ x ((b μ i : S μ) : E) = 0 := by
        exact (mem_orthogonal' _ _).mp hx _ (subset_span ⟨⟨μ, i⟩, rfl⟩)
      have hh := ((innerSL ℂ x).comp (S μ).subtypeL).hasSum ((b μ).hasSum_repr y)
      simpa [ContinuousLinearMap.comp_apply, hi] using hh.tsum_eq.symm
    have hx' : x ∈ (⨆ μ, eigenspace T.toLinearMap μ)ᗮ := by
      rw [← iInf_orthogonal]
      apply (mem_iInf _).mpr
      intro μ
      rw [mem_orthogonal']
      intro y hy
      exact hzero μ ⟨y, hy⟩
    rwa [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs] at hx'
  refine ⟨Σ μ, α μ, HilbertBasis.mkOfOrthogonalEqBot hv hsp, Sigma.fst, ?_⟩
  intro j
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact mem_eigenspace_iff.mp (b j.1 j.2).property

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
open ContinuousLinearMap Module.End Submodule


theorem solution.{u} : type_of% @_root_.OAI.QuantumTrace.exists_eigenbasis.{u} := @_root_.OAI.QuantumTrace.exists_eigenbasis.{u}

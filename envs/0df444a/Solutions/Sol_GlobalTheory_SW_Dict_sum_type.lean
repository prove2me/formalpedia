-- Prove2me | solution 1 for GlobalTheory.SW.Dict.sum_type
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:10.663801+00:00
-- url     : https://prove2.me/submissions/52651878-2458-4438-b72a-4ac1df2e698e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.Dict
namespace _root_.GlobalTheory.SW.Dict
theorem _root_.solution {Ψ : Finset (E →+* ℂ)}
    (hΨ : _root_.GlobalTheory.SW.IsType Ψ) (f : (E →+* ℂ) → ℂ) :
    ∑ σ, f σ = ∑ τ : Ψ, (f τ + f (ComplexEmbedding.conjugate τ.1)) := by
  classical
  have hc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
    fun φ => by ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [Finset.sum_add_distrib, Finset.sum_coe_sort Ψ f]
  have hconj : ∑ τ : Ψ, f (ComplexEmbedding.conjugate τ.1) = ∑ σ ∈ Ψᶜ, f σ := by
    rw [Finset.sum_coe_sort Ψ (fun σ => f (ComplexEmbedding.conjugate σ))]
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact Finset.mem_compl.mpr ((hΨ a).mp ha)
    · intro a ha
      have := (hΨ (ComplexEmbedding.conjugate a)).mpr
      rw [hc] at this
      exact this (Finset.mem_compl.mp ha)
    · intro a _; exact hc a
    · intro a _; exact hc a
    · intro a _; rfl
  rw [hconj]
  exact (Finset.sum_add_sum_compl Ψ f).symm
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict

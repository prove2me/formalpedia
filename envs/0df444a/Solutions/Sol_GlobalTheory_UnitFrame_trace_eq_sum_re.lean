-- Prove2me | solution 1 for GlobalTheory.UnitFrame.trace_eq_sum_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:20.470454+00:00
-- url     : https://prove2.me/submissions/ae6cf681-3cbc-4bbf-a523-65771d884a2e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemIffConjugateNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.UnitFrame
namespace _root_.GlobalTheory.UnitFrame
theorem _root_.solution (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : Ψ, 2 * (τ.1 z).re := by
  classical
  apply Complex.ofReal_injective
  have htr : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ τ : E →+* ℂ, τ z := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := z)
    rw [eq_ratCast] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun τ => τ z) (fun σ => σ z)
      (fun _ => rfl)).symm
  rw [Complex.ofReal_ratCast, htr]
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Ψ)]
  have hsplit : ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ ∉ Ψ), τ z
      = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ ∈ Ψ), conj (τ z) := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      by_contra h
      exact hτ ((hΨ _).2 (by simpa using h))
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact (hΨ τ).1 hτ
    · intro τ _; simp
    · intro τ _; simp
    · intro τ _; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hsplit, ← Finset.sum_add_distrib]
  rw [Finset.sum_subtype (Finset.univ.filter (· ∈ Ψ)) (p := (· ∈ Ψ)) (by simp)]
  refine Fintype.sum_congr _ _ (fun τ => ?_)
  rw [Complex.add_conj]
  push_cast; ring
end _root_.GlobalTheory.UnitFrame
end GlobalTheory.UnitFrame

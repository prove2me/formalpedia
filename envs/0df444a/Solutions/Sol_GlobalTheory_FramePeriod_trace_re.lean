-- Prove2me | solution 1 for GlobalTheory.FramePeriod.trace_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:25.904249+00:00
-- url     : https://prove2.me/submissions/5398529b-ccbb-46a4-a03a-dc9f9ede85e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [IsCMField E]
namespace GlobalTheory.FramePeriod
theorem _root_.solution (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : Ψ, 2 * (τ.1 z).re := by
  classical
  have h1 : algebraMap ℚ ℂ (Algebra.trace ℚ E z) = ∑ σ : E →ₐ[ℚ] ℂ, σ z :=
    trace_eq_sum_embeddings (K := ℚ) (E := ℂ) (x := z)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ z = ∑ σ : E →+* ℂ, σ z :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)) (fun σ : E →+* ℂ => σ z)
      (fun σ => σ z) (fun σ => rfl)).symm
  have h3 : ∑ σ ∈ Ψᶜ, σ z = ∑ σ ∈ Ψ, conj (σ z) := by
    refine Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      have := h (ComplexEmbedding.conjugate σ)
      rw [ComplexEmbedding.involutive_conjugate E σ] at this
      simp only [Finset.mem_compl] at hσ
      exact this.mpr hσ
    · intro σ hσ
      simp only [Finset.mem_compl]
      exact (h σ).mp hσ
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _; simp [ComplexEmbedding.conjugate_coe_eq]
  have h4 : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ ∈ Ψ, (σ z + conj (σ z)) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ) (Algebra.trace ℚ E z), h1, h2,
      ← Finset.sum_add_sum_compl Ψ, h3, Finset.sum_add_distrib]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h4, ← Finset.sum_coe_sort Ψ]
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Complex.add_conj]; push_cast; rfl
end GlobalTheory.FramePeriod

-- Prove2me | solution 1 for GlobalTheory.CMLattice.exists_real_combination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:03:57.516445+00:00
-- url     : https://prove2.me/submissions/ebe4d59f-7b38-4d93-805e-1e1f33e9abde

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Theorems.Thm_GlobalTheory_CMLattice_conjugate_conjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.CMLattice
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMLattice
theorem _root_.solution (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ → ComplexEmbedding.conjugate τ ∉ Ψ) (y : Ψ → ℂ) :
    ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ,
      ∀ τ : Ψ, y τ = ∑ i, (c i : ℂ) * τ.1 (integralBasis E i) := by
  classical
  let z : (E →+* ℂ) → ℂ := fun σ =>
    if hσ : σ ∈ Ψ then y ⟨σ, hσ⟩
    else if hσ' : ComplexEmbedding.conjugate σ ∈ Ψ then (starRingEnd ℂ) (y ⟨_, hσ'⟩) else 0
  let B := canonicalEmbedding.latticeBasis E
  have hz : ∀ σ, z σ = ∑ i, B.repr z i * σ (integralBasis E i) := by
    intro σ
    conv_lhs => rw [← B.sum_repr z]
    simp [B, canonicalEmbedding.latticeBasis_apply, Finset.sum_apply]
  refine ⟨fun i => (B.repr z i).re, fun τ => ?_⟩
  have h1 : y τ = ∑ i, B.repr z i * τ.1 (integralBasis E i) := by
    rw [← hz]; simp [z, τ.2]
  have h2 : (starRingEnd ℂ) (y τ) =
      ∑ i, B.repr z i * (starRingEnd ℂ) (τ.1 (integralBasis E i)) := by
    have := hz (ComplexEmbedding.conjugate τ.1)
    simp only [ComplexEmbedding.conjugate_coe_eq] at this
    rw [← this]
    have h3 := h τ.1 τ.2
    have h4 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ.1) ∈ Ψ := by
      rw [conjugate_conjugate]; exact τ.2
    simp only [z, dif_neg h3, dif_pos h4]
    congr 2
    exact Subtype.ext (conjugate_conjugate τ.1).symm
  have h5 : y τ = ∑ i, (starRingEnd ℂ) (B.repr z i) * τ.1 (integralBasis E i) := by
    have := congrArg (starRingEnd ℂ) h2
    simpa [map_sum] using this
  have h6 : y τ = (y τ + y τ) / 2 := by ring
  rw [h6]
  nth_rewrite 1 [h1]
  rw [h5, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_eq_add_conj]; ring
end GlobalTheory.CMLattice

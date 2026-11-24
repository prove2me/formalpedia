-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.sum_add_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:19.026326+00:00
-- url     : https://prove2.me/submissions/f565de3b-6e06-4c2d-a41e-92ad6741af91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_Base_map_cc
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e


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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (w : E) :
    ∑ τ : Ψ, τ.1 (w + cc w) = ((Algebra.trace ℚ E w : ℚ) : ℂ) := by
  have h2 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := w)
  have h3 : ∑ σ : E →ₐ[ℚ] ℂ, σ w = ∑ σ : E →+* ℂ, σ w :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom _ _) _ _ fun _ => rfl).symm
  have h4 : ∑ σ ∈ Ψᶜ, σ w = ∑ σ ∈ Ψ, σ (cc w) := by
    refine Finset.sum_bij' (fun σ _ => ComplexEmbedding.conjugate σ)
      (fun σ _ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      by_contra h
      exact (Finset.mem_compl.1 hσ) ((hΨ σ).2 h)
    · intro σ hσ
      exact Finset.mem_compl.2 ((hΨ σ).1 hσ)
    · intro σ _; ext x; simp
    · intro σ _; ext x; simp
    · intro σ _
      rw [Base.map_cc]
      simp
  rw [h3, ← Finset.sum_add_sum_compl Ψ, h4] at h2
  rw [Finset.sum_coe_sort Ψ (fun τ => τ (w + cc w))]
  simp only [map_add, Finset.sum_add_distrib]
  exact h2.symm
end GlobalTheory.SW.HeckeId

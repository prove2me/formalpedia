-- Prove2me | solution 1 for GlobalTheory.CMLattice.finrank_eq_two_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:03:58.278177+00:00
-- url     : https://prove2.me/submissions/34643fe1-2117-4f85-aef5-684ab486e096

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
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Module.finrank ℚ E = 2 * Ψ.card := by
  classical
  rw [← Embeddings.card E ℂ]
  have h1 : Ψ.card = Ψᶜ.card := by
    refine Finset.card_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
      (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_
    · intro τ hτ
      exact Finset.mem_compl.2 ((h τ).1 hτ)
    · intro τ hτ
      refine (h _).2 ?_
      rw [conjugate_conjugate]
      exact Finset.mem_compl.1 hτ
    · intro τ _; exact conjugate_conjugate τ
    · intro τ _; exact conjugate_conjugate τ
  rw [← Finset.card_add_card_compl Ψ, ← h1]; ring
end GlobalTheory.CMLattice

-- Prove2me | solution 1 for GlobalTheory.krasner_stabiliser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:01.529014+00:00
-- url     : https://prove2.me/submissions/2a3dadb8-9967-4dfa-88c1-7adef0ae07b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KrasnerLemmaDecompositionGroupStabilizerVersion
import Theorems.Thm_GlobalTheory_krasner_val_lt_apply_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (β β' : Ω)
    (h : ∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) :
    ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  intro σ hσ hfix
  by_contra hne
  have hσi : σ⁻¹ ∈ Dec (F := E) A := (Dec (F := E) A).inv_mem hσ
  have hne' : (σ⁻¹ : G E Ω) β ≠ β := by
    intro he
    apply hne
    conv_lhs => rw [← he]
    exact mul_inv_apply β
  have h1 := h σ hσ hne
  have h2 := h σ⁻¹ hσi hne'
  rw [← krasner_val_lt_apply_iff hσ, map_sub σ, map_sub σ, mul_inv_apply, hfix] at h2
  have e : β - σ β = (β - β') + (β' - σ β) := by ring
  have h3 : A.valuation (β - σ β) = A.valuation (σ β - β) := Valuation.map_sub_swap _ _ _
  have h4 : A.valuation (β - β') = A.valuation (β' - β) := Valuation.map_sub_swap _ _ _
  have key : A.valuation (β - σ β) < A.valuation (β - σ β) := by
    conv_lhs => rw [e]
    refine Valuation.map_add_lt _ ?_ h2
    rw [h4, h3]; exact h1
  exact lt_irrefl _ key
end GlobalTheory

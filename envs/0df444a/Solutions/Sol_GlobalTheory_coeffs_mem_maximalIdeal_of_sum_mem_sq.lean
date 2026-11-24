-- Prove2me | solution 1 for GlobalTheory.coeffs_mem_maximalIdeal_of_sum_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:53.852801+00:00
-- url     : https://prove2.me/submissions/dd593da4-e8ce-4a5f-9e6e-6407b89b15dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulMemOfForall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMinimalLocalGenerators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {n : ℕ} (z : Fin n → R) (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (hn : n = (maximalIdeal R).spanFinrank) (b : Fin n → R)
    (hb : ∑ j, b j * z j ∈ maximalIdeal R ^ 2) : ∀ j, b j ∈ maximalIdeal R := by
  have h : ∀ k, z k ∈ maximalIdeal R := fun k => hz ▸ Ideal.subset_span ⟨k, rfl⟩
  have h1 : Submodule.span R (Set.range fun k => (⟨z k, h k⟩ : maximalIdeal R)) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hz
  have h2 := IsLocalRing.CotangentSpace.span_image_eq_top_iff.2 h1
  rw [← Set.range_comp] at h2
  have hli := linearIndependent_of_top_le_span_of_card_le_finrank h2.ge (by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]; simp [hn])
  have key : ∑ k, residue R (b k) • ((maximalIdeal R).toCotangent ⟨z k, h k⟩ : CotangentSpace R)
      = 0 := by
    have h3 : ∑ k, residue R (b k) • ((maximalIdeal R).toCotangent ⟨z k, h k⟩ : CotangentSpace R)
        = (maximalIdeal R).toCotangent (∑ k, b k • (⟨z k, h k⟩ : maximalIdeal R)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      exact algebraMap_smul (ResidueField R) (b k) _
    rw [h3, Ideal.toCotangent_eq_zero]
    simpa using hb
  intro j
  have := Fintype.linearIndependent_iff.1 hli (fun k => residue R (b k)) key j
  exact (residue_eq_zero_iff _).1 this
end GlobalTheory

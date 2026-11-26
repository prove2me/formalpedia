-- Prove2me | solution 1 for LocalLemma.propertyB_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:31:33.224936+00:00
-- url     : https://prove2.me/submissions/6b0a6d78-c0ba-4128-9968-79c8e397f07c

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Theorems.Thm_LocalLemma_propertyB
public import Theorems.Thm_LocalLemma_exp_regular_bound

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {V : Type*} [DecidableEq V] (H : Finset (Finset V)) {k : ℕ}
    (h9 : 9 ≤ k) (hk : ∀ e ∈ H, e.card = k) (hdeg : ∀ v, (H.filter fun e => v ∈ e).card ≤ k) :
    ∃ c : V → Bool, ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y := by
  refine propertyB H hk (d := k * (k - 1)) (fun e he => ?_) (exp_regular_bound k h9)
  calc (H.filter fun f => f ≠ e ∧ ¬ Disjoint e f).card
      ≤ (e.biUnion fun v => (H.filter fun f => v ∈ f).erase e).card := by
        apply Finset.card_le_card
        intro f hf
        rw [Finset.mem_filter] at hf
        obtain ⟨v, hve, hvf⟩ := Finset.not_disjoint_iff.1 hf.2.2
        rw [Finset.mem_biUnion]
        exact ⟨v, hve, Finset.mem_erase.2 ⟨hf.2.1, Finset.mem_filter.2 ⟨hf.1, hvf⟩⟩⟩
    _ ≤ ∑ v ∈ e, ((H.filter fun f => v ∈ f).erase e).card := Finset.card_biUnion_le
    _ ≤ e.card • (k - 1) := Finset.sum_le_card_nsmul _ _ _ fun v hv => by
        rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨he, hv⟩)]
        have := hdeg v
        omega
    _ = k * (k - 1) := by rw [hk e he, smul_eq_mul]
end LocalLemma

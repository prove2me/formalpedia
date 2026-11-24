-- Prove2me | solution 1 for GlobalTheory.finrank_le_card_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:56:45.808803+00:00
-- url     : https://prove2.me/submissions/cf391134-7728-4ab6-97e0-cc2a7a1e3b6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (C V Γ : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u = ν v → ∃ c : C, u - c • v = 0 ∨ ν u < ν (u - c • v)) → ∀ (F : Submodule C V) [Module.Finite C F], ∃ f : Fin (Module.finrank C F) → V, (∀ i, f i ∈ F ∧ f i ≠ 0) ∧ Function.Injective (fun i => ν (f i)) := by
  intro C V Γ _ _ _ _ ν _h1 _h2 h3 F _
  classical
  set S : Set Γ := ν '' {u | u ∈ F ∧ u ≠ 0} with hS
  have hg : ∀ s ∈ S, ∃ u, (u ∈ F ∧ u ≠ 0) ∧ ν u = s := fun s hs => hs
  choose! g hgF hgν using hg
  suffices hcard : ∃ e : Fin (Module.finrank C F) → Γ, Function.Injective e ∧ ∀ i, e i ∈ S by
    obtain ⟨e, he, heS⟩ := hcard
    refine ⟨fun i => g (e i), fun i => hgF _ (heS i), ?_⟩
    intro i j hij
    simp only at hij
    rw [hgν _ (heS i), hgν _ (heS j)] at hij
    exact he hij
  by_cases hfin : S.Finite
  · have key : ∀ n : ℕ, ∀ u, u ∈ F → u ≠ 0 →
        (hfin.toFinset.filter (fun s => ν u < s)).card = n →
        u ∈ Submodule.span C (g '' S) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro u huF hu0 hn
      have huS : ν u ∈ S := ⟨u, ⟨huF, hu0⟩, rfl⟩
      obtain ⟨hgF', hg0⟩ := hgF _ huS
      obtain ⟨c, hc⟩ := h3 u (g (ν u)) hu0 hg0 (hgν _ huS).symm
      have hgmem : g (ν u) ∈ Submodule.span C (g '' S) := Submodule.subset_span ⟨ν u, huS, rfl⟩
      have hdec : u = (u - c • g (ν u)) + c • g (ν u) := (sub_add_cancel _ _).symm
      rw [hdec]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hgmem)
      rcases hc with hc | hc
      · rw [hc]; exact Submodule.zero_mem _
      · by_cases hw0 : u - c • g (ν u) = 0
        · rw [hw0]; exact Submodule.zero_mem _
        · have hwF : u - c • g (ν u) ∈ F := F.sub_mem huF (F.smul_mem c hgF')
          refine ih _ ?_ _ hwF hw0 rfl
          rw [← hn]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨ν (u - c • g (ν u)), ?_, ?_⟩
            · rw [Finset.mem_filter, Set.Finite.mem_toFinset]
              exact ⟨⟨_, ⟨hwF, hw0⟩, rfl⟩, hc⟩
            · rw [Finset.mem_filter]
              exact fun h => lt_irrefl _ h.2
          · intro s hs
            rw [Finset.mem_filter] at hs ⊢
            exact ⟨hs.1, lt_trans hc hs.2⟩
    have hle : F ≤ Submodule.span C (g '' S) := by
      intro u huF
      by_cases hu0 : u = 0
      · rw [hu0]; exact Submodule.zero_mem _
      · exact key _ u huF hu0 rfl
    have himg : g '' S = ((hfin.toFinset.image g : Finset V) : Set V) := by
      ext x; simp
    have hdim : Module.finrank C F ≤ hfin.toFinset.card := by
      rw [himg] at hle
      calc Module.finrank C F ≤ Module.finrank C (Submodule.span C ((hfin.toFinset.image g : Finset V) : Set V)) :=
            Submodule.finrank_mono hle
        _ ≤ (hfin.toFinset.image g).card := finrank_span_finset_le_card _
        _ ≤ hfin.toFinset.card := Finset.card_image_le
    let emb : Fin (Module.finrank C F) ↪ hfin.toFinset :=
      (Fin.castLEEmb hdim).trans hfin.toFinset.equivFin.symm.toEmbedding
    refine ⟨fun i => (emb i : Γ), ?_, ?_⟩
    · intro i j hij
      exact emb.injective (Subtype.ext hij)
    · intro i
      exact (Set.Finite.mem_toFinset hfin).1 (emb i).2
  · let emb : ℕ ↪ S := Set.Infinite.natEmbedding S hfin
    refine ⟨fun i => (emb i : Γ), ?_, fun i => (emb i).2⟩
    intro i j hij
    exact Fin.ext (emb.injective (Subtype.ext hij))
end GlobalTheory

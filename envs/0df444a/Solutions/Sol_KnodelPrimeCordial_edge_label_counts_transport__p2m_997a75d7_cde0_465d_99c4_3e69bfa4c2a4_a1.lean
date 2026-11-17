-- Prove2me | solution 1 for KnodelPrimeCordial.edge_label_counts_transport__p2m_997a75d7_cde0_465d_99c4_3e69bfa4c2a4_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:20:29.699094+00:00
-- url     : https://prove2.me/submissions/466be479-3eed-4c80-8f5e-b44af903b000

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
theorem KnodelPrimeCordial.edge_label_counts_transport__p2m_997a75d7_cde0_465d_99c4_3e69bfa4c2a4_a1 {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (e : V ≃ W) (hadj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) (f : V → ℕ) : (KnodelPrimeCordial.edgesLabelZero G f).card = (KnodelPrimeCordial.edgesLabelZero H (f ∘ e.symm)).card ∧ (KnodelPrimeCordial.edgesLabelOne G f).card = (KnodelPrimeCordial.edgesLabelOne H (f ∘ e.symm)).card := by
  have gen : ∀ Q : ℕ → Prop, [DecidablePred Q] →
      (G.edgeFinset.filter (fun s => Q (KnodelPrimeCordial.edgeGcd f s))).card =
      (H.edgeFinset.filter (fun s => Q (KnodelPrimeCordial.edgeGcd (f ∘ e.symm) s))).card := by
    intro Q _
    apply Finset.card_bij (fun s _ => Sym2.map e s)
    · intro s hs
      induction s using Sym2.ind with
      | h a b =>
        simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Sym2.map_pair_eq] at hs ⊢
        refine ⟨(hadj a b).mp hs.1, ?_⟩
        simpa [KnodelPrimeCordial.edgeGcd] using hs.2
    · intro s _ t _ h
      exact Sym2.map.injective e.injective h
    · intro t ht
      refine ⟨Sym2.map e.symm t, ?_, ?_⟩
      · induction t using Sym2.ind with
        | h a b =>
          simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            Sym2.map_pair_eq] at ht ⊢
          refine ⟨(hadj _ _).mpr (by simpa using ht.1), ?_⟩
          simpa [KnodelPrimeCordial.edgeGcd] using ht.2
      · rw [Sym2.map_map]; simp
  exact ⟨gen (fun g => 1 < g), gen (fun g => g = 1)⟩

theorem solution {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (e : V ≃ W) (hadj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) (f : V → ℕ) : (KnodelPrimeCordial.edgesLabelZero G f).card = (KnodelPrimeCordial.edgesLabelZero H (f ∘ e.symm)).card ∧ (KnodelPrimeCordial.edgesLabelOne G f).card = (KnodelPrimeCordial.edgesLabelOne H (f ∘ e.symm)).card := by
  have gen : ∀ Q : ℕ → Prop, [DecidablePred Q] →
      (G.edgeFinset.filter (fun s => Q (KnodelPrimeCordial.edgeGcd f s))).card =
      (H.edgeFinset.filter (fun s => Q (KnodelPrimeCordial.edgeGcd (f ∘ e.symm) s))).card := by
    intro Q _
    apply Finset.card_bij (fun s _ => Sym2.map e s)
    · intro s hs
      induction s using Sym2.ind with
      | h a b =>
        simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Sym2.map_pair_eq] at hs ⊢
        refine ⟨(hadj a b).mp hs.1, ?_⟩
        simpa [KnodelPrimeCordial.edgeGcd] using hs.2
    · intro s _ t _ h
      exact Sym2.map.injective e.injective h
    · intro t ht
      refine ⟨Sym2.map e.symm t, ?_, ?_⟩
      · induction t using Sym2.ind with
        | h a b =>
          simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            Sym2.map_pair_eq] at ht ⊢
          refine ⟨(hadj _ _).mpr (by simpa using ht.1), ?_⟩
          simpa [KnodelPrimeCordial.edgeGcd] using ht.2
      · rw [Sym2.map_map]; simp
  exact ⟨gen (fun g => 1 < g), gen (fun g => g = 1)⟩


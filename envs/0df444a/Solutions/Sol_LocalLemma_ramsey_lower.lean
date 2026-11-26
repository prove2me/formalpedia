-- Prove2me | solution 1 for LocalLemma.ramsey_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:29:48.689514+00:00
-- url     : https://prove2.me/submissions/ff38fe52-d5f4-46bf-bd1a-4c4dd7a65b92

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Theorems.Thm_LocalLemma_exists_good_coloring
public import Theorems.Thm_LocalLemma_card_filter_superset_le

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {n k : ℕ}
    (h : 2 * Real.exp 1 * ((k.choose 2 * n.choose (k - 2) : ℕ) + 1) ≤ 2 ^ k.choose 2) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  classical
  set P := (Finset.univ : Finset (Fin n)).powersetCard k with hP
  set f : Fin P.card ≃ P := P.equivFin.symm with hf
  let D : Fin P.card → Finset (Finset (Fin n)) := fun a => (f a).1.powersetCard 2
  let Γ : SimpleGraph (Fin P.card) :=
    SimpleGraph.fromRel fun a b => 2 ≤ ((f a).1 ∩ (f b).1).card
  have hfk : ∀ a, (f a).1.card = k := fun a => (Finset.mem_powersetCard.1 (f a).2).2
  have hΓ : ∀ i j, j ≠ i → ¬ Γ.Adj i j → Disjoint (D i) (D j) := by
    intro i j hji hadj
    have hlt : ¬ 2 ≤ ((f i).1 ∩ (f j).1).card := by
      intro hc
      exact hadj ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hji.symm, Or.inl hc⟩)
    rw [Finset.disjoint_left]
    intro e hei hej
    rw [Finset.mem_powersetCard] at hei hej
    apply hlt
    rw [← hei.2]
    exact Finset.card_le_card (Finset.subset_inter hei.1 hej.1)
  have hD : ∀ a, k.choose 2 ≤ (D a).card := by
    intro a
    simp only [D, Finset.card_powersetCard, hfk]; rfl
  have hdeg : ∀ a, Γ.degree a ≤ k.choose 2 * n.choose (k - 2) := by
    intro a
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hsub : (Γ.neighborFinset a).image (fun b => (f b).1) ⊆
        ((f a).1.powersetCard 2).biUnion (fun e => P.filter (e ⊆ ·)) := by
      intro T hT
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hT
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.fromRel_adj] at hb
      have h2 : 2 ≤ ((f a).1 ∩ (f b).1).card := by
        rcases hb.2 with h' | h'
        · exact h'
        · rwa [Finset.inter_comm]
      obtain ⟨e, he, hec⟩ := Finset.exists_subset_card_eq h2
      rw [Finset.mem_biUnion]
      refine ⟨e, Finset.mem_powersetCard.2 ⟨he.trans Finset.inter_subset_left, hec⟩, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨(f b).2, he.trans Finset.inter_subset_right⟩
    rw [← Finset.card_image_of_injective _ (fun b b' he => f.injective (Subtype.ext he))]
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    refine (Finset.sum_le_card_nsmul _ _ (n.choose (k - 2)) fun e he => ?_).trans ?_
    · exact card_filter_superset_le e (Finset.mem_powersetCard.1 he).2
    · simp [hfk]
  have hc : Real.exp 1 * (2 * (1 / 2) ^ k.choose 2) *
      (((k.choose 2 * n.choose (k - 2) : ℕ) : ℝ) + 1) ≤ 1 := by
    rw [one_div_pow, mul_one_div, mul_div_assoc', div_mul_eq_mul_div,
      div_le_one (by positivity)]
    linarith
  obtain ⟨ω, hω⟩ := exists_good_coloring D Γ hΓ hD hdeg hc
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel fun u v => ω {u, v} = true
  have key : ∀ S : Finset (Fin n), S.card = k → ∀ b : Bool,
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ω {u, v} = b) → False := by
    intro S hS b hb
    have hSP : S ∈ P := Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩
    apply hω (f.symm ⟨S, hSP⟩)
    refine ⟨b, fun e he => ?_⟩
    simp only [D, Equiv.apply_symm_apply, Finset.mem_powersetCard] at he
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 he.2
    exact hb u (he.1 (by simp)) v (he.1 (by simp)) huv
  refine ⟨G, fun S hS => ?_, fun S hS => ?_⟩
  · refine key S hS.card_eq true fun u hu v hv huv => ?_
    have := ((SimpleGraph.fromRel_adj _ _ _).1 (hS.isClique hu hv huv)).2
    rcases this with h' | h'
    · exact h'
    · rwa [Finset.pair_comm]
  · refine key S hS.card_eq false fun u hu v hv huv => ?_
    have := hS.isClique hu hv huv
    rw [SimpleGraph.compl_adj, SimpleGraph.fromRel_adj] at this
    have h' : ¬ ω {u, v} = true := fun h' => this.2 ⟨huv, Or.inl h'⟩
    simpa using h'
end LocalLemma

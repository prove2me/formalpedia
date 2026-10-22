-- Prove2me | solution 1 for LNTopology.Hermetic.lemma_B_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:59:29.94851+00:00
-- url     : https://prove2.me/submissions/1ed42db9-7474-4021-a9c0-5915886dec01

import Mathlib
set_option autoImplicit false

theorem solution {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (d : ℝ) (hd : 0 < d)
    (havg : 2 * d ≤ (∑ v, (G.degree v : ℝ)) / (Fintype.card W : ℝ)) :
    ∃ W' : Finset W, W'.Nonempty ∧
      ∀ v ∈ W', d < ((G.neighborFinset v ∩ W').card : ℝ) := by
  set A : W → W → ℝ := fun u w => if G.Adj u w then 1 else 0 with hA
  have hAsymm : ∀ u w, A u w = A w u := by
    intro u w; simp only [hA]; simp [G.adj_comm]
  have hAirr : ∀ u, A u u = 0 := by intro u; simp [hA]
  have hcard : ∀ (u : W) (S : Finset W), ((G.neighborFinset u ∩ S).card : ℝ) = ∑ w ∈ S, A u w := by
    intro u S
    have : G.neighborFinset u ∩ S = S.filter (fun w => G.Adj u w) := by
      ext w; simp [and_comm]
    rw [this, Finset.card_filter]
    push_cast
    rfl
  have key : ∀ (n : ℕ) (S : Finset W), S.card = n → S.Nonempty →
      2 * d * (S.card : ℝ) ≤ ∑ u ∈ S, ∑ w ∈ S, A u w →
      ∃ W' : Finset W, W'.Nonempty ∧ ∀ v ∈ W', d < ((G.neighborFinset v ∩ W').card : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro S hS hne
      exact absurd (Finset.card_eq_zero.mp hS) hne.ne_empty
    | succ n ih =>
      intro S hS hne hineq
      by_cases hall : ∀ v ∈ S, d < ((G.neighborFinset v ∩ S).card : ℝ)
      · exact ⟨S, hne, hall⟩
      · push Not at hall
        obtain ⟨v, hvS, hv⟩ := hall
        rw [hcard] at hv
        set S' := S.erase v with hS'
        have hS'card : S'.card = n := by
          rw [hS', Finset.card_erase_of_mem hvS, hS]; rfl
        have hSins : S = insert v S' := (Finset.insert_erase hvS).symm
        have hvS' : v ∉ S' := Finset.notMem_erase v S
        have hav : ∑ w ∈ S, A v w = ∑ w ∈ S', A v w := by
          rw [hSins, Finset.sum_insert hvS', hAirr, zero_add]
        have hD : ∑ u ∈ S, ∑ w ∈ S, A u w
            = ∑ u ∈ S', ∑ w ∈ S', A u w + 2 * ∑ w ∈ S, A v w := by
          have h1 : ∑ u ∈ S, ∑ w ∈ S, A u w = ∑ w ∈ S, A v w + ∑ u ∈ S', ∑ w ∈ S, A u w := by
            conv_lhs => rw [hSins, Finset.sum_insert hvS']
            rw [← hSins]
          have h2 : ∑ u ∈ S', ∑ w ∈ S, A u w = ∑ u ∈ S', (A u v + ∑ w ∈ S', A u w) := by
            apply Finset.sum_congr rfl
            intro u hu
            conv_lhs => rw [hSins, Finset.sum_insert hvS']
          rw [h1, h2, Finset.sum_add_distrib]
          have h3 : ∑ u ∈ S', A u v = ∑ w ∈ S, A v w := by
            rw [hav]
            exact Finset.sum_congr rfl (fun u _ => hAsymm u v)
          rw [h3]; ring
        by_cases hne' : S'.Nonempty
        · apply ih S' hS'card hne'
          rw [hS'card] at *
          have : (S.card : ℝ) = (n : ℝ) + 1 := by rw [hS]; push_cast; ring
          rw [hD, this] at hineq
          rw [hS'card]
          nlinarith
        · exfalso
          have hS'e : S' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
          have : ∑ u ∈ S, ∑ w ∈ S, A u w = 0 := by
            rw [hD, hav, hS'e]; simp
          have hc : S.card = 1 := by rw [hSins, hS'e]; simp
          rw [hc, this] at hineq
          simp at hineq
          linarith
  have hW : Nonempty W := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at havg
    linarith
  have hcardpos : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ hcardpos] at havg
  apply key (Fintype.card W) Finset.univ rfl Finset.univ_nonempty
  have : ∑ u, (G.degree u : ℝ) = ∑ u ∈ (Finset.univ : Finset W), ∑ w ∈ (Finset.univ : Finset W), A u w := by
    apply Finset.sum_congr rfl
    intro u _
    rw [← hcard, Finset.inter_univ, SimpleGraph.card_neighborFinset_eq_degree]
  rw [Finset.card_univ]
  linarith

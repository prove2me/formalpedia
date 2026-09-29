-- Prove2me | solution 1 for MonotoneDP.Increase.lemma3_compact_sublevel_min
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:06:35.655265+00:00
-- url     : https://prove2.me/submissions/0e6dc7aa-8f83-48e5-a644-c75d270adafe

import Mathlib

theorem solution {C : Type*} [TopologicalSpace C] [T2Space C]
    (f : C → EReal) (U : Set C) (hU : U.Nonempty)
    (hcpt : ∀ lam : ℝ, IsCompact {u ∈ U | f u ≤ (lam : EReal)}) :
    ∃ u ∈ U, IsMinOn f U u := by
  by_cases htop : ∀ u ∈ U, f u = ⊤
  · obtain ⟨u, hu⟩ := hU
    refine ⟨u, hu, ?_⟩
    intro x hx
    show f u ≤ f x
    rw [htop u hu, htop x hx]
  · push_neg at htop
    obtain ⟨u0, hu0U, hu0⟩ := htop
    have hmemT : ∀ x ∈ U, f x ≠ ⊤ → ∃ lam : ℝ,
        ({u ∈ U | f u ≤ (lam : EReal)}).Nonempty := by
      intro x hx hxt
      by_cases hb : f x = ⊥
      · exact ⟨0, ⟨x, hx, by rw [hb]; exact bot_le⟩⟩
      · exact ⟨(f x).toReal, ⟨x, hx, by rw [EReal.coe_toReal hxt hb]⟩⟩
    obtain ⟨lam0, hlam0⟩ := hmemT u0 hu0U hu0
    let T : Set ℝ := {lam : ℝ | ({u ∈ U | f u ≤ (lam : EReal)}).Nonempty}
    have hlam0T : lam0 ∈ T := hlam0
    have hne : Nonempty T := ⟨⟨lam0, hlam0T⟩⟩
    have hint : (⋂ lam : T, {u ∈ U | f u ≤ ((lam : ℝ) : EReal)}).Nonempty := by
      refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ ?_ ?_ ?_ ?_
      · intro a b
        rcases le_total (a : ℝ) (b : ℝ) with h | h
        · refine ⟨a, subset_rfl, fun u hu => ⟨hu.1, le_trans hu.2 ?_⟩⟩
          exact EReal.coe_le_coe_iff.mpr h
        · refine ⟨b, fun u hu => ⟨hu.1, le_trans hu.2 ?_⟩, subset_rfl⟩
          exact EReal.coe_le_coe_iff.mpr h
      · intro i; exact i.2
      · intro i; exact hcpt _
      · intro i; exact (hcpt _).isClosed
    obtain ⟨u, hu⟩ := hint
    have huU : u ∈ U := (Set.mem_iInter.mp hu ⟨lam0, hlam0T⟩).1
    refine ⟨u, huU, ?_⟩
    intro x hx
    show f u ≤ f x
    by_cases hxt : f x = ⊤
    · rw [hxt]; exact le_top
    · by_cases hb : f x = ⊥
      · have hall : ∀ r : ℝ, f u ≤ (r : EReal) := by
          intro r
          have hrT : r ∈ T := ⟨x, hx, by rw [hb]; exact bot_le⟩
          exact (Set.mem_iInter.mp hu ⟨r, hrT⟩).2
        have hfu : f u = ⊥ := by
          rcases eq_or_ne (f u) ⊤ with h | h
          · exfalso
            have h0 := hall 0
            rw [h] at h0
            simp at h0
          · rcases eq_or_ne (f u) ⊥ with h' | h'
            · exact h'
            · exfalso
              set r := (f u).toReal with hr
              have hc : ((r : ℝ) : EReal) = f u := EReal.coe_toReal h h'
              have h2 := hall (r - 1)
              rw [← hc, EReal.coe_le_coe_iff] at h2
              linarith
        rw [hfu, hb]
      · have hrT : (f x).toReal ∈ T := ⟨x, hx, by rw [EReal.coe_toReal hxt hb]⟩
        have h1 := (Set.mem_iInter.mp hu ⟨(f x).toReal, hrT⟩).2
        rwa [EReal.coe_toReal hxt hb] at h1

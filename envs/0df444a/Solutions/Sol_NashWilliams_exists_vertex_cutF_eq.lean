-- Prove2me | solution 1 for NashWilliams.exists_vertex_cutF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:44:46.793358+00:00
-- url     : https://prove2.me/submissions/2aea4ce4-f82b-4242-a9dc-dff62427a344

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Mader
public import Theorems.Thm_NashWilliams_exists_tight_of_not_req
public import Theorems.Thm_NashWilliams_exists_smaller_tight
public import Theorems.Thm_NashWilliams_cutF_pair_le
public import Theorems.Thm_NashWilliams_cutF_sdiff_eq


set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
namespace NashWilliams
theorem _root_.solution {K : ℕ} (hK : 1 ≤ K) {T : Finset V} (hT : 1 < T.card)
    {ends : ι → V × V} {F : Finset ι} (hin : Inside T ends F) (hreq : Req K T ends F)
    (hmin : ∀ i ∈ F, ¬ Req K T ends (F.erase i)) : ∃ s ∈ T, cutF ends F {s} = K := by
  have hsing : ∀ x ∈ T, K ≤ cutF ends F {x} := by
    intro x hx
    refine hreq _ (by simpa using hx) (singleton_nonempty x) ?_
    intro h
    rw [← h] at hT
    simp at hT
  -- there is a tight set
  have hex : ∃ S, Tight K T ends F S := by
    rcases F.eq_empty_or_nonempty with hF | ⟨i, hi⟩
    · exfalso
      obtain ⟨x, hx⟩ : T.Nonempty := card_pos.1 (by omega)
      have := hsing x hx
      simp [hF, cutF] at this
      omega
    · obtain ⟨S, hS, -⟩ := exists_tight_of_not_req hreq (hmin i hi)
      exact ⟨S, hS⟩
  classical
  obtain ⟨X, hXmem, hXmin⟩ := (T.powerset.filter fun S => Tight K T ends F S).exists_min_image
    card (by
      obtain ⟨S, hS⟩ := hex
      exact ⟨S, mem_filter.2 ⟨mem_powerset.2 hS.1, hS⟩⟩)
  have hX : Tight K T ends F X := (mem_filter.1 hXmem).2
  have hnosmaller : ∀ Z, Tight K T ends F Z → X.card ≤ Z.card := fun Z hZ =>
    hXmin Z (mem_filter.2 ⟨mem_powerset.2 hZ.1, hZ⟩)
  by_cases h1 : X.card = 1
  · obtain ⟨s, rfl⟩ := card_eq_one.1 h1
    exact ⟨s, hX.1 (mem_singleton_self s), hX.2.2.2⟩
  exfalso
  have h2 : 1 < X.card := by
    have := hX.2.1.card_pos
    omega
  by_cases hinner : ∃ i ∈ F, (ends i).1 ∈ X ∧ (ends i).2 ∈ X
  · obtain ⟨i, hi, ha, hb⟩ := hinner
    obtain ⟨Y, hY, hcr⟩ := exists_tight_of_not_req hreq (hmin i hi)
    by_cases haY : (ends i).1 ∈ Y
    · have hbY : (ends i).2 ∉ Y := fun h => hcr (by simp [haY, h])
      obtain ⟨Z, hZ, hlt⟩ := exists_smaller_tight hreq hX hY ha hb haY hbY
      exact absurd (hnosmaller Z hZ) (not_le.2 hlt)
    · have hbY : (ends i).2 ∈ Y := by
        by_contra h
        exact hcr (by simp [haY, h])
      -- use the complement `T \ Y`, which is also tight
      obtain ⟨hYT, hYne, hYT', hYc⟩ := hY
      have hY' : Tight K T ends F (T \ Y) := by
        refine ⟨sdiff_subset, ?_, ?_, by rw [cutF_sdiff_eq hin]; exact hYc⟩
        · obtain ⟨t, htT, htY⟩ : ∃ t ∈ T, t ∉ Y := by
            by_contra! h
            exact hYT' (Subset.antisymm hYT h)
          exact ⟨t, mem_sdiff.2 ⟨htT, htY⟩⟩
        · intro h
          obtain ⟨y, hy⟩ := hYne
          have : y ∈ T \ Y := by rw [h]; exact hYT hy
          simp [hy] at this
      have haY' : (ends i).1 ∈ T \ Y := mem_sdiff.2 ⟨hX.1 ha, haY⟩
      have hbY' : (ends i).2 ∉ T \ Y := by simp [hbY]
      obtain ⟨Z, hZ, hlt⟩ := exists_smaller_tight hreq hX hY' ha hb haY' hbY'
      exact absurd (hnosmaller Z hZ) (not_le.2 hlt)
  · push Not at hinner
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.1 h2
    have := cutF_pair_le hxy hx hy (fun i hi h => hinner i hi h.1 h.2)
    have hx' := hsing x (hX.1 hx)
    have hy' := hsing y (hX.1 hy)
    have := hX.2.2.2
    omega
end NashWilliams

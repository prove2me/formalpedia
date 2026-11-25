-- Prove2me | solution 1 for NashWilliams.exists_orientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:45:54.085889+00:00
-- url     : https://prove2.me/submissions/2122b3ca-c4af-49ae-9fe9-2b184fc80945

module
public import Definitions.Def_NashWilliamsLib_Mader
public import Definitions.Def_NashWilliamsLib_Splitting
public import Definitions.Def_NashWilliamsLib_Orientation
public import Theorems.Thm_NashWilliams_outCutF_mono
public import Theorems.Thm_NashWilliams_outCutF_erase_congr
public import Theorems.Thm_NashWilliams_split_all
public import Theorems.Thm_NashWilliams_req_erase_of_req
public import Theorems.Thm_NashWilliams_exists_vertex_cutF_eq
public import Theorems.Thm_NashWilliams_outCutF_erase_le


set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
omit [DecidableEq ι]
namespace NashWilliams
theorem _root_.solution (k : ℕ) : ∀ (n : ℕ) (T : Finset V) (ends : ι → V × V) (F : Finset ι),
    F.card = n → Inside T ends F → Req (2 * k) T ends F →
    ∃ o : ι → Bool, ∀ S ⊆ T, S.Nonempty → S ≠ T → k ≤ outCutF ends o F S := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T ends F hn hin hreq
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨fun _ => true, fun _ _ _ _ => Nat.zero_le _⟩
  by_cases hT : T.card ≤ 1
  · refine ⟨fun _ => true, fun S hS hne hneT => ?_⟩
    have h1 := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hS, hneT⟩)
    have h2 := hne.card_pos
    omega
  push Not at hT
  by_cases hdel : ∃ i ∈ F, Req (2 * k) T ends (F.erase i)
  · obtain ⟨i, hi, hreq'⟩ := hdel
    obtain ⟨o, ho⟩ := ih _ (hn ▸ card_erase_lt_of_mem hi) T ends (F.erase i) rfl
      (fun l hl => hin l (mem_of_mem_erase hl)) hreq'
    exact ⟨o, fun S hS hne hneT => (ho S hS hne hneT).trans (outCutF_erase_le ends o F S i)⟩
  push Not at hdel
  obtain ⟨s, hsT, hcut⟩ := exists_vertex_cutF_eq (by omega) hT hin hreq hdel
  obtain ⟨ends', F', hcard, hin', hreq', hcut0, htrans⟩ :=
    split_all (by omega) k ends F hin (req_erase_of_req hreq s) hcut
  -- the only edges at `s` left are loops; drop them
  have hloopS : ∀ l ∈ F', ((ends' l).1 = s) ↔ ((ends' l).2 = s) := by
    intro l hl
    by_contra h
    have : 0 < cutF ends' F' {s} := card_pos.2 ⟨l, mem_filter.2 ⟨hl, by simpa using h⟩⟩
    omega
  set F'' := F'.filter fun l => (ends' l).1 ≠ s ∧ (ends' l).2 ≠ s with hF''
  have hF''s : ∀ l ∈ F'', (ends' l).1 ≠ s ∧ (ends' l).2 ≠ s := fun l hl => (mem_filter.1 hl).2
  have hcut'' : ∀ S, cutF ends' F'' S = cutF ends' F' S := by
    intro S
    unfold cutF
    rw [hF'', filter_filter]
    congr 1
    refine filter_congr fun l hl => ?_
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      by_contra h'
      have h1 : (ends' l).1 = s := by
        by_contra h1
        exact h' ⟨h1, fun h2 => h1 ((hloopS l hl).2 h2)⟩
      have h2 := (hloopS l hl).1 h1
      exact h (by rw [h1, h2])
  have hin'' : Inside (T.erase s) ends' F'' := by
    intro l hl
    obtain ⟨h1, h2⟩ := hin' l (mem_filter.1 hl).1
    obtain ⟨h3, h4⟩ := hF''s l hl
    exact ⟨mem_erase.2 ⟨h3, h1⟩, mem_erase.2 ⟨h4, h2⟩⟩
  have hreq'' : Req (2 * k) (T.erase s) ends' F'' := fun S hS hne hneT =>
    (hcut'' S).symm ▸ hreq' S hS hne hneT
  obtain ⟨o', ho'⟩ := ih F''.card (by
    have : F''.card ≤ F'.card := card_filter_le _ _
    omega) (T.erase s) ends' F'' rfl hin'' hreq''
  obtain ⟨o, ha, hb1, hb2⟩ := htrans o'
  refine ⟨o, fun S hS hne hneT => ?_⟩
  by_cases h1 : S = {s}
  · exact h1 ▸ hb1
  by_cases h2 : S = T.erase s
  · exact h2 ▸ hb2
  have hS' : S.erase s ⊆ T.erase s := erase_subset_erase s hS
  have hne' : (S.erase s).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    by_cases hxs : x = s
    · subst hxs
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      exact h1 (by
        ext y
        constructor
        · intro hy
          by_contra hys
          have : y ∈ S.erase x := mem_erase.2 ⟨by simpa using hys, hy⟩
          simp [h] at this
        · intro hy
          rw [mem_singleton] at hy
          exact hy ▸ hx)
    · exact ⟨x, mem_erase.2 ⟨hxs, hx⟩⟩
  have hneT' : S.erase s ≠ T.erase s := by
    intro h
    by_cases hsS : s ∈ S
    · exact hneT (by rw [← insert_erase hsS, h, insert_erase hsT])
    · exact h2 (by rw [← h, erase_eq_of_notMem hsS])
  calc k ≤ outCutF ends' o' F'' (S.erase s) := ho' _ hS' hne' hneT'
    _ = outCutF ends' o' F'' S := outCutF_erase_congr hF''s S
    _ ≤ outCutF ends' o' F' S := outCutF_mono (filter_subset _ _) S
    _ ≤ outCutF ends o F S := ha S
end NashWilliams

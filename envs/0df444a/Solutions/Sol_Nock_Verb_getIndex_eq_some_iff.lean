-- Prove2me | solution 1 for Nock.Verb.getIndex_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:00.349806+00:00
-- url     : https://prove2.me/submissions/29af7c5b-7462-44bc-8364-79c9ce52b306

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_isPendingIdx_iff_mem
section
@[expose] public section
namespace Nock
namespace Verb
private theorem maximumPendingIndex_eq_none :
    ∀ {L : List (Nat × Verb)},
      maximumPendingIndex L = none ↔ ∀ p ∈ L, p.2.isPending = false
  | [] => by simp [maximumPendingIndex]
  | (i, w) :: t => by
      simp only [maximumPendingIndex]
      by_cases hw : w.isPending = true
      · rw [if_pos hw]
        constructor
        · intro h; cases maximumPendingIndex t <;> simp at h
        · intro h; exact absurd (h (i, w) (by simp)) (by simp [hw])
      · rw [if_neg hw]
        rw [maximumPendingIndex_eq_none]
        constructor
        · intro h p hp
          rcases List.mem_cons.1 hp with heq | hmem
          · subst heq; simpa using hw
          · exact h p hmem
        · intro h p hp; exact h p (List.mem_cons_of_mem _ hp)
private theorem maximumPendingIndex_mem :
    ∀ {L : List (Nat × Verb)} {i : Nat},
      maximumPendingIndex L = some i → ∃ v, (i, v) ∈ L ∧ v.isPending = true
  | [], i, h => by simp [maximumPendingIndex] at h
  | (j, w) :: t, i, h => by
      simp only [maximumPendingIndex] at h
      by_cases hw : w.isPending = true
      · rw [if_pos hw] at h
        cases hr : maximumPendingIndex t with
        | none => rw [hr] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨w, by simp, hw⟩
        | some k =>
            rw [hr] at h; simp only [Option.some.injEq] at h
            -- h : Nat.max j k = i
            rcases Nat.le_total j k with hjk | hkj
            · have hmx : Nat.max j k = k := Nat.max_eq_right hjk
              have hik : i = k := hmx ▸ h.symm
              subst hik
              obtain ⟨v, hv, hvp⟩ := maximumPendingIndex_mem hr
              exact ⟨v, List.mem_cons_of_mem _ hv, hvp⟩
            · have hmx : Nat.max j k = j := Nat.max_eq_left hkj
              have hij : i = j := hmx ▸ h.symm
              subst hij
              exact ⟨w, by simp, hw⟩
      · rw [if_neg hw] at h
        obtain ⟨v, hv, hvp⟩ := maximumPendingIndex_mem h
        exact ⟨v, List.mem_cons_of_mem _ hv, hvp⟩
private theorem maximumPendingIndex_ge :
    ∀ {L : List (Nat × Verb)} {i : Nat},
      maximumPendingIndex L = some i → ∀ j v, (j, v) ∈ L → v.isPending = true → j ≤ i
  | [], i, h => by simp [maximumPendingIndex] at h
  | (p, w) :: t, i, h => by
      intro j v hmem hvp
      simp only [maximumPendingIndex] at h
      by_cases hw : w.isPending = true
      · rw [if_pos hw] at h
        cases hr : maximumPendingIndex t with
        | none =>
            rw [hr] at h; simp only [Option.some.injEq] at h
            -- h : p = i
            rcases List.mem_cons.1 hmem with heq | hmem'
            · simp only [Prod.mk.injEq] at heq; have hjp := heq.1; omega
            · have hnone := (maximumPendingIndex_eq_none).1 hr
              exact absurd (hnone (j, v) hmem') (by simp [hvp])
        | some k =>
            rw [hr] at h; simp only [Option.some.injEq] at h
            -- h : Nat.max p k = i  (kept as an opaque atom for omega)
            rcases List.mem_cons.1 hmem with heq | hmem'
            · simp only [Prod.mk.injEq] at heq
              have hjp : j = p := heq.1
              have hle : p ≤ Nat.max p k := Nat.le_max_left p k; omega
            · have hjk := maximumPendingIndex_ge hr j v hmem' hvp
              have hle : k ≤ Nat.max p k := Nat.le_max_right p k; omega
      · rw [if_neg hw] at h
        rcases List.mem_cons.1 hmem with heq | hmem'
        · simp only [Prod.mk.injEq] at heq
          obtain ⟨_, rfl⟩ := heq; simp [hvp] at hw
        · exact maximumPendingIndex_ge h j v hmem' hvp
private theorem maximumPendingIndex_of {L : List (Nat × Verb)} {i : Nat}
    (hmem : ∃ v, (i, v) ∈ L ∧ v.isPending = true)
    (hmax : ∀ j v, (j, v) ∈ L → v.isPending = true → j ≤ i) :
    maximumPendingIndex L = some i := by
  obtain ⟨v, hv, hvp⟩ := hmem
  cases hm : maximumPendingIndex L with
  | none =>
      have hnone := (maximumPendingIndex_eq_none).1 hm
      exact absurd (hnone (i, v) hv) (by simp [hvp])
  | some m =>
      obtain ⟨w, hw, hwp⟩ := maximumPendingIndex_mem hm
      have h1 : m ≤ i := hmax m w hw hwp
      have h2 : i ≤ m := maximumPendingIndex_ge hm i v hv hvp
      have : m = i := by omega
      rw [this]
end Verb
end Nock
end
end

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {a : Verb} {i : Nat} :
    getIndex a = some i ↔ IsMaxPending dfsLt a i := by
  unfold getIndex IsMaxPending dfsLt
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨v, hv, hvp⟩ := maximumPendingIndex_mem h
      exact isPendingIdx_iff_mem.2 ⟨v, hv, hvp⟩
    · intro j hj
      rw [Nat.not_lt]
      obtain ⟨w, hw, hwp⟩ := isPendingIdx_iff_mem.1 hj
      exact maximumPendingIndex_ge h j w hw hwp
  · rintro ⟨hip, hmax⟩
    obtain ⟨v, hv, hvp⟩ := isPendingIdx_iff_mem.1 hip
    apply maximumPendingIndex_of ⟨v, hv, hvp⟩
    intro j w hjw hwp
    have hj : IsPendingIdx a j := isPendingIdx_iff_mem.2 ⟨w, hjw, hwp⟩
    have := hmax j hj
    omega
end Nock.Verb

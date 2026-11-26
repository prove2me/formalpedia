-- Prove2me | solution 1 for NisanRonen.Rounding.loadStates_length_le
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:39:47.077796+00:00
-- url     : https://prove2.me/submissions/c7426dbe-1aac-40e2-afe8-23bd67ff0585

import Definitions.Def_NisanRonen_Rounding_boundedLoadDP
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Nodup

open NisanRonen.Rounding
set_option autoImplicit false

private def allocationLoads {n : ℕ} :
    List (Fin n → ℕ) → List (Fin n) → Fin n → ℕ
  | column :: columns, agent :: agents, i =>
      (if i = agent then column i else 0) + allocationLoads columns agents i
  | _, _, _ => 0

private theorem mem_keepLoadStates {n : ℕ} {states : List (LoadState n)} {s : LoadState n}
    (h : s ∈ keepLoadStates states) : s ∈ states := by
  cases states with
  | nil => simp [keepLoadStates] at h
  | cons t states =>
    rw [keepLoadStates, List.eraseDupsBy_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · have hm := mem_keepLoadStates (show s ∈ keepLoadStates _ from h)
      exact List.mem_cons_of_mem t (List.mem_filter.mp hm).1
termination_by states.length
decreasing_by
  subst_vars
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem state_sound {n : ℕ} {columns : List (Fin n → ℕ)} {s : LoadState n}
    (h : s ∈ loadStates columns) :
    s.2.length = columns.length ∧ s.1 = allocationLoads columns s.2 := by
  induction columns generalizing s with
  | nil =>
    simp only [loadStates, List.mem_singleton] at h
    subst s
    exact ⟨rfl, rfl⟩
  | cons column columns ih =>
    rw [loadStates] at h
    obtain ⟨t, ht, hs⟩ := List.mem_flatMap.mp (mem_keepLoadStates h)
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hlen, hload⟩ := ih ht
    refine ⟨by simp [prependJob, hlen], ?_⟩
    funext j
    simp [prependJob, allocationLoads, hload]

private theorem kept_keys_nodup {n : ℕ} (states : List (LoadState n)) :
    ((keepLoadStates states).map Prod.fst).Nodup := by
  cases states with
  | nil => simp [keepLoadStates]
  | cons t states =>
    rw [keepLoadStates, List.eraseDupsBy_cons, List.map_cons, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨s, hs, hkeys⟩ := List.mem_map.mp hm
      have hf := (List.mem_filter.mp (mem_keepLoadStates hs)).2
      simp [hkeys] at hf
    · exact kept_keys_nodup _
termination_by states.length
decreasing_by
  subst_vars
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem allocationLoads_le {n : ℕ} (cap : ℕ) (columns : List (Fin n → ℕ))
    (agents : List (Fin n)) (hc : ∀ c ∈ columns, ∀ i, c i ≤ cap) (i : Fin n) :
    allocationLoads columns agents i ≤ columns.length * cap := by
  induction columns generalizing agents with
  | nil => simp [allocationLoads]
  | cons c cs ih =>
    cases agents with
    | nil => simp [allocationLoads]
    | cons a as =>
      have hc0 := hc c List.mem_cons_self i
      have hcs := ih as (fun d hd => hc d (List.mem_cons_of_mem c hd))
      have hfirst : (if i = a then c i else 0) ≤ cap := by split <;> omega
      rw [allocationLoads, List.length_cons, Nat.succ_mul]
      omega

theorem solution {n : ℕ} (cap : ℕ) (columns : List (Fin n → ℕ))
    (hc : ∀ c ∈ columns, ∀ i, c i ≤ cap) :
    (loadStates columns).length ≤ (columns.length * cap + 1) ^ n := by
  let keys := (loadStates columns).map Prod.fst
  have hn : keys.Nodup := by
    cases columns with
    | nil => simp [keys, loadStates]
    | cons c cs => exact kept_keys_nodup _
  have hb : ∀ v ∈ keys, ∀ i, v i ≤ columns.length * cap := by
    intro v hv i
    obtain ⟨s, hs, hkey⟩ := List.mem_map.mp hv
    rw [← hkey, (state_sound hs).2]
    exact allocationLoads_le cap columns s.2 hc i
  let packed (j : Fin keys.length) (i : Fin n) : Fin (columns.length * cap + 1) :=
    ⟨keys[j] i, Nat.lt_succ_of_le (hb _ (List.getElem_mem j.isLt) i)⟩
  have hinj : Function.Injective packed := by
    intro j₁ j₂ h
    apply (List.nodup_iff_injective_getElem.mp hn)
    funext i
    exact congrArg (fun q : Fin n → Fin (columns.length * cap + 1) => (q i).val) h
  simpa [keys, Fintype.card_fun] using Fintype.card_le_of_injective packed hinj


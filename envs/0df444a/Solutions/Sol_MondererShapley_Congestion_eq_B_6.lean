-- Prove2me | solution 1 for MondererShapley.Congestion.eq_B_6
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:20:27.872105+00:00
-- url     : https://prove2.me/submissions/110d6d12-bf54-407c-89f0-071ec57a3426

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotential
import Definitions.Def_MondererShapley_Congestion_FacilityConstruction

open MondererShapley.Congestion

private theorem minus_unique {ι : Type*} [DecidableEq ι] {Y : ι → Type*}
    [∀ i, DecidableEq (Y i)] (i j : ι) (m q : ∀ k, Y k)
    (h : epsMinus i m = epsMinus j q) :
    i = j ∧ ∀ k, k ≠ i → m k = q k := by
  have hij : i = j := by
    by_contra hn
    have hh := congrFun (congrFun h j) (m j)
    simp [epsMinus, Ne.symm hn] at hh
  subst j
  refine ⟨rfl, ?_⟩
  intro k hk
  have hh := congrFun (congrFun h k) (m k)
  simpa [epsMinus, hk] using hh

private theorem minus_value {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}
    [∀ i, DecidableEq (Y i)] (u : ι → (∀ i, Y i) → ℝ)
    (P : (∀ i, Y i) → ℝ) (hP : MondererShapley.ClosedPath.IsPotential u P)
    (i : ι) (m : ∀ k, Y k) : x1 u P (epsMinus i m) = u i m - P m := by
  classical
  unfold x1
  split
  next h =>
    let j := h.choose
    let q := h.choose_spec.choose
    have he : epsMinus i m = epsMinus j q := h.choose_spec.choose_spec
    obtain ⟨hj, hq⟩ := minus_unique i j m q he
    have hprof : q = Function.update m i (q i) := by
      funext k
      by_cases hk : k = i
      · subst k; simp
      · simp [Function.update_of_ne hk, (hq k hk).symm]
    change u j q - P q = _
    rw [← hj, hprof]
    have hp := hP i m (q i) (m i)
    simp only [Function.update_eq_self] at hp
    linarith
  next h => exact (h ⟨i, m, rfl⟩).elim

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] (u : ι → (∀ i, Y i) → ℝ) (P : (∀ i, Y i) → ℝ)
    (hP : MondererShapley.ClosedPath.IsPotential u P) (m : ∀ i, Y i) (i : ι) :
    vecSum (x1 u P) (stratFac i (m i) ∩ (⋃ k ∈ {k | k ≠ i}, stratFac k (m k))ᶜ) =
        x1 u P (epsMinus i m) ∧
      x1 u P (epsMinus i m) = u i m - P m := by
  classical
  have hv := minus_value u P hP i m
  refine ⟨?_, hv⟩
  unfold vecSum
  let B := stratFac i (m i) ∩ (⋃ k ∈ {k | k ≠ i}, stratFac k (m k))ᶜ
  have hmem : epsMinus i m ∈ B := by
    simp [B, stratFac, epsMinus]
  change (∑ᶠ ε ∈ B, x1 u P ε) = _
  rw [finsum_mem_def]
  rw [finsum_eq_single _ (epsMinus i m)]
  · simp [hmem]
  · intro ε hε
    by_cases hB : ε ∈ B
    · rw [Set.indicator_of_mem hB]
      unfold x1
      split
      next h =>
        obtain ⟨j, q, he⟩ := h
        have hij : j = i := by
          by_contra hn
          have hh := hB.2
          apply hh
          simp only [Set.mem_iUnion]
          exact ⟨j, ⟨hn, by simpa [he, stratFac, epsMinus]⟩⟩
        subst j
        have hq : ∀ k, k ≠ i → q k = m k := by
          intro k hk
          have hh := hB.2
          have hh' : ε ∉ stratFac k (m k) := by
            intro hh'; apply hh; simp only [Set.mem_iUnion]; exact ⟨k, ⟨hk, hh'⟩⟩
          exact (by simpa [he, stratFac, epsMinus, hk] using hh' : m k = q k).symm
        have hsame : ε = epsMinus i m := by
          rw [he]
          funext k y
          by_cases hk : k = i
          · subst k; simp [epsMinus]
          · simp [epsMinus, hk, hq k hk]
        exact (hε hsame).elim
      next h => rfl
    · simp [Set.indicator_of_notMem hB]

#print axioms solution

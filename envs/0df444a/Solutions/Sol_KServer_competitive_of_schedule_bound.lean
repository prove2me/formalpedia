-- Prove2me | solution 1 for KServer.competitive_of_schedule_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T03:48:33.061668+00:00
-- url     : https://prove2.me/submissions/9380813d-ac97-4662-b8e5-78154883860c

import Mathlib
import Definitions.Def_KServer_model

open KServer

private theorem schedule_exists' {k : ℕ} (hk : 1 ≤ k) {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem σ _ j.2]
  simp

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (A : OnlineAlgorithm k M) (c a : ℝ) (hc : 0 ≤ c)
    (h : ∀ (σ : List M) (S : ℕ → Config k M), ServesFrom (A.conf []) σ S →
      A.cost σ ≤ c * (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))) + a) :
    IsCompetitive A c := by
  classical
  refine ⟨a, fun σ => ?_⟩
  set T : Set ℝ := {x : ℝ | ∃ S : ℕ → Config k M, ServesFrom (A.conf []) σ S ∧
    x = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} with hT
  obtain ⟨S₀, hS₀⟩ := schedule_exists' hk (A.conf []) σ
  have hTne : T.Nonempty := ⟨_, ⟨S₀, hS₀, rfl⟩⟩
  have hmem : ∀ x ∈ T, A.cost σ - a ≤ c * x := by
    rintro x ⟨S, hS, rfl⟩
    linarith [h σ S hS]
  rcases eq_or_lt_of_le hc with hc0 | hc0
  · obtain ⟨x, hx⟩ := hTne
    have hx' := hmem x hx
    rw [← hc0] at hx' ⊢
    simp only [zero_mul] at hx' ⊢
    linarith
  · have hdiv : (A.cost σ - a) / c ≤ sInf T := by
      refine le_csInf hTne ?_
      intro x hx
      rw [div_le_iff₀ hc0]
      linarith [hmem x hx]
    rw [div_le_iff₀ hc0] at hdiv
    have hoff : offlineCost (A.conf []) σ = sInf T := by rw [hT]; rfl
    rw [hoff]
    linarith [hdiv]

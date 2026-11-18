-- Prove2me | solution 1 for MetricMSO.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-17T14:11:31.391315+00:00
-- url     : https://prove2.me/submissions/cef8b8a8-f6a8-4916-9a95-b0dffb430ef5

import Mathlib

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) {s t : V} (p : G.Walk s t)
    (hp : p.IsPath) :
    p.length = G.dist s t ↔
      ∃ lam : V → ℤ, (∀ u v, G.Adj u v → |lam u - lam v| ≤ 1) ∧
        ∀ i, i < p.length → lam (p.getVert (i + 1)) = lam (p.getVert i) + 1 := by
  constructor
  · intro hlen
    refine ⟨fun v => (G.dist s v : ℤ), ?_, ?_⟩
    · intro u v huv
      change |(G.dist s u : ℤ) - (G.dist s v : ℤ)| ≤ 1
      have h := huv.diff_dist_adj (u := s)
      rcases h with h | h | h
      · have h' : (G.dist s v : ℤ) = (G.dist s u : ℤ) := by exact_mod_cast h
        rw [h']
        simp
      · have h' : (G.dist s v : ℤ) = (G.dist s u : ℤ) + 1 := by
          rw [h]
          push_cast
          ring
        rw [h']
        simp
      · by_cases hzero : G.dist s u = 0
        · have hv0 : G.dist s v = 0 := by omega
          rw [hzero, hv0]
          simp
        · have h' : (G.dist s v : ℤ) = (G.dist s u : ℤ) - 1 := by
            rw [h]
            have : 1 ≤ G.dist s u := Nat.one_le_iff_ne_zero.mpr hzero
            omega
          rw [h']
          simp
    · intro i hi
      have htake_i : (p.take i).length = i := by
        rw [SimpleGraph.Walk.take_length, Nat.min_eq_left (le_of_lt hi)]
      have htake_succ : (p.take (i + 1)).length = i + 1 := by
        rw [SimpleGraph.Walk.take_length, Nat.min_eq_left (Nat.succ_le_of_lt hi)]
      have hdi : G.dist s (p.getVert i) = i := by
        rw [← SimpleGraph.length_eq_dist_of_subwalk hlen (p.isSubwalk_take i)]
        exact htake_i
      have hdsucc : G.dist s (p.getVert (i + 1)) = i + 1 := by
        rw [← SimpleGraph.length_eq_dist_of_subwalk hlen (p.isSubwalk_take (i + 1))]
        exact htake_succ
      change (G.dist s (p.getVert (i + 1)) : ℤ) = (G.dist s (p.getVert i) : ℤ) + 1
      rw [hdsucc, hdi]
      push_cast
      ring
  · rintro ⟨lam, hlip, hinc⟩
    have hinc' : ∀ i ≤ p.length, lam (p.getVert i) = lam s + (i : ℤ) := by
      intro i hi
      induction i with
      | zero => simp [SimpleGraph.Walk.getVert_zero]
      | succ i ih =>
        have hi' : i < p.length := Nat.lt_of_succ_le hi
        have hstep := hinc i hi'
        have hprev := ih (le_of_lt hi')
        rw [hstep, hprev]
        push_cast
        ring
    have hlen_p : lam t - lam s = (p.length : ℤ) := by
      have h := hinc' p.length le_rfl
      rw [SimpleGraph.Walk.getVert_length] at h
      linarith
    have hwalk : ∀ {u v : V} (q : G.Walk u v), lam v - lam u ≤ (q.length : ℤ) := by
      intro u v q
      induction q with
      | nil => simp
      | cons hadj q ih =>
        rename_i a b c
        have h1 : lam b - lam a ≤ 1 := by
          have h := abs_le.mp (hlip a b hadj)
          linarith [h.1, h.2]
        have h2 : lam c - lam b ≤ (q.length : ℤ) := ih
        rw [SimpleGraph.Walk.length_cons]
        push_cast
        linarith
    have hreach : G.Reachable s t := p.reachable
    obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
    have hle : p.length ≤ G.dist s t := by
      rw [← hq]
      have := hwalk q
      linarith
    exact le_antisymm hle (G.dist_le p)


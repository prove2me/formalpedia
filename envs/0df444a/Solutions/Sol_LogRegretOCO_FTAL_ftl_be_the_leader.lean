-- Prove2me | solution 1 for LogRegretOCO.FTAL.ftl_be_the_leader
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:24:55.392853+00:00
-- url     : https://prove2.me/submissions/be0cb5a8-405b-4c5a-bf56-e79b8c577cc7

import Mathlib
import Definitions.Def_LogRegretOCO_FTAL_IsFTLRun

open LogRegretOCO.FTAL

/-- Be-the-leader: the leader sequence has no regret against any fixed point. -/
private theorem btl {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : IsFTLRun P f x) :
    ∀ T : ℕ, ∀ u ∈ P, ∑ t ∈ Finset.Icc 1 T, f t (x (t + 1)) ≤ ∑ t ∈ Finset.Icc 1 T, f t u := by
  intro T
  induction T with
  | zero => intro u _; simp
  | succ T ih =>
    intro u hu
    have hmem : x (T + 2) ∈ P := (hx (T + 2) (by omega)).1
    have h1 : ∑ t ∈ Finset.Icc 1 T, f t (x (t + 1))
        ≤ ∑ t ∈ Finset.Icc 1 T, f t (x (T + 2)) := ih _ hmem
    have hIcc : Finset.Icc 1 (T + 1) = insert (T + 1) (Finset.Icc 1 T) := by
      ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnm : (T + 1) ∉ Finset.Icc 1 T := by simp
    have hsplit : ∀ g : ℕ → ℝ, ∑ t ∈ Finset.Icc 1 (T + 1), g t
        = g (T + 1) + ∑ t ∈ Finset.Icc 1 T, g t := by
      intro g; rw [hIcc, Finset.sum_insert hnm]
    rw [hsplit (fun t => f t (x (t + 1))), hsplit (fun t => f t u)]
    -- the leader at time T+2 beats `u` on rounds 1..T+1
    have hlead := (hx (T + 2) (by omega)).2 u hu
    have hIco : Finset.Ico 1 (T + 2) = Finset.Icc 1 (T + 1) := by
      ext a; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco, hsplit (fun t => f t (x (T + 2))), hsplit (fun t => f t u)] at hlead
    have : f (T + 1) (x (T + 1 + 1)) = f (T + 1) (x (T + 2)) := by norm_num
    rw [this]
    linarith

theorem solution {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : IsFTLRun P f x) (T : ℕ) :
    ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t u
        ≤ ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t (x (t + 1)) := by
  intro u hu
  have := btl P f x hx T u hu
  linarith

-- Prove2me | solution 1 for MarkovMixing.strong_stationary_bound
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:23:45.492271+00:00
-- url     : https://prove2.me/submissions/d7e29d1d-0a75-40d9-9c26-ef82bfa572f4

import Theorems.Thm_MarkovMixing_tv_le_sep
import Theorems.Thm_MarkovMixing_sep_le_stopping_tail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open scoped BigOperators
open scoped Matrix
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ)
    (hs : ∀ x : V, IsStrongStationaryTime P π x s) (t : ℕ) :
    distStationary P π t ≤ ⨆ x : V, stopTailProb P x s t := by
  classical
  -- the stationary distribution of an irreducible chain is strictly positive
  have hpow_nonneg : ∀ (n : ℕ) (a b : V), 0 ≤ (P ^ n) a b := by
    intro n
    induction n with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ m ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hP.1 w b)
  have hstat_pow : ∀ n : ℕ, π ᵥ* (P ^ n) = π := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]
  have hpos : ∀ y : V, 0 < π y := by
    intro y
    obtain ⟨z, hz⟩ : ∃ z : V, 0 < π z := by
      by_contra hcon
      push_neg at hcon
      have hzero : ∀ z : V, π z = 0 := fun z => le_antisymm (hcon z) (hπ.1.1 z)
      have h := hπ.1.2
      simp [hzero] at h
    obtain ⟨n, hn⟩ := hirr z y
    have hval : π y = ∑ w, π w * (P ^ n) w y := (congrFun (hstat_pow n) y).symm
    have hterm : π z * (P ^ n) z y ≤ ∑ w, π w * (P ^ n) w y :=
      Finset.single_le_sum (f := fun w => π w * (P ^ n) w y)
        (fun w _ => mul_nonneg (hπ.1.1 w) (hpow_nonneg n w y)) (Finset.mem_univ z)
    have : 0 < π z * (P ^ n) z y := mul_pos hz hn
    rw [hval]; linarith
  -- chain the two milestone bounds
  have hbddR : BddAbove (Set.range fun x : V => stopTailProb P x s t) :=
    Set.Finite.bddAbove (Set.range fun x : V => stopTailProb P x s t).toFinite
  refine ciSup_le fun x => ?_
  calc tvDist (rowDist P t x) π
      ≤ sepDist P π x t := MarkovMixing.tv_le_sep P hP π hπ hpos x t
    _ ≤ stopTailProb P x s t :=
        MarkovMixing.sep_le_stopping_tail P hP hirr π hπ s x (hs x) t
    _ ≤ ⨆ y : V, stopTailProb P y s t := le_ciSup hbddR x

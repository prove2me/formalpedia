-- Prove2me | solution 1 for HarmonicGames.Pareto.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:25:27.866472+00:00
-- url     : https://prove2.me/submissions/1b2d0f52-f5ae-4d8b-b6fe-562aea94bf37

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_Pareto_Games

open HarmonicGames.Decomposition HarmonicGames.GenericPure HarmonicGames.Pareto

private theorem normalize_game {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : Games E) :
    ∃ v : Games E, potentialComponent E v = potentialComponent E u ∧
      harmonicComponent E v = harmonicComponent E u ∧
      (∀ p m, v m p ≤ 0) ∧
      (∀ p, AGT.IsPureNash (payoff E u) p → ∀ m, v m p = 0) := by
  classical
  let B (m : ι) (p : ∀ k, E k) : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty (fun a : E m => u m (Function.update p m a))
  let v : Games E := WithLp.toLp 2 (fun m => WithLp.toLp 2 (fun p => u m p-B m p))
  have hBu (p : ∀ k, E k) (m : ι) : u m p ≤ B m p := by
    simpa only [Function.update_eq_self] using (Finset.le_sup' (fun a : E m => u m (Function.update p m a))
      (Finset.mem_univ (p m)))
  have hBeq (m : ι) (p q : ∀ k, E k) (h : ∀ k, k ≠ m → p k = q k) : B m p = B m q := by
    apply congrArg (Finset.univ.sup' Finset.univ_nonempty)
    funext a
    apply congrArg (fun r : ∀ k, E k => u m r)
    funext k
    by_cases hk : k=m
    · subst k; simp
    · simpa [Function.update_of_ne hk] using h k hk
  have hflow : Dop E v = Dop E u := by
    change (∑ m, Dm E m (v m)) = ∑ m, Dm E m (u m)
    apply Finset.sum_congr rfl
    intro m hm
    apply HarmonicGames.Decomposition.C1.ext
    intro p q
    change (if MComparable E m p q then (1:ℝ) else 0) *
      ((u m q-B m q)-(u m p-B m p)) =
      (if MComparable E m p q then (1:ℝ) else 0) * (u m q-u m p)
    by_cases hpq : MComparable E m p q
    · rw [if_pos hpq, hBeq m p q hpq.2]
      ring
    · simp [hpq]
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · simp only [potentialComponent, LinearMap.comp_apply, hflow]
  · simp only [harmonicComponent, LinearMap.comp_apply, hflow]
  · intro p m
    change u m p-B m p ≤ 0
    exact sub_nonpos.mpr (hBu p m)
  · intro p hp m
    have hB : B m p ≤ u m p := by
      apply Finset.sup'_le
      intro a ha
      exact hp m a
    change u m p-B m p = 0
    exact sub_eq_zero.mpr (le_antisymm (hBu p m) hB)


theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) :
    ∃ û : HarmonicGames.Decomposition.Games E, HarmonicGames.Decomposition.potentialComponent E û = HarmonicGames.Decomposition.potentialComponent E u ∧
      HarmonicGames.Decomposition.harmonicComponent E û = HarmonicGames.Decomposition.harmonicComponent E u ∧
      ∀ p : ∀ m, E m, AGT.IsPureNash (HarmonicGames.GenericPure.payoff E u) p → ∀ m, HarmonicGames.GenericPure.payoff E û m p = 0 := by
  obtain ⟨v,hP,hH,hn,hz⟩ := normalize_game E u
  exact ⟨v,hP,hH,hz⟩

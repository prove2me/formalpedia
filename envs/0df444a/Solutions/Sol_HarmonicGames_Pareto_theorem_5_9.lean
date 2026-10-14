-- Prove2me | solution 1 for HarmonicGames.Pareto.theorem_5_9
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:36:21.698683+00:00
-- url     : https://prove2.me/submissions/0dc7a314-e52c-4451-abf7-73e18292a35e

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_Pareto_Games
import Definitions.Def_HarmonicGames_Pareto_IsParetoOptimal
import Theorems.Thm_HarmonicGames_Pareto_same_components_same_pure_nash

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
    (u : HarmonicGames.Decomposition.Games E) (hNE : ∃ p : ∀ m, E m, AGT.IsPureNash (HarmonicGames.GenericPure.payoff E u) p) :
    ∃ ū : HarmonicGames.Decomposition.Games E, HarmonicGames.Decomposition.potentialComponent E ū = HarmonicGames.Decomposition.potentialComponent E u ∧
      HarmonicGames.Decomposition.harmonicComponent E ū = HarmonicGames.Decomposition.harmonicComponent E u ∧
      ∀ p : ∀ m, E m, AGT.IsPureNash (HarmonicGames.GenericPure.payoff E ū) p ↔ IsParetoOptimal (HarmonicGames.GenericPure.payoff E ū) p := by
  classical
  obtain ⟨v,hP,hH,hn,hz⟩ := normalize_game E u
  refine ⟨v,hP,hH,?_⟩
  have he (p : ∀ m,E m) : AGT.IsPureNash (payoff E v) p ↔ AGT.IsPureNash (payoff E u) p :=
    same_components_same_pure_nash E v u hP hH p
  intro p
  constructor
  · intro hp ⟨q,hq,k,hk⟩
    have hz' := hz p ((he p).mp hp) k
    change v k p < v k q at hk
    linarith [hn q k]
  · intro hp
    by_contra hnot
    have hstrict : ∃ m, v m p < 0 := by
      by_contra hh
      push_neg at hh
      apply hnot
      intro m a
      exact (hn _ m).trans (hh m)
    obtain ⟨m,hm⟩ := hstrict
    obtain ⟨r,hr⟩ := hNE
    apply hp
    refine ⟨r,?_,m,?_⟩
    · intro k
      change v k p ≤ v k r
      rw [hz r hr k]
      exact hn p k
    · change v m p < v m r
      rw [hz r hr m]
      exact hm

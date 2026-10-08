-- Prove2me | solution 1 for HartSchmeidler.Finite.aux_game_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:35:08.127273+00:00
-- url     : https://prove2.me/submissions/0dd1fbc3-57c8-406f-aa48-76f951dc1d86

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HartSchmeidler_Finite_Game

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open HartSchmeidler.Finite

namespace HsWork

open Finset

theorem aux_game_correspondence {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    (h : ι → (∀ i, S i) → ℝ) (p : (∀ i, S i) → ℝ) :
    IsCorrelatedEq h p ↔ AGT.IsLottery p ∧
      ∀ y : Deviation S → ℝ, AGT.IsLottery y →
        0 ≤ ∑ s, ∑ c, p s * y c * auxPayoff h s c := by
  have key : ∀ y : Deviation S → ℝ,
      ∑ s, ∑ c, p s * y c * auxPayoff h s c = ∑ c, y c * ∑ s, p s * auxPayoff h s c := by
    intro y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hc : ∀ c : Deviation S, ∑ s, p s * auxPayoff h s c =
      ∑ s ∈ Finset.univ.filter (fun s : ∀ j, S j => s c.1 = c.2.1),
        p s * (h c.1 s - h c.1 (Function.update s c.1 c.2.2)) := by
    intro c
    unfold auxPayoff
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  constructor
  · rintro ⟨hp, hce⟩
    refine ⟨hp, fun y hy => ?_⟩
    rw [key]
    refine Finset.sum_nonneg fun c _ => mul_nonneg (hy.1 c) ?_
    rw [hc]
    exact hce c.1 c.2.1 c.2.2
  · rintro ⟨hp, hy⟩
    refine ⟨hp, fun i r t => ?_⟩
    classical
    obtain ⟨c0, hc0⟩ : ∃ c0 : Deviation S, c0 = ⟨i, (r, t)⟩ := ⟨_, rfl⟩
    have hlot : AGT.IsLottery (Pi.single c0 (1 : ℝ) : Deviation S → ℝ) := by
      refine ⟨fun c => ?_, by simp⟩
      by_cases hcc : c = c0
      · subst hcc; simp
      · simp [Pi.single_apply, hcc]
    have := hy _ hlot
    rw [key] at this
    have h2 : ∑ c, (Pi.single c0 (1 : ℝ) : Deviation S → ℝ) c *
        ∑ s, p s * auxPayoff h s c = ∑ s, p s * auxPayoff h s c0 := by
      rw [Finset.sum_eq_single c0 (fun c _ hc => by simp [Pi.single_apply, hc]) (by simp)]
      simp
    rw [h2, hc c0] at this
    subst hc0
    exact this


end HsWork

open HartSchmeidler.Finite Finset

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    (h : ι → (∀ i, S i) → ℝ) (p : (∀ i, S i) → ℝ) :
    IsCorrelatedEq h p ↔ AGT.IsLottery p ∧
      ∀ y : Deviation S → ℝ, AGT.IsLottery y →
        0 ≤ ∑ s, ∑ c, p s * y c * auxPayoff h s c :=
  HsWork.aux_game_correspondence h p

#print axioms solution

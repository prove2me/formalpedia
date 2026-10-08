-- Prove2me | solution 1 for KelsoCrawford.NoCore.inequalities_24_to_27
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:48:57.78631+00:00
-- url     : https://prove2.me/submissions/fa477241-2bba-4440-ade4-c9bb17557528

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Model
import Definitions.Def_KelsoCrawford_NoCore_Notions
import Definitions.Def_KelsoCrawford_NoCore_Example

open KelsoCrawford.NoCore

theorem solution (A : Allocation (Fin 3) (Fin 2))
    (hj : A.hired 0 = {0}) (hk : A.hired 1 = {1, 2})
    (h24 : ¬ noCoreMarket.CoalitionCanStrictlyImprove KelsoCrawford.ContinuousCore.anySalary A 0 {2})
    (h25 : ¬ noCoreMarket.CoalitionCanStrictlyImprove KelsoCrawford.ContinuousCore.anySalary A 0 {0, 1})
    (h26 : ¬ noCoreMarket.CoalitionCanStrictlyImprove KelsoCrawford.ContinuousCore.anySalary A 1 {0})
    (h27 : ¬ noCoreMarket.CoalitionCanStrictlyImprove KelsoCrawford.ContinuousCore.anySalary A 1 {2}) :
    4 - A.sal 0 + A.sal 2 ≥ 17 / 4 ∧
    4 - A.sal 0 + A.sal 0 + A.sal 1 ≥ 15 / 2 ∧
    15 / 2 - A.sal 1 - A.sal 2 + A.sal 0 ≥ 17 / 4 ∧
    15 / 2 - A.sal 1 - A.sal 2 + A.sal 2 ≥ 4 := by
  classical
  have pj : KelsoCrawford.Process.profit (noCoreMarket.y 0) (A.hired 0) A.sal = 4 - A.sal 0 := by
    rw [hj]; simp +decide [KelsoCrawford.Process.profit, noCoreMarket, techJ]
  have pk : KelsoCrawford.Process.profit (noCoreMarket.y 1) (A.hired 1) A.sal =
      15 / 2 - A.sal 1 - A.sal 2 := by
    rw [hk]; simp +decide [KelsoCrawford.Process.profit, noCoreMarket, techK]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    apply h24
    refine ⟨fun i => A.sal i + (17 / 4 - (4 - A.sal 0 + A.sal 2)) / 2, ?_, ?_, ?_⟩
    · simp [KelsoCrawford.ContinuousCore.anySalary]
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      subst i
      dsimp [noCoreMarket]
      linarith
    · rw [pj]
      simp +decide [KelsoCrawford.Process.profit, noCoreMarket, techJ]
      linarith
  · by_contra h
    apply h25
    refine ⟨fun i => A.sal i + (15 / 2 - (4 - A.sal 0 + A.sal 0 + A.sal 1)) / 3, ?_, ?_, ?_⟩
    · simp [KelsoCrawford.ContinuousCore.anySalary]
    · intro i hi
      dsimp [noCoreMarket]
      linarith
    · rw [pj]
      simp +decide [KelsoCrawford.Process.profit, noCoreMarket, techJ]
      linarith
  · by_contra h
    apply h26
    refine ⟨fun i => A.sal i + (17 / 4 - (15 / 2 - A.sal 1 - A.sal 2 + A.sal 0)) / 2, ?_, ?_, ?_⟩
    · simp [KelsoCrawford.ContinuousCore.anySalary]
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      subst i
      dsimp [noCoreMarket]
      linarith
    · rw [pk]
      simp +decide [KelsoCrawford.Process.profit, noCoreMarket, techK]
      linarith
  · by_contra h
    apply h27
    refine ⟨fun i => A.sal i + (4 - (15 / 2 - A.sal 1 - A.sal 2 + A.sal 2)) / 2, ?_, ?_, ?_⟩
    · simp [KelsoCrawford.ContinuousCore.anySalary]
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      subst i
      dsimp [noCoreMarket]
      linarith
    · rw [pk]
      simp +decide [KelsoCrawford.Process.profit, noCoreMarket, techK]
      linarith


#print axioms solution

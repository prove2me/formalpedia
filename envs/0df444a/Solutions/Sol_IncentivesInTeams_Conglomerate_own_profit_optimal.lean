-- Prove2me | solution 1 for IncentivesInTeams.Conglomerate.own_profit_optimal
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T12:53:08.236948+00:00
-- url     : https://prove2.me/submissions/c29b3355-3904-43e7-8112-6153c1f8c301

import Theorems.Thm_IncentivesInTeams_Conglomerate_appendix_A1

open IncentivesInTeams.Conglomerate

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀]
    {S : ι → Type*} [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*}
    {D₀ : Type*} {D : ι → Type*} (T : Model S₀ S Z₀ Z M₀ M D₀ D) (hT : T.WeightsOK)
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (hA : T.AssumptionA βs) (A : ι → ℝ) :
    T.InClassJ (T.WII βs A) ∧ T.IsOptimal (T.WII βs A) βs := by
  classical
  constructor
  · exact ⟨T.CII βs A, fun _ _ _ => rfl⟩
  · intro i b hb
    have hself : βs.update i (βs.sub i) = βs := by
      cases βs
      simp only [JointStrategy.update, Function.update_eq_self]
    have hbase := appendix_A1 T hT βs A i (βs.sub i) (hA.1.2 i)
    rw [hself] at hbase
    have hdev := appendix_A1 T hT βs A i b hb
    have hmem : T.Mem (βs.update i b) := by
      refine ⟨hA.1.1, ?_⟩
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [JointStrategy.update, Function.update_self] using hb
      · simpa only [JointStrategy.update, Function.update_of_ne hji] using hA.1.2 j
    constructor
    · have hle := hA.2.1 (βs.update i b) hmem
      linarith
    · intro hne
      have hlt := hA.2.2 i b hb hne
      linarith

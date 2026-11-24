-- Prove2me | solution 1 for IndependentInfoPricing.Main.reverse_closure
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T18:55:44.197825+00:00
-- url     : https://prove2.me/submissions/ffc5dfcc-6463-4319-a586-de07ecadc87b

import Definitions.Def_IndependentInfoPricing_Main_Menus

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

theorem solution {Q : ℕ} (M : IndependentInfoPricing.Main.Menu (Fin Q))
    (hM : IndependentInfoPricing.Main.ValidMenu M)
    (hr : IndependentInfoPricing.Main.ReverseClosed M) : ∀ v,
    IndependentInfoPricing.Main.menuValue true M v = IndependentInfoPricing.Main.menuValue false M v ∧
      ∃ e ∈ M, IndependentInfoPricing.Main.dot v e.1 - e.2 = IndependentInfoPricing.Main.menuValue true M v := by
  open IndependentInfoPricing.Main in
  intro v
  obtain ⟨⟨h0, h1⟩, hv⟩ := hM
  obtain ⟨e0, he0, hmax⟩ := Finset.exists_max_image M (fun e => dot v e.1 - e.2) ⟨_, h0⟩
  have hone : dot v (1 : Values (Fin Q)) = ∑ i, v i := by simp [dot]
  have hzero : dot v (0 : Values (Fin Q)) = 0 := by simp [dot]
  have hF : IsGreatest {u | ∃ e ∈ M, u = dot v e.1 - e.2} (dot v e0.1 - e0.2) :=
    ⟨⟨e0, he0, rfl⟩, by rintro u ⟨e, he, rfl⟩; exact hmax e he⟩
  have hbd : ∀ e ∈ M, binaryValue v e.1 - e.2 ≤ dot v e0.1 - e0.2 := by
    intro e he
    have a1 := hmax _ (hr _ he)
    have a2 := hmax _ h1
    have a3 := hmax _ h0
    have p0 := (hv _ he).1
    have a0 := hmax _ he
    simp only [Prod.fst_sub, Prod.snd_sub] at a1 a2 a3 a0 ⊢
    rw [hone] at a2; rw [hzero] at a3
    unfold binaryValue
    simp only [max_le_iff, tsub_le_iff_right]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hT : IsGreatest {u | ∃ e ∈ M, u = binaryValue v e.1 - e.2} (dot v e0.1 - e0.2) := by
    constructor
    · refine ⟨e0, he0, le_antisymm ?_ ?_⟩
      · have : dot v e0.1 ≤ binaryValue v e0.1 := by
          unfold binaryValue; exact le_trans (le_max_left _ _) (le_max_left _ _)
        linarith
      · exact hbd e0 he0
    · rintro u ⟨e, he, rfl⟩; exact hbd e he
  have e1 : menuValue true M v = dot v e0.1 - e0.2 := by
    unfold menuValue; simpa using hT.csSup_eq
  have e2 : menuValue false M v = dot v e0.1 - e0.2 := by
    unfold menuValue; simpa using hF.csSup_eq
  exact ⟨by rw [e1, e2], e0, he0, e1.symm⟩

-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageFiniteHitMeasurableNonneg
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T03:08:34.67937+00:00
-- url     : https://prove2.me/submissions/f06de975-c5aa-4275-affc-14cd330eaf9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Measurability of `{τ_x^+ < ∞}` for `x ≥ 0`.

Identify the finiteness event with that of `twoSidedExitUpTime` (using `X_0 = 0 ≤ x`),
then apply Proved `upperPassage_measurable_from_stopping`.
-/

namespace Kyprianou.Ch03

private lemma upTime_ne_top_iff
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) :
    twoSidedExitUpTime X b ω ≠ ⊤ ↔ ∃ t : NNReal, b < X.X t ω := by
  constructor
  · intro hne
    by_contra hnone
    have hnone' : ∀ t, ¬ b < X.X t ω := fun t ht => hnone ⟨t, ht⟩
    have htop : twoSidedExitUpTime X b ω = ⊤ := by
      unfold twoSidedExitUpTime
      refine iInf_eq_top.mpr ?_
      intro t
      refine iInf_eq_top.mpr ?_
      intro ht
      exact (hnone' t ht).elim
    exact hne htop
  · rintro ⟨t, ht⟩
    intro htop
    have hle : twoSidedExitUpTime X b ω ≤ (t : ℝ≥0∞) := by
      unfold twoSidedExitUpTime
      exact iInf₂_le t ht
    rw [htop] at hle
    exact WithTop.not_top_le_coe t hle

private lemma firstHitting_ne_top_iff
    {Omega : Type} (X : NNReal → Omega → Real) (x : Real) (ω : Omega) :
    firstHittingTime X (Ioi x) ω ≠ ⊤ ↔
      ∃ t : NNReal, 0 < t ∧ X t ω ∈ Ioi x := by
  constructor
  · intro hne
    by_contra hnone
    have hempty :
        ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ X t ω ∈ Ioi x}) = ∅ := by
      ext u
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact hnone ⟨t, ht⟩
      · intro h; exact h.elim
    have htop : firstHittingTime X (Ioi x) ω = ⊤ := by
      simp only [firstHittingTime, hempty, sInf_empty]
    exact hne htop
  · rintro ⟨t, ht0, htmem⟩
    have hmem :
        (t : WithTop NNReal) ∈
          (fun u : NNReal => (u : WithTop NNReal)) ''
            {u : NNReal | 0 < u ∧ X u ω ∈ Ioi x} :=
      ⟨t, ⟨ht0, htmem⟩, rfl⟩
    have hle : firstHittingTime X (Ioi x) ω ≤ (t : WithTop NNReal) :=
      csInf_le (OrderBot.bddBelow _) hmem
    intro htop
    rw [htop] at hle
    exact WithTop.not_top_le_coe t hle

private lemma finiteHit_eq_upTime_ne_top
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (X : SpectrallyNegativeLevy P 𝓕) (x : Real) (hx : 0 ≤ x) (ω : Ω) :
    (firstHittingTime X.X (Ioi x) ω ≠ ⊤) ↔
      (twoSidedExitUpTime X x ω ≠ ⊤) := by
  rw [firstHitting_ne_top_iff, upTime_ne_top_iff]
  constructor
  · rintro ⟨t, _, htmem⟩
    exact ⟨t, htmem⟩
  · rintro ⟨t, ht⟩
    by_cases ht0 : t = 0
    · have : x < X.X 0 ω := by simpa [ht0] using ht
      rw [X.X_zero] at this
      exact (not_lt.mpr hx this).elim
    · exact ⟨t, lt_of_le_of_ne bot_le (Ne.symm ht0), ht⟩

end Kyprianou.Ch03

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : Real) (hx : 0 ≤ x) :
    MeasurableSet {omega : Omega |
      firstHittingTime L.X (Set.Ioi x) omega != ⊤} := by
  have hset :
      {omega : Omega | firstHittingTime L.X (Ioi x) omega != ⊤} =
        {omega : Omega | twoSidedExitUpTime L x omega ≠ ⊤} := by
    ext omega
    simpa [bne_iff_ne] using finiteHit_eq_upTime_ne_top L x hx omega
  rw [hset]
  exact (upperPassage_measurable_from_stopping L x)
    (measurableSet_singleton (⊤ : ℝ≥0∞)).compl

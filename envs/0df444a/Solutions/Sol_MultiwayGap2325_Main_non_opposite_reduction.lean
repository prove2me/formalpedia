-- Prove2me | solution 1 for MultiwayGap2325.Main.non_opposite_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:38:46.361493+00:00
-- url     : https://prove2.me/submissions/46ec5e96-5bf2-4d40-99ee-b0e498fbb331
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MultiwayGap2325_Main_RandomCuts
import Theorems.Thm_MultiwayGap2325_Main_gap_sequence_well_posed
import Theorems.Thm_MultiwayGap2325_Main_exists_nonOppositeCut_of_tendsto_gapSequence
section
set_option autoImplicit false

namespace MultiwayGap2325.Main

theorem chk_non_opposite_reduction (q : ℕ) (hq : 2 ≤ q) (b : ℝ) (hb : 0 < b)
    (hcuts : ∀ (Ξ : Type) [MeasurableSpace Ξ]
      (P : MeasureTheory.Measure Ξ) [MeasureTheory.IsProbabilityMeasure P]
      (C : RandomNonOppositeCut q Ξ P) (α : ℝ),
      HasApproximationFactor C α → b ≤ α) :
    AsymptoticGapAtLeast b := by
  obtain ⟨hk, -, g, hg⟩ := gap_sequence_well_posed
  obtain ⟨Ξ, inst, P, hP, C, hC⟩ := exists_nonOppositeCut_of_tendsto_gapSequence q hq g hg
  have hbg : b ≤ g := @hcuts Ξ inst P hP C g hC
  refine ⟨g, hg, hbg, fun η hη => ?_⟩
  have hev : ∀ᶠ k in Filter.atTop, g - η / 2 < gapSequence k :=
    hg.eventually (lt_mem_nhds (by linarith))
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max K0 2, le_max_right _ _, fun k hkK => ?_⟩
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hkK
  have hkK0 : K0 ≤ k := le_trans (le_max_left _ _) hkK
  obtain ⟨-, hne, hbdd, -, -, -, -, -⟩ := hk k hk2
  have hlt : gapSequence k - η / 2 < gapSequence k := by linarith
  have hgs : gapSequence k = sSup (finiteGapValues k) := by simp [gapSequence, hk2]
  rw [hgs] at hlt
  obtain ⟨r, hr, hrlt⟩ := exists_lt_of_lt_csSup hne hlt
  obtain ⟨n, I, rfl⟩ := hr
  refine ⟨n, I, ?_⟩
  have := hK0 k hkK0
  rw [hgs] at this
  linarith

end MultiwayGap2325.Main
end

theorem solution : type_of% @MultiwayGap2325.Main.chk_non_opposite_reduction := @MultiwayGap2325.Main.chk_non_opposite_reduction

-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_shifted_controlled_bad_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:20:37.170968+00:00
-- url     : https://prove2.me/submissions/75865935-882e-494d-9f84-bf694cfd54e8

import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact first-record clock reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (a : ℝ) (ω : Ω) (u : ℝ≥0),
      (⨅ (t : ℝ≥0) (_ : a + (X.X (u+t) ω - X.X u ω) <
        max 0 (sSup ((fun r : ℝ≥0 => X.X (u+r) ω) '' Icc 0 t) - X.X u ω)),
        (t : ℝ≥0∞)) =
      (⨅ i : {t : ℝ≥0 // X.X (u+t) ω-X.X u ω -
        sSup ((fun r : ℝ≥0 => X.X (u+r) ω-X.X u ω) '' Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)) := by
  intro Ω mΩ P F X a ω u
  have he (t : ℝ≥0) :
      (a + (X.X (u+t) ω-X.X u ω) <
        max 0 (sSup ((fun r : ℝ≥0 => X.X (u+r) ω) '' Icc 0 t)-X.X u ω)) ↔
      X.X (u+t) ω-X.X u ω -
        sSup ((fun r : ℝ≥0 => X.X (u+r) ω-X.X u ω) '' Icc 0 t) < -a := by
    have hb : BddAbove ((fun r : ℝ≥0 => X.X (u+r) ω) '' Icc 0 t) :=
      (levyPath_bddAbove_Icc X ω (u+t)).mono (by
        rintro z ⟨r,hr,rfl⟩
        exact ⟨u+r,⟨bot_le,add_le_add_right hr.2 u⟩,rfl⟩)
    have hnon : X.X u ω ≤ sSup ((fun r : ℝ≥0 => X.X (u+r) ω) '' Icc 0 t) :=
      le_csSup hb ⟨0,⟨le_rfl,bot_le⟩,by simp⟩
    rw [shiftedSup_increment_eq_sup_sub (fun r => X.X r ω) u t hb,
      max_eq_right (sub_nonneg.mpr hnon)]
    constructor <;> intro h <;> linarith
  simp only [iInf_subtype,he]

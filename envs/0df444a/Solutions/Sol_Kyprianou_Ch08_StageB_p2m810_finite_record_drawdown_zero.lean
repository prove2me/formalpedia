-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_finite_record_drawdown_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:45:05.552927+00:00
-- url     : https://prove2.me/submissions/94e18f88-ddaf-4611-b923-2dc3598e11c7


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict record limit proof. -/
theorem solution :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
      (l : ℝ) (u : ℝ≥0), 0 < l → X 0 ω = 0 →
      BddAbove {z : ℝ | ∃ s : ℝ≥0, s ≤ u ∧ z = X s ω} →
      l ≤ X u ω → tauPlus X l ω = (u : WithTop ℝ≥0) →
      reflectAtSup X 0 u ω = 0 := by
  intro Ω X ω l u hl h0 hb hXu ht
  have hm : runningSup X u ω = X u ω := by
    unfold runningSup
    apply le_antisymm
    · refine csSup_le ⟨X u ω,u,le_rfl,rfl⟩ ?_
      rintro z ⟨v,hv,rfl⟩
      rcases eq_or_lt_of_le hv with he | hlt
      · simp [he]
      · by_cases hv0 : v=0
        · simpa [hv0,h0] using hl.le.trans hXu
        · have hle : X v ω ≤ l := by
            by_contra! hcross
            have hτ : tauPlus X l ω ≤ (v:WithTop ℝ≥0) :=
              sInf_le ⟨v,pos_iff_ne_zero.mpr hv0,rfl,hcross⟩
            rw [ht] at hτ
            exact (not_le_of_gt hlt) (WithTop.coe_le_coe.mp hτ)
          exact hle.trans hXu
    · exact le_csSup hb ⟨u,le_rfl,rfl⟩
  rw [reflectAtSup,hm,max_eq_right (hl.le.trans hXu),sub_self]

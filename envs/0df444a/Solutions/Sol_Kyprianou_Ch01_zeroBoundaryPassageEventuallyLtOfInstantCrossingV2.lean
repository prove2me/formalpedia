-- Prove2me | solution 1 for Kyprianou.Ch01.zeroBoundaryPassageEventuallyLtOfInstantCrossingV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:43:59.429432+00:00
-- url     : https://prove2.me/submissions/1bb0da6e-87ec-4572-a8fa-bc5c6c8b9402

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_of_strict_crossingV1
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hCross : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ 0 < X t ω)
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ (u : ℝ≥0) in 𝓝[Ici (0 : ℝ≥0)] 0,
      (if u = 0 then (0 : ℝ)
      else (match firstUpperPassage X (u : ℝ) ω with
      | none => (0 : ℝ)
      | some v => (v : ℝ))) < a := by
  let aNN : ℝ≥0 := ⟨a, le_of_lt ha⟩
  have haNN : 0 < aNN := by exact_mod_cast ha
  obtain ⟨v, hvpos, hvlt, hvCross⟩ := hCross aNN haNN
  have hvReal : (v : ℝ) < a := by exact_mod_cast hvlt
  have hOpen : IsOpen {u : ℝ≥0 | (u : ℝ) < X v ω} :=
    isOpen_lt NNReal.continuous_coe continuous_const
  have hOrigin : (0 : ℝ≥0) ∈
      {u : ℝ≥0 | (u : ℝ) < X v ω} := by simpa using hvCross
  have hnear : ∀ᶠ (u : ℝ≥0) in 𝓝 (0 : ℝ≥0), (u : ℝ) < X v ω :=
    hOpen.mem_nhds hOrigin
  have hwithin : ∀ᶠ (u : ℝ≥0) in 𝓝[Ici (0 : ℝ≥0)] 0,
      (u : ℝ) < X v ω :=
    hnear.filter_mono nhdsWithin_le_nhds
  filter_upwards [hwithin] with u hcross
  by_cases hu : u = 0
  · simpa [hu] using ha
  · have hUp : firstUpperPassage X (u : ℝ) ω ≤
        (v : WithTop ℝ≥0) :=
      firstUpperPassage_le_of_strict_crossingV1 X (u : ℝ)
        ω v hvpos hcross
    cases hPass : firstUpperPassage X (u : ℝ) ω with
    | top =>
        have hTop : (⊤ : WithTop ℝ≥0) ≤
            (v : WithTop ℝ≥0) := by simpa [hPass] using hUp
        exact False.elim (WithTop.not_top_le_coe v hTop)
    | coe w =>
        have hwTop : (w : WithTop ℝ≥0) ≤
            (v : WithTop ℝ≥0) := by simpa [hPass] using hUp
        have hw : w ≤ v := WithTop.coe_le_coe.mp hwTop
        have hwReal : (w : ℝ) ≤ (v : ℝ) := by exact_mod_cast hw
        have hBound : (w : ℝ) < a := lt_of_le_of_lt hwReal hvReal
        simpa [hu, hPass] using hBound

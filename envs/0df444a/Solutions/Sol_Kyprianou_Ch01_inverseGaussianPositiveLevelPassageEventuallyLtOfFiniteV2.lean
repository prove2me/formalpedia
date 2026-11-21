-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianPositiveLevelPassageEventuallyLtOfFiniteV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:43:49.711974+00:00
-- url     : https://prove2.me/submissions/e624ddbd-e1bf-4a5d-95cc-f7531614a654

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_crossingBefore_of_ltV1
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_of_strict_crossingV1
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hFinite : ∀ s : ℝ≥0, 0 < s →
      firstUpperPassage X (s : ℝ) ω ≠ ⊤)
    (s : ℝ≥0) (hs : 0 < s)
    (a : ℝ)
    (ha : (if s = 0 then (0 : ℝ)
      else (match firstUpperPassage X (s : ℝ) ω with
      | none => (0 : ℝ)
      | some t => (t : ℝ))) < a) :
    ∀ᶠ (u : ℝ≥0) in 𝓝[Ici s] s,
      (if u = 0 then (0 : ℝ)
      else (match firstUpperPassage X (u : ℝ) ω with
      | none => (0 : ℝ)
      | some t => (t : ℝ))) < a := by
  classical
  cases hPass : firstUpperPassage X (s : ℝ) ω with
  | top =>
      exact False.elim (hFinite s hs hPass)
  | coe τ =>
      have hTA : (τ : ℝ) < a := by
        simpa [ne_of_gt hs, hPass] using ha
      have hTnonneg : (0 : ℝ) ≤ (τ : ℝ) := by
        exact_mod_cast (show (0 : ℝ≥0) ≤ τ from zero_le)
      have hApos : 0 < a := lt_of_le_of_lt hTnonneg hTA
      let aNN : ℝ≥0 := ⟨a, le_of_lt hApos⟩
      have hLtNN : τ < aNN := by exact_mod_cast hTA
      have hPassLt : firstUpperPassage X (s : ℝ) ω <
          (aNN : WithTop ℝ≥0) := by
        rw [hPass]
        exact WithTop.coe_lt_coe.mpr hLtNN
      obtain ⟨v, hvpos, hvlt, hvCross⟩ :=
        firstUpperPassage_crossingBefore_of_ltV1 X (s : ℝ)
          ω aNN hPassLt
      have hvReal : (v : ℝ) < a := by exact_mod_cast hvlt
      have hOpen : IsOpen {u : ℝ≥0 | (u : ℝ) < X v ω} :=
        isOpen_lt NNReal.continuous_coe continuous_const
      have hnear : ∀ᶠ (u : ℝ≥0) in 𝓝 s, (u : ℝ) < X v ω :=
        hOpen.mem_nhds hvCross
      have hwithin : ∀ᶠ (u : ℝ≥0) in 𝓝[Ici s] s, (u : ℝ) < X v ω :=
        hnear.filter_mono nhdsWithin_le_nhds
      filter_upwards [hwithin, self_mem_nhdsWithin] with u hcross hu
      have huPos : 0 < u := lt_of_lt_of_le hs hu
      have hUp : firstUpperPassage X (u : ℝ) ω ≤
          (v : WithTop ℝ≥0) :=
        firstUpperPassage_le_of_strict_crossingV1 X (u : ℝ)
          ω v hvpos hcross
      cases hU : firstUpperPassage X (u : ℝ) ω with
      | top =>
          have hTop : (⊤ : WithTop ℝ≥0) ≤
              (v : WithTop ℝ≥0) := by simpa [hU] using hUp
          exact False.elim (WithTop.not_top_le_coe v hTop)
      | coe w =>
          have hwTop : (w : WithTop ℝ≥0) ≤
              (v : WithTop ℝ≥0) := by simpa [hU] using hUp
          have hw : w ≤ v := WithTop.coe_le_coe.mp hwTop
          have hwReal : (w : ℝ) ≤ (v : ℝ) := by exact_mod_cast hw
          have hBound : (w : ℝ) < a := lt_of_le_of_lt hwReal hvReal
          simpa [ne_of_gt huPos, hU] using hBound

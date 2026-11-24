-- Prove2me | solution 1 for Kyprianou.Ch03.momentCPSeriesIffFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T13:09:20.661933+00:00
-- url     : https://prove2.me/submissions/607f879c-f3c2-4e8d-882f-7d199359d8b9

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_momentCPSeriesLintegralV1
import Theorems.Thm_Kyprianou_Ch03_momentCPConvPowBoundV1
import Theorems.Thm_Kyprianou_Ch03_momentCPWeightedGeometricSumFiniteV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real) [IsFiniteMeasure mu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂(KSATSingleFlip.Connect.compoundPoisson mu)) < ⊤ ↔
      (∫⁻ x, ENNReal.ofReal (g x) ∂mu) < ⊤ := by
  let f (x : ℝ) := ENNReal.ofReal (g x)
  let J (m : Measure ℝ) := ∫⁻ x, f x ∂m
  let w (n : ℕ) := ENNReal.ofReal (Real.exp (-(mu Set.univ).toReal) / (n.factorial : ℝ))
  change J (KSATSingleFlip.Connect.compoundPoisson mu) < ⊤ ↔ J mu < ⊤
  have hJ : J (KSATSingleFlip.Connect.compoundPoisson mu) =
      ∑' n : ℕ, w n * J (KSATSingleFlip.Connect.convPow mu n) :=
    Kyprianou.Ch03.momentCPSeriesLintegralV1 mu f
  rw [hJ]
  constructor
  · intro h
    have h1 : KSATSingleFlip.Connect.convPow mu 1 = mu := by simp [KSATSingleFlip.Connect.convPow]
    have hh : w 1 * J (KSATSingleFlip.Connect.convPow mu 1) ≤
        ∑' n : ℕ, w n * J (KSATSingleFlip.Connect.convPow mu n) := ENNReal.le_tsum 1
    rw [h1] at hh
    have hw : w 1 ≠ 0 := by dsimp [w]; positivity
    exact ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top h.ne hh) hw
  · intro h
    obtain ⟨c, hc, hsub⟩ := hg.2
    let r := ENNReal.ofReal c * J mu
    have hr : r ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top h.ne
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_))
      (Kyprianou.Ch03.momentCPWeightedGeometricSumFiniteV1 (g 0) (mu Set.univ).toReal (hg.1 0) r hr)
    have hh := Kyprianou.Ch03.momentCPConvPowBoundV1 mu g hg hg_meas c hc hsub n
    gcongr

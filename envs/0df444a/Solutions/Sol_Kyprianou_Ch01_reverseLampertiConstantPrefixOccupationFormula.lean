-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiConstantPrefixOccupationFormula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:20:15.646927+00:00
-- url     : https://prove2.me/submissions/9c9e27c7-cfd7-4f1f-9fe6-f17f11bdcf7d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type*} (X : NNReal -> Omega -> Int) (omega : Omega)
    (y : Nat) (s : NNReal)
    (hConst : ∀ u : NNReal, u ≤ s -> X u omega = (y : Int)) :
    reciprocalOccupation X s omega =
      (y : ENNReal)⁻¹ * (s : ENNReal) := by
  let E : Set Real := Set.Ioc (0 : Real) (s : Real)
  have hAe : ∀ᵐ u ∂(volume.restrict E),
      (ENNReal.ofReal (X (Real.toNNReal u) omega : Real))⁻¹ =
      (y : ENNReal)⁻¹ := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc)] with u hu
    have huNN : Real.toNNReal u ≤ s := by
      apply NNReal.coe_le_coe.mp
      simpa only [Real.coe_toNNReal u (le_of_lt hu.1)] using hu.2
    have hLocal := hConst (Real.toNNReal u) huNN
    simp [hLocal, ENNReal.ofReal_natCast]
  have hIntegral :
      (∫⁻ u in E,
        (ENNReal.ofReal (X (Real.toNNReal u) omega : Real))⁻¹
        ∂volume) =
      (∫⁻ _u in E, (y : ENNReal)⁻¹ ∂volume) :=
    lintegral_congr_ae hAe
  have hMeasure : (volume.restrict E) Set.univ = (s : ENNReal) := by
    simp [Measure.restrict_apply, Real.volume_Ioc, E]
  unfold reciprocalOccupation
  change (∫⁻ u in E,
      (ENNReal.ofReal (X (Real.toNNReal u) omega : Real))⁻¹
      ∂volume) = _
  rw [hIntegral, lintegral_const, hMeasure]
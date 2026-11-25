-- Prove2me | solution 1 for Kyprianou.Ch04.intensityCompensationClockRegularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:54:33.243905+00:00
-- url     : https://prove2.me/submissions/3193bb3a-e654-460c-9a3f-02c4b9bdac17

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_jointNestedNonnegIntegralsMeasurable
import Theorems.Thm_Kyprianou_Ch04_nestedNonnegativeIntegralToReal
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04
/-- Intensity clock adaptedness and almost-sure real conversion. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (phi : Real → Real → Omega → Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (t : NNReal)
    (hKernelPast : Measurable[(F t).prod inferInstance]
      (fun z : Omega × (Real × Real) =>
        if z.2.1 ∈ Set.Icc (0 : Real) (t : Real) then phi z.2.1 z.2.2 z.1 else 0))
    (hFinite : (∫⁻ w, ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume ∂P) < ⊤) :
    Measurable[F t] (fun w => ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume) ∧
    StronglyMeasurable[F t] (fun w => ∫ s in Set.Icc (0 : Real) (t : Real),
      ∫ x, phi s x w ∂levyMeasure ∂volume) ∧
    (fun w => ∫ s in Set.Icc (0 : Real) (t : Real),
      ∫ x, phi s x w ∂levyMeasure ∂volume) =ᵐ[P]
    (fun w => (∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume).toReal) := by
  let U := Set.Icc (0 : ℝ) (t : ℝ)
  let mu := (volume : Measure ℝ).restrict U
  let f (z : Omega × (ℝ × ℝ)) :=
    if z.2.1 ∈ U then phi z.2.1 z.2.2 z.1 else 0
  obtain ⟨hL, hR⟩ := @jointNestedNonnegIntegralsMeasurable Omega (F t) mu levyMeasure
    inferInstance inferInstance f hKernelPast
  have heL (w : Omega) : (∫⁻ s, ∫⁻ x, ENNReal.ofReal (f (w,(s,x)))
      ∂levyMeasure ∂mu) = ∫⁻ s in U, ∫⁻ x, ENNReal.ofReal (phi s x w)
      ∂levyMeasure ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simp [f, hs]
  have heR (w : Omega) : (∫ s, ∫ x, f (w,(s,x)) ∂levyMeasure ∂mu) =
      ∫ s in U, ∫ x, phi s x w ∂levyMeasure ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simp [f, hs]
  simp_rw [heL] at hL
  simp_rw [heR] at hR
  refine ⟨hL, hR.stronglyMeasurable, ?_⟩
  filter_upwards [ae_lt_top (hL.mono (F.le t) le_rfl) hFinite.ne] with w hw
  exact nestedNonnegativeIntegralToReal mu levyMeasure (fun z => phi z.1 z.2 w)
    (hPhi.2.1.comp measurable_prodMk_right) (fun z => hPhi.1 _ _ _) hw.ne

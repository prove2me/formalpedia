-- Prove2me | solution 1 for Kyprianou.Ch04.signedNestedIntegralSplitAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:21:10.231039+00:00
-- url     : https://prove2.me/submissions/5dbe87a4-9df1-41c7-bd35-7b82030e5bc7

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteRandomIntegralSplitAE
import Theorems.Thm_Kyprianou_Ch04_nonnegativeHorizonPhysicalFubini
import Theorems.Thm_Kyprianou_Ch04_referenceIntensityHorizonProd
import Theorems.Thm_Kyprianou_Ch04_jointNestedNonnegIntegralsMeasurable
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite expected signed-part compensator masses justify nested subtraction. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (nu : Measure ℝ) [SigmaFinite nu] (t : NNReal)
    (f : Omega → ℝ × ℝ → ℝ)
    (hf : Measurable (fun z : Omega × (ℝ × ℝ) => f z.1 z.2))
    (hp : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (f w (s,x)) 0) ∂nu ∂volume ∂P) < ⊤)
    (hn : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (-f w (s,x)) 0) ∂nu ∂volume ∂P) < ⊤) :
    ∀ᵐ w ∂P,
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, f w (s,x) ∂nu ∂volume) =
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, max (f w (s,x)) 0 ∂nu ∂volume) -
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, max (-f w (s,x)) 0 ∂nu ∂volume) := by
  let V := volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))
  let S := (referenceIntensity nu).restrict (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ)
  have hpm : Measurable (fun z : Omega × (ℝ × ℝ) => max (f z.1 z.2) 0) :=
    hf.max measurable_const
  have hnm : Measurable (fun z : Omega × (ℝ × ℝ) => max (-f z.1 z.2) 0) :=
    hf.neg.max measurable_const
  have hFp := nonnegativeHorizonPhysicalFubini P nu t
    (fun w z => max (f w z) 0) hpm (fun _ _ => le_max_right _ _) hp
  have hFn := nonnegativeHorizonPhysicalFubini P nu t
    (fun w z => max (-f w z) 0) hnm (fun _ _ => le_max_right _ _) hn
  have hP : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal (max (f w z) 0) ∂S) P :=
    (jointNestedNonnegIntegralsMeasurable V nu _ hpm).1.aemeasurable.congr
      (Eventually.of_forall fun w => (hFp.1 w).symm)
  have hN : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal (max (-f w z) 0) ∂S) P :=
    (jointNestedNonnegIntegralsMeasurable V nu _ hnm).1.aemeasurable.congr
      (Eventually.of_forall fun w => (hFn.1 w).symm)
  have hPfin : (∫⁻ w, ∫⁻ z, ENNReal.ofReal (max (f w z) 0) ∂S ∂P) < ⊤ :=
    lt_of_eq_of_lt (lintegral_congr hFp.1) hp
  have hNfin : (∫⁻ w, ∫⁻ z, ENNReal.ofReal (max (-f w z) 0) ∂S ∂P) < ⊤ :=
    lt_of_eq_of_lt (lintegral_congr hFn.1) hn
  have h := finiteRandomIntegralSplitAE P (fun _ => S) f
    (fun w => hf.comp (measurable_const.prodMk measurable_id)) hP hN hPfin hNfin
  filter_upwards [h,hFp.2,hFn.2] with w hw hwp hwn
  have hS : S = V.prod nu := referenceIntensityHorizonProd nu t
  have hi := hw.1
  rw [hS] at hi
  have he : (∫ z, f w z ∂S) = ∫ s, ∫ x, f w (s,x) ∂nu ∂V := by
    rw [hS]
    exact integral_prod _ hi
  exact he.symm.trans (hw.2.trans (congrArg₂ (· - ·) hwp hwn))

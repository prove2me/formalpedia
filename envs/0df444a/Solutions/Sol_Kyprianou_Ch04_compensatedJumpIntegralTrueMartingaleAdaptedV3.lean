-- Prove2me | solution 1 for Kyprianou.Ch04.compensatedJumpIntegralTrueMartingaleAdaptedV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:36:29.365747+00:00
-- url     : https://prove2.me/submissions/ddc80f12-ba5c-46ff-852e-305b73736681

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_rawCompensationClockRegularity
import Theorems.Thm_Kyprianou_Ch04_intensityCompensationClockRegularity
import Theorems.Thm_Kyprianou_Ch04_conditionalENNClockBalance
import Theorems.Thm_Kyprianou_Ch04_realCompensationMartingaleOfENNBalance
import Theorems.Thm_Kyprianou_Ch04_nonnegativePredictableJumpCompensationCommonNullV2
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

/-- Combine the adapted clocks, compensation and real martingale constructor. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ omega ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega)))
    (hPast : ∀ (t : NNReal) (B : Set (Real × Real)),
      MeasurableSet B →
      B ⊆ Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ →
      Measurable[F t] (fun omega => N.N omega B))
    (hKernelPast : ∀ t : NNReal,
      Measurable[(F t).prod inferInstance]
        (fun z : Omega × (Real × Real) =>
          if z.2.1 ∈ Set.Icc (0 : Real) (t : Real)
          then phi z.2.1 z.2.2 z.1 else 0))
    (hLocalFinite : ∀ (t : NNReal) (n : Nat) (omega : Omega),
      N.N omega (Set.Icc (0 : Real) (t : Real) ×ˢ spanningSets levyMeasure n) ≠ ⊤)
    (hFinite : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) < ⊤) :
    MeasureTheory.Martingale
      (fun (t : NNReal) omega =>
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
          phi z.1 z.2 omega ∂(N.N omega)) -
        (∫ s in Set.Icc (0 : Real) (t : Real),
          (∫ x, phi s x omega ∂levyMeasure) ∂volume))
      F P := by
  let J (t : NNReal) (w : Omega) := ∫⁻ z in
    Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ, ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)
  let C (t : NNReal) (w : Omega) := ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
    ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume
  let j (t : NNReal) (w : Omega) := ∫ z in
    Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ, phi z.1 z.2 w ∂(N.N w)
  let c (t : NNReal) (w : Omega) := ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
    ∫ x, phi s x w ∂levyMeasure ∂volume
  have hraw (t : NNReal) := rawCompensationClockRegularity P levyMeasure F phi hPhi t
    (hKernelPast t) N (hPast t) (hLocalFinite t)
  have hint (t : NNReal) := intensityCompensationClockRegularity P levyMeasure F phi hPhi t
    (hKernelPast t) (hFinite t)
  have hJ : ∀ t, Measurable (J t) := fun t => (hraw t).1.mono (F.le t) le_rfl
  have hC : ∀ t, Measurable (C t) := fun t => (hint t).1.mono (F.le t) le_rfl
  have hfinJ (t : NNReal) : (∫⁻ w, J t w ∂P) < ⊤ := by
    have heq : (∫⁻ w, J t w ∂P) = ∫⁻ w, C t w ∂P :=
      nonnegativePredictableJumpCompensationCommonNullV2 P levyMeasure F N
        hFuture phi hPhi hCommon t
    exact lt_of_eq_of_lt heq (hFinite t)
  exact realCompensationMartingaleOfENNBalance P F J C j c
    (fun t => (hraw t).2.1) (fun t => (hint t).2.1) hJ hC hfinJ hFinite
    (fun t => Eventually.of_forall (hraw t).2.2) (fun t => (hint t).2.2)
    (conditionalENNClockBalance P levyMeasure F N hFuture phi hPhi hCommon hJ hC)

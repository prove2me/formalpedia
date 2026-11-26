-- Prove2me | solution 1 for Kyprianou.Ch04.signedCompensatedJumpTrueMartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:24:48.061802+00:00
-- url     : https://prove2.me/submissions/74c5b5d6-1b85-4607-8317-fb21b9792a70

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_compensatedJumpIntegralTrueMartingaleAdaptedV3
import Theorems.Thm_Kyprianou_Ch04_signedKernelPositiveParts
import Theorems.Thm_Kyprianou_Ch04_signedPartsHorizonMeasurable
import Theorems.Thm_Kyprianou_Ch04_finiteSignedPartsHorizon
import Theorems.Thm_Kyprianou_Ch04_signedRawHorizonRegularity
import Theorems.Thm_Kyprianou_Ch04_signedNestedHorizonAdapted
import Theorems.Thm_Kyprianou_Ch04_signedNestedIntegralSplitAE
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Signed physical Poisson compensation is a true martingale under finite absolute mass. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N)
    (k : ℝ → ℝ → Omega → ℝ)
    (hm : Measurable (fun z : (ℝ × ℝ) × Omega => k z.1.1 z.1.2 z.2))
    (ha : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => k (t : ℝ) z.2 z.1))
    (hc : ∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => k s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (k (t : ℝ) x w)))
    (hPast : ∀ (t : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ →
      Measurable[F t] (fun w => N.N w B))
    (hLocal : ∀ (t : NNReal) (n : ℕ) (w : Omega),
      N.N w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ spanningSets nu n) ≠ ⊤)
    (hKernelPast : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × (ℝ × ℝ) =>
        if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0))
    (hFin : ∀ t : NNReal, (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal |k s x w| ∂nu ∂volume ∂P) < ⊤) :
    Martingale (fun (t : NNReal) w =>
      (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ, k z.1 z.2 w ∂(N.N w)) -
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, k s x w ∂nu ∂volume) F P := by
  let kp := fun s x w => max (k s x w) 0
  let kn := fun s x w => max (-k s x w) 0
  obtain ⟨hP,hN,hcP,hcN⟩ := signedKernelPositiveParts P F k hm ha hc
  have hmp (t : NNReal) := (signedPartsHorizonMeasurable F k t (hKernelPast t)).1
  have hmn (t : NNReal) := (signedPartsHorizonMeasurable F k t (hKernelPast t)).2
  have hfp (t : NNReal) := (finiteSignedPartsHorizon P nu k t (hFin t)).1
  have hfn (t : NNReal) := (finiteSignedPartsHorizon P nu k t (hFin t)).2
  have hMP := compensatedJumpIntegralTrueMartingaleAdaptedV3 P nu F N hFuture kp hP hcP
    hPast hmp hLocal hfp
  have hMN := compensatedJumpIntegralTrueMartingaleAdaptedV3 P nu F N hFuture kn hN hcN
    hPast hmn hLocal hfn
  have hraw (t : NNReal) := signedRawHorizonRegularity P nu F N hFuture k hm t
    (hPast t) (hLocal t) hP hN hcP hcN (hmp t) (hmn t) (hfp t) (hfn t)
  have hnest (t : NNReal) := signedNestedIntegralSplitAE P nu t
    (fun w z => k z.1 z.2 w) (hm.comp measurable_swap) (hfp t) (hfn t)
  apply (hMP.sub hMN).congr
  · intro t
    exact (hraw t).1.sub (signedNestedHorizonAdapted nu F k t (hKernelPast t))
  · intro t
    filter_upwards [(hraw t).2,hnest t] with w hwR hwS
    change ((∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ, kp z.1 z.2 w ∂(N.N w)) -
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, kp s x w ∂nu ∂volume)) -
      ((∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ, kn z.1 z.2 w ∂(N.N w)) -
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, kn s x w ∂nu ∂volume)) = _
    rw [hwR,hwS]
    dsimp only [kp,kn]; ring

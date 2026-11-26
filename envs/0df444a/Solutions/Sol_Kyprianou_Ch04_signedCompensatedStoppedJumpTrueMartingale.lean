-- Prove2me | solution 1 for Kyprianou.Ch04.signedCompensatedStoppedJumpTrueMartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:41:51.782804+00:00
-- url     : https://prove2.me/submissions/73d5c263-c3ed-40c6-83d0-be23b756e8b8

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_signedCompensatedJumpTrueMartingale
import Theorems.Thm_Kyprianou_Ch04_closedStopKernelRegularity
import Theorems.Thm_Kyprianou_Ch04_closedStopRawIntegral
import Theorems.Thm_Kyprianou_Ch04_closedStopNestedIntegral
import Theorems.Thm_Kyprianou_Ch04_clippedClockCoe
open MeasureTheory Filter Set LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Signed physical Poisson compensation at a closed stopping clock is a true martingale under finite stopped absolute mass. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N)
    (tau : Omega → WithTop NNReal) (htau : IsStoppingTime F tau)
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
      ∫⁻ x, ENNReal.ofReal |if (s.toNNReal : WithTop NNReal) ≤ tau w then k s x w else 0|
        ∂nu ∂volume ∂P) < ⊤) :
    let c := fun w (t : NNReal) => (min (tau w) (t : WithTop NNReal)).untopD t
    Martingale (fun (t : NNReal) w =>
      (∫ z in Set.Icc (0 : ℝ) (c w t : ℝ) ×ˢ Set.univ, k z.1 z.2 w ∂(N.N w)) -
      ∫ s in Set.Icc (0 : ℝ) (c w t : ℝ), ∫ x, k s x w ∂nu ∂volume) F P := by
  classical
  let c := fun w (t : NNReal) => (min (tau w) (t : WithTop NNReal)).untopD t
  let H := fun s x w => if (s.toNNReal : WithTop NNReal) ≤ tau w then k s x w else 0
  obtain ⟨hmH,haH,hcH,hpH⟩ := closedStopKernelRegularity P F tau htau k hm ha hc hKernelPast
  have hM := signedCompensatedJumpTrueMartingale P nu F N hFuture H hmH haH hcH
    hPast hLocal hpH hFin
  have he : (fun (t : NNReal) w =>
      (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ, H z.1 z.2 w ∂(N.N w)) -
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, H s x w ∂nu ∂volume) =
      (fun (t : NNReal) w =>
      (∫ z in Set.Icc (0 : ℝ) (c w t : ℝ) ×ˢ Set.univ, k z.1 z.2 w ∂(N.N w)) -
      ∫ s in Set.Icc (0 : ℝ) (c w t : ℝ), ∫ x, k s x w ∂nu ∂volume) := by
    funext t w
    exact congrArg₂ (· - ·)
      (closedStopRawIntegral (N.N w) (fun z => k z.1 z.2 w) (tau w) t (c w t)
        (clippedClockCoe (tau w) t))
      (closedStopNestedIntegral nu (fun s x => k s x w) (tau w) t (c w t)
        (clippedClockCoe (tau w) t))
  exact Eq.mp (congrArg (fun q => Martingale q F P) he) hM

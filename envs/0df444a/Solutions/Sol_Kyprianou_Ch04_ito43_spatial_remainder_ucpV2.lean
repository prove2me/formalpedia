-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_remainder_ucpV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:36:45.761694+00:00
-- url     : https://prove2.me/submissions/6fb6003f-f7f6-4dc0-b6b3-7ea500aed261
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_no_fixed_jump
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_current_grid_ucp
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Fixed deterministic grid times have no jumps, with the corrected initial condition. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
    (hLeftZero : ∀ᵐ omega ∂P, Xleft 0 omega = X 0 omega)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega)))
    (f : Real × Real -> Real)
    (hfJointC1 : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (hfSpaceC2 : forall s : NNReal,
      ContDiff Real 2 (fun x : Real => f ((s : Real), x)))
    (hfSpaceSecondContinuous :
      ContinuousOn
        (fun z : Real × Real =>
          iteratedDeriv 2 (fun x : Real => f (z.1, x)) z.2)
        (Set.prod (Set.Ici (0 : Real)) Set.univ))
 :
    ∀ (T : NNReal) (epsilon : Real), 0 < epsilon →
    Tendsto (fun n : Nat =>
      (P {omega : Omega | ∃ t : NNReal, t ≤ T ∧
        let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
        let v : ℕ → NNReal := fun k => min t (u k)
        epsilon ≤ abs (((triplet.gaussianVariance : Real) / 2) *
          (∫ s in Set.Icc (0 : Real) (t : Real),
            iteratedDeriv 2 (fun x : Real => f ((s : Real), x))
              (X (Real.toNNReal s) omega) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) -
           z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
          ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
          (f ((v k : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v k) omega) -
          fderiv Real f ((u k : Real), Xleft (u k) omega) (0, 1) *
            (X (v (k+1)) omega - X (v k) omega))))}).toReal)
      atTop (nhds 0) := by
  intro T epsilon he
  have hEq (n k : ℕ) :
      ∀ᵐ w ∂P, Xleft (T * (k : NNReal) / (n : NNReal)) w =
        X (T * (k : NNReal) / (n : NNReal)) w := by
    let t := T * (k : NNReal) / (n : NNReal)
    change ∀ᵐ w ∂P, Xleft t w = X t w
    by_cases ht : t = 0
    · simpa only [ht] using hLeftZero
    · exact (Kyprianou.Ch04.ito43_levy_no_fixed_jump P X Xleft hLevy t
        (pos_iff_ne_zero.mpr ht) (hLeft.mono fun w hw => hw t (pos_iff_ne_zero.mpr ht))).mono
          (fun w hw => hw.symm)
  have hAll : ∀ᵐ w ∂P, ∀ n k : ℕ,
      Xleft (T * (k : NNReal) / (n : NNReal)) w =
        X (T * (k : NNReal) / (n : NNReal)) w :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr (hEq n)
  apply (Kyprianou.Ch04.ito43_spatial_current_grid_ucp P X hLevy triplet hTriplet Xleft
    hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T epsilon he).congr
  intro n
  congr 1
  apply measure_congr
  filter_upwards [hAll] with w hw
  change (∃ t ≤ T, _) = (∃ t ≤ T, _)
  simp only [hw]

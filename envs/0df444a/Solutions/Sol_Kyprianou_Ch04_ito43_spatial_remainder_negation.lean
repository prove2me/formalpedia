-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_remainder_negation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:17:53.404182+00:00
-- url     : https://prove2.me/submissions/ce38e4a4-92cd-4ef3-9357-8fb1a0c602fc

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_ce_trivial_measure
import Theorems.Thm_Kyprianou_Ch04_ito43_ce_linear_levy
import Theorems.Thm_Kyprianou_Ch04_ito43_ce_bad_first_grid
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open Set

/-- The unrestricted value at time zero gives a deterministic drift counterexample. -/
theorem solution : ¬ (∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
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
        (Set.prod (Set.Ici (0 : Real)) Set.univ)),
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
      atTop (nhds 0)) := by
  intro h
  letI m : MeasurableSpace ℕ := ⊥
  let P : Measure ℕ := Measure.dirac 0
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let X : NNReal → ℕ → ℝ := fun t _ => (t : ℝ)
  let Y : NNReal → ℕ → ℝ := fun t w => if t = 0 then (w : ℝ) else (t : ℝ)
  let f : ℝ × ℝ → ℝ := fun z => z.2 ^ 2
  obtain ⟨tr,hX,hvar,htr⟩ := Kyprianou.Ch04.ito43_ce_linear_levy P
  have hLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s w) (nhdsWithin t (Iio t)) (nhds (Y t w)) := by
    filter_upwards [] with w
    intro t ht
    simpa only [X,Y,if_neg ht.ne'] using
      (NNReal.continuous_coe.continuousWithinAt :
        ContinuousWithinAt (fun s : NNReal => (s : ℝ)) (Iio t) t).tendsto
  have hf : ContDiff ℝ 1 f := by dsimp [f]; fun_prop
  have hf2 (s : NNReal) : ContDiff ℝ 2 (fun x : ℝ => f ((s : ℝ),x)) := by
    dsimp [f]; fun_prop
  have hd2 : (fun z : ℝ × ℝ => iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) z.2) =
      fun _ => (2 : ℝ) := by
    funext z
    simp [f,iteratedDeriv_succ,deriv_pow,deriv_const_mul]
  have hf3 : ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) z.2)
      (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)) := by rw [hd2]; exact continuousOn_const
  have H := @h ℕ m P inferInstance X hX tr htr Y hLeft f hf.contDiffOn hf2 hf3 1 1 zero_lt_one
  have hJ (w : ℕ) : pathJumpMeasure X Y w = 0 := by
    have hS : {t : NNReal | 0 < t ∧ X t w ≠ Y t w} = ∅ := by
      ext t
      simp only [mem_setOf_eq,mem_empty_iff_false,iff_false,not_and]
      intro ht
      simp [X,Y,ht.ne']
    simp [pathJumpMeasure,hS]
  simp only [hvar,NNReal.coe_zero,zero_div,zero_mul,hJ,Measure.restrict_zero,integral_zero_measure,
    zero_add,zero_sub,abs_neg,one_mul] at H
  let E : ℕ → Set ℕ := fun n => {w | ∃ t : NNReal, t ≤ 1 ∧
    let u : ℕ → NNReal := fun k => (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    1 ≤ |∑ k ∈ Finset.range n,
      (f ((v k : ℝ),X (v (k+1)) w) - f ((v k : ℝ),X (v k) w) -
        fderiv ℝ f ((u k : ℝ),Y (u k) w) (0,1) * (X (v (k+1)) w - X (v k) w))|}
  change Tendsto (fun n => (P (E n)).toReal) atTop (nhds 0) at H
  have hOne : (fun n => (P (E n)).toReal) =ᶠ[atTop] fun _ => (1 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hE : (E n).Nonempty := ⟨n,1/(n : NNReal),
      Kyprianou.Ch04.ito43_ce_bad_first_grid n hn⟩
    rw [Kyprianou.Ch04.ito43_ce_trivial_measure P (E n) hE,ENNReal.toReal_one]
  exact one_ne_zero (tendsto_const_nhds_iff.mp (H.congr' hOne))

-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42FixedLipschitzChainRuleV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:56:30.701864+00:00
-- url     : https://prove2.me/submissions/642cf667-305e-4e5b-880d-dc4b1de03a23

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteTruncationIdentityV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzTruncatedFderivIntegralLimitV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzTruncatedWeightedIntegralLimitV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzTruncatedJumpSumLimitV1
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open ProbabilityTheory Set Topology
open scoped Topology
open Kyprianou.Ch04

/-- Pass to the limit in the finite-jump Lipschitz chain rule. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hd : 0 < c) (hzero : X 0 omega = 0)
    (hCadlag : IsCadlag (fun t : NNReal => X t omega))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hNeg : ∀ t : NNReal, 0 < t → X t omega ≤ Xleft t omega)
    (hRep : ∀ t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (U : NNReal → Real) (K : NNReal) (hU : LipschitzWith K U)
    (hU0 : 0 ≤ U 0) (hUp : ∀ s : NNReal, 0 < s → 0 < U s)
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (t : NNReal) :
    f (U t, X t omega) =
      f (U 0, X 0 omega) + c *
        (∫ s in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (U s.toNNReal, X s.toNNReal omega) (0, 1) ∂volume) +
      (∫ s in Set.Icc (0 : Real) (t : Real),
        fderiv Real f (U s.toNNReal, X s.toNNReal omega) (1, 0) *
          deriv (fun z : Real => U z.toNNReal) s ∂volume) +
      (∑' s : Set.Ioc (0 : NNReal) t,
        (f (U s, X s omega) - f (U s, Xleft s omega))) := by
  classical
  let I := Ioc (0 : NNReal) t
  let j : I → ℝ := fun s => X s omega - Xleft s omega
  let P (S : Finset I) (u : NNReal) :=
    X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
  have hj : Summable j :=
    Summable.of_norm (by simpa only [j, Real.norm_eq_abs] using (hRep t).1)
  have ht : Tendsto (fun S : Finset I => P S t) atTop (nhds (X t omega)) := by
    have hs : Tendsto (fun S : Finset I => ∑ s ∈ S, j s) atTop
        (nhds (∑' s : I, j s)) := hj.hasSum
    have h := (tendsto_const_nhds (x := X 0 omega + c * (t : ℝ))).add hs
    have htarget : X 0 omega + c * (t : ℝ) + (∑' s : I, j s) = X t omega :=
      (hRep t).2.symm
    rw [htarget] at h
    have hcut (s : I) : (s : NNReal) ≤ t := s.property.2
    simpa only [P, hcut, if_true] using h
  have hn : 0 ≤ U t := by
    by_cases hz : t = 0
    · simpa only [hz] using hU0
    · exact (hUp t (pos_iff_ne_zero.mpr hz)).le
  have hc : Continuous (fun x : ℝ => f (U t,x)) :=
    hf.continuousOn.comp_continuous (Continuous.prodMk_right (U t))
      (fun x => ⟨hn, Set.mem_univ x⟩)
  have hL : Tendsto (fun S : Finset I => f (U t,P S t)) atTop
      (nhds (f (U t,X t omega))) := hc.continuousAt.tendsto.comp ht
  have hD := Kyprianou.Ch04.exercise42LipschitzTruncatedFderivIntegralLimitV1
    X Xleft omega c hRep hLeft U K hU hU0 hUp f hf t (0,1)
  have hW := Kyprianou.Ch04.exercise42LipschitzTruncatedWeightedIntegralLimitV1
    X Xleft omega c hRep hLeft U K hU hU0 hUp f hf t (1,0)
  have hJ := Kyprianou.Ch04.exercise42LipschitzTruncatedJumpSumLimitV1
    X Xleft omega c hRep hLeft U K hU hU0 hUp f hf t
  have hF := Kyprianou.Ch04.exercise42LipschitzFiniteTruncationIdentityV1
    X Xleft omega c U K hU hU0 hUp f hf t
  have hR := ((tendsto_const_nhds (x := f (U 0,X 0 omega))).add
    ((tendsto_const_nhds (x := c)).mul hD)).add hW |>.add hJ
  exact tendsto_nhds_unique hL (hR.congr (fun S => (hF S).symm))

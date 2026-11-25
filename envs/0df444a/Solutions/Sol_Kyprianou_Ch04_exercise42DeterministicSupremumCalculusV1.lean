-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42DeterministicSupremumCalculusV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T16:05:26.031132+00:00
-- url     : https://prove2.me/submissions/250b69cd-040d-4371-a693-1100c760eb10
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42SupremumIncrementBoundsV1
import Theorems.Thm_Kyprianou_Ch04_exercise42FixedLipschitzChainRuleV1
import Theorems.Thm_Kyprianou_Ch04_exercise42FixedLipschitzGridLimitV1
import Theorems.Thm_Kyprianou_Ch04_exercise42NegativeAtomicJumpBridgeV1
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
    (hPos : ∀ t : NNReal, 0 < t →
      0 < sSup ((fun s : NNReal => X s omega) '' Set.Iic t))
    (hMon : Monotone (fun t : NNReal => (t : Real) * c - X t omega))
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    let supX : NNReal -> Omega -> Real := fun t omega =>
      sSup ((fun s : NNReal => X s omega) '' Set.Iic t)
    ∀ t : NNReal,
      ∃ maxIntegral : Real,
        Tendsto
          (fun n : Nat =>
            ∑ k ∈ Finset.range n,
              let u : NNReal := t * (k : NNReal) / (n : NNReal)
              let v : NNReal := t * ((k + 1 : Nat) : NNReal) / (n : NNReal)
              fderiv Real f (supX u omega, X u omega) (1, 0) *
                (supX v omega - supX u omega))
          atTop (nhds maxIntegral) ∧
        f (supX t omega, X t omega) =
          f (supX 0 omega, X 0 omega) +
          c *
            (∫ s in Set.Icc (0 : Real) (t : Real),
              fderiv Real f
                (supX (Real.toNNReal s) omega, X (Real.toNNReal s) omega)
                (0, 1) ∂volume) +
          maxIntegral +
          (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
              (Set.Iio (0 : Real)),
            (f (supX (Real.toNNReal z.1) omega,
                Xleft (Real.toNNReal z.1) omega + z.2) -
              f (supX (Real.toNNReal z.1) omega,
                Xleft (Real.toNNReal z.1) omega))
            ∂(pathJumpMeasure X Xleft omega)) := by
  intro supX t
  let U : NNReal → ℝ := fun s => supX s omega
  have h := exercise42SupremumIncrementBoundsV1 (fun s => X s omega) c hd hzero hMon
  change U 0 = 0 ∧ (∀ s, 0 ≤ U s) ∧ _ ∧ LipschitzWith c.toNNReal U at h
  have hU0 : 0 ≤ U 0 := h.2.1 0
  have hUp : ∀ s, 0 < s → 0 < U s := hPos
  have hU := h.2.2.2
  let I : ℝ := ∫ s in Icc 0 (t : ℝ),
    fderiv ℝ f (U s.toNNReal, X s.toNNReal omega) (1, 0) *
      deriv (fun z : ℝ => U z.toNNReal) s
  refine ⟨I, ?_, ?_⟩
  · exact exercise42FixedLipschitzGridLimitV1 X Xleft omega c hd hzero hCadlag
      hLeft hNeg hRep U c.toNNReal hU hU0 hUp f hf t
  · have hc := exercise42FixedLipschitzChainRuleV1 X Xleft omega c hd hzero hCadlag
      hLeft hNeg hRep U c.toNNReal hU hU0 hUp f hf t
    have hj := exercise42NegativeAtomicJumpBridgeV1 X Xleft omega hNeg
      (fun s => (hRep s).1) U f t
    change _ = _ + _ + I + _ at hc
    rw [hj]
    exact hc

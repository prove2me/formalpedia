-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ContinuousPathLedgerV8
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:35:33.443204+00:00
-- url     : https://prove2.me/submissions/fb37f107-4ed8-4c18-a301-fc6f409b9245

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41SmoothApproxDataV9
import Theorems.Thm_Kyprianou_Ch04_exercise41SmoothScalarChainV9
import Theorems.Thm_Kyprianou_Ch04_exercise41AtomicJumpIocV9
import Theorems.Thm_Kyprianou_Ch04_exercise41PassLimitV7
import Theorems.Thm_Kyprianou_Ch04_bvPositiveJumpSupportCountableV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type}
    (X Xleft : NNReal → Ω → ℝ) (w : Ω) (c : ℝ)
    (hd : 0 < c) (hzero : X 0 w = 0)
    (hCadlag : IsCadlag (fun t : NNReal => X t w))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w)))
    (hNeg : ∀ t : NNReal, 0 < t → X t w ≤ Xleft t w)
    (hRep : ∀ t : NNReal,
      Summable (fun s : Ioc (0 : NNReal) t => |X s w - Xleft s w|) ∧
      X t w = X 0 w + c * (t : ℝ) +
        ∑' s : Ioc (0 : NNReal) t, (X s w - Xleft s w))
    (fLeft fRight : ℝ → ℝ)
    (hC1Left : ContDiff ℝ 1 fLeft) (hC1Right : ContDiff ℝ 1 fRight)
    (t : NNReal) :
    let g := fun x : ℝ => if x < 0 then fLeft x - fLeft 0
        else if 0 < x then fRight x - fRight 0 else 0
    let D := fun x : ℝ => if x < 0 then deriv fLeft x
        else if 0 < x then deriv fRight x else 0
    let μ := (pathJumpMeasure X Xleft w).restrict
        (Ioc (0 : ℝ) (t : ℝ) ×ˢ Iio (0 : ℝ))
    let J := fun z : ℝ × ℝ => g (Xleft z.1.toNNReal w + z.2) - g (Xleft z.1.toNNReal w)
    Integrable J μ ∧
      g (X t w) = g (X 0 w) +
        c * (∫ s in Icc (0 : ℝ) (t : ℝ), D (X s.toNNReal w) ∂volume) +
        ∫ z, J z ∂μ := by
  letI : MeasurableSpace Ω := ⊤
  let g0 : ℝ → ℝ := fun x => if x < 0 then fLeft x - fLeft 0
    else if 0 < x then fRight x - fRight 0 else 0
  let D0 : ℝ → ℝ := fun s => if X s.toNNReal w < 0 then deriv fLeft (X s.toNNReal w)
    else if 0 < X s.toNNReal w then deriv fRight (X s.toNNReal w) else 0
  let I := Ioc (0 : NNReal) t
  let m := (volume : Measure ℝ).restrict (Icc 0 (t : ℝ))
  let μ := (pathJumpMeasure X Xleft w).restrict (Ioc (0 : ℝ) (t : ℝ) ×ˢ Iio 0)
  let J : ℝ × ℝ → ℝ := fun z => g0 (Xleft z.1.toNNReal w + z.2) -
    g0 (Xleft z.1.toNNReal w)
  change Integrable J μ ∧ g0 (X t w) = g0 (X 0 w) +
    c * (∫ s, D0 s ∂m) + ∫ z, J z ∂μ
  obtain ⟨G,K,B,hG,hlim,hm,hK,hDb,hDl,hB,hJb,hs⟩ :=
    exercise41SmoothApproxDataV9 X Xleft w c hd hzero hCadlag hLeft hNeg hRep
      fLeft fRight hC1Left hC1Right t
  have hJ := bvPositiveJumpSupportCountableV1 X Xleft w (fun s => (hRep s).1)
  obtain ⟨hInt,hEq⟩ := exercise41AtomicJumpIocV9 X Xleft w hNeg hJ t g0 hs
  refine ⟨hInt, ?_⟩
  rw [hEq]
  exact exercise41PassLimitV7 m G g0 (X 0 w) (X t w) c
    (fun n s => deriv (G n) (X s.toNNReal w)) D0
    (fun n (k : I) => G n (X k w) - G n (Xleft k w))
    (fun k : I => g0 (X k w) - g0 (Xleft k w)) K B
    (hlim _) (hlim _) hm hK hDb hDl hB
    (fun k => (hlim (X k w)).sub (hlim (Xleft k w))) hJb
    (fun n => exercise41SmoothScalarChainV9 X Xleft w c hd hzero hCadlag
      hLeft hNeg hRep (G n) (hG n) t)

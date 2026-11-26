-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_grid_sections
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:48:09.973541+00:00
-- url     : https://prove2.me/submissions/3b91e88a-99f9-46f4-a8df-fcf8ecd4a440

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
/-- Fixed-time grid sums are measurable. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
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
        (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    ∀ (T : NNReal) (m : ℕ),
    let S : ℕ → NNReal → Omega → ℝ := fun n t omega =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
      (∑ k ∈ Finset.range n,let dx := X (v (k+1)) omega - X (v k) omega
       (f ((v k : ℝ),X (v (k+1)) omega) - f ((v k : ℝ),X (v k) omega) -
        deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx -
        iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx^2 / 2)
          * chi dx)
    ∀ n t, AEMeasurable (S n t) P := by
  intro T m S n t
  let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
  let v : ℕ → NNReal := fun k => min t (u k)
  have hx := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hLevy
  change AEMeasurable (fun w => ∑ k ∈ Finset.range n, _) P
  apply Finset.aemeasurable_fun_sum
  intro k hk
  have h1 : Continuous (fun x => f ((v k : ℝ),x)) :=
    (hfSpaceC2 (v k)).continuous
  have h2 : Continuous (deriv (fun x => f ((u k : ℝ),x))) :=
    (hfSpaceC2 (u k)).continuous_deriv (by norm_num)
  have h3 : Continuous (iteratedDeriv 2 (fun x => f ((u k : ℝ),x))) :=
    ContDiff.continuous_iteratedDeriv 2 (hfSpaceC2 (u k)) (by norm_num)
  have hd := (hx (v (k+1))).sub (hx (v k))
  have ha := h1.measurable.comp_aemeasurable (hx (v (k+1)))
  have hb := h1.measurable.comp_aemeasurable (hx (v k))
  have hc := h2.measurable.comp_aemeasurable (hx (u k))
  have hf := h3.measurable.comp_aemeasurable (hx (u k))
  have hchi : Continuous (fun z : ℝ => min 1 (max 0 (|z| * ((m:ℝ)+1)-1))) := by
    exact continuous_const.min (continuous_const.max
      ((continuous_abs.mul continuous_const).sub continuous_const))
  exact (((ha.sub hb).sub (hc.mul hd)).sub
    ((hf.mul (hd.pow_const (2 : ℕ))).div_const 2)).mul
      (hchi.measurable.comp_aemeasurable hd)

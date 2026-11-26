-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_grid_sum_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:58:28.032472+00:00
-- url     : https://prove2.me/submissions/bb9192ec-c69b-46d7-bd5d-b7044802376f

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
theorem solution   {Omega : Type} [MeasurableSpace Omega]
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
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :
    ∀ (T : NNReal) (n : ℕ) (t : NNReal),
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      AEMeasurable (fun w => ∑ k ∈ Finset.range n,
        g ((u k:ℝ),X (u k) w)*(X (v (k+1)) w-X (v k) w)^2/2) P := by
  intro T n t u v
  have hx := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hLevy
  apply Finset.aemeasurable_fun_sum
  intro k hk
  have hG : Continuous (fun x : ℝ => g ((u k:ℝ),x)) :=
    hg.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨(u k).coe_nonneg,Set.mem_univ _⟩)
  exact ((hG.measurable.comp_aemeasurable (hx (u k))).mul
    (((hx (v (k+1))).sub (hx (v k))).pow_const (2:ℕ))).div_const 2

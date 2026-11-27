-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_jump_cutoff_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:21:53.204848+00:00
-- url     : https://prove2.me/submissions/2495cce1-609c-47a5-aa3f-57b77d5cbb78

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_path_cutoff_limit
import Theorems.Thm_Kyprianou_Ch04_ito43_ae_jump_summable_at_time
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set
theorem solution    {Omega : Type} [MeasurableSpace Omega]
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
    ∀ t : NNReal, ∀ᵐ w ∂P, Tendsto (fun m : ℕ =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        g (z.1,Xleft z.1.toNNReal w)*z.2^2/2 *
          min 1 (max 0 (|z.2| * ((m:ℝ)+1)-1))
          ∂(pathJumpMeasure X Xleft w)) atTop
      (nhds (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        g (z.1,Xleft z.1.toNNReal w)*z.2^2/2 ∂(pathJumpMeasure X Xleft w))) := by
  intro t
  have he := ito43_ae_jump_summable_at_time P X Xleft hLevy triplet hTriplet hLeft t
  exact (hLevy.cadlag_ae.and (hLeft.and he)).mono fun w hw =>
    ito43_weighted_path_cutoff_limit X Xleft w hw.1 hw.2.1 g hg t hw.2.2

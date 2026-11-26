-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_time_integral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:55:12.124666+00:00
-- url     : https://prove2.me/submissions/5ece7389-070c-4e55-a7e9-7a8d296faece

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_joint_version
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
    ∀ t : NNReal, AEMeasurable (fun w =>
      ∫ s in Set.Icc (0:ℝ) (t:ℝ), g (s,X (Real.toNNReal s) w) ∂volume) P := by
  intro t
  obtain ⟨Y,hY,hEq,hCad⟩ := Kyprianou.Ch04.ito43_levy_joint_version P X hLevy
  have hg0 : Continuous (fun z : ℝ × ℝ => g (max 0 z.1,z.2)) :=
    hg.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
      (fun z => ⟨show 0 ≤ max 0 z.1 from le_max_left _ _,Set.mem_univ _⟩)
  let F : Omega × ℝ → ℝ := fun z => g (max 0 z.2,Y (Real.toNNReal z.2) z.1)
  have h1 : Measurable (fun z : Omega × ℝ => Y (Real.toNNReal z.2) z.1) :=
    hY.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hF : Measurable F := hg0.measurable.comp (measurable_snd.prodMk h1)
  have hI := (hF.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Icc (0:ℝ) (t:ℝ)))).measurable
  apply hI.aemeasurable.congr
  filter_upwards [hEq] with w hw
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  simp [F,max_eq_right hs.1,hw]

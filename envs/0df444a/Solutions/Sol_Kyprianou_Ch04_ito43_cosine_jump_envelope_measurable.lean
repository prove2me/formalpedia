-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_jump_envelope_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:38:18.516308+00:00
-- url     : https://prove2.me/submissions/6c13e79f-a2b7-478b-865c-b2dc27ec4395

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_jump_energy_localisation
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_deficit_square_bound
import Theorems.Thm_Kyprianou_Ch02_cadlagWeightedJumpSumBorelFunctionalV1
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch04_ito43_mark_integral_series
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Omega : Type} [MeasurableSpace Omega]
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
          (nhds (Xleft t omega))) :
    ∀ T : NNReal,
    let q : ℕ → ℝ → ℝ := fun m z => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2
    let J : ℕ → NNReal → Omega → ℝ := fun m t w =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        q m z.2 ∂(pathJumpMeasure X Xleft w)
    ∀ m, AEStronglyMeasurable (J m (T+1)) P := by 
  intro T q J m
  let g : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (q m z)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    (show Continuous (q m) by dsimp [q]; fun_prop).measurable
  have h0 : q m 0 = 0 := by simp [q]
  obtain ⟨F,hF,hEq⟩ := Kyprianou.Ch02.cadlagWeightedJumpSumBorelFunctionalV1 (T+1) g hg (by simp [g,h0])
  have hm := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hLevy
  have hf : AEStronglyMeasurable (fun w => (F (fun s => X s w)).toReal) P :=
    (ENNReal.measurable_toReal.comp_aemeasurable (hF.comp_aemeasurable hm)).aestronglyMeasurable
  have henergy := (ito43_levy_jump_energy_localisation P X Xleft hLevy triplet hTriplet hLeft (T+1) (by positivity)).1
  apply hf.congr
  filter_upwards [hLevy.cadlag_ae,hLeft,henergy] with w hc hl hs
  have hnon (s : Ioc (0:NNReal) (T+1)) : 0 ≤ q m (X s w-Xleft s w) :=
    (ito43_cosine_deficit_square_bound ((m:ℝ)+1) _ (by positivity)).1
  have hsum : Summable (fun s : Ioc (0:NNReal) (T+1) => q m (X s w-Xleft s w)) :=
    Summable.of_nonneg_of_le hnon (fun s => by
      have h := ito43_cosine_deficit_square_bound ((m:ℝ)+1) (X s w-Xleft s w) (by positivity)
      linarith [h.2.1,sq_nonneg (X s w-Xleft s w)]) hs
  have hleft (s : Ioc (0:NNReal) (T+1)) : Function.leftLim (fun t => X t w) s = Xleft s w := by
    haveI : (nhdsWithin (s:NNReal) (Iio s)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,s.property.1⟩
    exact leftLim_eq_of_tendsto (hl s s.property.1)
  rw [hEq _ (fun s => (hc s).1) (fun s hs => ⟨Xleft s w,hl s hs⟩)]
  have hseries : (∑' s : Ioc (0:NNReal) (T+1), g (X s w - Function.leftLim (fun t => X t w) s)) =
      ENNReal.ofReal (∑' s : Ioc (0:NNReal) (T+1), q m (X s w-Xleft s w)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnon hsum]
    apply tsum_congr
    intro s
    rw [hleft s]
  rw [hseries,ENNReal.toReal_ofReal (tsum_nonneg hnon)]
  exact (ito43_mark_integral_series X Xleft w hc hl (q m) h0 (T+1)).symm

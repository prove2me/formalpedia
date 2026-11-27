-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ActualSmallBandFullLimitV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:40:56.53075+00:00
-- url     : https://prove2.me/submissions/3fdfe5d2-9c84-40dc-aa12-70ff4c4d2573
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise45UniformCutoffCauchyLimitV1
import Theorems.Thm_Kyprianou_Ch04_exercise45CompactUniformLimitRightV1
import Theorems.Thm_Kyprianou_Ch04_exercise45StrictBandRightV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ActualSmallBandUniformCauchyV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hZero : ∀ᵐ w ∂P, N.N w ({0} ×ˢ (Set.univ : Set ℝ)) = 0) :
    ∃ Z : NNReal → Ω → ℝ, ∀ᵐ w ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun s => Z s w) (Ici t) t ∧
      Tendsto (fun e : ℝ =>
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
          z.2 ∂(N.N w)) -
        (t : ℝ) * ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (Z t w)) := by
  classical
  let A : ℝ → NNReal → Ω → ℝ := fun e t w =>
    (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
      z.2 ∂(N.N w)) - (t:ℝ)*∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν
  let e : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc := Kyprianou.Ch04.exercise45ActualSmallBandUniformCauchyV1 P ν hν N hZero
  have hr (n : ℕ) := Kyprianou.Ch04.exercise45StrictBandRightV1 P ν hν N hZero
    (e n) (he n)
  have hrc : ∀ᵐ w ∂P, ∀ n : ℕ, ∀ t : NNReal,
      ContinuousWithinAt (fun s => A (e n) s w) (Ici t) t :=
    ae_all_iff.2 hr
  have hwitness : ∀ᵐ w ∂P, ∃ z : NNReal → ℝ, ∀ t : NNReal,
      ContinuousWithinAt z (Ici t) t ∧
      Tendsto (fun r => A r t w) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (z t)) := by
    filter_upwards [hc,hrc] with w hw hwr
    obtain ⟨z,hu,hl⟩ := Kyprianou.Ch04.exercise45UniformCutoffCauchyLimitV1
      (fun r t => A r t w) e he he0 hw
    refine ⟨z,fun t => ⟨?_,hl t⟩⟩
    apply Kyprianou.Ch04.exercise45CompactUniformLimitRightV1
      (fun n s => A (e n) s w) z (t+1) t (by simp) (fun n => hwr n t)
    intro δ hδ
    obtain ⟨a,ha,h⟩ := hu (t+1) δ hδ
    obtain ⟨n,hn⟩ := eventually_atTop.1 (he0 (Iio_mem_nhds ha))
    exact ⟨n,fun m hm s hs => h (e m) (he m) (hn m hm) s hs⟩
  let Z : NNReal → Ω → ℝ := fun t w =>
    if h : ∃ z : NNReal → ℝ, ∀ s : NNReal,
        ContinuousWithinAt z (Ici s) s ∧
        Tendsto (fun r => A r s w) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (z s))
      then Classical.choose h t else 0
  refine ⟨Z,?_⟩
  filter_upwards [hwitness] with w hw
  intro t
  have heq : (fun s => Z s w) = Classical.choose hw := by
    funext s
    simp only [Z,dif_pos hw]
  have hh := Classical.choose_spec hw t
  rw [heq,show Z t w = Classical.choose hw t from congrFun heq t]
  exact hh

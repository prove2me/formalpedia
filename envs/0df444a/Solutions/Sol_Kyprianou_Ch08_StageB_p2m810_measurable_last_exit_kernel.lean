-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_measurable_last_exit_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:47:53.782173+00:00
-- url     : https://prove2.me/submissions/cc91381b-be33-4609-a780-991f4cb45ca2

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_last_negative_rational_sup
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_measurable_ruin_path_reward
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ H : ℝ × (ℝ≥0 → ℝ) → ℝ,
      Measurable H ∧ (∀ z, 0 ≤ H z ∧ H z ≤ 1) ∧
      ∀ (x : ℝ) (f : ℝ≥0 → ℝ),
        (∀ t, ContinuousWithinAt f (Ici t) t) →
        H (x,f) = discountedAt q (lastNegativeVisit (fun t (_ : Unit) => x + f t) ()) := by
  classical
  obtain ⟨hm,hb,_⟩ := source_result81_measurable_ruin_path_reward q 0 hq
  let C : ℚ → ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞ := fun r z =>
    if 0 < (r : ℝ) ∧ z.1 + z.2 (Real.toNNReal (r : ℝ)) < 0
      then (Real.toNNReal (r : ℝ) : ℝ≥0∞) else 0
  let H : ℝ × (ℝ≥0 → ℝ) → ℝ := fun z => discountedAt q (⨆ r, C r z)
  have hC (r : ℚ) : Measurable (C r) := by
    by_cases hp : 0 < (r : ℝ)
    · have he : Measurable (fun z : ℝ × (ℝ≥0 → ℝ) =>
          z.1 + z.2 (Real.toNNReal (r : ℝ))) :=
        measurable_fst.add ((measurable_pi_apply _).comp measurable_snd)
      simpa only [C,hp,true_and] using
        (Measurable.ite (measurableSet_lt he measurable_const)
          measurable_const measurable_const : Measurable (fun z : ℝ × (ℝ≥0 → ℝ) =>
            if z.1 + z.2 (Real.toNNReal (r : ℝ)) < 0
              then (Real.toNNReal (r : ℝ) : ℝ≥0∞) else 0))
    · simpa only [C,hp,false_and,if_false] using
        (measurable_const : Measurable (fun _ : ℝ × (ℝ≥0 → ℝ) => (0 : ℝ≥0∞)))
  refine ⟨H,hm.comp (Measurable.iSup hC),fun z => hb _,?_⟩
  intro x f hr
  have h := p2m810_last_negative_rational_sup (fun t => x + f t)
    (fun t => continuousWithinAt_const.add (hr t))
  change discountedAt q (⨆ r, C r (x,f)) =
    discountedAt q (lastNegativeVisit (fun t (_ : Unit) => x + f t) ())
  rw [h]
  rfl

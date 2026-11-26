-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49StoppedDeficitFutureProductV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:33:56.602521+00:00
-- url     : https://prove2.me/submissions/21eb565c-1478-4a69-b5b0-86fe4bf81c6c

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_levyProcessCompletionTransportV1
import Theorems.Thm_Kyprianou_Ch04_exercise49StoppedDeficitFutureProductCompleteV1
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Transport the stopped product law from the completed probability space. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ w, IsCadlag (fun t => X t w))
    (τ : Ω → WithTop NNReal)
    (hτ : ∀ w, τ w = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0})
    (hτm : Measurable τ) (f : Ω → NNReal) (hf : Measurable f)
    (he : ∀ w, τ w ≠ ⊤ → τ w = (f w : WithTop NNReal)) :
    let D : Set Ω := {w | τ w ≠ ⊤}
    let I : Ω → ℝ := fun w => -X (f w) w
    let Y : Ω → (NNReal → ℝ) := fun w u => X (f w + u) w - X (f w) w
    Measure.map (fun w => (I w, Y w)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map (fun w u => X u w) P) := by
  let Q := P.completion
  letI : IsProbabilityMeasure Q := ⟨by change P univ = 1; exact measure_univ⟩
  let Xc : NNReal → NullMeasurableSpace Ω P → ℝ := fun t w => X t w
  have hXc := Kyprianou.Ch03.levyProcessCompletionTransportV1 P X hX hm
  have hmc : ∀ t, Measurable (Xc t) := fun t _ h => (hm t h).nullMeasurableSet
  have hτc : Measurable (fun w : NullMeasurableSpace Ω P => τ w) :=
    fun _ h => (hτm h).nullMeasurableSet
  have hfc : Measurable (fun w : NullMeasurableSpace Ω P => f w) :=
    fun _ h => (hf h).nullMeasurableSet
  have h := Kyprianou.Ch04.exercise49StoppedDeficitFutureProductCompleteV1
    Q Xc hXc hmc hc τ hτ hτc f hfc he
  let D : Set Ω := {w | τ w ≠ ⊤}
  have hD : MeasurableSet D := (hτm (measurableSet_singleton ⊤)).compl
  let I : Ω → ℝ := fun w => -X (f w) w
  let Y : Ω → (NNReal → ℝ) := fun w u => X (f w + u) w - X (f w) w
  let V : Ω → (NNReal → ℝ) := fun w u => X u w
  have hj := AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
    X hm (fun w t => (hc w t).1)
  have hi : Measurable I := (hj.comp (hf.prodMk measurable_id)).neg
  have hy : Measurable Y := measurable_pi_iff.mpr fun u =>
    (hj.comp ((hf.add measurable_const).prodMk measurable_id)).sub
      (hj.comp (hf.prodMk measurable_id))
  have hv : Measurable V := measurable_pi_iff.mpr hm
  have hMap {E : Type} [MeasurableSpace E] (g : Ω → E) (hg : Measurable g)
      (A : Set Ω) (hA : MeasurableSet A) :
      (Q.restrict {w : NullMeasurableSpace Ω P | w ∈ A}).map
        (fun w : NullMeasurableSpace Ω P => g w) =
        (P.restrict A).map g := by
    have hgc : Measurable (fun w : NullMeasurableSpace Ω P => g w) :=
      fun _ hb => (hg hb).nullMeasurableSet
    ext B hB
    rw [Measure.map_apply hgc hB, Measure.map_apply hg hB,
      Measure.restrict_apply (hgc hB), Measure.restrict_apply (hg hB)]
    rfl
  change (Q.restrict {w : NullMeasurableSpace Ω P | w ∈ D}).map (fun w : NullMeasurableSpace Ω P => (I w, Y w)) =
    ((Q.restrict {w : NullMeasurableSpace Ω P | w ∈ D}).map (fun w : NullMeasurableSpace Ω P => I w)).prod
      (Q.map (fun w : NullMeasurableSpace Ω P => V w)) at h
  have hV : Q.map (fun w : NullMeasurableSpace Ω P => V w) = P.map V := by
    have hvc : Measurable (fun w : NullMeasurableSpace Ω P => V w) :=
      fun _ hb => (hv hb).nullMeasurableSet
    ext B hB
    rw [Measure.map_apply hvc hB, Measure.map_apply hv hB]
    rfl
  rw [hMap _ (hi.prodMk hy) D hD, hMap I hi D hD, hV] at h
  exact h

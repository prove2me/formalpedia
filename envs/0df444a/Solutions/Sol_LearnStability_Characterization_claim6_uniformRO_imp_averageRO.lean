-- Prove2me | solution 1 for LearnStability.Characterization.claim6_uniformRO_imp_averageRO
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:30:19.005133+00:00
-- url     : https://prove2.me/submissions/c9fd8166-aa77-4275-a122-9dca69475f72

import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties
import Definitions.Def_LearnStability_Characterization_Stability

open MeasureTheory Finset
open LearnStability.Characterization

theorem solution {H Z : Type*} [MeasurableSpace Z]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (ε : ℕ → ℝ)
    (hstab : UniformROStable f A ε) :
    ∀ D : Measure Z, IsProbabilityMeasure D → AverageROStable f A D ε := by
  classical
  intro D hD m hm
  letI := hD
  haveI : IsProbabilityMeasure (sampleLaw D m) := by unfold sampleLaw;infer_instance
  let Q := (sampleLaw D m).prod D
  let F (i : Fin m) (p : (Fin m → Z) × Z) := f (A m (Function.update p.1 i p.2)) p.2-f (A m p.1) p.2
  have hF (i : Fin m) : Measurable (F i) := by
    exact ((hA m).comp (measurable_update'.prodMk measurable_snd)).sub (hA m)
  have hFi (i : Fin m) : Integrable (F i) Q := by
    apply Integrable.of_bound (hF i).aestronglyMeasurable (2*B)
    filter_upwards [] with p
    change ‖f (A m (Function.update p.1 i p.2)) p.2-f (A m p.1) p.2‖ ≤ 2*B
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hP.bounded (A m (Function.update p.1 i p.2)) p.2,hP.bounded (A m p.1) p.2])
  have he (i : Fin m) :
      (∫ p, (f (A m (Function.update p.1 i (p.2 i))) (p.2 i) - f (A m p.1) (p.2 i))
        ∂((sampleLaw D m).prod (sampleLaw D m)))=∫ p,F i p ∂Q := by
    have hp : MeasurePreserving (fun p : (Fin m → Z) × (Fin m → Z)=>(p.1,p.2 i))
        ((sampleLaw D m).prod (sampleLaw D m)) Q :=
      (MeasurePreserving.id (sampleLaw D m)).prod (measurePreserving_eval (fun _ : Fin m=>D) i)
    change (∫ p,F i (p.1,p.2 i) ∂((sampleLaw D m).prod (sampleLaw D m)))=∫ p,F i p ∂Q
    rw [←hp.map_eq,integral_map hp.measurable.aemeasurable (hF i).aestronglyMeasurable]
  simp_rw [he]
  rw [←integral_finsetSum _ (fun i _=>hFi i),←integral_div]
  have hb (p : (Fin m → Z) × Z) : |(∑ i,F i p)/(m : ℝ)| ≤ ε m := by
    rw [abs_div]
    have hmn : |(m : ℝ)|=m := abs_of_nonneg (Nat.cast_nonneg m)
    rw [hmn]
    apply (div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg m)).trans
    exact hstab m hm p.1 (fun _=>p.2) p.2
  have hh:=norm_integral_le_of_norm_le_const (μ:=Q)
    (f:=fun p=>(∑ i,F i p)/(m : ℝ)) (C:=ε m)
    (Filter.Eventually.of_forall (fun p=>by simpa only [Real.norm_eq_abs] using hb p))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

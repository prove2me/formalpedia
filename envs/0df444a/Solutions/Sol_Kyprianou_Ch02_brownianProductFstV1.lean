-- Prove2me | solution 1 for Kyprianou.Ch02.brownianProductFstV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:45:47.939816+00:00
-- url     : https://prove2.me/submissions/5eeeff58-e98b-4a61-bccc-9ecddc54b93a

import Theorems.Thm_Kyprianou_Ch02_indepComapFstProductV1
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (B₁ : LevyStochCalc.Brownian.BrownianMotion P₁) :
    ∃ B : LevyStochCalc.Brownian.BrownianMotion (P₁.prod P₂),
      ∀ (t : ℝ) (ω : Ω₁ × Ω₂), B.W t ω = B₁.W t ω.1 := by
  let P : Measure (Ω₁ × Ω₂) := P₁.prod P₂
  have hP : IsProbabilityMeasure P := inferInstance
  have hmap_fst : P.map Prod.fst = P₁ := by
    simp [P, Measure.map_fst_prod]
  have hmap_snd : P.map Prod.snd = P₂ := by
    simp [P, Measure.map_snd_prod]
  let B : LevyStochCalc.Brownian.BrownianMotion P :=
    { W := fun t ω => B₁.W t ω.1
      measurable_eval := fun t => (B₁.measurable_eval t).comp measurable_fst
      joint_measurable := by
        have hcomp : Function.uncurry (fun (t : ℝ) (ω : Ω₁ × Ω₂) => B₁.W t ω.1) =
            (Function.uncurry B₁.W) ∘ (Prod.map id Prod.fst) := rfl
        rw [hcomp]
        exact B₁.joint_measurable.comp (measurable_id.prodMap measurable_fst)
      initial_zero := Measure.quasiMeasurePreserving_fst.ae B₁.initial_zero
      increment_gaussian := fun {s t} hs hst => by
        have hmeas : Measurable (fun ω₁ : Ω₁ => B₁.W t ω₁ - B₁.W s ω₁) :=
          (B₁.measurable_eval t).sub (B₁.measurable_eval s)
        have hcomp : (fun ω : Ω₁ × Ω₂ => B₁.W t ω.1 - B₁.W s ω.1) =
            (fun ω₁ : Ω₁ => B₁.W t ω₁ - B₁.W s ω₁) ∘ Prod.fst := rfl
        rw [hcomp, ← Measure.map_map hmeas measurable_fst, hmap_fst]
        exact B₁.increment_gaussian hs hst
      continuous_paths := Measure.quasiMeasurePreserving_fst.ae B₁.continuous_paths
      negative_zero := fun s hs => Measure.quasiMeasurePreserving_fst.ae (B₁.negative_zero s hs)
      joint_increment_independent := fun {s t} hs hst => by
        have hbase := Kyprianou.Ch02.indepComapFstProductV1 P₁ P₂
          (B₁.joint_increment_independent hs hst)
        have hL : (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => B₁.W j ω.1) inferInstance) =
            (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (B₁.W j) inferInstance).comap Prod.fst := by
          simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
          rfl
        have hR : MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => B₁.W t ω.1 - B₁.W s ω.1) inferInstance =
            (MeasurableSpace.comap (fun ω₁ : Ω₁ => B₁.W t ω₁ - B₁.W s ω₁) inferInstance).comap Prod.fst := by
          rw [MeasurableSpace.comap_comp]; rfl
        rw [hL, hR]
        exact hbase }
  refine ⟨B, ?_⟩
  intro t ω
  rfl


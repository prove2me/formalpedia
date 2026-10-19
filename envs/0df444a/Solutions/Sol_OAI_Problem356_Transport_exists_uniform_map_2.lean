-- Prove2me | solution 2 for OAI.Problem356.Transport.exists_uniform_map
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:57:49.52864+00:00
-- url     : https://prove2.me/submissions/db5613d0-fa3f-4bb6-bdf9-a6556ff6dc1f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/AtomlessTransport.lean:L16-L31
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.Transport.exists_uniform_map. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Theorems.Thm_OAI_Problem356_Transport_measureReal_cdf_sublevel

-- ---- from OAI.Analysis.CoulombTransport.AtomlessMap ----
namespace OAI

universe uAlpha uBeta

/-! # Atomlessness of injective measurable pushforwards

This supports the standard-Borel-to-real reduction in the construction of
measure-preserving maps.
-/

open MeasureTheory

namespace Problem356

variable {α : Type uAlpha} {β : Type uBeta} [MeasurableSpace α] [MeasurableSpace β]

/-- An injective measurable map preserves the property of having null
singletons. No probability or finiteness hypothesis is needed. -/
theorem nullSingletonClass_map_of_injective (μ : Measure α)
    [NullSingletonClass μ] [MeasurableSingletonClass β]
    {f : α → β} (hf : Measurable f) (hinj : Function.Injective f) :
    NullSingletonClass (Measure.map f μ) := by
  constructor
  intro y
  rw [Measure.map_apply hf (measurableSet_singleton y)]
  have hsub : (f ⁻¹' {y}).Subsingleton := by
    intro x hx z hz
    apply hinj
    exact hx.trans hz.symm
  exact hsub.countable.measure_zero μ

/-- The real-valued measurable embedding used for standard Borel spaces
sends a singleton-null measure to a singleton-null real measure. -/
theorem nullSingletonClass_map_embeddingReal (μ : Measure α)
    [StandardBorelSpace α] [NullSingletonClass μ] :
    NullSingletonClass (Measure.map (embeddingReal α) μ) :=
  nullSingletonClass_map_of_injective μ (measurable_embeddingReal α)
    (measurableEmbedding_embeddingReal α).injective

end Problem356

end OAI

-- ---- from OAI.Analysis.CoulombTransport.BorelTransport ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology unitInterval

namespace Problem356.Transport

/-- A continuous CDF sends its law to uniform probability on the unit interval. -/
theorem map_cdf_unitInterval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) :
    μ.map (fun x : ℝ => (⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩ : I)) = volume := by
  let f : ℝ → I := fun x => ⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩
  have hf : Measurable f := hc.measurable.subtype_mk
  apply Measure.ext_of_Iic
  intro u
  rw [Measure.map_apply hf measurableSet_Iic, unitInterval.volume_Iic]
  change μ {x : ℝ | cdf μ x ≤ (u : ℝ)} = ENNReal.ofReal (u : ℝ)
  rw [← ofReal_measureReal (measure_ne_top μ _),
    measureReal_cdf_sublevel μ hc u.property.1 u.property.2]

end Problem356.Transport

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.ContinuousCDF ----
namespace OAI

noncomputable section

open MeasureTheory Function
open scoped Topology ENNReal

namespace Problem356

/-- A Stieltjes function has no jumps when its associated measure has no point atoms. -/
theorem continuous_stieltjesFunction_of_nullSingletonClass
    (f : StieltjesFunction ℝ) [NullSingletonClass f.measure] : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply f.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [f.rightLim_eq]
  have hz : ENNReal.ofReal (f x - leftLim f x) = 0 := by
    rw [← f.measure_singleton]
    exact measure_singleton x
  exact le_antisymm (f.mono.leftLim_le le_rfl)
    (sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hz))

/-- The cumulative distribution function of an atomless real probability measure is continuous. -/
theorem continuous_cdf_of_nullSingletonClass (mu : Measure ℝ)
    [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    Continuous (ProbabilityTheory.cdf mu) := by
  have : NullSingletonClass (ProbabilityTheory.cdf mu).measure := by
    rw [ProbabilityTheory.measure_cdf]
    infer_instance
  exact continuous_stieltjesFunction_of_nullSingletonClass _

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.AtomlessTransport ----
namespace OAI

universe uX uY

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal unitInterval

namespace Problem356.Transport

/-- Every atomless standard Borel probability admits a uniform random variable. -/
theorem exists_uniform_map {X : Type uX} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∃ f : X → I, Measurable f ∧ Measure.map f μ = volume := by
  let e := embeddingReal X
  have he : Measurable e := measurable_embeddingReal X
  let η := Measure.map e μ
  have : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map he.aemeasurable
  have : NullSingletonClass η := nullSingletonClass_map_embeddingReal μ
  have hc : Continuous (cdf η) := continuous_cdf_of_nullSingletonClass η
  let F : ℝ → I := fun x => ⟨cdf η x, cdf_nonneg η x, cdf_le_one η x⟩
  have hF : Measurable F := hc.measurable.subtype_mk
  refine ⟨F ∘ e, hF.comp he, ?_⟩
  rw [← Measure.map_map hF he]
  exact map_cdf_unitInterval η hc

end Problem356.Transport

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.Transport
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal unitInterval


theorem solution.{uX} : type_of% @_root_.OAI.Problem356.Transport.exists_uniform_map.{uX} := @_root_.OAI.Problem356.Transport.exists_uniform_map.{uX}

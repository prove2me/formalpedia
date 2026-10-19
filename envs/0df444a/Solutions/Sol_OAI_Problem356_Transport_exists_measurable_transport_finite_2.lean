-- Prove2me | solution 2 for OAI.Problem356.Transport.exists_measurable_transport_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:59:12.688978+00:00
-- url     : https://prove2.me/submissions/f39b29db-58a5-40c2-9f40-bbdd9954ac1b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/AtomlessTransport.lean:L46-L77
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.Transport.exists_measurable_transport_finite. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Theorems.Thm_OAI_Problem356_Transport_exists_uniform_map

-- ---- from OAI.Analysis.CoulombTransport.AtomlessTransport ----
namespace OAI

universe uX uY

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal unitInterval

namespace Problem356.Transport

/-- A singleton-null standard Borel probability can be transported measurably to
any probability on a nonempty standard Borel target. -/
theorem exists_measurable_transport {X : Type uX} {Y : Type uY}
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass μ] :
    ∃ Q : X → Y, Measurable Q ∧ Measure.map Q μ = ν := by
  obtain ⟨f, hf, hfμ⟩ := exists_uniform_map μ
  obtain ⟨g, hg, hgν⟩ := ν.exists_measurable_map_eq
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  rw [← Measure.map_map hg hf, hfμ, hgν]

/-- Equal finite masses can be transported provided the source has no point atoms. -/
theorem exists_measurable_transport_finite {X : Type uX} {Y : Type uY}
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NullSingletonClass μ]
    (hmass : μ univ = ν univ) :
    ∃ Q : X → Y, Measurable Q ∧ Measure.map Q μ = ν := by
  by_cases hμ : μ = 0
  · have hν : ν = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [← hmass, hμ]
      simp
    exact ⟨fun _ => Classical.choice inferInstance, measurable_const, by simp [hμ, hν]⟩
  · have : NeZero μ := ⟨hμ⟩
    have hν : ν ≠ 0 := by
      intro hν
      apply hμ
      apply Measure.measure_univ_eq_zero.mp
      rw [hmass, hν]
      simp
    have : NeZero ν := ⟨hν⟩
    have : NullSingletonClass ((μ univ)⁻¹ • μ) := ⟨fun x => by simp⟩
    obtain ⟨Q, hQ, hmap⟩ := exists_measurable_transport
      ((μ univ)⁻¹ • μ) ((ν univ)⁻¹ • ν)
    refine ⟨Q, hQ, ?_⟩
    have hscale := congrArg (fun m : Measure Y => μ univ • m) hmap
    rw [Measure.map_smul _ _ Q, smul_smul, ENNReal.mul_inv_cancel
      (NeZero.ne (μ univ)) (measure_ne_top μ univ), one_smul] at hscale
    rw [hmass, smul_smul, ENNReal.mul_inv_cancel
      (NeZero.ne (ν univ)) (measure_ne_top ν univ), one_smul] at hscale
    exact hscale

end Problem356.Transport

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.Transport
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal unitInterval


theorem solution.{uX,uY} : type_of% @_root_.OAI.Problem356.Transport.exists_measurable_transport_finite.{uX,uY} := @_root_.OAI.Problem356.Transport.exists_measurable_transport_finite.{uX,uY}

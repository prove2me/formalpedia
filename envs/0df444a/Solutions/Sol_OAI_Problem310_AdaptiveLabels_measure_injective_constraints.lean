-- Prove2me | solution 1 for OAI.Problem310.AdaptiveLabels.measure_injective_constraints
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:25:01.143334+00:00
-- url     : https://prove2.me/submissions/8293bd0d-4ab7-46d5-b50b-747813e109da

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/AdaptiveLabels.lean:L12-L34
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.AdaptiveLabels.measure_injective_constraints. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic

-- ---- from OAI.MeasureTheory.DyadicAvoidance.AdaptiveLabels ----
namespace OAI

universe u_I u_K u_B u_A

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.AdaptiveLabels

/-- Distinct table addresses read independent labels, including when some
addresses in the table are unused. -/
theorem measure_injective_constraints
    {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype I] [Fintype K] [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (addr : I → K) (hinj : Function.Injective addr)
    (s : I → Set B) (hs : ∀ i, MeasurableSet (s i)) :
    (Measure.pi (fun _ : K => ν)) {ω | ∀ i, ω (addr i) ∈ s i} =
      ∏ i, ν (s i) := by
  classical
  have hind : iIndepFun (fun k (ω : K → B) => ω k)
      (Measure.pi (fun _ : K => ν)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have h := (hind.precomp hinj).measure_inter_preimage_eq_mul
    Finset.univ (fun i _ => hs i)
  simp only [Finset.mem_univ, Set.iInter_true] at h
  rw [show {ω : K → B | ∀ i, ω (addr i) ∈ s i} =
    (⋂ i, (fun ω : K → B => ω (addr i)) ⁻¹' s i) by ext ω; simp]
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  exact (measurePreserving_eval (fun _ : K => ν) (addr i)).measure_preimage
    (hs i).nullMeasurableSet

end Problem310.AdaptiveLabels

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.AdaptiveLabels
open MeasureTheory ProbabilityTheory
open scoped BigOperators


theorem solution.{u_I,u_K,u_B} : type_of% @_root_.OAI.Problem310.AdaptiveLabels.measure_injective_constraints.{u_I,u_K,u_B} := @_root_.OAI.Problem310.AdaptiveLabels.measure_injective_constraints.{u_I,u_K,u_B}

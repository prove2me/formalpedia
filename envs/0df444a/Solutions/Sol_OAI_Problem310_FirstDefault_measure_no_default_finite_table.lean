-- Prove2me | solution 1 for OAI.Problem310.FirstDefault.measure_no_default_finite_table
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:54:33.624684+00:00
-- url     : https://prove2.me/submissions/27e5abf4-c39f-448b-b685-d65158c39f64

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/FiniteTableFirstDefault.lean:L12-L34
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.FirstDefault.measure_no_default_finite_table. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Theorems.Thm_OAI_Problem310_FirstDefault_measure_no_default_bounded

-- ---- from OAI.MeasureTheory.DyadicAvoidance.FiniteTableFirstDefault ----
namespace OAI

universe u_K

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem310.FirstDefault

/-- Transport of the finite-depth survival law to actual finite spatial
selector tables. The center lookup need only select distinct coordinates;
unused table entries are integrated out automatically. -/
theorem measure_no_default_finite_table {M d : ℕ} {K : Type u_K} [Fintype K]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfair : ∀ b, ν {b} = (2 : ENNReal)⁻¹)
    (center : BoundedAddress M d → K) (hinj : Function.Injective center) :
    (Measure.pi (fun _ : K => ν))
        (⋃ f : Path M d, {ω | ∀ i : Tests f,
          ω (center (boundedAddress f i)) = requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  apply measure_no_default_bounded
    (Measure.pi (fun _ : K => ν)) (fun a ω => ω (center a))
  · intro a
    exact measurable_pi_apply _
  · have hi : iIndepFun (fun k (ω : K → Bool) => ω k)
        (Measure.pi (fun _ : K => ν)) :=
      iIndepFun_pi (fun _ => measurable_id.aemeasurable)
    exact hi.precomp hinj
  · intro a b
    rw [(measurePreserving_eval (fun _ : K => ν) (center a)).measure_preimage
      (measurableSet_singleton b).nullMeasurableSet]
    exact hfair b

end Problem310.FirstDefault

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.FirstDefault
open MeasureTheory ProbabilityTheory


theorem solution.{u_K} : type_of% @_root_.OAI.Problem310.FirstDefault.measure_no_default_finite_table.{u_K} := @_root_.OAI.Problem310.FirstDefault.measure_no_default_finite_table.{u_K}

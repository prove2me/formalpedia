-- Prove2me | solution 1 for OAI.Problem310.FiniteTableModel.measure_center_no_default_prod
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:56:15.668992+00:00
-- url     : https://prove2.me/submissions/542aef9b-48bf-40b3-aab6-9e56beaea4ca

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/CenterFirstDefault.lean:L47-L72
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.FiniteTableModel.measure_center_no_default_prod. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Theorems.Thm_OAI_Problem310_FirstDefault_measure_no_default_finite_table

-- ---- from OAI.MeasureTheory.DyadicAvoidance.CenterFirstDefault ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u_T

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem310.FiniteTableModel

lemma centerTableAddress_injective {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ) :
    Function.Injective (centerTableAddress b x) := by
  intro a c h
  have hp := congrArg Sigma.fst h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : Node M d × Fin M => z.1.val) hp
  · exact congrArg (fun z : Node M d × Fin M => z.2) hp

/-- Exact no-default probability for the canonical spatial selector tables,
at every real center and every choice of deterministic grid resolutions. -/
theorem measure_center_no_default {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfair : ∀ bit, ν {bit} = (2 : ENNReal)⁻¹) (x : ℝ) :
    (Measure.pi (fun _ : SelectorAddress b => ν))
      (⋃ f : FirstDefault.Path M d, {ω | ∀ i : FirstDefault.Tests f,
        selectorValue b ω (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  have h := FirstDefault.measure_no_default_finite_table ν hfair
    (centerTableAddress b x) (centerTableAddress_injective b x)
  simpa only [centerTableAddress, FirstDefault.boundedAddress,
    selectorValue, dite_eq_left (FirstDefault.address_length_lt _ _)] using h

/-- Adding the independent terminal tables does not change the center-path
survival probability. This is the full outcome-space form used by repair. -/
theorem measure_center_no_default_prod {M d : ℕ}
    {T : Type u_T} [MeasurableSpace T] (τ : Measure T) [IsProbabilityMeasure τ]
    (b : Node M d → Fin M → ℕ)
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfair : ∀ bit, ν {bit} = (2 : ENNReal)⁻¹) (x : ℝ) :
    ((Measure.pi (fun _ : SelectorAddress b => ν)).prod τ)
      (⋃ f : FirstDefault.Path M d, {ω : SelectorTable b × T |
        ∀ i : FirstDefault.Tests f,
        selectorValue b ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  let E : Set (SelectorTable b) := ⋃ f : FirstDefault.Path M d,
    {ω | ∀ i : FirstDefault.Tests f,
      selectorValue b ω (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
        FirstDefault.requiredBit f i}
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  have heq : (⋃ f : FirstDefault.Path M d, {ω : SelectorTable b × T |
        ∀ i : FirstDefault.Tests f,
        selectorValue b ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) = Prod.fst ⁻¹' E := by
    ext ω
    simp only [E, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_preimage]
  rw [heq, measurePreserving_fst.measure_preimage hE.nullMeasurableSet]
  exact measure_center_no_default b ν hfair x

end Problem310.FiniteTableModel

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.FiniteTableModel
open MeasureTheory ProbabilityTheory


theorem solution.{u_T} : type_of% @_root_.OAI.Problem310.FiniteTableModel.measure_center_no_default_prod.{u_T} := @_root_.OAI.Problem310.FiniteTableModel.measure_center_no_default_prod.{u_T}

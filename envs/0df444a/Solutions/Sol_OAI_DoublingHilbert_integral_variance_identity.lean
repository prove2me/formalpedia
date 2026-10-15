-- Prove2me | solution 1 for OAI.DoublingHilbert.integral_variance_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:23:58.341325+00:00
-- url     : https://prove2.me/submissions/e1d5bca5-518f-4489-8398-f9925e0ffac6

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Extremal.lean:L87-L102
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.integral_variance_identity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets

-- ---- from OAI.Geometry.DoublingHilbert.Extremal ----
namespace OAI

/-! Compact lexicographic extrema and quantitative second-moment estimates. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory
open scoped BigOperators

section Moments

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The variance identity over an arbitrary probability space. -/
theorem integral_variance_identity {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) (a : E) :
    (∫ x, ‖G x - a‖ ^ 2 ∂μ) = (∫ x, ‖G x‖ ^ 2 ∂μ) - ‖a‖ ^ 2 -
      2 * inner ℝ a ((∫ x, G x ∂μ) - a) := by
  have hpoint (x : X) : ‖G x - a‖ ^ 2 =
      ‖G x‖ ^ 2 - 2 * inner ℝ a (G x) + ‖a‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm (G x) a]
  simp_rw [hpoint]
  rw [integral_add (f := fun x => ‖G x‖ ^ 2 - 2 * inner ℝ a (G x))
      (g := fun _ => ‖a‖ ^ 2) (hG2.sub ((hG.const_inner a).const_mul 2)) (integrable_const _),
    integral_sub hG2 ((hG.const_inner a).const_mul 2), integral_const_mul,
    integral_inner hG a]
  simp only [integral_const, probReal_univ, one_smul, inner_sub_right,
    real_inner_self_eq_norm_sq]
  ring

end Moments

end DoublingHilbert

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory
open scoped BigOperators
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem solution {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) (a : E) :
    (∫ x, ‖G x - a‖ ^ 2 ∂μ) = (∫ x, ‖G x‖ ^ 2 ∂μ) - ‖a‖ ^ 2 -
      2 * inner ℝ a ((∫ x, G x ∂μ) - a) := by
  first
    | exact OAI.DoublingHilbert.integral_variance_identity hG hG2 a
    | exact OAI.DoublingHilbert.integral_variance_identity
    | (apply OAI.DoublingHilbert.integral_variance_identity <;> assumption)
    | (intros; apply OAI.DoublingHilbert.integral_variance_identity <;> assumption)

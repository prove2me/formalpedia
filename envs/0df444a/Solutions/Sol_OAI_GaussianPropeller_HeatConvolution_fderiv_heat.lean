-- Prove2me | solution 1 for OAI.GaussianPropeller.HeatConvolution.fderiv_heat
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:57:46.227162+00:00
-- url     : https://prove2.me/submissions/1872b159-de45-4bc0-ae05-92ef96dfca21

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/HeatConvolution.lean:L48-L62
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.HeatConvolution.fderiv_heat. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution

-- ---- from OAI.Probability.GaussianPropeller.HeatConvolution ----
namespace OAI

universe uV uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

namespace GaussianPropeller.HeatConvolution
-- [generator] dropped: open GaussianPropeller.Stein
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

section General
variable {V : Type uV} [NormedAddCommGroup V]

lemma integrable_shift [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {F : E → V} (hF : Continuous F) {B : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) (t : ℝ) (x : E) :
    Integrable (fun z => F (x+Real.sqrt t • z)) γ :=
  Integrable.mono' (integrable_const B) (by fun_prop) (ae_of_all _ (fun z => hB _))

variable [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

lemma fderiv_heat {F : E → V} {D : E → E →L[ℝ] V}
    (hD : ∀ x, HasFDerivAt F (D x) x) (hcD : Continuous D)
    {B C : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖D x‖ ≤ C)
    (t : ℝ) (x : E) : HasFDerivAt (heat F t) (heat D t x) x := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (bound := fun _ => C) (F' := fun x z => D (x+Real.sqrt t • z)) (by simp)
  · exact Filter.Eventually.of_forall (fun x => by fun_prop)
  · exact integrable_shift hc hB t x
  · fun_prop
  · exact ae_of_all _ (fun z x _ => hC _)
  · exact integrable_const _
  · filter_upwards [] with z x _
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using
      (hD (x+Real.sqrt t • z)).comp x ((hasFDerivAt_id x).add_const _)

end General

end GaussianPropeller.HeatConvolution

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.HeatConvolution
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology


theorem solution.{uV,uι} : type_of% @_root_.OAI.GaussianPropeller.HeatConvolution.fderiv_heat.{uV,uι} := @_root_.OAI.GaussianPropeller.HeatConvolution.fderiv_heat.{uV,uι}

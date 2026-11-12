-- Prove2me | solution 1 for OAI.IsingPerceptron.cascadeCompact_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:12:04.327343+00:00
-- url     : https://prove2.me/submissions/49073297-04aa-4915-93fe-805f776a9f38

import Mathlib
import Definitions.Def_OAIQ4Ip000

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CascadeFreshMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cascade Fresh Moments. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

lemma cascadeCompact_integral_oai (n : ℕ) (b a : ℕ → ℝ) {F : JointArray → ℝ}
    (hF : Measurable F) :
    (∫ x, F x ∂(cascadeCompactLaw n b a : Measure JointArray)) =
      ∫ σ, F (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) ∂cascadeReplicaLaw n b := by
  exact integral_map
    (continuous_compactScalarArray.measurable.comp ((measurable_diagonalPatch 1).comp (measurable_cascadeScalarArray n a))).aemeasurable
    hF.aestronglyMeasurable

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix

end

end OAI
end

theorem solution : type_of% @OAI.IsingPerceptron.cascadeCompact_integral_oai := @OAI.IsingPerceptron.cascadeCompact_integral_oai

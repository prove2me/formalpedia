-- Prove2me | solution 1 for OAI.CurrentProjection.actualRowRefinement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:53:12.285805+00:00
-- url     : https://prove2.me/submissions/0ec42955-582a-42f2-8466-aae5616398fd

import Mathlib
import Definitions.Def_GaussianReplacement

section
-- module Solutions.OAIQW_CurrentProjection.Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

open InformationTheory

lemma rowInformation_refinement {S W X E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] [MeasurableSpace E]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (γ : Measure X) [IsProbabilityMeasure γ] (e : S×W → E) (he : Measurable e) :
    rowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) γ =
      rowInformation P γ := by
  let f : S×W → S×(W×E) := fun sw => (sw.1,(sw.2,e sw))
  let g : S×(W×E) → S×W := fun sw => (sw.1,sw.2.1)
  have hf : Measurable f := measurable_fst.prodMk (measurable_snd.prodMk he)
  have hg : Measurable g := measurable_fst.prodMk measurable_snd.fst
  let T := Prod.map f (id : X → X)
  let U := Prod.map g (id : X → X)
  have hT : Measurable T := hf.prodMap measurable_id
  have hU : Measurable U := hg.prodMap measurable_id
  have hfst : (P.map T).fst = P.fst.map f := by
    simp only [Measure.fst, Measure.map_map measurable_fst hT,
      Measure.map_map hf measurable_fst]
    rfl
  have hRef : (P.map T).fst.prod γ = (P.fst.prod γ).map T := by
    rw [hfst]
    change _ = (P.fst.prod γ).map (Prod.map f id)
    rw [← Measure.map_prod_map P.fst γ hf measurable_id, Measure.map_id]
  change klDiv (P.map T) ((P.map T).fst.prod γ) = klDiv P (P.fst.prod γ)
  rw [hRef]
  apply le_antisymm (klDiv_map_le _ _ hT)
  have hd := klDiv_map_le (P.map T) ((P.fst.prod γ).map T) hU
  have heq : U ∘ T = id := rfl
  simpa only [Measure.map_map hU hT, heq, Measure.map_id] using hd



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ActualRow
attribute [-instance] _root_.OAI.CurrentProjection.alignedExperiment_probability _root_.OAI.CurrentProjection.blockLaw_probability _root_.OAI.CurrentProjection.endingSignalLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


theorem actualRowRefinement_oai {d m : ℕ} {W E : Type*} [MeasurableSpace W]
    [MeasurableSpace E] [Countable W] [MeasurableSingletonClass W]
    [Countable E] [MeasurableSingletonClass E]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (e : Sphere d×W → E) (he : Measurable e)
    (_hEntropy : shannonEntropy
      ((P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))).map swapLast).snd ≠ ∞) :
    rowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) (gaussianRows m d) =
      rowInformation P (gaussianRows m d) :=
  rowInformation_refinement P (gaussianRows m d) e he



end CurrentProjection

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CurrentProjection.actualRowRefinement_oai.{u_1, u_2} := @OAI.CurrentProjection.actualRowRefinement_oai.{u_1, u_2}

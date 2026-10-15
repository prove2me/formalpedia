-- Prove2me | solution 1 for OAI.IndependentProducts.measurePreserving_sampleSelector
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:30:19.825613+00:00
-- url     : https://prove2.me/submissions/61cb0422-c2b3-400e-bd32-1296776f6f84

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/FiniteHeads.lean:L166-L187
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.measurePreserving_sampleSelector. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads

-- ---- from OAI.Analysis.ProductSpaces.FiniteHeads ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uκ

namespace IndependentProducts
namespace FiniteHead
variable (T : FiniteHead)

end FiniteHead
end IndependentProducts

namespace IndependentProducts

section Selector
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- Any coordinatewise choice from independent whole samples is again a product sample.
The second index is unchanged, so the selected scalar coordinates are all distinct. -/
lemma measurePreserving_sampleSelector {κ : Type uκ} [Fintype κ] (s : Edge → κ) :
    MeasurePreserving (fun ω : κ → Sample => fun e => ω (s e) e)
      (Measure.pi (fun _ : κ => productMeasure μ)) (productMeasure μ) := by
  have hi : iIndepFun (fun (p : (k : κ) × Edge) (ω : κ → Sample) => ω p.1 p.2)
      (Measure.pi (fun _ : κ => productMeasure μ)) := by
    have h := iIndepFun_uncurry_infinitePi
      (fun (_ : κ) (_ : Edge) => μ) (X := fun (_ : κ) (_ : Edge) (x : ℝ) => x)
      (by fun_prop)
    simpa only [Measure.infinitePi_eq_pi, productMeasure] using h
  have hinj : Function.Injective (fun e : Edge => (⟨s e, e⟩ : (k : κ) × Edge)) := by
    intro e f h
    exact congrArg Sigma.snd h
  have hsel := hi.precomp hinj
  refine ⟨by fun_prop, ?_⟩
  rw [hsel.map_fun_eq_infinitePi_map (by fun_prop)]
  unfold productMeasure
  congr 1
  funext e
  exact ((measurePreserving_eval_infinitePi (fun _ : Edge => μ) e).comp
    (measurePreserving_eval (fun _ : κ => productMeasure μ) (s e))).map_eq

end Selector
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uκ
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

theorem solution {κ : Type uκ} [Fintype κ] (s : Edge → κ) :
    MeasurePreserving (fun ω : κ → Sample => fun e => ω (s e) e)
      (Measure.pi (fun _ : κ => productMeasure μ)) (productMeasure μ) := by
  first
    | exact OAI.IndependentProducts.measurePreserving_sampleSelector s
    | exact OAI.IndependentProducts.measurePreserving_sampleSelector μ s
    | exact OAI.IndependentProducts.measurePreserving_sampleSelector
    | (apply OAI.IndependentProducts.measurePreserving_sampleSelector <;> assumption)
    | (intros; apply OAI.IndependentProducts.measurePreserving_sampleSelector <;> assumption)

-- Prove2me | solution 1 for GroundTheory.Automorphic.analyticAt_expChartProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:12.650214+00:00
-- url     : https://prove2.me/submissions/17a7c668-8145-49dc-95ae-b9f589c4f3db

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace GroundTheory.Automorphic
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : AnalyticAt ℝ (expChartProd b X) p := by
  have h1 : AnalyticAt ℝ (fun q : EuclideanSpace ℝ (Fin d) × ℝ => ((coordEquiv b q.1 : 𝔤) : 𝔸)) p :=
    (𝔤.subtypeL.comp ((coordEquiv b : EuclideanSpace ℝ (Fin d) →L[ℝ] 𝔤).comp
      (ContinuousLinearMap.fst ℝ _ ℝ))).analyticAt p
  have h2 : AnalyticAt ℝ (fun q : EuclideanSpace ℝ (Fin d) × ℝ => q.2 • (X : 𝔸)) p :=
    ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) ℝ).smulRight (X : 𝔸)).analyticAt p
  have h1' := (exp_analytic (𝕂 := ℝ) _).comp h1
  have h2' := (exp_analytic (𝕂 := ℝ) _).comp h2
  exact h1'.mul h2'
end GroundTheory.Automorphic

-- Prove2me | solution 1 for GroundTheory.Automorphic.analyticAt_expChartFlow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:41.969205+00:00
-- url     : https://prove2.me/submissions/ca086042-f3af-4fb4-a587-c47874fc3287

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpChart
import Theorems.Thm_GroundTheory_Automorphic_analyticAt_expPartialHomeomorph_symm
import Theorems.Thm_GroundTheory_Automorphic_analyticAt_expChartProd
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm


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
    {p : EuclideanSpace ℝ (Fin d) × ℝ}
    (hp : expChartProd b X p ∈ (expPartialHomeomorph ℝ 𝔸).target) :
    AnalyticAt ℝ (expChartFlow b X) p := by
  have hL : AnalyticAt ℝ (fun w : 𝔸 => (coordEquiv b).symm (subspaceProj 𝔤 w))
      ((expPartialHomeomorph ℝ 𝔸).symm (expChartProd b X p)) :=
    (((coordEquiv b).symm : 𝔤 →L[ℝ] EuclideanSpace ℝ (Fin d)).comp (subspaceProj 𝔤)).analyticAt _
  have h2 : AnalyticAt ℝ ((expPartialHomeomorph ℝ 𝔸).symm ∘ expChartProd b X) p :=
    (analyticAt_expPartialHomeomorph_symm hp).comp (analyticAt_expChartProd b X p)
  exact AnalyticAt.comp (f := (expPartialHomeomorph ℝ 𝔸).symm ∘ expChartProd b X)
    (g := fun w : 𝔸 => (coordEquiv b).symm (subspaceProj 𝔤 w)) hL h2
end GroundTheory.Automorphic

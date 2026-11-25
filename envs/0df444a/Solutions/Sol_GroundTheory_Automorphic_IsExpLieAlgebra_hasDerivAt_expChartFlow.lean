-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.hasDerivAt_expChartFlow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:17:22.474503+00:00
-- url     : https://prove2.me/submissions/9a3411a1-ebf0-4271-b307-93564f9e1713

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpChart
import Theorems.Thm_GroundTheory_Automorphic_analyticAt_expChartFlow
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expChartProd_zero_mem_nhdOne

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
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    HasDerivAt (fun t : ℝ => expChartFlow b X (x, t)) (expChartCoeff b X x) 0 := by
  have hA : AnalyticAt ℝ (expChartFlow b X) (x, 0) :=
    analyticAt_expChartFlow b X (h.nhdOne_subset_target (h.expChartProd_zero_mem_nhdOne b X hx))
  have hl : HasDerivAt (fun t : ℝ => (x, t)) ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id 0)
  exact hA.differentiableAt.hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hl
end GroundTheory.Automorphic.IsExpLieAlgebra

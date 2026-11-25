-- Prove2me | solution 1 for GroundTheory.Automorphic.continuous_expChartProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:57.96403+00:00
-- url     : https://prove2.me/submissions/e14f4419-c820-4a56-abf4-8fb43e726b00

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
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤) :
    Continuous (expChartProd b X) := by
  unfold expChartProd
  refine Continuous.mul ?_ ?_
  · exact (contDiff_exp ℝ 𝔸 (n := 0)).continuous.comp
      (continuous_subtype_val.comp ((coordEquiv b).continuous.comp continuous_fst))
  · exact (contDiff_exp ℝ 𝔸 (n := 0)).continuous.comp (continuous_snd.smul continuous_const)
end GroundTheory.Automorphic

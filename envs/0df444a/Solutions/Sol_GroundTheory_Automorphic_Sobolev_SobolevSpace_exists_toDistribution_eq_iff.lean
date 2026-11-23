-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.SobolevSpace.exists_toDistribution_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:42.592156+00:00
-- url     : https://prove2.me/submissions/b40e5803-7cab-447a-8f95-6a1721ecb2c2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_memSobolev_toDistribution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s : ℝ}
namespace GroundTheory.Automorphic.Sobolev.SobolevSpace
theorem _root_.solution (u : 𝓢'(E, F)) :
    (∃ v : SobolevSpace E F s, toDistribution v = u) ↔ MemSobolev s 2 u :=
  ⟨fun ⟨v, hv⟩ ↦ hv ▸ memSobolev_toDistribution v, fun hu ↦ ⟨mk u hu, rfl⟩⟩
end GroundTheory.Automorphic.Sobolev.SobolevSpace

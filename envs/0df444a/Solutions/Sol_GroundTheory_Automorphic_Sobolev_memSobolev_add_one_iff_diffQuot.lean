-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.memSobolev_add_one_iff_diffQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:27.544398+00:00
-- url     : https://prove2.me/submissions/9f6b018d-59a8-44d6-bd58-f36452a6be65

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_norm_diffQuot_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_memSobolev_add_one_of_diffQuot
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_inclusion_mk_eq

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
open Filter Topology
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) ↔
      ∀ v : E, ∃ C, ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖SobolevSpace.diffQuot v t u‖ ≤ C := by
  refine ⟨fun hu v ↦ ⟨2 * Real.pi * ‖v‖ * ‖SobolevSpace.mk (s := s + 1) _ hu‖,
    Eventually.of_forall fun t ↦ ?_⟩, memSobolev_add_one_of_diffQuot u⟩
  have h := SobolevSpace.norm_diffQuot_le v t (SobolevSpace.mk (s := s + 1) _ hu)
  rwa [inclusion_mk_eq u hu] at h
end GroundTheory.Automorphic.Sobolev

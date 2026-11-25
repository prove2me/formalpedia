-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_lineDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:34:04.165072+00:00
-- url     : https://prove2.me/submissions/f08bc582-1e30-4f41-9edf-4a17dc3bea82

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_toDistribution
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_exists_toDistribution_eq_iff
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_norm_lineDerivCLM_apply_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (v : E) {s : ℝ} {u : 𝓢'(E, ℂ)} (hu : MemSobolev s 2 u) :
    sob (s - 1) (LineDeriv.lineDerivOp v u) ≤ ENNReal.ofReal (2 * Real.pi * ‖v‖) * sob s u := by
  obtain ⟨w, rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu
  rw [← SobolevSpace.toDistribution_lineDerivCLM, sob_toDistribution, sob_toDistribution,
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (SobolevSpace.norm_lineDerivCLM_apply_le v w)
end GroundTheory.Automorphic.Sobolev

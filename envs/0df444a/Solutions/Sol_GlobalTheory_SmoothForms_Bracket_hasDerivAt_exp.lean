-- Prove2me | solution 1 for GlobalTheory.SmoothForms.Bracket.hasDerivAt_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:16.544398+00:00
-- url     : https://prove2.me/submissions/fe711453-a541-46ab-b63c-da14d00d3477

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracket

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Bracket
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
namespace GlobalTheory.SmoothForms.Bracket
theorem _root_.solution (A : 𝔸) : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
end GlobalTheory.SmoothForms.Bracket

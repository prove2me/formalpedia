-- Prove2me | solution 1 for GlobalTheory.SmoothForms.Bracket.unitary_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:13.486342+00:00
-- url     : https://prove2.me/submissions/3943399e-95d4-4cc8-af53-1da9b920118f

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
omit [FiniteDimensional ℝ 𝔸]
namespace GlobalTheory.SmoothForms.Bracket
theorem _root_.solution (H : IsLieData σ j s) {a b : 𝔸} (ha : σ a * a = 1) (hb : σ b * b = 1) :
    σ (a * b) * (a * b) = 1 := by
  rw [H.anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]
end GlobalTheory.SmoothForms.Bracket

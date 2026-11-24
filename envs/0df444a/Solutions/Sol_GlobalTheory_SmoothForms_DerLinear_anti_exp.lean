-- Prove2me | solution 1 for GlobalTheory.SmoothForms.DerLinear.anti_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:51:55.505927+00:00
-- url     : https://prove2.me/submissions/72bf8c1e-ca51-45cf-ac66-83288a8f3e62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinear

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
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.DerLinear
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
namespace GlobalTheory.SmoothForms.DerLinear
theorem _root_.solution (H : IsLieData σ j s) (a : 𝔸) : σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let f : 𝔸 →+* 𝔸ᵐᵒᵖ :=
    { toFun := fun b => MulOpposite.op (σ b)
      map_one' := by simp [H.one]
      map_mul' := fun b c => by simp [H.anti]
      map_zero' := by simp
      map_add' := fun b c => by simp }
  have hf : Continuous f := MulOpposite.continuous_op.comp (LinearMap.continuous_of_finiteDimensional σ)
  have h := NormedSpace.map_exp f hf a
  apply MulOpposite.op_injective
  rw [← NormedSpace.exp_op]
  exact h
end GlobalTheory.SmoothForms.DerLinear

-- Prove2me | solution 1 for GlobalTheory.SmoothForms.DerLinear.exp_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:29.07753+00:00
-- url     : https://prove2.me/submissions/cfb0340e-59a2-4711-b40f-1b116b663638

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinear
import Theorems.Thm_GlobalTheory_SmoothForms_DerLinear_anti_exp

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
theorem _root_.solution (H : IsLieData σ j s) (X : L) :
    σ (NormedSpace.exp (j X)) * NormedSpace.exp (j X) = 1 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hs : σ (j X) = -j X := (H.skew (j X)).2 ⟨X, rfl⟩
  rw [anti_exp H, hs, ← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl _)), neg_add_cancel,
    NormedSpace.exp_zero]
end GlobalTheory.SmoothForms.DerLinear

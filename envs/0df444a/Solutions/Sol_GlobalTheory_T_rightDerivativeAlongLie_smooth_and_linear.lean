-- Prove2me | solution 1 for GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:43:44.181335+00:00
-- url     : https://prove2.me/submissions/d82d27f3-2cea-4349-8474-b8123379bbbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinear
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinearStatement
import Theorems.Thm_GlobalTheory_SmoothForms_der_smooth_and_linear


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → (∀ X, Sm (expMap j s) (Der (expMap j s) X φ)) ∧ (∀ X Y, Der (expMap j s) (X + Y) φ = Der (expMap j s) X φ + Der (expMap j s) Y φ) ∧ ∀ (c : ℝ) X, Der (expMap j s) (c • X) φ = (c : ℂ) • Der (expMap j s) X φ := by
  first | exact @GlobalTheory.SmoothForms.der_smooth_and_linear | exact GlobalTheory.SmoothForms.der_smooth_and_linear | (intros; apply GlobalTheory.SmoothForms.der_smooth_and_linear <;> assumption)
end _root_.GlobalTheory.T

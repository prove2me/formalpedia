-- Prove2me | solution 1 for GlobalTheory.SmoothForms.der_smooth_and_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:31:17.287189+00:00
-- url     : https://prove2.me/submissions/9ac331fd-f029-4cf1-b1e6-24520746f351

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinear
import Theorems.Thm_GlobalTheory_SmoothForms_DerLinear_der_eq_fderiv
import Theorems.Thm_GlobalTheory_SmoothForms_DerLinear_sm_der

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
open GlobalTheory GlobalTheory.SmoothForms
namespace GlobalTheory.SmoothForms
theorem _root_.solution : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → (∀ X, Sm (expMap j s) (Der (expMap j s) X φ)) ∧ (∀ X Y, Der (expMap j s) (X + Y) φ = Der (expMap j s) X φ + Der (expMap j s) Y φ) ∧ ∀ (c : ℝ) X, Der (expMap j s) (c • X) φ = (c : ℂ) • Der (expMap j s) X φ := by
  intro 𝔸 L G _ _ _ _ _ _ σ j s H hl φ hφ
  refine ⟨fun X => DerLinear.sm_der H hl hφ X, fun X Y => ?_, fun c X => ?_⟩
  · funext g
    rw [Pi.add_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_add]
  · funext g
    rw [Pi.smul_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_smul, Complex.real_smul,
      smul_eq_mul]
end GlobalTheory.SmoothForms

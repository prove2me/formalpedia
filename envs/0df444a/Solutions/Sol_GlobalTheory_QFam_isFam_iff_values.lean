-- Prove2me | solution 1 for GlobalTheory.QFam.isFam_iff_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:41:34.84761+00:00
-- url     : https://prove2.me/submissions/2bd6b086-132d-4df5-8327-f0a609b640b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyIffValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution (ι : Type) (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ) :
    IsFam act w f ↔ ∀ (i : ι) (γ : SL(2, ℤ)) (τ : ℍ),
      f i (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * f (act i γ) τ := by
  unfold IsFam
  refine forall_congr' fun i => forall_congr' fun γ => ?_
  rw [funext_iff]
  refine forall_congr' fun τ => ?_
  have hD : UpperHalfPlane.denom γ τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [UpperHalfPlane.denom]
  have hne : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [ModularForm.SL_slash_apply, zpow_neg, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hne), hD,
    mul_comm (f (act i γ) τ)]
end GlobalTheory.QFam

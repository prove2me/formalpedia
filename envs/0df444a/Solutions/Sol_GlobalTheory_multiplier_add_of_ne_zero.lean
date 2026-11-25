-- Prove2me | solution 1 for GlobalTheory.multiplier_add_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:05:19.440238+00:00
-- url     : https://prove2.me/submissions/79161869-b886-4032-86d2-de8410868dd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_ReciprocityTheory_PTheta_dot_mulVec_symm
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_eC_eq_of_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply
attribute [local simp] GlobalTheory.thetaLevelBasis_apply

set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}
namespace GlobalTheory
theorem _root_.solution (hτ : τ.IsSymm) {χ : (ι → ℤ) → (ι → ℤ) → ℂ} (hf : f ≠ 0)
    (h : ∀ (n n' : ι → ℤ) (z : ι → ℂ), f (z + τ *ᵥ ofIntVec n + ofIntVec n') = χ n n' *
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z)
    (n n' m m' : ι → ℤ) : χ (n + m) (n' + m') = χ n n' * χ m m' := by
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hf
  have h1 := h (n + m) (n' + m') z
  rw [show z + τ *ᵥ ofIntVec (n + m) + ofIntVec (n' + m') =
    z + τ *ᵥ ofIntVec m + ofIntVec m' + τ *ᵥ ofIntVec n + ofIntVec n' by
      rw [ofIntVec_add, ofIntVec_add, mulVec_add]; abel, h, h] at h1
  have h2 : eC (-(N : ℂ) * (ofIntVec (n + m) ⬝ᵥ (τ *ᵥ ofIntVec (n + m)) / 2 + ofIntVec (n + m) ⬝ᵥ z)) =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 +
        ofIntVec n ⬝ᵥ (z + τ *ᵥ ofIntVec m + ofIntVec m'))) *
      eC (-(N : ℂ) * (ofIntVec m ⬝ᵥ (τ *ᵥ ofIntVec m) / 2 + ofIntVec m ⬝ᵥ z)) := by
    rw [← eC_add]
    refine eC_eq_of_int _ _ (N * (n ⬝ᵥ m')) ?_
    have hnm : ((n ⬝ᵥ m' : ℤ) : ℂ) = ofIntVec n ⬝ᵥ ofIntVec m' := by simp [dotProduct, ofIntVec]
    rw [Int.cast_mul, hnm]
    simp only [ofIntVec_add, mulVec_add, dotProduct_add, add_dotProduct,
      dot_mulVec_symm hτ (ofIntVec n) (ofIntVec m)]
    push_cast
    ring
  refine mul_right_cancel₀ (mul_ne_zero (eC_ne_zero (-(N : ℂ) *
    (ofIntVec (n + m) ⬝ᵥ (τ *ᵥ ofIntVec (n + m)) / 2 + ofIntVec (n + m) ⬝ᵥ z))) hz) ?_
  rw [h2] at h1 ⊢
  linear_combination -h1
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.mem_thetaLevelChar_iff_autFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:08:47.777286+00:00
-- url     : https://prove2.me/submissions/fcc7f40e-05b5-49a5-8560-9a7451e338f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Theorems.Thm_GlobalTheory_eC_nat_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}
namespace GlobalTheory
theorem _root_.solution : f ∈ thetaLevelChar a b N τ ↔ Differentiable ℂ f ∧
    ∀ (n n' : ι → ℤ) (z : ι → ℂ), f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      autFactor a b τ n n' z ^ N * f z := by
  have h (n n' : ι → ℤ) (z : ι → ℂ) : autFactor a b τ n n' z ^ N =
      eC ((N : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n)) *
        eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) := by
    rw [autFactor, mul_pow, ← eC_nat_mul, ← eC_nat_mul]; congr 2; ring
  simp only [h, mem_thetaLevelChar]
end GlobalTheory

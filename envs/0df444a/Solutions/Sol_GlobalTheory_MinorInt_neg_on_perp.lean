-- Prove2me | solution 1 for GlobalTheory.MinorInt.neg_on_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:18:49.34088+00:00
-- url     : https://prove2.me/submissions/3567cce7-1f16-4fe1-8762-f08d21ad8e2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
import Theorems.Thm_GlobalTheory_MinorInt_star_dot_self_re
import Theorems.Thm_GlobalTheory_MinorInt_form_diff_re
import Theorems.Thm_GlobalTheory_MinorInt_re_dot_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt
namespace GlobalTheory.MinorInt
theorem _root_.solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ) (hA : A.det ≠ 0)
    (h : ∀ t : ι → ℂ, (∑ i, ‖t i‖ ^ 2) / 2 ≤ (star t ⬝ᵥ (Aᴴ * A - Cᴴ * C) *ᵥ t).re)
    (b : ι → ℂ) (d : κ → ℂ) :
    ∑ a, ‖b a‖ ^ 2 ≤ 2 * ∑ i, ‖(Aᴴ *ᵥ b - Cᴴ *ᵥ d) i‖ ^ 2 + ∑ c, ‖d c‖ ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, b = A *ᵥ t :=
    ⟨A⁻¹ *ᵥ b, by rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hA), one_mulVec]⟩
  have h1 := h t
  rw [form_diff_re] at h1
  have key : star (A *ᵥ t) ⬝ᵥ (A *ᵥ t) =
      star (Aᴴ *ᵥ (A *ᵥ t) - Cᴴ *ᵥ d) ⬝ᵥ t + star d ⬝ᵥ (C *ᵥ t) := by
    rw [star_sub, sub_dotProduct, star_mulVec Aᴴ, star_mulVec Cᴴ, conjTranspose_conjTranspose,
      conjTranspose_conjTranspose, ← dotProduct_mulVec, ← dotProduct_mulVec]
    ring
  have h2 := congrArg Complex.re key
  rw [star_dot_self_re, Complex.add_re] at h2
  have h3 := re_dot_le 1 one_pos (Aᴴ *ᵥ (A *ᵥ t) - Cᴴ *ᵥ d) t
  have h4 := re_dot_le (1 / 2) (by norm_num) d (C *ᵥ t)
  rw [show (4 : ℝ) * (1 / 2) = 2 by norm_num] at h4
  rw [mul_one, one_mul] at h3
  linarith
end GlobalTheory.MinorInt

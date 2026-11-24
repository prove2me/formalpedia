-- Prove2me | solution 1 for GlobalTheory.UnitFrame.im_sum_periods
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:13:28.043803+00:00
-- url     : https://prove2.me/submissions/814c0343-684e-415b-b30e-cc538cb1cf89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemIffConjugateNotMem
import Theorems.Thm_GlobalTheory_UnitFrame_gram_eq
import Theorems.Thm_GlobalTheory_UnitFrame_hermC_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.UnitFrame
namespace _root_.GlobalTheory.UnitFrame
theorem _root_.solution {r : ℕ} (q : ℕ) (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ)
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ))
    (u v : Fin r → ℂ) :
    (∑ a : Fin r, (if (a : ℕ) < q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) u else (x⁻¹ *ᵥ u) a) *
      conj (if (a : ℕ) < q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) v else (x⁻¹ *ᵥ v) a)).im =
      -(_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v).im := by
  have hsgn : ∀ a : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 ∨ _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1 := by
    intro a; unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> simp
  have hdet : x.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hx
    rw [_root_.GlobalTheory.UnitFrame.gram_eq, det_mul, det_transpose, h0, zero_mul,
      det_diagonal] at h1
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
    rcases hsgn a with h | h <;> simp [h]
  have hx1 : x * x⁻¹ = 1 := mul_nonsing_inv x (isUnit_iff_ne_zero.2 hdet)
  have hback : ∀ y : Fin r → ℂ, x *ᵥ (x⁻¹ *ᵥ y) = y := by
    intro y; rw [mulVec_mulVec, hx1, one_mulVec]
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.col x a = x *ᵥ Pi.single a 1 := by
    intro a; funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, mulVec_single_one]
  have hkey : ∀ a (y : Fin r → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) y
      = ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) * conj ((x⁻¹ *ᵥ y) a) := by
    intro a y
    conv_lhs => rw [hcol, ← hback y]
    rw [_root_.GlobalTheory.UnitFrame.hermC_mulVec, hx]
    simp [mulVec_diagonal]
  have hfull : _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v
      = ∑ a, (x⁻¹ *ᵥ u) a * (((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) * conj ((x⁻¹ *ᵥ v) a)) := by
    conv_lhs => rw [← hback u, ← hback v]
    rw [_root_.GlobalTheory.UnitFrame.hermC_mulVec, hx]
    simp [dotProduct, mulVec_diagonal]
  rw [hfull, Complex.im_sum, Complex.im_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : (a : ℕ) < q
  · simp only [ha, if_true, hkey]
    have : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]
    simp [this, Complex.mul_im]
    ring
  · simp only [ha, if_false]
    have : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]
    simp [this, Complex.mul_im]
end _root_.GlobalTheory.UnitFrame
end GlobalTheory.UnitFrame

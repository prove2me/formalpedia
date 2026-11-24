-- Prove2me | solution 1 for GlobalTheory.ThetaExist.norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:48:23.732931+00:00
-- url     : https://prove2.me/submissions/b2641119-7dc0-4eb2-bfac-1329da357123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Theorems.Thm_GlobalTheory_ThetaExist_re_Hf_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
noncomputable section
open GlobalTheory GlobalTheory.ThetaExist
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.ThetaExist
theorem _root_.solution (Y : GT ι) (w : EuclideanSpace ℂ ι) {R : ℝ} (hw : ‖w‖ ≤ R) (γ : lat Y.b)
    {v : EuclideanSpace ℂ ι} (hv : ‖v‖ ≤ R) :
    ‖Y.ka γ * paU 1 γ (expH w) v‖ ≤ Real.exp (5 * Real.pi * R ^ 2) *
      Real.exp (-(Real.pi / 4) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) := by
  set g : EuclideanSpace ℂ ι := γ.1
  unfold paU expH
  rw [norm_mul, Y.ka_abs g γ.2, one_mul, ← Complex.exp_add, Complex.norm_exp, ← Real.exp_add,
    Real.exp_le_exp, Hf_self, sub_eq_add_neg v, Hf_add_left]
  have hR : 0 ≤ R := (norm_nonneg _).trans hw
  have h1 : (Hf v g).re ≤ R * ‖g‖ := (re_Hf_le v g).trans (by gcongr)
  have h2 : (Hf v w).re ≤ R * R := (re_Hf_le v w).trans (by gcongr)
  have h3 : (Hf (-g) w).re ≤ ‖g‖ * R := (re_Hf_le (-g) w).trans (by rw [norm_neg]; gcongr)
  have e : (((1 : ℕ) : ℂ) * Real.pi * Hf v g - ((1 : ℕ) : ℂ) * Real.pi * ((‖g‖ : ℝ) : ℂ) ^ 2 / 2 +
      Real.pi * (Hf v w + Hf (-g) w)).re =
      Real.pi * ((Hf v g).re - ‖g‖ ^ 2 / 2 + (Hf v w).re + (Hf (-g) w).re) := by
    simp only [← Complex.ofReal_pow]
    simp only [Nat.cast_one, one_mul, add_re, sub_re, re_ofReal_mul, div_ofNat_re, ofReal_re]
    ring
  rw [e]
  have : (Hf v g).re - ‖g‖ ^ 2 / 2 + (Hf v w).re + (Hf (-g) w).re ≤ 5 * R ^ 2 - ‖g‖ ^ 2 / 4 := by
    nlinarith [sq_nonneg (‖g‖ / 2 - 2 * R)]
  nlinarith [mul_le_mul_of_nonneg_left this Real.pi_pos.le]
end GlobalTheory.ThetaExist

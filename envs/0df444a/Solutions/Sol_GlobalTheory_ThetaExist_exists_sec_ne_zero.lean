-- Prove2me | solution 1 for GlobalTheory.ThetaExist.exists_sec_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:42:54.565823+00:00
-- url     : https://prove2.me/submissions/5a0bcc1e-b509-442d-85af-0c2716c80f00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Theorems.Thm_GlobalTheory_ThetaExist_coeff_eq_zero_of_fourier
import Theorems.Thm_GlobalTheory_ThetaExist_summable_gauss
import Theorems.Thm_GlobalTheory_ThetaExist_differentiable_paTh
import Theorems.Thm_GlobalTheory_ThetaExist_paTh_centre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_eq_inner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_ka_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paTh_add


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
theorem _root_.solution (Y : GT ι) (hC : Coc Y 1) : ∃ s ∈ Y.Sec 1, s ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hz : ∀ w, paTh Y 1 (expH w) = 0 := fun w =>
    hcon _ ⟨differentiable_paTh Y w, fun γ hγ v => paTh_add hC _ hγ v⟩
  set B := Y.b.restrictScalars ℤ with hB
  set c : lat Y.b → ℂ := fun γ =>
    Y.ka γ * (Real.exp (-(Real.pi / 2) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) : ℝ) with hc
  have hcs : Summable fun γ => ‖c γ‖ := by
    refine (summable_gauss Y (a := Real.pi / 2) (by positivity)).congr fun γ => ?_
    rw [hc]
    simp only [norm_mul, Y.ka_abs γ γ.2, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  choose x _ hx using fun j => Y.perfect (B.coord j).toAddMonoidHom
  have key := coeff_eq_zero_of_fourier (c := fun n => c (B.equivFun.symm n))
    ((B.equivFun.symm.toEquiv.summable_iff (f := fun γ => ‖c γ‖)).2 hcs) (fun t => ?_) 0
  · simp [hc, ka_zero hC] at key
  · set v : EuclideanSpace ℂ ι := ∑ j, (t j : ℂ) • x j with hv
    have h1 := paTh_centre Y v
    rw [hz v, Pi.zero_apply, eq_comm, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)] at h1
    rw [← h1, ← B.equivFun.symm.toEquiv.tsum_eq]
    refine tsum_congr fun n => ?_
    have h2 : ∀ j, (Hf (x j) (B.equivFun.symm n : lat Y.b)).im = n j := fun j => by
      rw [← hx j]
      simp [Finsupp.single_apply]
    suffices h3 : ∑ j, (n j : ℝ) * t j = (Hf v (B.equivFun.symm n : lat Y.b)).im by
      rw [h3]; rfl
    simp only [FPw.Hf_eq_inner] at h2 ⊢
    rw [hv, inner_sum, Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, Complex.im_ofReal_mul, h2, mul_comm]
end GlobalTheory.ThetaExist

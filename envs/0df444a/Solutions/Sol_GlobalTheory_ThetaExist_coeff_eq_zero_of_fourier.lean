-- Prove2me | solution 1 for GlobalTheory.ThetaExist.coeff_eq_zero_of_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:54:39.214463+00:00
-- url     : https://prove2.me/submissions/c01d8fe2-fa11-45c1-97b6-f501aa6405e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Theorems.Thm_GlobalTheory_ThetaExist_coeff_eq_zero_of_orthonormal

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
namespace GlobalTheory.ThetaExist
theorem _root_.solution {d : Type*} [Fintype d] {c : (d → ℤ) → ℂ}
    (hc : Summable fun n => ‖c n‖)
    (h0 : ∀ t : d → ℝ, ∑' n, c n * cexp (2 * Real.pi * I * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ)) = 0)
    (k : d → ℤ) : c k = 0 := by
  refine coeff_eq_zero_of_orthonormal _ UnitAddTorus.mFourier
    (UnitAddTorus.orthonormal_mFourier (d := d)) ?_ k
  have hs : Summable fun n => c n • UnitAddTorus.mFourier n :=
    .of_norm (by simpa [norm_smul, UnitAddTorus.mFourier_norm] using hc)
  suffices h : (0 : C(UnitAddTorus d, ℂ)) = ∑' n, c n • UnitAddTorus.mFourier n from
    h ▸ hs.hasSum
  ext x
  have hx : ∃ t : d → ℝ, x = fun j => (t j : UnitAddCircle) := by
    choose t ht using fun j => QuotientAddGroup.mk_surjective (x j)
    exact ⟨t, funext fun j => (ht j).symm⟩
  obtain ⟨t, rfl⟩ := hx
  rw [← ContinuousMap.tsum_apply hs, ContinuousMap.zero_apply, ← h0 t]
  refine tsum_congr fun n => ?_
  simp only [ContinuousMap.smul_apply, smul_eq_mul, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_coe_apply, ← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.ThetaExist

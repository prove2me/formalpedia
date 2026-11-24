-- Prove2me | solution 1 for GlobalTheory.GaussCusp.pnorm_coordProd_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:09:59.169911+00:00
-- url     : https://prove2.me/submissions/2fc07f80-4906-44fa-8b01-bab1aa524857

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstRaisingMemEquivariant
import Theorems.Thm_GlobalTheory_GaussCusp_dmin_zero
import Theorems.Thm_GlobalTheory_GaussCusp_dmin_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries (E4)
open GlobalTheory
open GlobalTheory.GaussCusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {ζ : E}
namespace GlobalTheory.GaussCusp
theorem _root_.solution (hζ : IsPrimitiveRoot ζ 4) (x : Frame (data hζ).Ψ 1) :
    (data hζ).pnorm 1 coordProd x ≤ 1 := by
  unfold Data.pnorm coordProd
  rw [norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_one (fun τ _ => by positivity) fun τ _ => ?_
  rw [Fin.prod_univ_one]
  change _ * ‖dmin 1 x τ _ / dmin 1 x τ _‖ ^ (-((1 : ℤ) : ℝ) / 2) ≤ 1
  rw [dmin_zero, dmin_one, div_one, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  have : ((2 : ℕ) : ℝ) * (-((1 : ℤ) : ℝ) / 2) = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  exact mul_inv_le_one
end GlobalTheory.GaussCusp

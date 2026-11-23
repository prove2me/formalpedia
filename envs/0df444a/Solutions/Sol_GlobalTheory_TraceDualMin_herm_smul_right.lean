-- Prove2me | solution 1 for GlobalTheory.TraceDualMin.herm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:59.84171+00:00
-- url     : https://prove2.me/submissions/dc75f1c8-4e83-4c1d-907b-5ac7279b5753

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Theorems.Thm_GlobalTheory_TraceDualMin_herm_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.TraceDualMin
namespace GlobalTheory.TraceDualMin
theorem _root_.solution {n : ℕ} (a : E) (x y : Fin n → E) :
    herm 1 x (a • y) = cc a * herm 1 x y := by
  simp [herm_one_eq, Finset.mul_sum, cc, mul_left_comm]
end GlobalTheory.TraceDualMin

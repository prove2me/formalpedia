-- Prove2me | solution 1 for GlobalTheory.TupleSumPos.five_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:22:20.654606+00:00
-- url     : https://prove2.me/submissions/b67ecbba-d001-447e-a433-0dd7f6f8fa83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroOnCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorsLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open scoped TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.TupleSumPos
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.TupleSumPos
theorem _root_.solution (T : PT E) {y : Vsp T.dim} (hy : y ∈ T.L) : (5 : ℂ) • y ∈ T.L := by
  have := T.L.nsmul_mem hy 5
  rwa [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat] at this
end GlobalTheory.TupleSumPos

-- Prove2me | solution 1 for GlobalTheory.EisPerB.latM_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:29:04.163628+00:00
-- url     : https://prove2.me/submissions/e22233f4-3888-4557-8aa2-380b703641af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemTraceDualSignedPositiveConeIffTotallyPositiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzConstantInverseDifferentEisensteinStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeSumEqConeSum
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_latM_eq_dual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.EisPerB
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.EisPerB
theorem _root_.solution (𝔞 : Frac F) : latM 𝔞 ≠ 0 := by
  rw [latM_eq_dual]
  exact FractionalIdeal.dual_ne_zero ℤ ℚ 𝔞.ne_zero
end GlobalTheory.EisPerB

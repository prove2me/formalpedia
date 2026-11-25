-- Prove2me | solution 1 for GlobalTheory.T.subgroupPowRelIndex_units_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:06.996296+00:00
-- url     : https://prove2.me/submissions/6b6afede-294a-4167-bb5a-98f556fcf55a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexUnitsOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexUnitsOfIsAdicCompleteStatement
import Theorems.Thm_GlobalTheory_CNorm_pIdx_units_of_isAdicComplete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → Nat.card (O ⧸ Ideal.span {(p : O) * π}) ≠ 0 → pTor p (⊤ : Subgroup Oˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Oˣ) = Nat.card (O ⧸ Ideal.span {(p : O)}) * pTor p (⊤ : Subgroup Oˣ) := by
  first | exact @GlobalTheory.CNorm.pIdx_units_of_isAdicComplete | exact GlobalTheory.CNorm.pIdx_units_of_isAdicComplete | (intros; apply GlobalTheory.CNorm.pIdx_units_of_isAdicComplete <;> assumption)
end _root_.GlobalTheory.T

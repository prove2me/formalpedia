-- Prove2me | solution 1 for GlobalTheory.T.subgroupPowImage_unitsCongruentOneMod_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:14.929862+00:00
-- url     : https://prove2.me/submissions/6f89e2dc-1adb-498c-9ecf-b250646f3c6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowImageUnitsCongruentOneModOfIsAdicComp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowImageUnitsCongruentOneModOfIsAdicCompStatement
import Theorems.Thm_GlobalTheory_CNorm_deep_units_pows


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
theorem _root_.solution : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → pows p (oneUnits ((p : O) * π)) = oneUnits ((p : O) ^ 2 * π) ∧ pTor p (oneUnits ((p : O) * π)) = 1 := by
  first | exact @GlobalTheory.CNorm.deep_units_pows | exact GlobalTheory.CNorm.deep_units_pows | (intros; apply GlobalTheory.CNorm.deep_units_pows <;> assumption)
end _root_.GlobalTheory.T

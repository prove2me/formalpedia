-- Prove2me | solution 1 for GlobalTheory.T.inducedClassFunctionFromSubgroup_eq_finsum_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:14:52.27798+00:00
-- url     : https://prove2.me/submissions/c124c428-b03a-400a-b92d-2c2b825175f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InducedClassFunctionFromSubgroupEqFinsumCosets
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InducedClassFunctionFromSubgroupEqFinsumCosetsStatement
import Theorems.Thm_GlobalTheory_BI_ind_eq_finsum_cosets


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), (∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) → ∀ g : G, ind H ψ g = ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) := by
  first | exact @GlobalTheory.BI.ind_eq_finsum_cosets | exact GlobalTheory.BI.ind_eq_finsum_cosets | (intros; apply GlobalTheory.BI.ind_eq_finsum_cosets <;> assumption)
end _root_.GlobalTheory.T

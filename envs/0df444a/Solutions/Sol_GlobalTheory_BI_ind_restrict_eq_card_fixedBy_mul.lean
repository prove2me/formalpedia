-- Prove2me | solution 1 for GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:26.220961+00:00
-- url     : https://prove2.me/submissions/e559a6d2-a28b-499a-baea-3177abda5a20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InducedClassFunctionFromSubgroupEqFinsumCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndRestrictEqCardFixedByMul
import Theorems.Thm_GlobalTheory_BI_out_conj_mem_iff_smul_eq
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
noncomputable section
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by
  intro L _ _ G _ _ H χ hχ g
  classical
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hψ : ∀ h x : H, (fun h : H => χ h) (x⁻¹ * h * x) = (fun h : H => χ h) h := by
    intro h x
    simpa using hχ h x
  have hterm : ∀ q : G ⧸ H, ext0 H (fun h : H => χ h) (q.out⁻¹ * g * q.out)
      = (if g • q = q then (1 : L) else 0) * χ g := by
    intro q
    unfold ext0
    by_cases hq : g • q = q
    · have hm := (out_conj_mem_iff_smul_eq H g q).2 hq
      rw [dif_pos hm, if_pos hq, one_mul]
      exact hχ g q.out
    · have hm : q.out⁻¹ * g * q.out ∉ H := fun h => hq ((out_conj_mem_iff_smul_eq H g q).1 h)
      rw [dif_neg hm, if_neg hq, zero_mul]
  rw [ind_eq_finsum_cosets L G H _ hψ g, finsum_eq_sum_of_fintype]
  simp_rw [hterm]
  rw [← Finset.sum_mul, Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl
end GlobalTheory.BI

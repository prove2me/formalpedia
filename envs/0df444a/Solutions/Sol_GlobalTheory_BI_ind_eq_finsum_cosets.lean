-- Prove2me | solution 1 for GlobalTheory.BI.ind_eq_finsum_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:15:59.487751+00:00
-- url     : https://prove2.me/submissions/381cde02-e03d-410d-b673-e9941bcccecb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InducedClassFunctionFromSubgroupEqFinsumCosets
import Theorems.Thm_GlobalTheory_BI_subgroupFunctionExtendByZero_conj_of_mem
import Theorems.Thm_GlobalTheory_BI_out_mul_bijective

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
theorem _root_.solution : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), (∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) → ∀ g : G, ind H ψ g = ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) := by
  intro L _ _ G _ _ H ψ hψ g
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite (G ⧸ H)
  have := Fintype.ofFinite H
  have hc : (Nat.card H : L) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold ind
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← (out_mul_bijective H).sum_comp (fun x : G => ext0 H ψ (x⁻¹ * g * x)), Fintype.sum_prod_type]
  have h1 : ∀ q : G ⧸ H, ∑ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G)))
      = (Nat.card H : L) * ext0 H ψ (q.out⁻¹ * g * q.out) := by
    intro q
    have h2 : ∀ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G)))
        = ext0 H ψ (q.out⁻¹ * g * q.out) := by
      intro y
      rw [← subgroupFunctionExtendByZero_conj_of_mem H ψ hψ (q.out⁻¹ * g * q.out) y]
      congr 1
      group
    simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  simp only [h1]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
end GlobalTheory.BI

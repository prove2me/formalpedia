-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.spanEq_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:51.8608+00:00
-- url     : https://prove2.me/submissions/3e97fe25-fc86-4723-bab5-a4c329d9d2ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowsP_zero
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowsP_mid
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowsP_last
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_det_rowsP
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_vecOf_zero
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_vecOf_mid
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_vecOf_last
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_vec_ext
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_smem
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_sum_smem
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_div_mem_int
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_v_zpow
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_pow_mem_int
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_zero_ne_last
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_zero_ne_mid
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_last_ne_mid
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_comb_C
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_comb_gC
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rho_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_rowLat_le
import Theorems.Thm_GlobalTheory_InertZeta_row_mem_rowLat
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid


attribute [local simp] GlobalTheory.InertZeta.RowSpan.vecOf_zero
attribute [local simp] GlobalTheory.InertZeta.RowSpan.vecOf_mid
attribute [local simp] GlobalTheory.InertZeta.RowSpan.vecOf_last

set_option autoImplicit false
open GlobalTheory.InertZeta Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.RowSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.InertZeta.RowSpan
theorem _root_.solution : SpanEq := by
  intro L _ _ ϖ N a g g₀ U V C r b c y hϖ hfrac hg00 hg0m hg0l hg10 hg11 hg12 hgl0 hglm hgll hy1 hy2 hy3 hy4
  obtain ⟨hU, hV, hC, hgC, hM⟩ := hfrac
  have hCM : C * (U + V * g₀) = 1 := mul_eq_one_comm.1 hM
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hvy : Valued.v y ≠ 0 := fun h => by rw [h] at hy1; exact WithZero.exp_ne_zero (le_zero_iff.1 hy1)
  have hy0 : y ≠ 0 := fun h => hvy (by rw [h, map_zero])
  refine ⟨rowsP a g U V y, vecOf 0 (fun j => ϖ ^ a.toNat * (r ᵥ* C) j)
    (ϖ ^ a.toNat * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y), ?_, vecOf_zero _ _ _, vecOf_mid _ _ _, vecOf_last _ _ _, ?_⟩
  · have hdet : Valued.v (U + V * g₀).det = (Valued.v C.det)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, ← Matrix.det_mul, hM, Matrix.det_one, map_one]
    rw [det_rowsP hg10 hg11, map_mul, map_mul, hdet, rowsP_zero]
    split_ifs with ha
    · rw [Int.toNat_of_nonpos (by omega)]; simp [Matrix.one_apply]
    · rw [hg00, v_zpow hϖ, Int.toNat_of_nonneg (by omega)]
  · rw [rho_mul hg10 hg11 hg12 hCM hy0]
    have hvy1 : 1 ≤ Valued.v y := le_trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) hy1
    have eS : ∀ i, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i ∈
        rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g :=
      fun i => Submodule.mem_sup_left (row_mem_rowLat _ i)
    have gS : ∀ i, g i ∈ rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g :=
      fun i => Submodule.mem_sup_right (row_mem_rowLat g i)
    have rS : ∀ k, rowM g U V k ∈ rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g :=
      fun k => add_mem (sum_smem (hU k) fun l => eS _) (sum_smem (hV k) fun l => gS _)
    have hgl : g (Fin.last (N + 1)) = ϖ ^ (-a) • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) :=
      vec_ext (by simp [hgl0, Matrix.one_apply]) (fun j => by simp [hglm, Matrix.one_apply, last_ne_mid])
        (by simp [hgll, Matrix.one_apply])
    have hw : vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) = if 0 ≤ a then
        g 0 - ϖ ^ a.toNat • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0
        else ϖ ^ (-a).toNat • g 0 - (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 := by
      split_ifs with ha
      · have hza : (ϖ ^ a.toNat : L) = ϖ ^ a := by rw [← zpow_natCast, Int.toNat_of_nonneg ha]
        refine vec_ext ?_ (fun j => ?_) ?_ <;>
          simp [hza, hg00, hg0m, hg0l, Matrix.one_apply, mid_ne_zero, zero_ne_mid, zero_ne_last]
      · have h1 : a.toNat = 0 := by omega
        have h2 : (ϖ ^ (-a).toNat : L) * ϖ ^ a = 1 := by
          rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), _root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hϖ0)]
        refine vec_ext ?_ (fun j => ?_) ?_ <;>
          simp [h1, hg00, hg0m, hg0l, Matrix.one_apply, mid_ne_zero, zero_ne_mid, zero_ne_last, ← mul_assoc, h2]
    apply le_antisymm
    · have PS : ∀ i, rowsP a g U V y i ∈ rowLat (rowsP a g U V y) ⊔
          Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)} :=
        fun i => Submodule.mem_sup_left (row_mem_rowLat _ i)
      have wS : vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) ∈ rowLat (rowsP a g U V y) ⊔
          Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)} :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      have mS : ∀ k, rowM g U V k ∈ rowLat (rowsP a g U V y) ⊔
          Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)} :=
        fun k => rowsP_mid a g U V y k ▸ PS (mid k)
      have lastS : ∀ x, Valued.v x ≤ Valued.v y → x • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) ∈
          rowLat (rowsP a g U V y) ⊔
          Submodule.span (intL L) {vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c)} := fun x hx => by
        have := smem (div_mem_int hx) (PS (Fin.last (N + 1)))
        rwa [rowsP_last, smul_smul, div_mul_cancel₀ _ hy0] at this
      apply sup_le <;> rw [rowLat_le] <;> intro i <;> rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl
      · by_cases ha : 0 ≤ a
        · have := PS 0; rwa [rowsP_zero, if_pos ha] at this
        · have h := hw; rw [if_neg ha] at h
          have hP0 := PS 0; rw [rowsP_zero, if_neg ha] at hP0
          rw [show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 = ϖ ^ (-a).toNat • g 0 -
            vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) by rw [h]; abel]
          exact sub_mem (smem (pow_mem_int hϖ _) hP0) wS
      · rw [show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) = ∑ k, C i k • rowM g U V k -
          ((C * V * g₀) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) by
          rw [comb_C hg10 hg11 hg12 hCM i]; abel]
        exact sub_mem (sum_smem (hC i) mS) (lastS _ (hy2 i))
      · have := lastS 1 (by rw [map_one]; exact hvy1); rwa [one_smul] at this
      · by_cases ha : 0 ≤ a
        · have h := hw; rw [if_pos ha] at h
          have hP0 := PS 0; rw [rowsP_zero, if_pos ha] at hP0
          rw [show g 0 = ϖ ^ a.toNat • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 +
            vecOf 0 (fun j => ϖ ^ a.toNat * r j) (ϖ ^ a.toNat * c) by rw [h]; abel]
          exact add_mem (smem (pow_mem_int hϖ _) hP0) wS
        · have := PS 0; rwa [rowsP_zero, if_neg ha] at this
      · rw [show g (mid i) = ∑ k, (g₀ * C) i k • rowM g U V k +
          ((g₀ * C * U) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) by
          rw [comb_gC hg10 hg11 hg12 hCM i]; abel]
        exact add_mem (sum_smem (hgC i) mS) (lastS _ (hy3 i))
      · rw [hgl]
        refine lastS _ (le_trans ?_ hy1)
        rw [v_zpow hϖ, neg_neg, WithZero.exp_le_exp]; omega
    · apply sup_le
      · rw [rowLat_le]; intro i; rcases idx_cases i with rfl | ⟨k, rfl⟩ | rfl
        · rw [rowsP_zero]; split_ifs
          exacts [eS 0, gS 0]
        · rw [rowsP_mid]; exact rS k
        · rw [rowsP_last]
          have key : ∀ x : L, x • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) ∈
              rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g → Valued.v y = Valued.v x →
              y • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) ∈
              rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g := fun x hx hv => by
            have hx0 : x ≠ 0 := fun h => hvy (by rw [hv, h, map_zero])
            rw [show y • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) =
              (y / x) • x • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) by
              rw [smul_smul, div_mul_cancel₀ _ hx0]]
            exact smem (div_mem_int hv.le) hx
          rcases hy4 with h | ⟨i, h⟩ | ⟨i, h⟩
          · by_cases ha : 0 ≤ a
            · refine key (ϖ ^ (-a)) (hgl ▸ gS _) ?_
              rw [h, v_zpow hϖ, neg_neg, Int.toNat_of_nonneg ha]
            · refine key 1 (by rw [one_smul]; exact eS _) ?_
              rw [h, map_one, Int.toNat_eq_zero.2 (by omega)]; simp
          · refine key _ ?_ h
            rw [show ((C * V * g₀) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) =
              ∑ k, C i k • rowM g U V k - (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) by
              rw [comb_C hg10 hg11 hg12 hCM i]; abel]
            exact sub_mem (sum_smem (hC i) rS) (eS _)
          · refine key _ ?_ h
            rw [show ((g₀ * C * U) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) =
              g (mid i) - ∑ k, (g₀ * C) i k • rowM g U V k by
              rw [comb_gC hg10 hg11 hg12 hCM i]; abel]
            exact sub_mem (gS _) (sum_smem (hgC i) rS)
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hw]
        split_ifs with ha
        · exact sub_mem (gS 0) (smem (pow_mem_int hϖ _) (eS 0))
        · exact sub_mem (smem (pow_mem_int hϖ _) (gS 0)) (eS 0)
end GlobalTheory.InertZeta.RowSpan

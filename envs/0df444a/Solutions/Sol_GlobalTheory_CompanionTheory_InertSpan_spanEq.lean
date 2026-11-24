-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertSpan.spanEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:58:50.349643+00:00
-- url     : https://prove2.me/submissions/e80bf60b-271e-4671-a61a-aaac1677e328

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_vec_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_scale
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_v_zpow
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_mid_le
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_mid_ge
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_first_row
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_vecMul_basis
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_det_basis
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_InertZeta_mid_injective
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_last
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


attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_first
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_middle
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_last
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_first
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_middle
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_last

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertSpan
namespace GlobalTheory.CompanionTheory.InertSpan
theorem _root_.solution : SpanEq := by
  intro L _ _ ϖ N a g g₀ U V C r b c y hϖ hf h00 h0m h0l hm0 hmm hml hl0 hlm hll hya hy1 hy2 hyc
  have eg0 : g 0 = vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c) :=
    vec_ext (by simp [h00]) (fun j => by simp [h0m]) (by simp [h0l])
  have egm : ∀ i, g (mid i) = vec3 (0 : L) (g₀ i) ((g₀ *ᵥ b) i) :=
    fun i => vec_ext (by simp [hm0]) (fun j => by simp [hmm]) (by simp [hml])
  have egl : g (Fin.last (N + 1)) = vec3 (0 : L) (0 : Fin N → L) (ϖ ^ (-a)) :=
    vec_ext (by simp [hl0]) (fun j => by simp [hlm]) (by simp [hll])
  have e10 : (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 = vec3 (1 : L) (0 : Fin N → L) 0 :=
    vec_ext (by simp) (fun j => by simp [Matrix.one_apply, (mid_ne_zero j).symm])
      (by simp [Matrix.one_apply])
  have e1m : ∀ k, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid k) =
      vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) 0 :=
    fun k => vec_ext (by simp [Matrix.one_apply, mid_ne_zero])
      (fun j => by simp [Matrix.one_apply, mid_injective.eq_iff])
      (by simp [Matrix.one_apply, mid_ne_last])
  have e1l : (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) = vec3 (0 : L) (0 : Fin N → L) 1 :=
    vec_ext (by simp [Matrix.one_apply]) (fun j => by simp [Matrix.one_apply, (mid_ne_last j).symm]) (by simp)
  obtain ⟨R, hR⟩ : ∃ R, R = rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g := ⟨_, rfl⟩
  have r1 : ∀ i, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i ∈ R :=
    fun i => hR ▸ Submodule.mem_sup_left (row_mem_rowLat _ i)
  have r2 : ∀ i, g i ∈ R := fun i => hR ▸ Submodule.mem_sup_right (row_mem_rowLat _ i)
  obtain ⟨q, hq0, hqR, hwR, ⟨w, hw, hwl⟩, hback⟩ := first_row hϖ a r c R (by rw [← e10]; exact r1 0)
    (by rw [← eg0]; exact r2 0) (by rw [← e1l]; exact r1 _) (by rw [← egl]; exact r2 _)
  obtain ⟨m1, m2, m3⟩ := mid_le (b := b) hf (R := R) (fun k => by rw [← e1m]; exact r1 _)
    (fun k => by rw [← egm]; exact r2 _)
  have hval : WithZero.exp (a.toNat : ℤ) ≠ 0 := WithZero.exp_ne_zero
  have hvy : Valued.v y ≠ 0 := fun h => by
    rw [h] at hya
    exact hval (le_antisymm hya zero_le')
  have hy0 : y ≠ 0 := fun h => hvy (by rw [h, map_zero])
  have hnz : ∀ t : L, Valued.v y = Valued.v t → t ≠ 0 := fun t h h0 => hvy (by rw [h, h0, map_zero])
  have hyR : vec3 (0 : L) (0 : Fin N → L) y ∈ R := by
    rcases hyc with h | ⟨i, h⟩ | ⟨i, h⟩
    · exact scale R (hnz w (h.trans hw.symm)) (h.trans hw.symm).le hwl
    · exact scale R (hnz _ h) h.le (m2 i)
    · exact scale R (hnz _ h) h.le (m3 i)
  have e' : C * (U + V * g₀) = 1 := mul_eq_one_comm.1 hf.2.2.2.2
  obtain ⟨M, hM⟩ : ∃ M : Fin N → Fin (N + 2) → L,
      M = fun k => vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = mat3 q M (vec3 (0 : L) 0 y) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = vec3 (0 : L) (ϖ ^ a.toNat • (r ᵥ* C))
      (ϖ ^ a.toNat * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y) := ⟨_, rfl⟩
  have eρ : ρ ᵥ* P = vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) := by
    rw [hρ, hP, hM]
    exact vecMul_basis q g₀ U V C r b c y _ hy0 e'
  have hdet : Valued.v (U + V * g₀).det = (Valued.v C.det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, ← Matrix.det_mul, hf.2.2.2.2, Matrix.det_one, map_one]
  refine ⟨P, ρ, ?_, by rw [hρ]; simp, fun j => by rw [hρ]; simp, by rw [hρ]; simp, ?_⟩
  · rw [hP, hM, det_basis q (U + V * g₀) ((V * g₀) *ᵥ b) y, map_mul, map_mul, hq0, hdet]
    exact mul_right_comm _ _ _
  rw [← hR]
  obtain ⟨R', hR'⟩ : ∃ R', R' = rowLat P ⊔ Submodule.span (intL L) {ρ ᵥ* P} := ⟨_, rfl⟩
  rw [← hR']
  have p1 : ∀ i, P i ∈ R' := fun i => hR' ▸ Submodule.mem_sup_left (row_mem_rowLat _ i)
  have hq' : q ∈ R' := by simpa [hP] using p1 0
  have hm' : ∀ k, vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) ∈ R' := fun k => by
    have := p1 (mid k)
    simpa [hP, hM] using this
  have hy' : vec3 (0 : L) (0 : Fin N → L) y ∈ R' := by simpa [hP] using p1 (Fin.last (N + 1))
  have hw' : vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R' := by
    rw [← eρ, hR']
    exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  have sc : ∀ t, Valued.v t ≤ Valued.v y → vec3 (0 : L) (0 : Fin N → L) t ∈ R' :=
    fun t ht => scale R' hy0 ht hy'
  obtain ⟨n1, n2⟩ := mid_ge (b := b) hf hm' (fun i => sc _ (hy1 i)) (fun i => sc _ (hy2 i))
  obtain ⟨f1, f2⟩ := hback R' hq' hw'
  have hone : Valued.v (1 : L) ≤ Valued.v y := by
    refine le_trans ?_ hya
    rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hD : Valued.v (ϖ ^ (-a)) ≤ Valued.v y := by
    refine le_trans ?_ hya
    rw [v_zpow hϖ, WithZero.exp_le_exp]
    omega
  apply le_antisymm
  · rw [hR]
    refine sup_le (rowLat_le.2 fun i => ?_) (rowLat_le.2 fun i => ?_)
    · rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
      · rw [e10]; exact f1
      · rw [e1m]; exact n1 j
      · rw [e1l]; exact sc 1 hone
    · rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
      · rw [eg0]; exact f2
      · rw [egm]; exact n2 j
      · rw [egl]; exact sc _ hD
  · rw [hR']
    refine sup_le (rowLat_le.2 fun i => ?_) ?_
    · rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
      · simpa [hP] using hqR
      · simpa [hP, hM] using m1 j
      · simpa [hP] using hyR
    · rw [Submodule.span_le, Set.singleton_subset_iff, eρ]
      exact hwR
end GlobalTheory.CompanionTheory.InertSpan

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLevi.leviExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:02:55.76962+00:00
-- url     : https://prove2.me/submissions/d95f7dab-df9e-4896-a45c-a2fff5f2f10f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LeviDecompositionExists
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_edge_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_edge_mid
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_edge_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_blkMat_gram
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
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


attribute [local simp] GlobalTheory.CompanionTheory.InertLevi.edge_zero
attribute [local simp] GlobalTheory.CompanionTheory.InertLevi.edge_mid
attribute [local simp] GlobalTheory.CompanionTheory.InertLevi.edge_last

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLevi
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertLevi
theorem _root_.solution : LeviExists := by
  intro L _ _ ϖ σ q N hU a g₀
  obtain ⟨_, _, hσϖ, hvϖ, _⟩ := hU
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    simp at hvϖ
  have hσx : σ (ϖ ^ a) = ϖ ^ a := by rw [map_zpow₀, hσϖ]
  have hσy : σ (ϖ ^ (-a)) = ϖ ^ (-a) := by rw [map_zpow₀, hσϖ]
  have hxy : σ (ϖ ^ a) * ϖ ^ (-a) = 1 := by rw [hσx, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  have hyx : σ (ϖ ^ (-a)) * ϖ ^ a = 1 := by rw [hσy, ← zpow_add₀ hϖ, neg_add_cancel, zpow_zero]
  have hA : cT σ (mat g₀) * antiJ L N * mat g₀ = antiJ L N := g₀.2
  have hJJ : antiJ L (N + 2) * antiJ L (N + 2) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, antiJ, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    have hi := i.isLt
    have hj := j.isLt
    rw [Finset.sum_eq_single i.rev]
    · rw [if_pos (by simp only [Fin.val_rev]; omega)]
      by_cases h : i = j
      · subst h
        rw [if_pos (by simp only [Fin.val_rev]; omega), if_pos rfl]
      · rw [if_neg (by simp only [Fin.val_rev]; intro h'; apply h; ext; omega), if_neg h]
    · intro l _ hl
      rw [if_neg]
      intro h'
      apply hl
      ext
      have := l.isLt
      simp only [Fin.val_rev]
      omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  set B := blkMat (ϖ ^ a) (ϖ ^ (-a)) (mat g₀) with hB
  have hG : cT σ B * antiJ L (N + 2) * B = antiJ L (N + 2) := blkMat_gram hxy hyx hA
  have hCB : antiJ L (N + 2) * cT σ B * antiJ L (N + 2) * B = 1 := by
    calc antiJ L (N + 2) * cT σ B * antiJ L (N + 2) * B
        = antiJ L (N + 2) * (cT σ B * antiJ L (N + 2) * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hG, hJJ]
  have hBC : B * (antiJ L (N + 2) * cT σ B * antiJ L (N + 2)) = 1 := mul_eq_one_comm.mp hCB
  let U : GL (Fin (N + 2)) L := ⟨B, antiJ L (N + 2) * cT σ B * antiJ L (N + 2), hBC, hCB⟩
  have hU : U ∈ GU σ (N + 2) := hG
  refine ⟨⟨U, hU⟩, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    show B i j = 0
    rcases idx_cases i with rfl | ⟨r, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨s, rfl⟩ | rfl <;>
      simp [hB, blkMat, blk_zero, blk_mid, blk_last] at hij ⊢
  · show B 0 0 = ϖ ^ a
    simp [hB, blkMat]
  · show B (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a)
    simp [hB, blkMat]
  · intro i j
    show B (mid i) (mid j) = mat g₀ i j
    simp [hB, blkMat]
end GlobalTheory.CompanionTheory.InertLevi

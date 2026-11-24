-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.small_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:04:41.349897+00:00
-- url     : https://prove2.me/submissions/443a0549-e442-4672-9868-e18c291b6ae6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
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



set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}
namespace GlobalTheory.CompanionTheory.InertCount
theorem _root_.solution {e f : ℕ} {C D : Matrix (Fin N) (Fin N) L}
    (hinv : ∀ u ∈ radQ σ N, ∀ k ∈ radQ σ N, k ∈ KU σ (N + 2) → Small ϖ e f C D u → Small ϖ e f C D (u * k))
    (v : radQ σ N) :
    Small ϖ e f C D ((QuotientGroup.mk v : RadQuot σ N).out : radQ σ N).1 ↔ Small ϖ e f C D v.1 := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((KU σ (N + 2)).subgroupOf (radQ σ N)) v
  rw [hh]
  have hk : ((h : radQ σ N) : GU σ (N + 2)) ∈ KU σ (N + 2) := Subgroup.mem_subgroupOf.mp h.2
  have hkr : ((h : radQ σ N) : GU σ (N + 2)) ∈ radQ σ N := (h : radQ σ N).2
  constructor
  · intro hs
    have h2 := hinv _ (v * h).2 _ (inv_mem hkr) (inv_mem hk) hs
    simpa using h2
  · intro hs
    exact hinv _ v.2 _ hkr hk hs
end GlobalTheory.CompanionTheory.InertCount

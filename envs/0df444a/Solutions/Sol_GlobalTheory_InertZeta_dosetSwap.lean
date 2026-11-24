-- Prove2me | solution 1 for GlobalTheory.InertZeta.dosetSwap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:09.296536+00:00
-- url     : https://prove2.me/submissions/1f17b142-06c2-4b5a-ae9f-3d4fe99966b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BiInvariantReplaceSameDoubleCosetSums
import Theorems.Thm_GlobalTheory_InertZeta_finite_dosetOf_fibre
import Theorems.Thm_GlobalTheory_InertZeta_biInv_of_dosetOf_eq
import Theorems.Thm_GlobalTheory_InertZeta_hAct_dosetInd_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_HasLen_unique
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
open GlobalTheory.InertZeta
noncomputable section
open GlobalTheory GlobalTheory.InertZeta
open Formalism.UG
namespace GlobalTheory.InertZeta
theorem _root_.solution : DosetSwap := by
  intro G _ K hK F w φ Z hF hw hH hZ
  haveI : ∀ S : Set G, Finite {x : G ⧸ K // dosetOf K x = S} := finite_dosetOf_fibre hK
  let e := Equiv.sigmaFiberEquiv (dosetOf K)
  let f₁ : G ⧸ K → ℂ := fun x => F x.out * φ x.out
  let f₂ : G ⧸ K → ℂ := fun x => F x.out * w x.out
  have hs : ∀ S : Set G, ∑' y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1 =
      ∑' y : {x : G ⧸ K // dosetOf K x = S}, f₁ y.1 := by
    intro S
    by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
    · obtain ⟨x₀, rfl⟩ := h
      have e₂ : ∀ y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, f₂ y.1 = F x₀.out * w y.1.out :=
        fun y => by simp only [f₂, biInv_of_dosetOf_eq hF y.2]
      have e₁ : ∀ y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, f₁ y.1 = F x₀.out * φ y.1.out :=
        fun y => by simp only [f₁, biInv_of_dosetOf_eq hF y.2]
      rw [tsum_congr e₂, tsum_congr e₁, tsum_mul_left, tsum_mul_left, ← hAct_dosetInd_eq hK,
        ← hAct_dosetInd_eq hK, hH]
    · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
      simp [tsum_empty]
  have hn : ∀ S : Set G, ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₂ y.1‖ ≤
      ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₁ y.1‖ := by
    intro S
    by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
    · obtain ⟨x₀, hx₀⟩ := h
      have c : ∀ y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1 = F x₀.out * w x₀.out := fun y => by
        have hy : dosetOf K y.1 = dosetOf K x₀ := y.2.trans hx₀.symm
        simp only [f₂, biInv_of_dosetOf_eq hF hy, biInv_of_dosetOf_eq hw hy]
      have key : ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₂ y.1‖ =
          ‖∑' y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1‖ := by
        rw [tsum_congr (fun y => congrArg norm (c y)), tsum_congr c, tsum_const, tsum_const, nsmul_eq_mul,
          nsmul_eq_mul]
        simp [norm_mul]
      rw [key, hs]
      exact norm_tsum_le_tsum_norm Summable.of_finite
    · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
      simp [tsum_empty]
  have h₁ : HasSum (f₁ ∘ e) Z := (e.hasSum_iff).2 hZ
  have h₁n : Summable fun p => ‖(f₁ ∘ e) p‖ := summable_norm_iff.2 h₁.summable
  have h₂n : Summable fun p => ‖(f₂ ∘ e) p‖ := by
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)] at h₁n ⊢
    refine ⟨fun S => Summable.of_finite, ?_⟩
    exact h₁n.2.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) hn
  have h₂ : Summable (f₂ ∘ e) := summable_norm_iff.1 h₂n
  have A := h₂.hasSum.sigma (fun S => (Summable.of_finite).hasSum)
  have B := h₁.sigma (fun S => (Summable.of_finite).hasSum)
  have hZ' : ∑' p, (f₂ ∘ e) p = Z := by
    refine A.unique ?_
    have : (fun S => ∑' c : {x : G ⧸ K // dosetOf K x = S}, (f₂ ∘ e) ⟨S, c⟩) =
        fun S => ∑' c : {x : G ⧸ K // dosetOf K x = S}, (f₁ ∘ e) ⟨S, c⟩ := funext hs
    rw [this]
    exact B
  have := h₂.hasSum
  rw [hZ', e.hasSum_iff] at this
  exact this
end GlobalTheory.InertZeta

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertGenFun.hasSum_of_counts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:15.518303+00:00
-- url     : https://prove2.me/submissions/76d07e31-b001-4c50-8d97-13bcc8b924f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_GeneratingFunctionIdentity
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertGenFun
namespace GlobalTheory.CompanionTheory.InertGenFun
theorem _root_.solution {ι : Type} (g : ι → ℕ) (A : ℕ → ℕ) (hA : ∀ j, A j ≠ 0)
    (hc : ∀ j, Nat.card {i // g i ≤ j} = A j) (X s : ℂ)
    (hT : HasSum (fun j : ℕ => (A j : ℂ) * X ^ j) s) :
    HasSum (fun i => X ^ g i) ((1 - X) * s) := by
  have hfinle : ∀ j, Finite {i // g i ≤ j} := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hc j]; exact hA j)
  have hfin : ∀ j, Finite {i // g i = j} := fun j =>
    Finite.of_injective (fun c : {i // g i = j} => (⟨c.1, c.2.le⟩ : {i // g i ≤ j}))
      (fun a b h => Subtype.ext (congrArg Subtype.val h :))
  have hcard : ∀ j, Nat.card {i // g i = j} + (if j = 0 then 0 else A (j - 1)) = A j := by
    intro j
    rcases j with _ | k
    · simp only [if_true, add_zero, ← hc 0]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun i => by omega))
    · have : ∀ i, g i ≤ k + 1 ↔ g i ≤ k ∨ g i = k + 1 := fun i => by omega
      have e := (Equiv.subtypeEquivRight this).trans
        (subtypeOrEquiv (fun i => g i ≤ k) (fun i => g i = k + 1)
          (Pi.disjoint_iff.2 fun i => Prop.disjoint_iff.2 (by omega)))
      rw [← hc (k + 1), Nat.card_congr e, Nat.card_sum, if_neg (Nat.succ_ne_zero k),
        Nat.add_sub_cancel, ← hc k, add_comm]
  have hfib : ∀ (j : ℕ) {M : Type} [AddCommMonoid M] [TopologicalSpace M] (F : ℕ → M),
      HasSum (fun c : {i // g i = j} => F (g c)) (Nat.card {i // g i = j} • F j) := by
    intro j M _ _ F
    have := hfin j
    have : Fintype {i // g i = j} := Fintype.ofFinite _
    convert hasSum_fintype (fun c : {i // g i = j} => F (g c)) using 1
    rw [Finset.sum_congr rfl (fun c _ => by rw [c.2]), Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hle : ∀ j, Nat.card {i // g i = j} ≤ A j := fun j => by
    have := hcard j
    omega
  have hnorm : Summable (fun j : ℕ => (A j : ℝ) * ‖X‖ ^ j) := by
    have := hT.summable.norm
    simpa [norm_mul, norm_pow] using this
  have hsum : Summable (fun i => X ^ g i) := by
    apply Summable.of_norm
    rw [← (Equiv.sigmaFiberEquiv g).summable_iff]
    show Summable fun p : (Σ j : ℕ, {i // g i = j}) => ‖X ^ g (p.2 : ι)‖
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun j => (hfib j (fun n => ‖X ^ n‖)).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun _ => norm_nonneg _) (fun j => ?_) hnorm
    have h1 := (hfib j (fun n => ‖X ^ n‖)).tsum_eq
    rw [h1, nsmul_eq_mul, norm_pow]
    gcongr
    exact_mod_cast hle j
  obtain ⟨t, ht⟩ := hsum
  have hsig := ((Equiv.sigmaFiberEquiv g).hasSum_iff.2 ht).sigma
    (fun j => hfib j (fun n => X ^ n))
  have hshift : HasSum (fun j : ℕ => ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) (s * X) := by
    have h0 : HasSum (fun n : ℕ => ((if n + 1 = 0 then 0 else A (n + 1 - 1) : ℕ) : ℂ) * X ^ (n + 1))
        (s * X) := by
      have hfun : (fun n : ℕ => ((if n + 1 = 0 then 0 else A (n + 1 - 1) : ℕ) : ℂ) * X ^ (n + 1)) =
          fun n => (A n : ℂ) * X ^ n * X := by
        funext n
        rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, pow_succ]
        ring
      rw [hfun]
      exact hT.mul_right X
    have h1 := (hasSum_nat_add_iff
      (f := fun j : ℕ => ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) 1).1 h0
    simp only [Finset.sum_range_one, ↓reduceIte, Nat.cast_zero, zero_mul, add_zero] at h1
    exact h1
  have hdiff := hT.sub hshift
  have heq : (fun j : ℕ => (A j : ℂ) * X ^ j - ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) =
      fun j => Nat.card {i // g i = j} • X ^ j := by
    funext j
    rw [nsmul_eq_mul, ← hcard j]
    push_cast
    ring
  rw [heq] at hdiff
  have := hsig.unique hdiff
  rw [this] at ht
  rwa [show (1 - X) * s = s - s * X by ring]
end GlobalTheory.CompanionTheory.InertGenFun

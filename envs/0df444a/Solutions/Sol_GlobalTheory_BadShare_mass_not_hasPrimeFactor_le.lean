-- Prove2me | solution 1 for GlobalTheory.BadShare.mass_not_hasPrimeFactor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:02:33.928355+00:00
-- url     : https://prove2.me/submissions/88aa0fcb-a6de-4df0-848a-810da7375460

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassDegTypeLeCycleTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardCycleTypeConsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralBinomLePowCardPrimesBetween
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassNoLargePrimeFactorLe
import Theorems.Thm_GlobalTheory_BadShare_card_perm_no_long_cycle
import Theorems.Thm_GlobalTheory_BadShare_card_perm_long_cycle
import Theorems.Thm_GlobalTheory_BadShare_inv_log_le_sum_inv_primes_between
import Theorems.Thm_GlobalTheory_T_mass_degType_le_card_cycleType_div


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 100000 ≤ N →
    (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ 1 - 1 / (10 * Real.log N) := by
  intro g _ N hN
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hSdef
  have hS : ∀ p ∈ S, N < 2 * p := fun p hp => (Finset.mem_filter.mp hp).2.2.1
  have hSN : ∀ p ∈ S, p ≤ N := fun p hp =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
  have hmono : (mass g N fun f => ¬ HasPrimeFactor g N f) ≤
      mass g N fun f => ∀ p ∈ S, p ∉ degType g f := by
    have hsub : (sqSet g N).filter (fun f => ¬ HasPrimeFactor g N f) ⊆
        (sqSet g N).filter (fun f => ∀ p ∈ S, p ∉ degType g f) := by
      intro f hf
      rw [Finset.mem_filter] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro p hp hpf
      apply hf.2
      unfold degType at hpf
      unfold HasPrimeFactor
      obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hpf
      obtain ⟨-, hpr, h2, h3⟩ := Finset.mem_filter.mp hp
      exact ⟨h, UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh,
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh, hpr, h2, h3⟩
    unfold mass
    convert Finset.sum_le_sum_of_subset_of_nonneg (f := fun f => ((torusCard g f : ℝ))⁻¹) hsub
      (fun f _ _ => by positivity)
    rfl
  have hT := GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun m : Multiset ℕ => ∀ p ∈ S, p ∉ m)
  have hcount := card_perm_no_long_cycle N S hS
  have hlong : ∀ p ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      p ∈ σ.partition.parts).card : ℝ) = N.factorial / p := by
    intro p hp
    have hp0 : 0 < p := by have := hS p hp; omega
    have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [eq_div_iff hp0']
    exact_mod_cast card_perm_long_cycle N p (hS p hp) (hSN p hp)
  have hfac : (N.factorial : ℝ) ≠ 0 := by positivity
  have hratio : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) / N.factorial = 1 - ∑ p ∈ S, (1 : ℝ) / p := by
    have hc : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) = N.factorial - ∑ p ∈ S, (N.factorial : ℝ) / p := by
      rw [← Finset.sum_congr rfl hlong]
      have := congrArg (fun n : ℕ => (n : ℝ)) hcount
      push_cast at this
      linarith
    rw [hc, sub_div, div_self hfac, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_right_comm, div_self hfac]
  have hprimes := inv_log_le_sum_inv_primes_between N hN
  calc _ ≤ _ := hmono
    _ ≤ _ := hT
    _ = 1 - ∑ p ∈ S, (1 : ℝ) / p := by convert hratio
    _ ≤ 1 - 1 / (10 * Real.log N) := by linarith
end GlobalTheory.BadShare

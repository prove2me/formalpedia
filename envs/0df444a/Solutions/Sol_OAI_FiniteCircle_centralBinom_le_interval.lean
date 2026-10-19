-- Prove2me | solution 1 for OAI.FiniteCircle.centralBinom_le_interval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:12:45.78409+00:00
-- url     : https://prove2.me/submissions/5ab7c3ac-2159-40ff-9664-4a509eedf256

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Primes.lean:L11-L78
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.centralBinom_le_interval. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes

-- ---- from OAI.Combinatorics.FiniteCircle.Primes ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem centralBinom_le_interval (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^Nat.sqrt (2*n) * 4^(2*n/3) * ∏ p ∈ primeInterval n, p := by
  classical
  let f : ℕ → ℕ := fun p => p^n.centralBinom.factorization p
  have hsmall : (∏ p ∈ Finset.range (2*n/3+1), f p) ≤ (2*n)^Nat.sqrt (2*n)*4^(2*n/3) := by
    let S := (Finset.range (2*n/3+1)).filter Nat.Prime
    have he : (∏ p ∈ S, f p) = ∏ p ∈ Finset.range (2*n/3+1), f p := by
      apply Finset.prod_filter_of_ne
      intro p _ hp
      contrapose hp
      simp only [f, Nat.factorization_eq_zero_of_not_prime n.centralBinom hp, pow_zero]
    rw [← he, ← Finset.prod_filter_mul_prod_filter_not S (fun p => p ≤ Nat.sqrt (2*n))]
    apply Nat.mul_le_mul
    · calc
        _ ≤ ∏ _p ∈ S.filter (fun p => p ≤ Nat.sqrt (2*n)), 2*n :=
          Finset.prod_le_prod' (fun p _ => Nat.pow_factorization_choose_le (by omega : 0<2*n))
        _ = (2*n)^(S.filter (fun p => p ≤ Nat.sqrt (2*n))).card := by simp
        _ ≤ _ := by
          apply Nat.pow_le_pow_right (by omega)
          have hs : S.filter (fun p => p ≤ Nat.sqrt (2*n)) ⊆ Finset.Icc 1 (Nat.sqrt (2*n)) := by
            intro p hp
            obtain ⟨hp,hq⟩ := Finset.mem_filter.mp hp
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.one_lt.le,hq⟩
          have hh := Finset.card_le_card hs
          simpa using hh
    · calc
        _ ≤ ∏ p ∈ S.filter (fun p => ¬p ≤ Nat.sqrt (2*n)), p := by
          apply Finset.prod_le_prod'
          intro p hp
          obtain ⟨hp,hq⟩ := Finset.mem_filter.mp hp
          dsimp [f]
          have hfac : n.centralBinom.factorization p ≤ 1 :=
            Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (lt_of_not_ge hq))
          exact (Nat.pow_le_pow_right (Finset.mem_filter.mp hp).2.one_lt.le hfac).trans_eq (pow_one p)
        _ ≤ primorial (2*n/3) := by
          apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
          intro p hp _
          exact (Finset.mem_filter.mp hp).2.one_lt.le
        _ ≤ _ := primorial_le_four_pow _
  have htail : (∏ p ∈ Finset.Ico (2*n/3+1) (2*n+1), f p) ≤ ∏ p ∈ primeInterval n, p := by
    have hs : primeInterval n ⊆ Finset.Ico (2*n/3+1) (2*n+1) := by
      intro p hp
      have h := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
      have hdiv : 2*n/3 ≤ n := (Nat.div_le_iff_le_mul_add_pred (by decide : 0<3)).mpr (by omega)
      exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
    have he : (∏ p ∈ primeInterval n, f p) = ∏ p ∈ Finset.Ico (2*n/3+1) (2*n+1), f p := by
      apply Finset.prod_subset hs
      intro p hp hnot
      dsimp [f]
      by_cases hprime : p.Prime
      · have hp' := Finset.mem_Ico.mp hp
        have hpn : p ≤ n := by
          by_contra h
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,by omega⟩,hprime⟩)
        rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn (by omega), pow_zero]
      · rw [Nat.factorization_eq_zero_of_not_prime _ hprime, pow_zero]
    rw [← he]
    apply Finset.prod_le_prod'
    intro p hp
    obtain ⟨hpi,hp⟩ := Finset.mem_filter.mp hp
    have hpn := (Finset.mem_Ioc.mp hpi).1
    have hfac : n.centralBinom.factorization p ≤ 1 := Nat.factorization_choose_le_one (by nlinarith)
    exact (Nat.pow_le_pow_right hp.one_lt.le hfac).trans_eq (pow_one p)
  calc
    _ = (∏ p ∈ Finset.range (2*n/3+1), f p) * ∏ p ∈ Finset.Ico (2*n/3+1) (2*n+1), f p := by
      rw [Finset.prod_range_mul_prod_Ico _ (by omega)]
      exact (Nat.prod_pow_factorization_centralBinom n).symm
    _ ≤ _ := Nat.mul_le_mul hsmall htail

namespace StandingPrimes
variable {h : ℕ} {p : ℕ → ℕ → ℕ} (hp : StandingPrimes h p)
include hp

end StandingPrimes

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.centralBinom_le_interval := @_root_.OAI.FiniteCircle.centralBinom_le_interval

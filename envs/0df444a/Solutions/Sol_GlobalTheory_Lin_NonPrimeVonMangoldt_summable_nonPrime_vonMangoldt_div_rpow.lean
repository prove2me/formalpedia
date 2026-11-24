-- Prove2me | solution 1 for GlobalTheory.Lin.NonPrimeVonMangoldt.summable_nonPrime_vonMangoldt_div_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:53.854038+00:00
-- url     : https://prove2.me/submissions/ecb22c42-776d-4b43-8ed4-924608b53270

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
namespace GlobalTheory.Lin.NonPrimeVonMangoldt
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma log_div_pow_add_two_rpow_three_quarters_le (P : ℝ) (hP : 2 ≤ P) (k : ℕ) :
    Real.log P / (P ^ (k + 2)) ^ (3 / 4 : ℝ) ≤
      4 * P ^ (-(5 / 4 : ℝ)) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
  have hP0 : 0 < P := by linarith
  have hA : 0 < P ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hP0 _
  have hC : 0 < ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k := by positivity
  have hCB : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k ≤ (P ^ (3 / 4 : ℝ)) ^ k :=
    pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hP (by norm_num)) k
  have hsplit : (P ^ (k + 2)) ^ (3 / 4 : ℝ) = P ^ (3 / 2 : ℝ) * (P ^ (3 / 4 : ℝ)) ^ k := by
    rw [← Real.rpow_pow_comm hP0.le, pow_add, mul_comm, ← Real.rpow_natCast (P ^ (3 / 4 : ℝ)) 2,
      ← Real.rpow_mul hP0.le]
    norm_num
  have hlog : Real.log P ≤ 4 * P ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div hP0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith [show P ^ (1 / 4 : ℝ) / (1 / 4) = 4 * P ^ (1 / 4 : ℝ) by ring]
  have hrhs : 4 * P ^ (-(5 / 4 : ℝ)) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k
      = 4 * P ^ (1 / 4 : ℝ) / (P ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k) := by
    rw [show (-(5 / 4 : ℝ)) = 1 / 4 - 3 / 2 by norm_num, Real.rpow_sub hP0,
      Real.rpow_neg (by norm_num), inv_pow]
    field_simp
  rw [hsplit, hrhs]
  exact div_le_div₀ (by positivity) hlog (mul_pos hA hC) (mul_le_mul_of_nonneg_left hCB hA.le)
end GlobalTheory.Lin.NonPrimeVonMangoldt
end

set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.NonPrimeVonMangoldt
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open scoped Classical
namespace GlobalTheory.Lin.NonPrimeVonMangoldt
namespace _root_.GlobalTheory.Lin.NonPrimeVonMangoldt
theorem _root_.solution :
    Summable (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  set F := (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) with hF
  set g : Nat.Primes × ℕ → ℕ := fun pk => (pk.1 : ℕ) ^ (pk.2 + 2) with hg_def
  have hg : Function.Injective g := by
    rintro ⟨p, k⟩ ⟨q, m⟩ h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj p.2 q.2 (h : (p : ℕ) ^ ((k + 1) + 1) = (q : ℕ) ^ ((m + 1) + 1))
    exact Prod.ext (Subtype.ext h1) (by simpa using h2)
  have hrange : ∀ n ∉ Set.range g, F n = 0 := by
    intro n hn
    by_cases hp : n.Prime
    · simp [hF, hp]
    by_cases hΛ : Λ n = 0
    · simp [hF, hΛ]
    exfalso
    apply hn
    obtain ⟨p, k, hp', hk, rfl⟩ := (isPrimePow_nat_iff _).1 (vonMangoldt_ne_zero_iff.1 hΛ)
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : k = 1 := by omega
      subst this
      exact hp (by simpa using hp')
    exact ⟨(⟨p, hp'⟩, k - 2), by simp only [hg_def]; congr 1; omega⟩
  rw [← hg.summable_iff hrange]
  have hmaj : Summable (fun pk : Nat.Primes × ℕ =>
      (4 * ((pk.1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ pk.2) := by
    refine Summable.mul_of_nonneg (f := fun p : Nat.Primes => 4 * ((p : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)))
      (g := fun k : ℕ => ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k) ?_ ?_ ?_ ?_
    · exact (Nat.Primes.summable_rpow.2 (by norm_num)).mul_left 4
    · exact summable_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
    · intro p; simp only [Pi.zero_apply]; positivity
    · intro k; simp only [Pi.zero_apply]; positivity
  refine Summable.of_nonneg_of_le (fun pk => ?_) (fun pk => ?_) hmaj
  · simp only [Function.comp_apply, hF]
    refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    split_ifs
    · exact le_rfl
    · exact vonMangoldt_nonneg
  · obtain ⟨⟨p, hp⟩, k⟩ := pk
    have hnp : ¬ (p ^ (k + 2)).Prime := Nat.Prime.not_prime_pow (by omega)
    simp only [Function.comp_apply, hF, hg_def, if_neg hnp]
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp, Nat.cast_pow]
    exact log_div_pow_add_two_rpow_three_quarters_le _ (by exact_mod_cast hp.two_le) k
end _root_.GlobalTheory.Lin.NonPrimeVonMangoldt
end GlobalTheory.Lin.NonPrimeVonMangoldt

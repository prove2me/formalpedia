-- Prove2me | solution 1 for JRPHard.Aperiodic.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T10:55:40.347604+00:00
-- url     : https://prove2.me/submissions/e3e00088-7e1d-4197-bb85-1cc03a5dd480

import Definitions.Def_JRPHard_Aperiodic_Setting
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Theorems.Thm_JRPHard_Aperiodic_item2_pinned
import Theorems.Thm_JRPHard_Aperiodic_coprime_lower_bound
import Theorems.Thm_JRPHard_Aperiodic_multiple_of_M
import Theorems.Thm_JRPHard_Aperiodic_exists_good_multiple
import Theorems.Thm_JRPHard_Aperiodic_reduction_to_2
open JRPHard.Aperiodic


private lemma reduced_ge_four (M q : ℕ) (h1 : 1 < M) (hq : 0 < q) :
    4 * (q : ℝ) ≤ jrpRed M q := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hden : (q : ℝ) ≤ (Nat.lcm q M : ℝ) := by
    exact_mod_cast Nat.le_lcm_left q (show 0 < M by omega)
  have hinv : (1 : ℝ) / (Nat.lcm q M : ℝ) ≤ 1 / q :=
    div_le_div_of_nonneg_left (by norm_num) hqR hden
  have hnonneg := mul_nonneg
    (mul_nonneg (show 0 ≤ (M : ℝ) by positivity) (sub_nonneg.mpr hMR))
    (sub_nonneg.mpr hinv)
  unfold jrpRed
  exact le_add_of_nonneg_left hnonneg

private lemma reduced_min_exists (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    ∃ q : ℕ, 0 < q ∧ ∀ a : ℕ, 0 < a → jrpRed M q ≤ jrpRed M a := by
  classical
  let B := M ^ 2 + 4
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hmem : 1 ∈ Finset.Icc 1 B := Finset.mem_Icc.mpr ⟨le_rfl, hB⟩
  obtain ⟨q, hq, hmin⟩ := (Finset.Icc 1 B).exists_min_image (jrpRed M) ⟨1, hmem⟩
  have hqpos : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
  have hF1 : jrpRed M 1 ≤ (B : ℝ) := by
    rw [(JRPHard.Aperiodic.coprime_lower_bound M hodd h1 hcomp 1 (by decide)
      (Nat.coprime_one_left M)).1]
    dsimp [B]
    push_cast
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    nlinarith
  refine ⟨q, hqpos, ?_⟩
  intro a ha
  by_cases hab : a ≤ B
  · exact hmin a (Finset.mem_Icc.mpr ⟨ha, hab⟩)
  · have hlarge : (B : ℝ) < a := by exact_mod_cast (Nat.lt_of_not_ge hab)
    have hlow := reduced_ge_four M a h1 ha
    have hqa := hmin 1 hmem
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha
    linarith

theorem solution (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    (coefK0 M ≤ coefK1 M ∧ coefK0 M ≤ coefK2 M ∧
      coefK0 M ≤ M ^ 5 ∧ coefK1 M ≤ M ^ 5 ∧ coefK2 M ≤ M ^ 5 ∧ coefH1 ≤ M ^ 5 ∧
      coefH2 M ≤ M ^ 5) ∧
    (∃ q₁ q₂ : ℕ, IsOptimal (lemma1Cost M) q₁ q₂) ∧
    ∀ q₁ q₂ : ℕ, IsOptimal (lemma1Cost M) q₁ q₂ →
      q₂ = M ∧ 1 < Nat.gcd q₁ M ∧ Nat.gcd q₁ M < M := by
  have hM : 2 ≤ M := by omega
  have hMpos : 0 < M := by omega
  have hpow (i j : ℕ) (hij : i ≤ j) : M ^ i ≤ M ^ j :=
    pow_le_pow_right₀ (show 1 ≤ M by omega) hij
  have h13 : M ≤ M ^ 3 := by simpa using hpow 1 3 (by decide)
  have h12 : M ≤ M ^ 2 := by simpa using hpow 1 2 (by decide)
  have h25 : M ^ 2 ≤ M ^ 5 := hpow 2 5 (by decide)
  have h35 : M ^ 3 ≤ M ^ 5 := hpow 3 5 (by decide)
  have hK02 : coefK0 M ≤ coefK2 M :=
    Nat.mul_le_mul h13 (Nat.sub_le_sub_right h12 1)
  have hK05 : coefK0 M ≤ M ^ 5 := by
    calc
      coefK0 M = M * (M - 1) := rfl
      _ ≤ M * M := Nat.mul_le_mul_left M (Nat.sub_le M 1)
      _ = M ^ 2 := by ring
      _ ≤ M ^ 5 := h25
  have hK25 : coefK2 M ≤ M ^ 5 := by
    calc
      coefK2 M = M ^ 3 * (M ^ 2 - 1) := rfl
      _ ≤ M ^ 3 * M ^ 2 := Nat.mul_le_mul_left (M ^ 3) (Nat.sub_le (M ^ 2) 1)
      _ = M ^ 5 := by ring
  have hH15 : coefH1 ≤ M ^ 5 := by
    apply le_trans (show 4 ≤ M ^ 2 by nlinarith) h25
  have hH25 : coefH2 M ≤ M ^ 5 := by
    calc
      coefH2 M = M * (M ^ 2 - 1) := rfl
      _ ≤ M * M ^ 2 := Nat.mul_le_mul_left M (Nat.sub_le (M ^ 2) 1)
      _ = M ^ 3 := by ring
      _ ≤ M ^ 5 := h35
  have hpin := JRPHard.Aperiodic.item2_pinned M hodd h1 hcomp
  have hreduce (q : ℕ) (hq : 0 < q) :
      lemma1Cost M q M = eoq2 M M + jrpRed M q :=
    JRPHard.Aperiodic.reduction_to_2 M hodd h1 hcomp q hq
  have hexists : ∃ q₁ q₂ : ℕ, IsOptimal (lemma1Cost M) q₁ q₂ := by
    obtain ⟨q, hq, hmin⟩ := reduced_min_exists M hodd h1 hcomp
    refine ⟨q, M, hq, hMpos, ?_⟩
    intro a b ha hb
    by_cases hbM : b = M
    · subst b
      rw [hreduce q hq, hreduce a ha]
      linarith [hmin a ha]
    · have hcmp : lemma1Cost M q M ≤ lemma1Cost M 1 M := by
        rw [hreduce q hq, hreduce 1 (by decide)]
        linarith [hmin 1 (by decide)]
      exact hcmp.trans (hpin.2.le.trans (hpin.1 a b ha hb hbM).2)
  refine ⟨⟨le_rfl, hK02, hK05, hK05, hK25, hH15, hH25⟩, hexists, ?_⟩
  rintro q₁ q₂ ⟨hq₁, hq₂, hopt⟩
  have hq₂M : q₂ = M := by
    by_contra hne
    have hbad := (hpin.1 q₁ q₂ hq₁ hq₂ hne).2
    have hcmp := hopt 1 M (by decide) hMpos
    linarith [hpin.2]
  obtain ⟨p, hpM, hp2, hplt⟩ := (Nat.not_prime_iff_exists_dvd_lt hM).mp hcomp
  have hpne : p ≠ 2 := by
    intro heq
    exact hodd.not_two_dvd_nat (by simpa [heq] using hpM)
  have hp3 : 3 ≤ p := by omega
  obtain ⟨q, hq, hpq, hqlo, hqhi, hgood⟩ :=
    JRPHard.Aperiodic.exists_good_multiple M hodd h1 hcomp p hpM hp3 hplt
  have hcompare : jrpRed M q₁ ≤ jrpRed M q := by
    have hh := hopt q M hq hMpos
    rw [hq₂M, hreduce q₁ hq₁, hreduce q hq] at hh
    linarith
  have hgp : 0 < Nat.gcd q₁ M := Nat.gcd_pos_of_pos_left M hq₁
  have hgne : Nat.gcd q₁ M ≠ 1 := by
    intro heq
    have hcop : Nat.Coprime q₁ M := Nat.coprime_iff_gcd_eq_one.mpr heq
    have hlower := (JRPHard.Aperiodic.coprime_lower_bound M hodd h1 hcomp q₁ hq₁ hcop).2
    linarith
  have hglt : Nat.gcd q₁ M < M := by
    have hle := Nat.le_of_dvd hMpos (Nat.gcd_dvd_right q₁ M)
    by_contra hnot
    have heq : Nat.gcd q₁ M = M := by omega
    have hMdvd : M ∣ q₁ := by rw [← heq]; exact Nat.gcd_dvd_left q₁ M
    have hlower := ((JRPHard.Aperiodic.multiple_of_M M hodd h1 hcomp).1 q₁ hq₁ hMdvd).2
    linarith
  exact ⟨hq₂M, by omega, hglt⟩


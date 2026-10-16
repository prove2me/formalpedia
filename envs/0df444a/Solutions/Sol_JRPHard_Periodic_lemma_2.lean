-- Prove2me | solution 1 for JRPHard.Periodic.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T07:41:54.659983+00:00
-- url     : https://prove2.me/submissions/af0462fd-f3ff-470f-955f-7489ac46af8b

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting
open JRPHard.Periodic
set_option autoImplicit false

namespace JRPResearch

theorem item2_gap (M q : ℕ) (hM : 0 < M) (hq : 0 < q) (hne : q ≠ M) :
    2 * (M : ℝ)^2 * (M + 1) + M ≤ JRPHard.Periodic.eoq2 M q := by
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hg : (q : ℝ) ≤ (M + 1) * ((q : ℝ) - M)^2 := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hh : (q : ℝ) + 1 ≤ M := by exact_mod_cast h
      have hs : (1 : ℝ) ≤ ((q : ℝ) - M)^2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (M : ℝ) + 1 by positivity)
      nlinarith
    · have hh : (M : ℝ) + 1 ≤ q := by exact_mod_cast h
      have hd : 0 ≤ (q : ℝ) - M := by linarith
      have hm := mul_nonneg (show 0 ≤ (q : ℝ) - M - 1 by linarith)
        (show 0 ≤ ((M : ℝ) + 1) * ((q : ℝ) - M) + M by positivity)
      nlinarith
  unfold JRPHard.Periodic.eoq2 JRPHard.Aperiodic.eoq JRPHard.Periodic.coefK2 JRPHard.Periodic.coefH2
  push_cast
  apply (mul_le_mul_iff_left₀ hqR).mp
  simp only [add_mul, div_mul_cancel₀ _ (ne_of_gt hqR)]
  have hm := mul_le_mul_of_nonneg_left hg hMR.le
  nlinarith

end JRPResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Schulz and Telha, arXiv:2007.09045v1, proof of Lemma 2.
-- Includes the full integer EOQ gap proof; platform imports do not export helpers.
theorem JRPResearch.pinned (M : ℕ) (hM : 2 ≤ M) :
    (∀ q₁ q₂ : ℕ, 0 < q₁ → 0 < q₂ → q₂ ≠ M →
      (M : ℝ) + eoq2 M M + 1 < lemma2Cost M q₁ q₂) ∧
    lemma2Cost M M M = (M : ℝ) + eoq2 M M + 1 := by
  have hMp : 0 < M := by omega
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hMp
  have he0 : eoq2 M M = 2 * (M : ℝ)^2 * (M + 1) := by
    unfold eoq2 JRPHard.Aperiodic.eoq coefK2 coefH2
    push_cast
    field_simp
    ring
  constructor
  · intro q₁ q₂ hq₁ hq₂ hne
    have he := JRPResearch.item2_gap M q₂ hMp hq₂ hne
    rw [← he0] at he
    have hg : 0 < (Nat.gcd q₁ q₂ : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left q₂ hq₁
    have hq : (1 : ℝ) ≤ q₁ := by exact_mod_cast hq₁
    have hf : 0 < (M : ℝ) / (Nat.gcd q₁ q₂ : ℝ) := div_pos hMR hg
    simp only [lemma2Cost, periodicCost, coefK0, coefK1, coefH1, Nat.cast_zero, Nat.cast_one]
    change (M : ℝ) + eoq2 M M + 1 <
      JRPHard.Aperiodic.eoq 0 1 q₁ + eoq2 M q₂ + (M : ℝ) / (Nat.gcd q₁ q₂ : ℝ)
    simp only [JRPHard.Aperiodic.eoq, zero_div, one_mul, zero_add]
    linarith
  · simp only [lemma2Cost, periodicCost, coefK0, coefK1, coefH1, Nat.cast_zero, Nat.cast_one]
    change JRPHard.Aperiodic.eoq 0 1 M + eoq2 M M + (M : ℝ) / (Nat.gcd M M : ℝ) = _
    simp only [JRPHard.Aperiodic.eoq, zero_div, one_mul, zero_add, Nat.gcd_self,
      div_self (ne_of_gt hMR)]

namespace JRPResearch

theorem cost_decompose (M q : ℕ) :
    lemma2Cost M q M = obj4 M q + eoq2 M M := by
  simp only [lemma2Cost, periodicCost, coefK0, coefK1, coefH1, Nat.cast_zero,
    Nat.cast_one, JRPHard.Aperiodic.eoq, zero_div, one_mul, zero_add, obj4, eoq2]
  ring

theorem optimal_exists (M : ℕ) (hM : 2 ≤ M) :
    ∃ q₁ q₂ : ℕ, JRPHard.Aperiodic.IsOptimal (lemma2Cost M) q₁ q₂ := by
  classical
  have hp : 0 < M := by omega
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hp
  have hbase : obj4 M M = M + 1 := by
    simp [obj4, Nat.gcd_self, div_self (ne_of_gt hMR), add_comm]
  have hMmem : M ∈ Finset.Icc 1 (M+1) := by simp; omega
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 (M+1)) (obj4 M) ⟨M,hMmem⟩
  have hqp : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
  have hle : obj4 M q ≤ (M : ℝ) + 1 := by simpa only [hbase] using hmin M hMmem
  refine ⟨q, M, hqp, hp, ?_⟩
  intro a b ha hb
  by_cases he : b = M
  · subst b
    rw [cost_decompose, cost_decompose]
    apply (add_le_add_iff_right (eoq2 M M)).2
    by_cases hamem : a ≤ M+1
    · exact hmin a (Finset.mem_Icc.mpr ⟨ha,hamem⟩)
    · have har : (M : ℝ)+1 < a := by exact_mod_cast (show M+1 < a by omega)
      have hn : 0 ≤ (M : ℝ) / (Nat.gcd a M : ℝ) := by positivity
      dsimp [obj4] at hle ⊢
      linarith
  · have hh := (pinned M hM).1 a b ha hb he
    rw [cost_decompose]
    linarith

end JRPResearch


theorem JRPResearch.small_divisor (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    ∃ p : ℕ, p ∣ M ∧ 3 ≤ p ∧ 3 * p ≤ M := by
  have hp := Nat.minFac_prime (ne_of_gt h1)
  have hd := Nat.minFac_dvd M
  have hp3 : 3 ≤ M.minFac := by
    have hp2 := hp.two_le
    have hne : M.minFac ≠ 2 := by
      intro he
      rw [he] at hd
      exact hodd.not_two_dvd_nat hd
    omega
  refine ⟨M.minFac, hd, hp3, ?_⟩
  have hs := Nat.minFac_sq_le_self (by omega : 0 < M) hcomp
  nlinarith

theorem JRPResearch.small_value (M p : ℕ) (hpM : p ∣ M) (hp3 : 3 ≤ p) (hple : 3 * p ≤ M) :
    obj4 M p ≤ 2 * (M : ℝ) / 3 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpleR : 3 * (p : ℝ) ≤ M := by exact_mod_cast hple
  have hd : (M : ℝ) / p ≤ (M : ℝ) / 3 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hpR
  rw [obj4, Nat.gcd_eq_left hpM]
  linarith

theorem JRPResearch.trivial_gcd (M q : ℕ) (hq : 0 < q)
    (hg : Nat.gcd q M = 1 ∨ Nat.gcd q M = M) :
    (M : ℝ) ≤ obj4 M q := by
  rcases hg with hg | hg
  · simp only [obj4, hg, Nat.cast_one, div_one]
    linarith [Nat.cast_nonneg (α := ℝ) q]
  · have hmq : (M : ℝ) ≤ q := by
      have hh := Nat.gcd_le_left M hq
      rw [hg] at hh
      exact_mod_cast hh
    rw [obj4, hg]
    have hh : 0 ≤ (M : ℝ) / M := by positivity
    linarith

-- Full existing Lemma 2; original mathematical authors Schulz and Telha.
theorem solution (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    (0 < coefK0 M ∧
      coefK0 M ≤ M ^ 5 ∧ coefK1 ≤ M ^ 5 ∧ coefK2 M ≤ M ^ 5 ∧ coefH1 ≤ M ^ 5 ∧
      coefH2 M ≤ M ^ 5) ∧
    (∃ q₁ q₂ : ℕ, JRPHard.Aperiodic.IsOptimal (lemma2Cost M) q₁ q₂) ∧
    ∀ q₁ q₂ : ℕ, JRPHard.Aperiodic.IsOptimal (lemma2Cost M) q₁ q₂ →
      q₂ = M ∧ 1 < Nat.gcd q₁ M ∧ Nat.gcd q₁ M < M := by
  have hM : 2 ≤ M := by omega
  have hp : 0 < M := by omega
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hp
  have h13 : M ≤ M^3 := by simpa using (pow_le_pow_right' (by omega : 1 ≤ M) (by decide : 1 ≤ 3))
  have h35 : M^3 ≤ M^5 := pow_le_pow_right' (by omega) (by decide)
  have hplus : M+1 ≤ M^2 := by nlinarith
  have hk2 : coefK2 M ≤ M^5 := by
    unfold coefK2
    calc
      M^3*(M+1) ≤ M^3*M^2 := Nat.mul_le_mul_left _ hplus
      _ = M^5 := by ring
  have hh2 : coefH2 M ≤ M^5 := by
    unfold coefH2
    exact (Nat.mul_le_mul_left M hplus).trans (by simpa [pow_succ, mul_assoc] using h35)
  refine ⟨?_, JRPResearch.optimal_exists M hM, ?_⟩
  · refine ⟨hp, h13.trans h35, ?_, hk2, ?_, hh2⟩
    · exact Nat.zero_le _
    · change 1 ≤ M^5
      exact Nat.one_le_pow _ _ hp
  · intro q₁ q₂ hopt
    have hpin := JRPResearch.pinned M hM
    have hq2 : q₂ = M := by
      by_contra hn
      have hlt := hpin.1 q₁ q₂ hopt.1 hopt.2.1 hn
      have hle := hopt.2.2 M M hp hp
      rw [hpin.2] at hle
      linarith
    subst q₂
    obtain ⟨p,hpd,hp3,hpb⟩ := JRPResearch.small_divisor M hodd h1 hcomp
    have hsmall := JRPResearch.small_value M p hpd hp3 hpb
    have hle := hopt.2.2 p M (by omega) hp
    rw [JRPResearch.cost_decompose, JRPResearch.cost_decompose] at hle
    have hobj : obj4 M q₁ < M := by linarith
    have hgpos := Nat.gcd_pos_of_pos_left M hopt.1
    have hgle := Nat.gcd_le_right q₁ hp
    have hgne1 : Nat.gcd q₁ M ≠ 1 := by
      intro he
      have hh := JRPResearch.trivial_gcd M q₁ hopt.1 (Or.inl he)
      linarith
    have hgneM : Nat.gcd q₁ M ≠ M := by
      intro he
      have hh := JRPResearch.trivial_gcd M q₁ hopt.1 (Or.inr he)
      linarith
    exact ⟨rfl, by omega, by omega⟩

#print axioms solution

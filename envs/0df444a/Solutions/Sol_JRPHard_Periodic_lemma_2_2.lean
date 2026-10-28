-- Prove2me | solution 2 for JRPHard.Periodic.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:33.368424+00:00
-- url     : https://prove2.me/submissions/1c29809f-9dad-47bc-95a3-f34ae710f20c

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting
import Theorems.Thm_JRPHard_Periodic_item2_pinned
import Theorems.Thm_JRPHard_Periodic_exists_small_divisor
import Theorems.Thm_JRPHard_Periodic_trivial_gcd_value

-- carved verbatim out of submission af0462fd-f3ff-470f-955f-7489ac46af8b, lines 140-193

section
open JRPHard.Periodic
set_option autoImplicit false

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
  · have hh := (JRPHard.Periodic.item2_pinned M hM).1 a b ha hb he
    rw [cost_decompose]
    linarith

theorem JRPResearch.small_value (M p : ℕ) (hpM : p ∣ M) (hp3 : 3 ≤ p) (hple : 3 * p ≤ M) :
    obj4 M p ≤ 2 * (M : ℝ) / 3 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpleR : 3 * (p : ℝ) ≤ M := by exact_mod_cast hple
  have hd : (M : ℝ) / p ≤ (M : ℝ) / 3 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hpR
  rw [obj4, Nat.gcd_eq_left hpM]
  linarith

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
  refine ⟨?_, optimal_exists M hM, ?_⟩
  · refine ⟨hp, h13.trans h35, ?_, hk2, ?_, hh2⟩
    · exact Nat.zero_le _
    · change 1 ≤ M^5
      exact Nat.one_le_pow _ _ hp
  · intro q₁ q₂ hopt
    have hpin := JRPHard.Periodic.item2_pinned M hM
    have hq2 : q₂ = M := by
      by_contra hn
      have hlt := hpin.1 q₁ q₂ hopt.1 hopt.2.1 hn
      have hle := hopt.2.2 M M hp hp
      rw [hpin.2] at hle
      linarith
    subst q₂
    obtain ⟨p,hpd,hp3,hpb⟩ := JRPHard.Periodic.exists_small_divisor M hodd h1 hcomp
    have hsmall := JRPResearch.small_value M p hpd hp3 hpb
    have hle := hopt.2.2 p M (by omega) hp
    rw [cost_decompose, cost_decompose] at hle
    have hobj : obj4 M q₁ < M := by linarith
    have hgpos := Nat.gcd_pos_of_pos_left M hopt.1
    have hgle := Nat.gcd_le_right q₁ hp
    have hgne1 : Nat.gcd q₁ M ≠ 1 := by
      intro he
      have hh := JRPHard.Periodic.trivial_gcd_value M q₁ hopt.1 (Or.inl he)
      linarith
    have hgneM : Nat.gcd q₁ M ≠ M := by
      intro he
      have hh := JRPHard.Periodic.trivial_gcd_value M q₁ hopt.1 (Or.inr he)
      linarith
    exact ⟨rfl, by omega, by omega⟩

end

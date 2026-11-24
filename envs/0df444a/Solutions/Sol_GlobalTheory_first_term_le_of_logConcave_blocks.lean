-- Prove2me | solution 1 for GlobalTheory.first_term_le_of_logConcave_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:31:26.159802+00:00
-- url     : https://prove2.me/submissions/410cfcf2-dc0a-4b85-811c-adf807313f3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogConcaveMultiplicativeGrowthBound
import Theorems.Thm_GlobalTheory_nat_le_of_forall_pow_le_mul_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (g : ℕ → ℕ) (e C B : ℕ), 1 ≤ e → g 0 = 1 → (∀ n, 0 < g n) →
    (∀ k, g (k + 2) * g k ≤ g (k + 1) ^ 2) → (∀ j, g (e * (j + 1)) = g (e * j) * g e) →
    (∀ n, g n ≤ C * B ^ n) → g 1 ≤ B := by
  intro g e C B he h0 hpos hlc hblk hgr
  set r : ℕ → ℝ := fun k => (g (k+1) : ℝ) / g k with hr
  have gpos : ∀ n, (0:ℝ) < g n := fun n => by exact_mod_cast hpos n
  have rpos : ∀ k, 0 < r k := fun k => div_pos (gpos _) (gpos _)
  have rstep : ∀ k, r (k+1) ≤ r k := by
    intro k
    simp only [hr]
    rw [div_le_div_iff₀ (gpos _) (gpos _)]
    have h1 : ((g (k+2) : ℝ)) * g k ≤ (g (k+1):ℝ)^2 := by exact_mod_cast hlc k
    have h2 : k + 1 + 1 = k + 2 := by ring
    rw [h2]; nlinarith [h1]
  have ranti : Antitone r := antitone_nat_of_succ_le rstep
  have gmul : ∀ a n, (g (a + n) : ℝ) = g a * ∏ i ∈ Finset.range n, r (a + i) := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
      simp only [hr]
      rw [← add_assoc]
      field_simp [(gpos (a+n)).ne']
  have g0 : (g 0 : ℝ) = 1 := by exact_mod_cast h0
  have ge : (g e : ℝ) = ∏ i ∈ Finset.range e, r i := by
    have := gmul 0 e; simpa [g0] using this
  have g2e : (g (e + e) : ℝ) = g e * g e := by
    have := hblk 1
    have h2 : e * (1+1) = e + e := by ring
    rw [h2, mul_one] at this
    exact_mod_cast this
  have hprodeq : ∏ i ∈ Finset.range e, r (e + i) = ∏ i ∈ Finset.range e, r i := by
    have := gmul e e
    rw [g2e] at this
    have hne : (g e : ℝ) ≠ 0 := (gpos e).ne'
    rw [← ge]
    exact (mul_left_cancel₀ hne this).symm
  have hre : r e = r 0 := by
    apply le_antisymm (ranti (Nat.zero_le e))
    by_contra hlt
    push_neg at hlt
    have : ∏ i ∈ Finset.range e, r (e + i) < ∏ i ∈ Finset.range e, r i := by
      apply Finset.prod_lt_prod
      · intro i _; exact rpos _
      · intro i _; exact ranti (by omega)
      · exact ⟨0, Finset.mem_range.2 (by omega), by simpa using hlt⟩
    rw [hprodeq] at this
    exact lt_irrefl _ this
  have hconst : ∀ i ∈ Finset.range e, r i = r 0 := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    apply le_antisymm (ranti (Nat.zero_le i))
    rw [← hre]; exact ranti (by omega)
  have r0 : r 0 = g 1 := by simp [hr, g0]
  have geR : (g e : ℝ) = (g 1 : ℝ) ^ e := by
    rw [ge, Finset.prod_congr rfl hconst, Finset.prod_const, Finset.card_range, r0]
  have geN : g e = g 1 ^ e := by exact_mod_cast geR
  have gej : ∀ j, g (e * j) = (g 1 ^ e) ^ j := by
    intro j
    induction j with
    | zero => simp [h0]
    | succ j ih => rw [hblk, ih, geN, pow_succ]
  have hpow : g 1 ^ e ≤ B ^ e := by
    apply nat_le_of_forall_pow_le_mul_pow _ _ C
    intro j
    rw [← gej, ← pow_mul]
    exact hgr _
  exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by omega : e ≠ 0)).1 hpow
end GlobalTheory

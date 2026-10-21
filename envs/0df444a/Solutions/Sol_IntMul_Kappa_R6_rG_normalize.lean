-- Prove2me | solution 1 for IntMul.Kappa.R6.rG_normalize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-20T23:14:26.316095+00:00
-- url     : https://prove2.me/submissions/b23cbd4f-abdb-4e86-b823-f564fd4259a8

import Definitions.Def_IntMul_Kappa_R6_Defs1
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# Normalizing a crude-guard assembly to a round-six parameter record, for any networks

xuanji's `r6_normalize` with Jain's round-six histograms replaced by hypotheses: the two moment
exponents `1 - ab` and `1 - ac` are positive (for concrete data this follows from a large first
histogram entry), and the guard uses an arbitrary complex width `mc` and rank sum `sc`.
-/

namespace IntMul.Kappa.R6

namespace Prm

theorem lt_gapG_iff (P : Prm) (κ : ℝ) :
    κ < P.gap ↔ κ < 1 - P.ε ∧ κ < P.ε * (1 - P.lamp) ∧ κ < 1 - P.ε - P.poly ∧
      κ < P.ε ∧ κ < max P.ε (1 - P.ε) * (1 - P.τ) := by
  unfold gap; simp only [lt_min_iff]; tauto

end Prm

open IntMul.Kappa

/-- `(1+y) (10⁻²²/y) = 10⁻²²/y + 10⁻²²` for `y ≠ 0`. -/
theorem polyG_eq (y : ℝ) (hy : y ≠ 0) :
    (1 + y) * (1 / 10 ^ 22 / y) = 1 / 10 ^ 22 / y + 1 / 10 ^ 22 := by
  field_simp

theorem rG_normalize_sol_aux (mc sc : ℕ) (ab ac ε x C₁ κ : ℝ)
    (hτ : 0 < 1 - ab) (hσ : 0 < 1 - ac) (hab : 0 ≤ ab) (hac : 0 ≤ ac)
    (hasm : CrudeAssembly ab ac (1 / 1000) ε x C₁ κ mc sc) :
    ∃ P : Prm, P.Ok ∧ κ < P.gap ∧ P.τ = 1 - ab ∧ P.σ = 1 - ac ∧
      2 + mc * Real.log sc ≤ P.C1 := by
  obtain ⟨-, hC, hlamp, h2l, -, -, hε0, hε1, h2ε, ⟨hδ0, -⟩, k1, k2, k3, k4, k5⟩ := hasm
  have hC' : 2 + mc * Real.log (sc : ℝ) ≤ C₁ := by exact_mod_cast hC
  clear hC
  set L := lampOf (1 - ab) (1 - ac) with hL
  have hlamp' : L < 1 := hlamp
  have k2' : κ < ε * (1 - L) := k2
  have hx0 : 0 < x := by
    by_contra hx; push Not at hx
    have : 1 / 10 ^ 22 / x ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) hx
    linarith
  have hC0 : (0 : ℝ) ≤ C₁ := by
    have : (0 : ℝ) ≤ Real.log (sc : ℝ) := Real.log_natCast_nonneg _
    have : (0 : ℝ) ≤ (mc : ℝ) * Real.log (sc : ℝ) := mul_nonneg (Nat.cast_nonneg _) this
    linarith
  set P : Prm := ⟨1 - ab, 1 - ac, max ε (1 / 2), L, ⌈x⌉₊ + ⌈C₁⌉₊ + 3, ⌈C₁⌉₊⟩ with hP
  have hxc : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hCc : C₁ ≤ (⌈C₁⌉₊ : ℝ) := Nat.le_ceil C₁
  have hX : (P.x : ℝ) = ⌈x⌉₊ + ⌈C₁⌉₊ + 3 := by simp [hP]
  have hXge : x + C₁ + 3 ≤ (P.x : ℝ) := by rw [hX]; linarith
  have hXpos : (0 : ℝ) < P.x := by linarith
  have hLτ : (1 - ab) + 2 / 10 ^ 16 ≤ L := by
    rw [hL]; unfold lampOf
    have h1 := le_max_left (max (max (1 - ab) (1 - ac))
      ((1 - ab) + (1 - beta) * max ((1 - ac) - (1 - ab)) 0) + 1 / 10 ^ 16)
      ((1 - ac) + beta * (1 - (1 - ac)))
    have h2 := le_max_left (max (1 - ab) (1 - ac))
      ((1 - ab) + (1 - beta) * max ((1 - ac) - (1 - ab)) 0)
    have h3 := le_max_left (1 - ab) (1 - ac)
    linarith
  have hLpos : 0 < L := by linarith
  have hpoly0 : P.poly ≤ 2 / 10 ^ 22 := by
    have e1 : P.poly = 1 / 10 ^ 22 / (P.x : ℝ) + 1 / 10 ^ 22 := by
      unfold Prm.poly Prm.δ; exact polyG_eq _ hXpos.ne'
    have : 1 / 10 ^ 22 / (P.x : ℝ) ≤ 1 / 10 ^ 22 / 1 :=
      div_le_div_of_nonneg_left (by norm_num) one_pos (by linarith)
    rw [e1]; linarith
  have hε'1 : max ε (1 / 2) < 1 := max_lt hε1 (by norm_num)
  have hε'h : 1 / 2 ≤ max ε (1 / 2) := le_max_right _ _
  have h2l' : ε * (2 - L) < 1 := h2l
  have h2ε' : 2 * ε - 1 < L * ε := h2ε
  have hC1 : (0 : ℝ) ≤ (⌈C₁⌉₊ : ℝ) := by positivity
  refine ⟨P, ?_, ?_, rfl, rfl, hC'.trans hCc⟩
  · refine ⟨by simpa [hP] using hτ, by simp [hP]; linarith, by simpa [hP] using hσ,
      by simp [hP]; linarith, hε'h, hε'1, by simp [hP], le_refl _, hlamp', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases le_total ε (1 / 2) with h | h
      · show max ε (1 / 2) * (2 - L) < 1
        rw [max_eq_right h]; linarith
      · show max ε (1 / 2) * (2 - L) < 1
        rw [max_eq_left h]; exact h2l'
    · show max ε (1 / 2) * (⌈C₁⌉₊ : ℝ) < 1 + (P.x : ℝ)
      have : max ε (1 / 2) * (⌈C₁⌉₊ : ℝ) ≤ (⌈C₁⌉₊ : ℝ) :=
        mul_le_of_le_one_left hC1 hε'1.le
      linarith
    · show 2 * max ε (1 / 2) + max ε (1 / 2) < 1 + (P.x : ℝ)
      linarith
    · rcases le_total ε (1 / 2) with h | h
      · show 2 * max ε (1 / 2) - 1 < L * max ε (1 / 2)
        rw [max_eq_right h]; linarith
      · show 2 * max ε (1 / 2) - 1 < L * max ε (1 / 2)
        rw [max_eq_left h]; exact h2ε'
    · unfold Prm.δ; positivity
    · unfold Prm.δ
      have : 1 / 10 ^ 22 / (P.x : ℝ) ≤ 1 / 10 ^ 22 / 1 :=
        div_le_div_of_nonneg_left (by norm_num) one_pos (by linarith)
      linarith
  · rw [Prm.lt_gapG_iff]
    have k3' : κ < 1 - ε - (1 + x) * (1 / 10 ^ 22 / x) := k3
    have k5' : κ < max ε (1 - ε) * (1 - (1 - ab)) := k5
    show κ < 1 - max ε (1 / 2) ∧ κ < max ε (1 / 2) * (1 - L) ∧ κ < 1 - max ε (1 / 2) - P.poly ∧
      κ < max ε (1 / 2) ∧ κ < max (max ε (1 / 2)) (1 - max ε (1 / 2)) * (1 - (1 - ab))
    have hpolyx : P.poly ≤ (1 + x) * (1 / 10 ^ 22 / x) := by
      have e1 : P.poly = 1 / 10 ^ 22 / (P.x : ℝ) + 1 / 10 ^ 22 := by
        unfold Prm.poly Prm.δ; exact polyG_eq _ hXpos.ne'
      rw [e1, polyG_eq _ hx0.ne']
      have : 1 / 10 ^ 22 / (P.x : ℝ) ≤ 1 / 10 ^ 22 / x :=
        div_le_div_of_nonneg_left (by norm_num) hx0 (by linarith)
      linarith
    rcases le_total ε (1 / 2) with h | h
    · rw [max_eq_right h]
      have hm : max (1 / 2 : ℝ) (1 - 1 / 2) = 1 / 2 := by norm_num
      rw [hm]
      have hk : κ < 1 / 2 * (1 - L) := by
        have : ε * (1 - L) ≤ 1 / 2 * (1 - L) :=
          mul_le_mul_of_nonneg_right h (by linarith)
        linarith
      refine ⟨by linarith, hk, by linarith, by linarith, by linarith⟩
    · rw [max_eq_left h]
      refine ⟨k1, k2', by linarith, k4, k5'⟩

end IntMul.Kappa.R6

theorem solution : type_of% @IntMul.Kappa.R6.rG_normalize_sol_aux := @IntMul.Kappa.R6.rG_normalize_sol_aux

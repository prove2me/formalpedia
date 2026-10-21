-- Prove2me | solution 1 for ModernOnlineLearning.ParameterFree.eq_13_1
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T05:12:58.85963+00:00
-- url     : https://prove2.me/submissions/8ffc0d35-3c53-4ac2-9739-88bc36329e8c

import Definitions.Def_ModernOnlineLearning_ParameterFree_Defs

open ModernOnlineLearning.ParameterFree

private lemma gamma_product_interpolation (A B a b : ℝ)
    (hA : 0 < A) (hB : 0 < B) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Real.Gamma (A + a) * Real.Gamma (B + b) ≤
      (a * A + b * B) * Real.Gamma A * Real.Gamma B := by
  have hA1 : 0 < A + 1 := by linarith
  have hB1 : 0 < B + 1 := by linarith
  have hAa : 0 < A + a := by linarith
  have hBb : 0 < B + b := by linarith
  have hga := Real.convexOn_log_Gamma.2 (x := A + 1) hA1 (y := A) hA ha hb hab
  have hgb := Real.convexOn_log_Gamma.2 (x := B) hB (y := B + 1) hB1 ha hb hab
  simp only [Function.comp_apply, smul_eq_mul] at hga hgb
  rw [show a * (A + 1) + b * A = A + a by nlinarith [hab]] at hga
  rw [show a * B + b * (B + 1) = B + b by nlinarith [hab]] at hgb
  have hlog : Real.log (Real.Gamma (A + a)) + Real.log (Real.Gamma (B + b)) ≤
      a * (Real.log (Real.Gamma (A + 1)) + Real.log (Real.Gamma B)) +
      b * (Real.log (Real.Gamma A) + Real.log (Real.Gamma (B + 1))) := by linarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_log (Real.Gamma_pos_of_pos hAa),
    Real.exp_log (Real.Gamma_pos_of_pos hBb)] at he
  have hc := convexOn_exp.2
    (x := Real.log (Real.Gamma (A + 1)) + Real.log (Real.Gamma B)) (Set.mem_univ _)
    (y := Real.log (Real.Gamma A) + Real.log (Real.Gamma (B + 1))) (Set.mem_univ _)
    ha hb hab
  simp only [smul_eq_mul] at hc
  rw [Real.exp_add (Real.log (Real.Gamma (A + 1))) (Real.log (Real.Gamma B)),
    Real.exp_add (Real.log (Real.Gamma A)) (Real.log (Real.Gamma (B + 1))),
    Real.exp_log (Real.Gamma_pos_of_pos hA1), Real.exp_log (Real.Gamma_pos_of_pos hB),
    Real.exp_log (Real.Gamma_pos_of_pos hA), Real.exp_log (Real.Gamma_pos_of_pos hB1),
    Real.Gamma_add_one hA.ne', Real.Gamma_add_one hB.ne'] at hc
  rw [Real.Gamma_add_one hA.ne', Real.Gamma_add_one hB.ne'] at he
  calc
    _ ≤ _ := he.trans hc
    _ = _ := by ring

theorem solution (ε : ℝ) (hε : 0 < ε) (t : ℕ) (ht : 1 ≤ t)
    (c z : ℝ) (hc : -1 ≤ c ∧ c ≤ 1)
    (hz : -((t - 1 : ℕ) : ℝ) ≤ z ∧ z ≤ ((t - 1 : ℕ) : ℝ)) :
    ktPotential ε t (z + c) ≤
      (1 + c * z / (t : ℝ)) * ktPotential ε (t - 1) z := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at hz ⊢
  let A : ℝ := ((n : ℝ) + 1 + z) / 2
  let B : ℝ := ((n : ℝ) + 1 - z) / 2
  let a : ℝ := (1 + c) / 2
  let b : ℝ := (1 - c) / 2
  have hA : 0 < A := by dsimp [A]; linarith [hz.1]
  have hB : 0 < B := by dsimp [B]; linarith [hz.2]
  have ha : 0 ≤ a := by dsimp [a]; linarith [hc.1]
  have hb : 0 ≤ b := by dsimp [b]; linarith [hc.2]
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hgn : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos hn
  have hgn2 : 0 < Real.Gamma ((n : ℝ) + 1 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hk : 0 ≤ ε * 2 ^ (n + 1) / (Real.pi * Real.Gamma ((n : ℝ) + 1 + 1)) := by positivity
  have hi := mul_le_mul_of_nonneg_left (gamma_product_interpolation A B a b hA hB ha hb hab) hk
  have hleft : ε * 2 ^ (n + 1) / (Real.pi * Real.Gamma ((n : ℝ) + 1 + 1)) *
      (Real.Gamma (A + a) * Real.Gamma (B + b)) = ktPotential ε (n + 1) (z + c) := by
    unfold ktPotential
    simp only [Nat.cast_add, Nat.cast_one]
    have h1 : A + a = ((n : ℝ) + 1 + 1 + (z + c)) / 2 := by dsimp [A, a]; ring
    have h2 : B + b = ((n : ℝ) + 1 + 1 - (z + c)) / 2 := by dsimp [B, b]; ring
    rw [h1, h2]
    ring
  have hright : ε * 2 ^ (n + 1) / (Real.pi * Real.Gamma ((n : ℝ) + 1 + 1)) *
      ((a * A + b * B) * Real.Gamma A * Real.Gamma B) =
      (1 + c * z / ((n : ℝ) + 1)) * ktPotential ε n z := by
    rw [Real.Gamma_add_one hn.ne', pow_succ]
    unfold ktPotential
    dsimp [A, B, a, b]
    field_simp
    ring
  rw [hleft, hright] at hi
  exact hi


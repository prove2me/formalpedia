-- Prove2me | solution 1 for ModernOnlineLearning.ToX.corollary_16_7
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:05:28.685884+00:00
-- url     : https://prove2.me/submissions/a866a571-d12a-4ec2-a716-db2dbb28c6f8

import Mathlib
import Definitions.Def_ModernOnlineLearning_ToX_Rademacher

namespace RRAux_ModernOnlineLearning_ToX_corollary_16_7

open ModernOnlineLearning.ToX

theorem cosh_step (l c G : ℝ) (hc : |c| ≤ G) :
    Real.exp (l * (1 * c)) + Real.exp (l * (-1 * c)) ≤ 2 * Real.exp (l ^ 2 * G ^ 2 / 2) := by
  have h1 := Real.cosh_le_exp_half_sq (l * c)
  rw [Real.cosh_eq] at h1
  have h2 : (l * c) ^ 2 / 2 ≤ l ^ 2 * G ^ 2 / 2 := by
    have : c ^ 2 ≤ G ^ 2 := by
      have := sq_le_sq' (abs_le.mp hc).1 (abs_le.mp hc).2; exact this
    have hl : 0 ≤ l ^ 2 := sq_nonneg l
    nlinarith
  have h3 := Real.exp_le_exp.mpr h2
  have e1 : l * (1 * c) = l * c := by ring
  have e2 : l * (-1 * c) = -(l * c) := by ring
  rw [e1, e2]
  linarith

theorem exp_sum_bound {T d : ℕ} (z : ℕ → Fin d → ℝ) (G l : ℝ) (i : Fin d)
    (hz : ∀ t ∈ Finset.Icc 1 T, ∀ i : Fin d, |z t i| ≤ G) :
    ∑ ε : Round T → Bool, Real.exp (l * ∑ t : Round T, sign ε t * z t i) ≤
      (2 : ℝ) ^ T * Real.exp (T * (l ^ 2 * G ^ 2 / 2)) := by
  have e : ∀ ε : Round T → Bool, Real.exp (l * ∑ t : Round T, sign ε t * z t i) =
      ∏ t : Round T, (fun (t : Round T) (b : Bool) => Real.exp (l * ((if b then 1 else -1) * z t i))) t (ε t) := by
    intro ε
    rw [Finset.mul_sum, Real.exp_sum]
    rfl
  rw [Finset.sum_congr rfl (fun ε _ => e ε)]
  have key := (Fintype.prod_sum (κ := fun _ : Round T => Bool)
    (fun (t : Round T) (b : Bool) => Real.exp (l * ((if b then 1 else -1) * z t i)))).symm
  rw [key]
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  calc ∏ t : Round T, (Real.exp (l * (1 * z t i)) + Real.exp (l * (-1 * z t i)))
      ≤ ∏ _t : Round T, 2 * Real.exp (l ^ 2 * G ^ 2 / 2) := by
        apply Finset.prod_le_prod
        · intro t _; positivity
        · intro t _; exact cosh_step l _ G (hz t t.2 i)
    _ = (2 : ℝ) ^ T * Real.exp (T * (l ^ 2 * G ^ 2 / 2)) := by
        rw [Finset.prod_const, Real.exp_nat_mul, mul_pow]
        simp

theorem lam_bound {T d : ℕ} [NeZero d] (z : ℕ → Fin d → ℝ) (G l : ℝ) (hl : 0 < l)
    (hz : ∀ t ∈ Finset.Icc 1 T, ∀ i : Fin d, |z t i| ≤ G) :
    l * ((1 / (2 : ℝ) ^ T) * ∑ ε : Round T → Bool,
      Finset.univ.sup' Finset.univ_nonempty (fun i : Fin d => ∑ t : Round T, sign ε t * z t i))
      ≤ Real.log d + l ^ 2 * (T * G ^ 2 / 2) := by
  set M : (Round T → Bool) → ℝ := fun ε =>
    Finset.univ.sup' Finset.univ_nonempty (fun i : Fin d => ∑ t : Round T, sign ε t * z t i)
  have hw : ∑ _ε : Round T → Bool, (1 / (2 : ℝ) ^ T) = 1 := by
    simp
  have jensen := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ : Round T → Bool => 1 / (2:ℝ) ^ T)
    (p := fun ε => l * M ε) (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at jensen
  have hM : ∀ ε, Real.exp (l * M ε) ≤
      ∑ i : Fin d, Real.exp (l * ∑ t : Round T, sign ε t * z t i) := by
    intro ε
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin d))
      (fun i : Fin d => ∑ t : Round T, sign ε t * z t i)
    simp only [M]
    rw [hj]
    exact Finset.single_le_sum (f := fun i => Real.exp (l * ∑ t : Round T, sign ε t * z t i))
      (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ j)
  have h2 : ∑ ε : Round T → Bool, 1 / (2:ℝ) ^ T * Real.exp (l * M ε) ≤
      1 / (2:ℝ) ^ T * ∑ i : Fin d, ∑ ε : Round T → Bool,
        Real.exp (l * ∑ t : Round T, sign ε t * z t i) := by
    rw [Finset.sum_comm, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum fun ε _ => hM ε
  have h3 : ∑ i : Fin d, ∑ ε : Round T → Bool,
        Real.exp (l * ∑ t : Round T, sign ε t * z t i) ≤
      ∑ _i : Fin d, (2 : ℝ) ^ T * Real.exp (T * (l ^ 2 * G ^ 2 / 2)) :=
    Finset.sum_le_sum fun i _ => exp_sum_bound z G l i hz
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  have h4 : Real.exp (∑ ε : Round T → Bool, 1 / (2:ℝ) ^ T * (l * M ε)) ≤
      Real.exp (Real.log d + l ^ 2 * (T * G ^ 2 / 2)) := by
    rw [Real.exp_add, Real.exp_log (by have := NeZero.ne d; positivity)]
    have h5 : 1 / (2:ℝ) ^ T * (↑d * (2 ^ T * Real.exp (↑T * (l ^ 2 * G ^ 2 / 2)))) =
        ↑d * Real.exp (l ^ 2 * (↑T * G ^ 2 / 2)) := by
      field_simp
    calc _ ≤ _ := jensen
      _ ≤ _ := h2
      _ ≤ 1 / (2:ℝ) ^ T * (↑d * (2 ^ T * Real.exp (↑T * (l ^ 2 * G ^ 2 / 2)))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := h5
  have h6 := Real.exp_le_exp.mp h4
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h6
  linarith [show l * (1 / (2:ℝ) ^ T * ∑ ε, M ε) = 1 / 2 ^ T * (l * ∑ ε, M ε) by ring]

theorem opt (A a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ∀ l : ℝ, 0 < l → l * A ≤ a + l ^ 2 * b) :
    A ≤ 2 * Real.sqrt (a * b) := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0
    simp only [zero_mul, Real.sqrt_zero, mul_zero, zero_add]
    by_contra hA
    push Not at hA
    have hb1 : 0 < b + 1 := by linarith
    set l := A / (2 * (b + 1)) with hl
    have hlpos : 0 < l := by positivity
    have h1 := h l hlpos
    have h2 : A ≤ l * b := by
      have : l * A ≤ l * (l * b) := by nlinarith
      exact le_of_mul_le_mul_left this hlpos
    have h3 : l * b < A := by
      rw [hl, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · subst hb0
    simp only [mul_zero, Real.sqrt_zero]
    by_contra hA
    push Not at hA
    have := h (2 * a / A) (by positivity)
    rw [show 2 * a / A * A = 2 * a by field_simp] at this
    simp at this
    linarith
  · set l := Real.sqrt (a / b) with hl
    have hlpos : 0 < l := Real.sqrt_pos.mpr (div_pos ha0 hb0)
    have h1 := h l hlpos
    have hl2 : l ^ 2 = a / b := Real.sq_sqrt (div_pos ha0 hb0).le
    rw [hl2, div_mul_cancel₀ _ hb0.ne'] at h1
    have hab : l * Real.sqrt (a * b) = a := by
      rw [hl, ← Real.sqrt_mul (div_pos ha0 hb0).le, show a / b * (a * b) = a ^ 2 by
        field_simp]
      exact Real.sqrt_sq ha0.le
    have : l * A ≤ l * (2 * Real.sqrt (a * b)) := by linarith
    exact le_of_mul_le_mul_left this hlpos

end RRAux_ModernOnlineLearning_ToX_corollary_16_7

open ModernOnlineLearning.ToX in
-- Orabona, Corollary 16.7 (Massart's Lemma)
theorem solution {d T : ℕ} [NeZero d] (hT : 1 ≤ T)
    (z : ℕ → Fin d → ℝ) (Ginf : ℝ)
    (hz : ∀ t ∈ Finset.Icc 1 T, ∀ i : Fin d, |z t i| ≤ Ginf) :
    empiricalRadMax (T := T) hT z ≤
      Ginf * Real.sqrt (2 * Real.log (d : ℝ)) / Real.sqrt (T : ℝ) := by
  have hG : 0 ≤ Ginf := le_trans (abs_nonneg _) (hz 1 (by simp; omega) ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩)
  have hd : (1 : ℝ) ≤ d := by
    have := Nat.pos_of_ne_zero (NeZero.ne d); exact_mod_cast this
  have hlog : 0 ≤ Real.log d := Real.log_nonneg hd
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hopt := RRAux_ModernOnlineLearning_ToX_corollary_16_7.opt _ _ _ hlog (by positivity)
    (fun l hl => RRAux_ModernOnlineLearning_ToX_corollary_16_7.lam_bound z Ginf l hl hz)
  unfold empiricalRadMax
  have e : 2 * Real.sqrt (Real.log d * (T * Ginf ^ 2 / 2)) =
      Ginf * Real.sqrt (2 * Real.log d) * Real.sqrt T := by
    rw [show Real.log d * (T * Ginf ^ 2 / 2) = (2 * Real.log d) * T * (Ginf / 2) ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  rw [e] at hopt
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hsT2 : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hTpos.le
  rw [mul_assoc]
  calc 1 / (T:ℝ) * ((1 / 2 ^ T) * ∑ ε : Round T → Bool,
        Finset.univ.sup' Finset.univ_nonempty (fun i : Fin d => ∑ t : Round T, sign ε t * z t i))
      ≤ 1 / (T:ℝ) * (Ginf * Real.sqrt (2 * Real.log d) * Real.sqrt T) :=
          mul_le_mul_of_nonneg_left hopt (by positivity)
    _ = _ := by
          rw [one_div_mul_eq_div, div_eq_div_iff hTpos.ne' hsT.ne', mul_assoc, hsT2]

#print axioms solution

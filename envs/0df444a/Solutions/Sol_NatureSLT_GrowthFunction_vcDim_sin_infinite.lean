-- Prove2me | solution 1 for NatureSLT.GrowthFunction.vcDim_sin_infinite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:05:42.652988+00:00
-- url     : https://prove2.me/submissions/497818e8-3954-40ea-85b4-8ec3a99c3baf

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_NatureSLT_GrowthFunction_stepFunction
open NatureSLT.GrowthFunction

theorem g69w_low_bound (c : ℕ → ℕ) (hc : ∀ j, c j ≤ 1) (i : ℕ) :
    9 * (∑ j ∈ Finset.range i, c j * 10 ^ (j + 1)) + 10 ≤ 10 ^ (i + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ]
    have : c i * 10 ^ (i + 1) ≤ 10 ^ (i + 1) := by
      calc c i * 10 ^ (i + 1) ≤ 1 * 10 ^ (i + 1) := Nat.mul_le_mul_right _ (hc i)
        _ = 10 ^ (i + 1) := one_mul _
    have e : 10 ^ (i + 1 + 1) = 10 * 10 ^ (i + 1) := by ring
    rw [e]
    linarith

theorem g69w_split (c : ℕ → ℕ) (hc : ∀ j, c j ≤ 1) {i ℓ : ℕ} (hi : i < ℓ) :
    ∃ R M : ℕ, ∑ j ∈ Finset.range ℓ, c j * 10 ^ (j + 1) = R + c i * 10 ^ (i + 1) + 10 ^ (i + 2) * M
      ∧ 9 * R + 10 ≤ 10 ^ (i + 1) := by
  have hdvd : 10 ^ (i + 2) ∣ ∑ j ∈ Finset.Ico (i + 1) ℓ, c j * 10 ^ (j + 1) := by
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact Dvd.dvd.mul_left (pow_dvd_pow 10 (by omega)) _
  obtain ⟨M, hM⟩ := hdvd
  refine ⟨∑ j ∈ Finset.range i, c j * 10 ^ (j + 1), M, ?_, g69w_low_bound c hc i⟩
  rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 ≤ ℓ by omega), Finset.sum_range_succ, hM]

theorem g69w_first (ℓ : ℕ) (δ : Fin ℓ → Bool) (i : Fin ℓ) :
      stepFunction (Real.sin
        ((Real.pi * (∑ j : Fin ℓ, (if δ j then (0 : ℝ) else 1) * (10 : ℝ) ^ ((j : ℕ) + 1) + 1)) *
          ((10 : ℝ) ^ ((i : ℕ) + 1))⁻¹)) = δ i := by
  set c : ℕ → ℕ := fun j => if h : j < ℓ then (if δ ⟨j, h⟩ then 0 else 1) else 0 with hcdef
  have hc : ∀ j, c j ≤ 1 := fun j => by
    simp only [hcdef]; split_ifs <;> omega
  have hsum : (∑ j : Fin ℓ, (if δ j then (0 : ℝ) else 1) * (10 : ℝ) ^ ((j : ℕ) + 1)) =
      ((∑ j ∈ Finset.range ℓ, c j * 10 ^ (j + 1) : ℕ) : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => c j * 10 ^ (j + 1))]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    simp only [hcdef, j.isLt, dite_true]
    split_ifs <;> simp
  obtain ⟨R, M, hN, hR⟩ := g69w_split c hc i.isLt
  rw [hsum, hN]
  push_cast
  have hci : c i = if δ i then 0 else 1 := by simp [hcdef, i.isLt]
  have hP : (0 : ℝ) < 10 ^ ((i : ℕ) + 1) := by positivity
  set P : ℝ := 10 ^ ((i : ℕ) + 1) with hPdef
  have hRr : 9 * (R : ℝ) + 10 ≤ P := by rw [hPdef]; exact_mod_cast hR
  set x : ℝ := ((R : ℝ) + 1) / P with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hP]; linarith
  have hP2 : (10 : ℝ) ^ ((i : ℕ) + 2) = 10 * P := by rw [hPdef]; ring
  have harg : Real.pi * ((R : ℝ) + (c i : ℝ) * P + 10 ^ ((i : ℕ) + 2) * (M : ℝ) + 1) * P⁻¹
      = (Real.pi * x + Real.pi * (c i : ℝ)) + ((5 * M : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hP2, hx]; push_cast; field_simp; ring
  rw [harg, Real.sin_add_nat_mul_two_pi]
  have hs : 0 < Real.sin (Real.pi * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  unfold stepFunction
  rw [hci]
  cases δ i
  · simp only [Bool.false_eq_true, if_false, Nat.cast_one, mul_one, Real.sin_add_pi]
    simp only [decide_eq_false_iff_not, not_le]; linarith
  · simp only [if_true, Nat.cast_zero, mul_zero, add_zero]
    simp only [decide_eq_true_eq]; exact hs.le

theorem g69w_supP_top (P : ℕ → Prop) (hall : ∀ n, P n) :
    (⨆ (h : ℕ) (_ : P h), (h : ℕ∞)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  refine ENat.forall_natCast_le_iff_le.mp fun n _ => ?_
  exact le_iSup₂_of_le (f := fun (h : ℕ) (_ : P h) => (h : ℕ∞)) n (hall n) le_rfl

theorem solution :
    (∀ (ℓ : ℕ) (δ : Fin ℓ → Bool) (i : Fin ℓ),
      stepFunction (Real.sin
        ((Real.pi * (∑ j : Fin ℓ, (if δ j then (0 : ℝ) else 1) * (10 : ℝ) ^ ((j : ℕ) + 1) + 1)) *
          ((10 : ℝ) ^ ((i : ℕ) + 1))⁻¹)) = δ i) ∧
    vcDim (fun (α : ℝ) (z : ℝ) => stepFunction (Real.sin (α * z))) = ⊤ := by
  refine ⟨g69w_first, ?_⟩
  unfold vcDim
  apply g69w_supP_top
  intro ℓ
  refine ⟨fun i => ((10 : ℝ) ^ ((i : ℕ) + 1))⁻¹, fun δ => ?_⟩
  exact ⟨_, fun i => g69w_first ℓ δ i⟩

-- Prove2me | solution 1 for LinMaxLoad.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:49:40.619204+00:00
-- url     : https://prove2.me/submissions/8c7f76c6-8c4d-4272-8b64-b36b29bec0e3

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinMaxLoad_expLoad
import Definitions.Def_LinMaxLoad_probLin
import Theorems.Thm_LinMaxLoad_theorem_7_km26_tail

section
set_option autoImplicit false
namespace LinMaxLoad.Dev.Thm7

open Classical

theorem maxLoad_le_card {A B : Type*} [DecidableEq B] (f : A → B) (S : Finset A) :
    LinMaxLoad.maxLoad f S ≤ S.card := by
  unfold LinMaxLoad.maxLoad
  apply Finset.sup_le
  intro b _
  exact Finset.card_filter_le _ _

theorem sum_indicator (m M : ℕ) (hM : M ≤ m) :
    ((M : ℕ) : ℝ) = ∑ T ∈ Finset.Icc 1 m, (if T ≤ M then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole]
  have : (Finset.Icc 1 m).filter (fun T => T ≤ M) = Finset.Icc 1 M := by
    ext T; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this]; simp

theorem expLoad_eq_sum {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (ℓ : ℕ) (S : Finset E) :
    LinMaxLoad.expLoad K E ℓ S = ∑ T ∈ Finset.Icc 1 S.card,
      LinMaxLoad.probLin K E ℓ (fun h => T ≤ LinMaxLoad.maxLoad (h : E → Fin ℓ → K) S) := by
  unfold LinMaxLoad.expLoad LinMaxLoad.probLin LinMaxLoad.avgLin
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  convert sum_indicator _ _ (maxLoad_le_card (h : E → Fin ℓ → K) S)

theorem probLin_le_one {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (ℓ : ℕ) (P : (E →ₗ[K] (Fin ℓ → K)) → Prop) : LinMaxLoad.probLin K E ℓ P ≤ 1 := by
  unfold LinMaxLoad.probLin LinMaxLoad.avgLin
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun h _ => ?_) (by simp)
  split_ifs <;> simp

theorem harmonic_real (m : ℕ) :
    ∑ T ∈ Finset.Icc 1 m, (1 : ℝ) / T ≤ 1 + Real.log m := by
  have h := harmonic_le_one_add_log m
  have key : ∀ n : ℕ, ∑ T ∈ Finset.Icc 1 n, (1 : ℝ) / T = ((harmonic n : ℚ) : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
      push_cast
      simp
  rw [key]; exact h

theorem le_exp_half (L : ℝ) (hL : 0 < L) : L ≤ Real.exp (L / 2) := by
  have h1 : L / 2 - 1 + 1 ≤ Real.exp (L / 2 - 1) := Real.add_one_le_exp _
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have h3 : Real.exp (L / 2) = Real.exp (L / 2 - 1) * Real.exp 1 := by
    rw [← Real.exp_add]; ring_nf
  rw [h3]
  nlinarith [Real.exp_pos (L / 2 - 1)]

/-- the analytic summation -/
theorem sum_bound (q : ℝ) (ℓ m : ℕ) (hq : 1 ≤ q) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m)
    (hmq : (m : ℝ) < q ^ ℓ) (p : ℕ → ℝ) (hp1 : ∀ T, p T ≤ 1)
    (hpT : ∀ T : ℕ, 8 * q + 48 * q * ℓ / Real.log (q ^ ℓ / m) ≤ T → T ≤ m →
      p T ≤ 9 / (T * Real.exp (Real.log (q ^ ℓ / m) / 2))) :
    ∑ T ∈ Finset.Icc 1 m, p T ≤ 66 * (q * ℓ / Real.log (q ^ ℓ / m) + q) := by
  set L := Real.log (q ^ ℓ / m) with hLdef
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hLpos : 0 < L := by
    apply Real.log_pos
    rw [lt_div_iff₀ hm0]; linarith
  set T0 : ℝ := 8 * q + 48 * q * ℓ / L with hT0
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hT0nn : 0 ≤ T0 := by rw [hT0]; positivity
  have hexp := le_exp_half L hLpos
  have hepos := Real.exp_pos (L / 2)
  -- termwise
  have hterm : ∀ T ∈ Finset.Icc 1 m, p T ≤
      (if (T : ℝ) < T0 then (1 : ℝ) else 0) + 9 / Real.exp (L / 2) * (1 / (T : ℝ)) := by
    intro T hT
    have hTm : T ≤ m := (Finset.mem_Icc.mp hT).2
    by_cases hlt : (T : ℝ) < T0
    · rw [if_pos hlt]
      have : 0 ≤ 9 / Real.exp (L / 2) * (1 / (T : ℝ)) := by positivity
      linarith [hp1 T]
    · rw [if_neg hlt]
      have := hpT T (not_lt.mp hlt) hTm
      have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (Finset.mem_Icc.mp hT).1
      have e : 9 / ((T : ℝ) * Real.exp (L / 2)) = 9 / Real.exp (L / 2) * (1 / (T : ℝ)) := by
        field_simp
      linarith
  have hsum1 := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum1
  -- counting
  have hcount : (∑ T ∈ Finset.Icc 1 m, (if (T : ℝ) < T0 then (1 : ℝ) else 0)) ≤ T0 := by
    rw [Finset.sum_boole]
    have hsub : (Finset.Icc 1 m).filter (fun T : ℕ => (T : ℝ) < T0) ⊆ Finset.Ico 1 ⌈T0⌉₊ := by
      intro T hT
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico] at hT ⊢
      refine ⟨hT.1.1, ?_⟩
      have : (T : ℝ) < ⌈T0⌉₊ := lt_of_lt_of_le hT.2 (Nat.le_ceil _)
      exact_mod_cast this
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hc
    have hlt := Nat.ceil_lt_add_one hT0nn
    have : ((⌈T0⌉₊ - 1 : ℕ) : ℝ) ≤ T0 := by
      rcases Nat.eq_zero_or_pos ⌈T0⌉₊ with h0 | h0
      · rw [h0]; simpa using hT0nn
      · rw [Nat.cast_sub h0]; push_cast; linarith
    calc (((Finset.Icc 1 m).filter (fun T : ℕ => (T : ℝ) < T0)).card : ℝ)
        ≤ ((⌈T0⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast hc
      _ ≤ T0 := this
  -- harmonic
  have hH := harmonic_real m
  have hlogm : Real.log m ≤ ℓ * q := by
    have h1 : Real.log m ≤ Real.log (q ^ ℓ) := Real.log_le_log hm0 hmq.le
    rw [Real.log_pow] at h1
    have h2 : Real.log q ≤ q := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < q); linarith
    have : (ℓ : ℝ) * Real.log q ≤ ℓ * q := mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have hqℓ : 1 ≤ (ℓ : ℝ) * q := by nlinarith
  have hfrac : 9 / Real.exp (L / 2) * (∑ T ∈ Finset.Icc 1 m, (1 : ℝ) / T) ≤ 18 * q * ℓ / L := by
    have h9 : 9 / Real.exp (L / 2) ≤ 9 / L := by
      apply div_le_div_of_nonneg_left (by norm_num) hLpos hexp
    have hH0 : 0 ≤ ∑ T ∈ Finset.Icc 1 m, (1 : ℝ) / T := Finset.sum_nonneg fun _ _ => by positivity
    calc 9 / Real.exp (L / 2) * (∑ T ∈ Finset.Icc 1 m, (1 : ℝ) / T)
        ≤ 9 / L * (1 + Real.log m) := by
          apply mul_le_mul h9 hH hH0 (by positivity)
      _ ≤ 9 / L * (2 * (ℓ * q)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 18 * q * ℓ / L := by field_simp; ring
  have hfin : T0 + 18 * q * ℓ / L ≤ 66 * (q * ℓ / L + q) := by
    rw [hT0]
    have h1 : 0 ≤ q * ℓ / L := by positivity
    have : 48 * q * ℓ / L = 48 * (q * ℓ / L) := by ring
    have : 18 * q * ℓ / L = 18 * (q * ℓ / L) := by ring
    nlinarith
  linarith

theorem main {K E : Type} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓE : ℓ ≤ Module.finrank K E) (S : Finset E)
    (hS : S.card < Fintype.card K ^ ℓ) :
    LinMaxLoad.expLoad K E ℓ S ≤
      66 * ((Fintype.card K : ℝ) * ℓ / Real.log ((Fintype.card K : ℝ) ^ ℓ / S.card) +
        Fintype.card K) := by
  have hqpos : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos
  rw [expLoad_eq_sum]
  by_cases hm : S.card = 0
  · rw [hm]
    simp only [Finset.Icc_eq_empty_of_lt (Nat.zero_lt_one), Finset.sum_empty]
    simp only [Nat.cast_zero, div_zero, Real.log_zero, zero_add]
    nlinarith
  · have hm1 : 1 ≤ S.card := Nat.pos_of_ne_zero hm
    apply sum_bound (Fintype.card K : ℝ) ℓ S.card hqpos hℓ hm1
    · exact_mod_cast hS
    · intro T; exact probLin_le_one _ _
    · intro T hT0 hTm
      have := LinMaxLoad.theorem_7_km26_tail (K := K) (E := E) ℓ hℓ hℓE S hS T hT0 hTm
      exact this.1.trans (this.2.1.trans (le_of_eq this.2.2))

end LinMaxLoad.Dev.Thm7

namespace LinMaxLoad
open LinMaxLoad.Dev.Thm7 in
theorem chk_theorem_7 :
    ∃ c : ℝ, ∀ (K E : Type) [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
      (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ Module.finrank K E → ∀ S : Finset E, S.card < Fintype.card K ^ ℓ →
        expLoad K E ℓ S ≤
          c * ((Fintype.card K : ℝ) * ℓ / Real.log ((Fintype.card K : ℝ) ^ ℓ / S.card) +
            Fintype.card K) := by
  refine ⟨66, ?_⟩
  intro K E _ _ _ _ _ ℓ hℓ hℓE S hS
  exact main ℓ hℓ hℓE S hS
end LinMaxLoad
end

theorem solution : type_of% @LinMaxLoad.chk_theorem_7 := @LinMaxLoad.chk_theorem_7

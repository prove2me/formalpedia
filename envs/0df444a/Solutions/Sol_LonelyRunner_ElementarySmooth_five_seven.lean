-- Prove2me | solution 1 for LonelyRunner.ElementarySmooth.five_seven
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-06T01:14:47.180719+00:00
-- url     : https://prove2.me/submissions/f40b81c9-1628-4fe9-8523-e3ff68662d93

import Definitions.Def_LRC_GW
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
namespace LonelyRunner.GWArithmetic
open LonelyRunner.SeparatedReplacements
theorem deficit_at_least_two {n s k : ℕ} (hsn : s < n) (hk : 2 ≤ k)
    (hgw : GW n s k) : 2 ≤ n-s := by
  by_contra! hh
  have heq : n-s=1 := by omega
  exact hgw 1 (by omega) (by simpa [heq] using (show 1 < k by omega)) (by simp)
end LonelyRunner.GWArithmetic
namespace LonelyRunner.ElementarySmooth
theorem density_factor {C : ℕ → Prop} {seed x K : ℕ}
    (hK : 0 < K) (hseed : C seed) (hx : seed < x)
    (hstep : ∀ w, C w → ∃ v, C v ∧ w < v ∧ v < K*w) :
    ∃ w, C w ∧ x ≤ w ∧ w < K*x := by
  classical
  let w := Nat.findGreatest C (x-1)
  have hwC : C w := Nat.findGreatest_spec (show seed ≤ x-1 by omega) hseed
  have hwx : w < x := by
    have hh := Nat.findGreatest_le (P := C) (x-1)
    dsimp [w]
    omega
  obtain ⟨v,hvC,hwv,hv⟩ := hstep w hwC
  have hxv : x ≤ v := by
    by_contra! hh
    exact (Nat.findGreatest_is_greatest hwv (by omega)) hvC
  exact ⟨v,hvC,hxv,lt_trans hv (Nat.mul_lt_mul_of_pos_left hwx hK)⟩
theorem triple_cycle {L K A B C x : ℕ}
    (hL : 0 < L) (hK : 0 < K) (hAB : A < B) (hBC : B < C)
    (hCA : C < L*A) (hBA : B < K*A) (hCB : C < K*B)
    (hAC : L*A < K*C) (hx : A < x) :
    ∃ w j, (w=L^j*A ∨ w=L^j*B ∨ w=L^j*C) ∧ x ≤ w ∧ w < K*x := by
  let P : ℕ → Prop := fun w => ∃ j, w=L^j*A ∨ w=L^j*B ∨ w=L^j*C
  have hseed : P A := ⟨0,Or.inl (by simp)⟩
  have hstep : ∀ w, P w → ∃ v, P v ∧ w < v ∧ v < K*w := by
    intro w hw
    obtain ⟨j,hj⟩ := hw
    have hpow : 0 < L^j := pow_pos hL _
    rcases hj with rfl | rfl | rfl
    · refine ⟨L^j*B,⟨j,Or.inr (Or.inl rfl)⟩,Nat.mul_lt_mul_of_pos_left hAB hpow,?_⟩
      nlinarith only [Nat.mul_lt_mul_of_pos_left hBA hpow]
    · refine ⟨L^j*C,⟨j,Or.inr (Or.inr rfl)⟩,Nat.mul_lt_mul_of_pos_left hBC hpow,?_⟩
      nlinarith only [Nat.mul_lt_mul_of_pos_left hCB hpow]
    · refine ⟨L^(j+1)*A,⟨j+1,Or.inl rfl⟩,?_,?_⟩
      · simpa [pow_succ,mul_assoc] using Nat.mul_lt_mul_of_pos_left hCA hpow
      · have hh := Nat.mul_lt_mul_of_pos_left hAC hpow
        simpa [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh
  obtain ⟨w,⟨j,hj⟩,hlo,hhi⟩ := density_factor hK hseed hx hstep
  exact ⟨w,j,hj,hlo,hhi⟩
end LonelyRunner.ElementarySmooth
open LonelyRunner.SeparatedReplacements LonelyRunner.GWArithmetic LonelyRunner.ElementarySmooth in
theorem solution {n s : ℕ} (hsn : s < n) (hgw : GW n s 3) :
    5 ∣ s ∨ 7 ∣ s ∨ n-s=8 := by
  have hc := deficit_at_least_two hsn (by norm_num) hgw
  by_cases h5 : 5 ∣ s
  · exact Or.inl h5
  by_cases h7 : 7 ∣ s
  · exact Or.inr (Or.inl h7)
  by_cases hc8 : n-s=8
  · exact Or.inr (Or.inr hc8)
  exfalso
  have hco5 : Nat.Coprime s 5 := (show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr h5 |>.symm
  have hco7 : Nat.Coprime s 7 := (show Nat.Prime 7 by decide).coprime_iff_not_dvd.mpr h7 |>.symm
  have hco25 : Nat.Coprime s 25 := by simpa using hco5.pow_right 2
  by_cases hc5 : n-s ≤ 5
  · exact hgw 5 hc5 (by omega) hco5
  by_cases hc7 : n-s ≤ 7
  · exact hgw 7 hc7 (by omega) hco7
  by_cases hc25 : n-s ≤ 25
  · exact hgw 25 hc25 (by omega) hco25
  obtain ⟨w,j,hw,hlo,hhi⟩ := triple_cycle (L := 5) (K := 3) (A := 25)
    (B := 35) (C := 49) (x := n-s) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega)
  apply hgw w hlo hhi
  rcases hw with rfl | rfl | rfl
  · exact (hco5.pow_right j).mul_right hco25
  · exact (hco5.pow_right j).mul_right (hco5.mul_right hco7)
  · exact (hco5.pow_right j).mul_right (by simpa using hco7.pow_right 2)

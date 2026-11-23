-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.p_q_are_integers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:10.24125+00:00
-- url     : https://prove2.me/submissions/bfc3a708-4b63-44cb-aec0-fb4117ac5cf3

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
section
namespace GroupTheoreticShannonCapacity.Construction
open Matrix
private lemma a_mod_denom (n : ℕ) (k b r s : ℤ) :
    (a n k b r s : ℤ) % (r + k * b^n) = (s * b) % (r + k * b^n) := by
  unfold a
  have h : k * b^n + s * b + r = s * b + (r + k * b^n) := by ring
  rw [h]
  simp only [Int.add_emod_right]
private lemma denom_pos (n k b r : ℕ) (_hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    0 < (r : ℤ) + (k : ℤ) * (b : ℤ)^n := by
  have hkpos : 0 < (k : ℤ) := by omega
  have hbpos : 0 < (b : ℤ)^n := by positivity
  have hrge : 0 ≤ (r : ℤ) := Int.natCast_nonneg r
  linarith [mul_pos hkpos hbpos]
private lemma denom_ne_zero (n k b r : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    (r : ℤ) + (k : ℤ) * (b : ℤ)^n ≠ 0 :=
  ne_of_gt (denom_pos n k b r hn hk hb)
private lemma p_numer_div_denom (n k b r s : ℕ) (_hn : 1 ≤ n) :
    ((r : ℤ) + (k : ℤ) * (b : ℤ)^n) ∣ ((s : ℤ)^n * r + (k : ℤ) * (a n k b r s)^n) := by
  set d : ℤ := r + k * (b : ℤ)^n with hd_def
  -- Key: a ≡ s·b (mod d)
  have ha_mod : a n k b r s ≡ (s : ℤ) * b [ZMOD d] := by
    rw [Int.ModEq, a_mod_denom]
  -- Therefore a^n ≡ (s·b)^n (mod d)
  have ha_pow_mod : (a n k b r s)^n ≡ ((s : ℤ) * b)^n [ZMOD d] := Int.ModEq.pow n ha_mod
  -- So k·a^n ≡ k·(s·b)^n = k·s^n·b^n (mod d)
  have hka_mod : (k : ℤ) * (a n k b r s)^n ≡ (k : ℤ) * ((s : ℤ) * b)^n [ZMOD d] :=
    Int.ModEq.mul_left k ha_pow_mod
  -- Simplify (s·b)^n = s^n·b^n
  have hsb_pow : ((s : ℤ) * b)^n = (s : ℤ)^n * (b : ℤ)^n := by ring
  rw [hsb_pow] at hka_mod
  -- The numerator is s^n·r + k·a^n ≡ s^n·r + k·s^n·b^n = s^n·(r + k·b^n) = s^n·d ≡ 0 (mod d)
  have hnumer_mod : (s : ℤ)^n * r + (k : ℤ) * (a n k b r s)^n ≡
                    (s : ℤ)^n * r + (k : ℤ) * (s : ℤ)^n * (b : ℤ)^n [ZMOD d] := by
    apply Int.ModEq.add rfl
    convert hka_mod using 1; ring
  have hfactor : (s : ℤ)^n * r + (k : ℤ) * (s : ℤ)^n * (b : ℤ)^n = (s : ℤ)^n * d := by
    rw [hd_def]; ring
  rw [Int.ModEq] at hnumer_mod
  have hmod_zero : ((s : ℤ)^n * d) % d = 0 := Int.mul_emod_left _ _
  rw [hfactor, hmod_zero] at hnumer_mod
  exact Int.dvd_of_emod_eq_zero hnumer_mod
private lemma q_numer_div_denom (n k b r s : ℕ) (hn : 1 ≤ n) :
    ((r : ℤ) + (k : ℤ) * (b : ℤ)^n) ∣
    ((s : ℤ)^(n-1) * r + (k : ℤ) * b * (a n k b r s)^(n-1)) := by
  set d : ℤ := r + k * (b : ℤ)^n with hd_def
  -- Key: a ≡ s·b (mod d)
  have ha_mod : a n k b r s ≡ (s : ℤ) * b [ZMOD d] := by
    rw [Int.ModEq, a_mod_denom]
  -- Therefore a^(n-1) ≡ (s·b)^(n-1) (mod d)
  have ha_pow_mod : (a n k b r s)^(n-1) ≡ ((s : ℤ) * b)^(n-1) [ZMOD d] :=
    Int.ModEq.pow (n-1) ha_mod
  -- So k·b·a^(n-1) ≡ k·b·(s·b)^(n-1) = k·s^(n-1)·b^n (mod d)
  have hkba_mod : (k : ℤ) * b * (a n k b r s)^(n-1) ≡
                  (k : ℤ) * b * ((s : ℤ) * b)^(n-1) [ZMOD d] :=
    Int.ModEq.mul_left ((k : ℤ) * b) ha_pow_mod
  -- Simplify
  have hsb_pow : ((s : ℤ) * b)^(n-1) = (s : ℤ)^(n-1) * (b : ℤ)^(n-1) := by ring
  have hsimp : (k : ℤ) * b * ((s : ℤ) * b)^(n-1) = (k : ℤ) * (s : ℤ)^(n-1) * (b : ℤ)^n := by
    rw [hsb_pow]
    have hpow : (b : ℤ) * (b : ℤ)^(n-1) = (b : ℤ)^n := by
      cases n with
      | zero => simp at hn
      | succ m => simp [pow_succ]; ring
    calc (k : ℤ) * b * ((s : ℤ)^(n-1) * (b : ℤ)^(n-1))
        = (k : ℤ) * (s : ℤ)^(n-1) * (b * (b : ℤ)^(n-1)) := by ring
      _ = (k : ℤ) * (s : ℤ)^(n-1) * (b : ℤ)^n := by rw [hpow]
  rw [hsimp] at hkba_mod
  -- The numerator ≡ s^(n-1)·(r + k·b^n) = s^(n-1)·d ≡ 0 (mod d)
  have hnumer_mod : (s : ℤ)^(n-1) * r + (k : ℤ) * b * (a n k b r s)^(n-1) ≡
                    (s : ℤ)^(n-1) * r + (k : ℤ) * (s : ℤ)^(n-1) * (b : ℤ)^n [ZMOD d] :=
    Int.ModEq.add rfl hkba_mod
  have hfactor : (s : ℤ)^(n-1) * r + (k : ℤ) * (s : ℤ)^(n-1) * (b : ℤ)^n =
                 (s : ℤ)^(n-1) * d := by rw [hd_def]; ring
  rw [Int.ModEq] at hnumer_mod
  have hmod_zero : ((s : ℤ)^(n-1) * d) % d = 0 := Int.mul_emod_left _ _
  rw [hfactor, hmod_zero] at hnumer_mod
  exact Int.dvd_of_emod_eq_zero hnumer_mod
section Tests
example : a 2 1 2 1 0 = 5 := by decide
example : p 2 1 2 1 0 = 5 := by
  simp only [p, a]
  norm_num
example : q 2 1 2 1 0 = 2 := by
  simp only [q, a]
  norm_num
example : p 2 1 2 1 0 = q 2 1 2 1 0 * 0 + 1 * (a 2 1 2 1 0)^(2-1) := by
  simp only [p, q, a]
  norm_num
example : p 2 1 2 1 0 * 2 = q 2 1 2 1 0 * (a 2 1 2 1 0) - 1 * 0^(2-1) := by
  simp only [p, q, a]
  norm_num
end Tests
end GroupTheoreticShannonCapacity.Construction
end

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    ∃ (p' q' : ℤ), p n k b r s = p' ∧ q n k b r s = q' := by
  -- Get the integer quotients from divisibility
  obtain ⟨p', hp'⟩ := p_numer_div_denom n k b r s hn
  obtain ⟨q', hq'⟩ := q_numer_div_denom n k b r s hn
  -- Denominator is nonzero in ℚ
  have hd_ne : ((r : ℤ) + (k : ℤ) * (b : ℤ)^n : ℚ) ≠ 0 := by
    exact_mod_cast denom_ne_zero n k b r hn hk hb
  refine ⟨p', q', ?_, ?_⟩
  · -- Show p = p'
    simp only [p]
    rw [div_eq_iff hd_ne, mul_comm]
    have hp_q : (((s : ℤ)^n * (r : ℤ) + (k : ℤ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n) : ℚ)
              = (((r : ℤ) + (k : ℤ) * (b : ℤ)^n) : ℚ) * ((p' : ℤ) : ℚ) := by exact_mod_cast hp'
    convert hp_q using 1 <;> push_cast <;> ring
  · -- Show q = q'
    simp only [q]
    rw [div_eq_iff hd_ne, mul_comm]
    have hq_q : (((s : ℤ)^(n-1) * (r : ℤ) +
                  (k : ℤ) * (b : ℤ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^(n-1)) : ℚ)
              = (((r : ℤ) + (k : ℤ) * (b : ℤ)^n) : ℚ) * ((q' : ℤ) : ℚ) := by exact_mod_cast hq'
    convert hq_q using 1 <;> push_cast <;> ring
end GroupTheoreticShannonCapacity.Construction

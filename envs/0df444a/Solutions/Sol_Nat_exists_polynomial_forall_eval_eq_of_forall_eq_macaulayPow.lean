-- Prove2me | solution 1 for Nat.exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a8653501-9b4b-5ec5-93ec-769f24934a44

import Mathlib
import Definitions.Def_Nat_MacaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow

set_option autoImplicit false

namespace PolyMaxSol

def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

theorem macaulayPow_zero (a : ℕ) : Nat.macaulayPow 0 a = 0 := by
  simp [Nat.macaulayPow]

theorem macaulayPow_succ (d a : ℕ) :
    Nat.macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) := by
  rw [Nat.macaulayPow]; rfl

theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

theorem choose_top_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a :=
  Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (Nat.zero_le _) (by simp)

theorem top_le (d a : ℕ) : top d a ≤ a + d + 1 := Nat.findGreatest_le _

theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) : a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

theorem lt_choose_top_succ (d a : ℕ) : a < (top d a + 1).choose (d + 1) :=
  lt_choose_of_top_lt d a (Nat.lt_succ_self _)

theorem top_eq_of (d a k : ℕ) (h₁ : k.choose (d + 1) ≤ a) (h₂ : a < (k + 1).choose (d + 1)) :
    top d a = k := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have : (k + 1).choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h
    have := choose_top_le d a
    omega
  · by_contra h
    push Not at h
    have := lt_choose_of_top_lt d a h
    omega

theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

theorem top_lt_of_lt_choose (d a k : ℕ) (h : a < k.choose (d + 1)) : top d a < k := by
  by_contra h'
  push Not at h'
  have : k.choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h'
  have := choose_top_le d a
  omega

theorem d_le_top (d a : ℕ) : d ≤ top d a :=
  le_top_of_choose_le d a d (by simp)

theorem top_zero_right (d : ℕ) : top d 0 = d :=
  top_eq_of d 0 d (by simp) (by simp)

theorem d_lt_top_of_pos (d a : ℕ) (ha : 0 < a) : d < top d a := by
  have := le_top_of_choose_le d a (d + 1) (by simp; omega)
  omega

theorem top_zero_left (a : ℕ) : top 0 a = a :=
  top_eq_of 0 a a (by simp) (by simp)

theorem rem_zero_left (a : ℕ) : rem 0 a = 0 := by
  simp [rem, top_zero_left]

theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

theorem top_mono (d : ℕ) {a b : ℕ} (h : a ≤ b) : top d a ≤ top d b :=
  le_top_of_choose_le d b _ ((choose_top_le d a).trans h)

theorem macaulayPow_lt_choose : ∀ (d m r : ℕ), r < m.choose d →
    Nat.macaulayPow d r < (m + 1).choose (d + 1)
  | 0, m, r, _ => by simp [macaulayPow_zero]
  | d + 1, m, r, h => by
      rw [macaulayPow_succ]
      show _ < (m + 1).choose (d + 2)
      have hK : top d r < m := top_lt_of_lt_choose d r m h
      have hrem : Nat.macaulayPow d (rem d r) < (top d r + 1).choose (d + 1) :=
        macaulayPow_lt_choose d (top d r) (rem d r) (rem_lt d r)
      have h1 : (top d r + 1).choose (d + 2) + (top d r + 1).choose (d + 1) =
          (top d r + 2).choose (d + 2) := by
        rw [Nat.choose_succ_succ' (top d r + 1) (d + 1), add_comm]
      have h2 : (top d r + 2).choose (d + 2) ≤ (m + 1).choose (d + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega

theorem top_macaulayPow (d a : ℕ) :
    top (d + 1) (Nat.macaulayPow (d + 1) a) = top d a + 1 := by
  apply top_eq_of
  · rw [macaulayPow_succ]; exact Nat.le_add_right _ _
  · rw [macaulayPow_succ]
    show _ < (top d a + 1 + 1).choose (d + 1 + 1)
    rw [Nat.choose_succ_succ' (top d a + 1) (d + 1)]
    show (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) <
      (top d a + 1).choose (d + 1) + (top d a + 1).choose (d + 2)
    have := macaulayPow_lt_choose d (top d a) (rem d a) (rem_lt d a)
    omega

theorem rem_macaulayPow (d a : ℕ) :
    rem (d + 1) (Nat.macaulayPow (d + 1) a) = Nat.macaulayPow d (rem d a) := by
  show Nat.macaulayPow (d + 1) a - (top (d + 1) (Nat.macaulayPow (d + 1) a)).choose (d + 1 + 1) = _
  rw [top_macaulayPow, macaulayPow_succ]
  simp

theorem macaulayPow_zero_right : ∀ d : ℕ, Nat.macaulayPow d 0 = 0
  | 0 => macaulayPow_zero 0
  | d + 1 => by
      rw [macaulayPow_succ, top_zero_right, Nat.choose_succ_self, zero_add]
      have : rem d 0 = 0 := by unfold rem; simp
      rw [this, macaulayPow_zero_right d]

def G (d a : ℕ) : ℕ → ℕ
  | 0 => a
  | j + 1 => Nat.macaulayPow (d + j + 1) (G d a j)

theorem G_zero (d a : ℕ) : G d a 0 = a := rfl
theorem G_succ (d a j : ℕ) : G d a (j + 1) = Nat.macaulayPow (d + j + 1) (G d a j) := rfl

theorem G_zero_mid : ∀ (d j : ℕ), G d 0 j = 0
  | d, 0 => rfl
  | d, j + 1 => by rw [G_succ, G_zero_mid d j, macaulayPow_zero_right]

theorem top_G (d a : ℕ) : ∀ j : ℕ, top (d + j) (G d a j) = top d a + j
  | 0 => rfl
  | j + 1 => by
      rw [G_succ, show d + (j + 1) = (d + j) + 1 from rfl, top_macaulayPow, top_G d a j]; omega

def tail : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | d + 1, r, j => G d r j

theorem rem_G : ∀ (d a j : ℕ), rem (d + j) (G d a j) = tail d (rem d a) j
  | 0, a, 0 => by simp [tail, G_zero, rem_zero_left]
  | 0, a, j + 1 => by
      rw [G_succ, show 0 + (j + 1) = (0 + j) + 1 from rfl, rem_macaulayPow, rem_G 0 a j]
      simp [tail, macaulayPow_zero_right]
  | d + 1, a, 0 => by simp [tail, G_zero]
  | d + 1, a, j + 1 => by
      rw [G_succ, show d + 1 + (j + 1) = (d + 1 + j) + 1 from rfl, rem_macaulayPow, rem_G (d + 1) a j]
      simp only [tail]
      rw [G_succ, show d + 1 + j = d + j + 1 by omega]

theorem G_eq (d a j : ℕ) : G d a j = (top d a + j).choose (d + j + 1) + tail d (rem d a) j := by
  have h := rem_add_choose (d + j) (G d a j)
  rw [top_G, rem_G] at h
  omega

theorem exists_poly_choose (t d : ℕ) (ht : d ≤ t) :
    ∃ P : Polynomial ℚ, ∀ j : ℕ, (((t + j).choose (d + j + 1) : ℕ) : ℚ) = P.eval (j : ℚ) := by
  rcases Nat.eq_or_lt_of_le ht with rfl | hlt
  · refine ⟨0, fun j => ?_⟩
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  ·
    set c := t - (d + 1) with hc
    refine ⟨Polynomial.C ((c.factorial : ℚ)⁻¹) * (descPochhammer ℚ c).comp (Polynomial.X + Polynomial.C (t : ℚ)),
      fun j => ?_⟩
    have hsymm : (t + j).choose (d + j + 1) = (t + j).choose c := by
      rw [show c = (t + j) - (d + j + 1) by omega]
      exact (Nat.choose_symm (by omega)).symm
    rw [hsymm, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, show ((j : ℚ) + (t : ℚ)) = ((t + j : ℕ) : ℚ) by push_cast; ring,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    have hf : (c.factorial : ℚ) ≠ 0 := by exact_mod_cast c.factorial_ne_zero
    push_cast
    field_simp

theorem exists_poly_tail_zero (r : ℕ) : ∃ P : Polynomial ℚ, ∀ j : ℕ, ((tail 0 r j : ℕ) : ℚ) = P.eval (j : ℚ) :=
  ⟨0, fun j => by simp [tail]⟩

theorem exists_poly_G : ∀ (d a : ℕ), ∃ P : Polynomial ℚ, ∀ j : ℕ, ((G d a j : ℕ) : ℚ) = P.eval (j : ℚ)
  | 0, a => by
      obtain ⟨P, hP⟩ := exists_poly_choose (top 0 a) 0 (d_le_top 0 a)
      refine ⟨P, fun j => ?_⟩
      rw [G_eq]; simp only [tail, add_zero]; rw [← hP]
  | d + 1, a => by
      obtain ⟨P, hP⟩ := exists_poly_choose (top (d + 1) a) (d + 1) (d_le_top (d + 1) a)
      obtain ⟨Q, hQ⟩ := exists_poly_G d (rem (d + 1) a)
      refine ⟨P + Q, fun j => ?_⟩
      rw [G_eq, Polynomial.eval_add, ← hP, ← hQ]
      simp only [tail]; push_cast; rfl

end PolyMaxSol

open PolyMaxSol in

theorem solution
    (H : ℕ → ℕ) (D₀ : ℕ) (hD₀ : 1 ≤ D₀)
    (hH : ∀ e, D₀ ≤ e → H (e + 1) = Nat.macaulayPow e (H e)) :
    ∃ P : Polynomial ℚ, ∀ e, D₀ ≤ e → (H e : ℚ) = P.eval (e : ℚ) := by
  obtain ⟨d, rfl⟩ : ∃ d, D₀ = d + 1 := ⟨D₀ - 1, by omega⟩
  have hG : ∀ j : ℕ, H (d + 1 + j) = PolyMaxSol.G d (H (d + 1)) j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [PolyMaxSol.G_succ, ← ih, show d + j + 1 = d + 1 + j by omega, show d + 1 + (j + 1) = (d + 1 + j) + 1 by omega]
        exact hH _ (by omega)
  obtain ⟨P, hP⟩ := PolyMaxSol.exists_poly_G d (H (d + 1))
  refine ⟨P.comp (Polynomial.X - Polynomial.C ((d + 1 : ℕ) : ℚ)), fun e he => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, e = d + 1 + j := ⟨e - (d + 1), by omega⟩
  rw [hG, hP, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  congr 1
  push_cast; ring

end S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow
end P2MW
export P2MW.S_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow (solution)

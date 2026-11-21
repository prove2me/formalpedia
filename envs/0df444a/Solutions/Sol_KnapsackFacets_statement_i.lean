-- Prove2me | solution 1 for KnapsackFacets.statement_i
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:20:20.717265+00:00
-- url     : https://prove2.me/submissions/2a3dd125-fab5-48d9-9121-951f09787871

import Definitions.Def_KnapsackFacets_KnapsackPolytope
import Definitions.Def_KnapsackFacets_Reduction

set_option autoImplicit false

namespace Aux_KFsi
open KnapsackFacets

theorem sum_split (g : ℕ → ℤ) (R n : ℕ) :
    ∑ j ∈ Finset.range (2 * R + n + 4), g j =
      ∑ j ∈ Finset.range (2 * R + 1), g j + g (2 * R + 1)
        + ∑ k ∈ Finset.range n, g (2 * R + 2 + k)
        + g (2 * R + n + 2) + g (2 * R + n + 3) := by
  have e1 : ∑ j ∈ Finset.range (2 * R + n + 4), g j =
      ∑ j ∈ Finset.range (2 * R + n + 3), g j + g (2 * R + n + 3) :=
    Finset.sum_range_succ g (2 * R + n + 3)
  have e2 : ∑ j ∈ Finset.range (2 * R + n + 3), g j =
      ∑ j ∈ Finset.range (2 * R + n + 2), g j + g (2 * R + n + 2) :=
    Finset.sum_range_succ g (2 * R + n + 2)
  have e3 : ∑ j ∈ Finset.range (2 * R + n + 2), g j =
      ∑ j ∈ Finset.range (2 * R + 2), g j + ∑ k ∈ Finset.range n, g (2 * R + 2 + k) := by
    rw [show 2 * R + n + 2 = 2 * R + 2 + n by omega]
    exact Finset.sum_range_add g (2 * R + 2) n
  have e4 : ∑ j ∈ Finset.range (2 * R + 2), g j =
      ∑ j ∈ Finset.range (2 * R + 1), g j + g (2 * R + 1) :=
    Finset.sum_range_succ g (2 * R + 1)
  rw [e1, e2, e3, e4]

section coef
variable {n : ℕ} (w : Fin n → ℕ) (t : ℕ)

theorem cA1 (j : ℕ) (hj : j < 2 * redR w + 1) :
    aCoef w t (j + 1) = t * shiftedFib (j + 1) := by
  unfold aCoef
  rw [if_pos ⟨by omega, by omega⟩]

theorem cA2 : aCoef w t (2 * redR w + 1 + 1) = t * (2 * redL w + 1) + 1 := by
  unfold aCoef
  rw [if_neg (fun h => by omega), if_pos (by omega)]

theorem cA3 (k : ℕ) (hk : k < n) :
    aCoef w t (2 * redR w + 2 + k + 1) = (t + 1) * wAt w k := by
  unfold aCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
    show 2 * redR w + 2 + k + 1 - (2 * redR w + 3) = k by omega]

theorem cA4 : aCoef w t (2 * redR w + n + 2 + 1) =
    t * shiftedFib (2 * redR w + 1) + t ^ 2 + t * (2 * redL w + 2) + 1 := by
  unfold aCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_neg (fun h => by omega),
    if_pos (by omega)]

theorem cA5 : aCoef w t (2 * redR w + n + 3 + 1) = t + 1 := by
  unfold aCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_neg (fun h => by omega),
    if_neg (by omega), if_pos (by omega)]

theorem cB1 (j : ℕ) (hj : j < 2 * redR w + 1) :
    alphaCoef w t (j + 1) = shiftedFib (j + 1) := by
  unfold alphaCoef
  rw [if_pos ⟨by omega, by omega⟩]

theorem cB2 : alphaCoef w t (2 * redR w + 1 + 1) = 2 * redL w + 2 := by
  unfold alphaCoef
  rw [if_neg (fun h => by omega), if_pos (by omega)]

theorem cB3 (k : ℕ) (hk : k < n) :
    alphaCoef w t (2 * redR w + 2 + k + 1) = wAt w k := by
  unfold alphaCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
    show 2 * redR w + 2 + k + 1 - (2 * redR w + 3) = k by omega]

theorem cB4 : alphaCoef w t (2 * redR w + n + 2 + 1) =
    shiftedFib (2 * redR w + 1) + t + 2 * redL w + 1 := by
  unfold alphaCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_neg (fun h => by omega),
    if_pos (by omega)]

theorem cB5 : alphaCoef w t (2 * redR w + n + 3 + 1) = 0 := by
  unfold alphaCoef
  rw [if_neg (fun h => by omega), if_neg (by omega), if_neg (fun h => by omega),
    if_neg (by omega)]

theorem sumA (X : ℕ → ℤ) :
    ∑ j ∈ Finset.range (redN w), (aCoef w t (j + 1) : ℤ) * X j =
      (t : ℤ) * (∑ j ∈ Finset.range (2 * redR w + 1), (shiftedFib (j + 1) : ℤ) * X j)
      + ((t : ℤ) * (2 * (redL w : ℤ) + 1) + 1) * X (2 * redR w + 1)
      + ((t : ℤ) + 1) * (∑ k ∈ Finset.range n, (wAt w k : ℤ) * X (2 * redR w + 2 + k))
      + ((t : ℤ) * (shiftedFib (2 * redR w + 1) : ℤ) + (t : ℤ) ^ 2
          + (t : ℤ) * (2 * (redL w : ℤ) + 2) + 1) * X (2 * redR w + n + 2)
      + ((t : ℤ) + 1) * X (2 * redR w + n + 3) := by
  rw [show redN w = 2 * redR w + n + 4 from rfl, sum_split, cA2, cA4, cA5,
    Finset.mul_sum, Finset.mul_sum]
  have h1 : ∑ j ∈ Finset.range (2 * redR w + 1), (aCoef w t (j + 1) : ℤ) * X j =
      ∑ j ∈ Finset.range (2 * redR w + 1), (t : ℤ) * ((shiftedFib (j + 1) : ℤ) * X j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [cA1 w t j hj]
    push_cast
    ring
  have h3 : ∑ k ∈ Finset.range n, (aCoef w t (2 * redR w + 2 + k + 1) : ℤ) *
        X (2 * redR w + 2 + k) =
      ∑ k ∈ Finset.range n, ((t : ℤ) + 1) * ((wAt w k : ℤ) * X (2 * redR w + 2 + k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [cA3 w t k hk]
    push_cast
    ring
  rw [h1, h3]
  push_cast
  ring

theorem sumB (X : ℕ → ℤ) :
    ∑ j ∈ Finset.range (redN w), (alphaCoef w t (j + 1) : ℤ) * X j =
      (∑ j ∈ Finset.range (2 * redR w + 1), (shiftedFib (j + 1) : ℤ) * X j)
      + (2 * (redL w : ℤ) + 2) * X (2 * redR w + 1)
      + (∑ k ∈ Finset.range n, (wAt w k : ℤ) * X (2 * redR w + 2 + k))
      + ((shiftedFib (2 * redR w + 1) : ℤ) + (t : ℤ) + 2 * (redL w : ℤ) + 1)
          * X (2 * redR w + n + 2) := by
  rw [show redN w = 2 * redR w + n + 4 from rfl, sum_split, cB2, cB4, cB5]
  have h1 : ∑ j ∈ Finset.range (2 * redR w + 1), (alphaCoef w t (j + 1) : ℤ) * X j =
      ∑ j ∈ Finset.range (2 * redR w + 1), (shiftedFib (j + 1) : ℤ) * X j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [cB1 w t j hj]
  have h3 : ∑ k ∈ Finset.range n, (alphaCoef w t (2 * redR w + 2 + k + 1) : ℤ) *
        X (2 * redR w + 2 + k) =
      ∑ k ∈ Finset.range n, (wAt w k : ℤ) * X (2 * redR w + 2 + k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [cB3 w t k hk]
  rw [h1, h3]
  push_cast
  ring

theorem wAt_fin (i : Fin n) : wAt w i = w i := by
  unfold wAt
  rw [dif_pos i.isLt]

theorem L_eq : (redL w : ℤ) = ∑ k ∈ Finset.range n, (wAt w k : ℤ) := by
  unfold redL
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun k => (wAt w k : ℤ))]
  exact Finset.sum_congr rfl (fun i _ => by rw [wAt_fin])

theorem W_eq (Y : ℕ → ℤ) (hY : ∀ k, Y k = 0 ∨ Y k = 1) :
    ∑ k ∈ Finset.range n, (wAt w k : ℤ) * Y k =
      ((∑ i ∈ Finset.univ.filter (fun i : Fin n => Y i = 1), w i : ℕ) : ℤ) := by
  push_cast
  rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range (fun k => (wAt w k : ℤ) * Y k)]
  apply Finset.sum_congr rfl
  intro i _
  rw [wAt_fin]
  rcases hY i with h | h <;> simp [h]

end coef

theorem phi_eq (R : ℕ) : ∑ j ∈ Finset.range (2 * R + 1), (shiftedFib (j + 1) : ℤ) =
    ((∑ i ∈ Finset.Icc 1 (2 * R + 1), shiftedFib i : ℕ) : ℤ) := by
  have h : Finset.Icc 1 (2 * R + 1) = Finset.Ico 1 (2 * R + 2) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    constructor <;> intro h <;> omega
  rw [h, Finset.sum_Ico_eq_sum_range]
  push_cast
  try rw [show 2 * R + 2 - 1 = 2 * R + 1 by omega]
  exact Finset.sum_congr rfl (fun j _ => by rw [add_comm])

theorem arith (t F Φ W L f y u v : ℤ) (ht : 2 ≤ t) (hF0 : 0 ≤ F) (hF1 : F ≤ Φ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ L) (hf : 0 ≤ f) (hL : 0 ≤ L)
    (hy : y = 0 ∨ y = 1) (hu : u = 0 ∨ u = 1) (hv0 : 0 ≤ v) (hWt : W ≠ t)
    (hcap : t * F + (t * (2 * L + 1) + 1) * y + (t + 1) * W
      + (t * f + t ^ 2 + t * (2 * L + 2) + 1) * u + (t + 1) * v
      ≤ t * Φ + t ^ 2 + t * (2 * L + 2) + 1) :
    F + (2 * L + 2) * y + W + (f + t + 2 * L + 1) * u ≤ Φ + t + 2 * L + 1 := by
  have h3 : 0 ≤ (t + 1) * v := mul_nonneg (by linarith) hv0
  rcases hy with rfl | rfl <;> rcases hu with rfl | rfl
  · linarith
  · by_contra hc
    push_neg at hc
    have h1 : Φ + 1 ≤ F + W + f := by omega
    have h2 : t * (Φ + 1) ≤ t * (F + W + f) := mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  · by_contra hc
    push_neg at hc
    have h1 : Φ + t ≤ F + W := by omega
    have h2 : t * (Φ + t) ≤ t * (F + W) := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h4 : W ≤ t := by nlinarith
    have h5 : t ≤ W := by linarith
    exact hWt (le_antisymm h4 h5)
  · by_contra hc
    push_neg at hc
    have h1 : Φ ≤ F + W + f + 2 * L + 1 := by omega
    have h2 : t * Φ ≤ t * (F + W + f + 2 * L + 1) := mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith

theorem hB_eq {n : ℕ} (w : Fin n → ℕ) (t : ℕ) :
    ((redB w t : ℕ) : ℤ) = (t : ℤ) * (∑ j ∈ Finset.range (2 * redR w + 1),
      (shiftedFib (j + 1) : ℤ)) + (t : ℤ) ^ 2 + (t : ℤ) * (2 * (redL w : ℤ) + 2) + 1 := by
  rw [phi_eq]
  unfold redB
  push_cast
  ring

theorem hBeta_eq {n : ℕ} (w : Fin n → ℕ) (t : ℕ) :
    ((redBeta w t : ℕ) : ℤ) = (∑ j ∈ Finset.range (2 * redR w + 1),
      (shiftedFib (j + 1) : ℤ)) + (t : ℤ) + 2 * (redL w : ℤ) + 1 := by
  rw [phi_eq]
  unfold redBeta
  push_cast
  ring

theorem core {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (ht : 2 ≤ t)
    (hno : ¬ ∃ S : Finset (Fin n), ∑ i ∈ S, w i = t)
    (X : ℕ → ℤ) (hX : ∀ j, X j = 0 ∨ X j = 1)
    (hcap : ∑ j ∈ Finset.range (redN w), (aCoef w t (j + 1) : ℤ) * X j ≤ (redB w t : ℤ)) :
    ∑ j ∈ Finset.range (redN w), (alphaCoef w t (j + 1) : ℤ) * X j ≤ (redBeta w t : ℤ) := by
  rw [sumA, hB_eq] at hcap
  rw [sumB, hBeta_eq]
  have hX0 : ∀ j, 0 ≤ X j := fun j => by rcases hX j with h | h <;> rw [h] <;> norm_num
  have hX1 : ∀ j, X j ≤ 1 := fun j => by rcases hX j with h | h <;> rw [h] <;> norm_num
  have hF0 : 0 ≤ ∑ j ∈ Finset.range (2 * redR w + 1), (shiftedFib (j + 1) : ℤ) * X j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hX0 j))
  have hF1 : ∑ j ∈ Finset.range (2 * redR w + 1), (shiftedFib (j + 1) : ℤ) * X j ≤
      ∑ j ∈ Finset.range (2 * redR w + 1), (shiftedFib (j + 1) : ℤ) :=
    Finset.sum_le_sum (fun j _ => by
      have := hX1 j
      have h0 : (0 : ℤ) ≤ (shiftedFib (j + 1) : ℤ) := Nat.cast_nonneg _
      nlinarith)
  have hW0 : 0 ≤ ∑ k ∈ Finset.range n, (wAt w k : ℤ) * X (2 * redR w + 2 + k) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hX0 _))
  have hW1 : ∑ k ∈ Finset.range n, (wAt w k : ℤ) * X (2 * redR w + 2 + k) ≤ (redL w : ℤ) := by
    rw [L_eq]
    exact Finset.sum_le_sum (fun k _ => by
      have := hX1 (2 * redR w + 2 + k)
      have h0 : (0 : ℤ) ≤ (wAt w k : ℤ) := Nat.cast_nonneg _
      nlinarith)
  have hWt : ∑ k ∈ Finset.range n, (wAt w k : ℤ) * X (2 * redR w + 2 + k) ≠ (t : ℤ) := by
    intro h
    apply hno
    refine ⟨Finset.univ.filter (fun i : Fin n => X (2 * redR w + 2 + i) = 1), ?_⟩
    have := W_eq w (fun k => X (2 * redR w + 2 + k)) (fun k => hX _)
    rw [h] at this
    exact_mod_cast this.symm
  exact arith (t : ℤ) _ _ _ (redL w : ℤ) (shiftedFib (2 * redR w + 1) : ℤ)
    (X (2 * redR w + 1)) (X (2 * redR w + n + 2)) (X (2 * redR w + n + 3))
    (by exact_mod_cast ht) hF0 hF1 hW0 hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (hX _) (hX _) (hX0 _) hWt hcap

theorem realA {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (X : ℕ → ℤ) (x : Fin (redN w) → ℝ)
    (hx : ∀ i, x i = (X i.val : ℝ)) :
    ∑ i, (redA w t i : ℝ) * x i =
      ((∑ j ∈ Finset.range (redN w), (aCoef w t (j + 1) : ℤ) * X j : ℤ) : ℝ) := by
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun j => ((aCoef w t (j + 1) : ℕ) : ℝ) * (X j : ℝ))]
  exact Finset.sum_congr rfl (fun i _ => by rw [hx i]; rfl)

theorem realB {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (X : ℕ → ℤ) (x : Fin (redN w) → ℝ)
    (hx : ∀ i, x i = (X i.val : ℝ)) :
    ∑ i, ((redAlpha w t i : ℤ) : ℝ) * x i =
      ((∑ j ∈ Finset.range (redN w), (alphaCoef w t (j + 1) : ℤ) * X j : ℤ) : ℝ) := by
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun j => ((alphaCoef w t (j + 1) : ℕ) : ℝ) * (X j : ℝ))]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [hx i]
    simp only [redAlpha, Int.cast_natCast])

noncomputable def toX {N : ℕ} (y : Fin N → ℝ) (j : ℕ) : ℤ :=
  if h : j < N then (if y ⟨j, h⟩ = 1 then 1 else 0) else 0

theorem toX_01 {N : ℕ} (y : Fin N → ℝ) (j : ℕ) : toX y j = 0 ∨ toX y j = 1 := by
  unfold toX
  split_ifs <;> simp

theorem toX_eq {N : ℕ} (y : Fin N → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1) (i : Fin N) :
    y i = (toX y i.val : ℝ) := by
  unfold toX
  rw [dif_pos i.isLt]
  rcases hy i with h | h
  · rw [if_neg (by rw [Fin.eta, h]; norm_num), h]
    simp
  · rw [if_pos (by rw [Fin.eta, h]), h]
    simp

def zS {n : ℕ} (S : Finset (Fin n)) (k : ℕ) : ℤ :=
  if h : k < n then (if (⟨k, h⟩ : Fin n) ∈ S then 1 else 0) else 0

def xS {n : ℕ} (R : ℕ) (S : Finset (Fin n)) (j : ℕ) : ℤ :=
  if j < 2 * R + 2 then 1 else zS S (j - (2 * R + 2))

theorem zS_01 {n : ℕ} (S : Finset (Fin n)) (k : ℕ) : zS S k = 0 ∨ zS S k = 1 := by
  unfold zS
  split_ifs <;> simp

theorem zS_ge {n : ℕ} (S : Finset (Fin n)) (k : ℕ) (hk : n ≤ k) : zS S k = 0 := by
  unfold zS
  rw [dif_neg (by omega)]

theorem xS_01 {n : ℕ} (R : ℕ) (S : Finset (Fin n)) (j : ℕ) : xS R S j = 0 ∨ xS R S j = 1 := by
  unfold xS
  split_ifs
  · right; rfl
  · exact zS_01 S _

theorem xS_lt {n : ℕ} (R : ℕ) (S : Finset (Fin n)) (j : ℕ) (hj : j < 2 * R + 2) :
    xS R S j = 1 := by
  unfold xS
  rw [if_pos hj]

theorem xS_ge {n : ℕ} (R : ℕ) (S : Finset (Fin n)) (k : ℕ) :
    xS R S (2 * R + 2 + k) = zS S k := by
  unfold xS
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem filter_zS {n : ℕ} (S : Finset (Fin n)) :
    Finset.univ.filter (fun i : Fin n => zS S i = 1) = S := by
  ext i
  by_cases hi : i ∈ S <;> simp [zS, hi]

end Aux_KFsi

open KnapsackFacets Aux_KFsi in
theorem solution {n : ℕ} (w : Fin n → ℕ) (t : ℕ) (ht : 2 ≤ t) (hw : ∀ i, w i + 1 ≤ t) :
    (¬ ∃ S : Finset (Fin n), ∑ i ∈ S, w i = t) ↔
      IsValid (redA w t) (redB w t) (redAlpha w t) (redBeta w t : ℤ) := by
  have hlin : IsLinearMap ℝ (fun x : Fin (redN w) → ℝ =>
      ∑ i, ((redAlpha w t i : ℤ) : ℝ) * x i) :=
    { map_add := fun x y => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring) }
  constructor
  · intro hno x hx
    have hconv := convex_halfSpace_le hlin (((redBeta w t : ℕ) : ℤ) : ℝ)
    have hsub : knapsackSet (redA w t) (redB w t) ⊆ {x : Fin (redN w) → ℝ |
        ∑ i, ((redAlpha w t i : ℤ) : ℝ) * x i ≤ (((redBeta w t : ℕ) : ℤ) : ℝ)} := by
      intro y hy
      obtain ⟨h01, hcap⟩ := hy
      have hyX := toX_eq y h01
      rw [realA w t (toX y) y hyX, ← Int.cast_natCast (R := ℝ) (redB w t)] at hcap
      have hc := core w t ht hno (toX y) (toX_01 y) (Int.cast_le.mp hcap)
      show ∑ i, ((redAlpha w t i : ℤ) : ℝ) * y i ≤ (((redBeta w t : ℕ) : ℤ) : ℝ)
      rw [realB w t (toX y) y hyX]
      exact Int.cast_le.mpr hc
    exact convexHull_min hsub hconv hx
  · intro hv hS
    obtain ⟨S, hS⟩ := hS
    have hF : ∑ j ∈ Finset.range (2 * redR w + 1), (shiftedFib (j + 1) : ℤ) *
        xS (redR w) S j = ∑ j ∈ Finset.range (2 * redR w + 1), (shiftedFib (j + 1) : ℤ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [xS_lt _ _ _ (by omega), mul_one]
    have hy1 : xS (redR w) S (2 * redR w + 1) = 1 := xS_lt _ _ _ (by omega)
    have hu0 : xS (redR w) S (2 * redR w + n + 2) = 0 := by
      rw [show 2 * redR w + n + 2 = 2 * redR w + 2 + n by omega, xS_ge, zS_ge _ _ le_rfl]
    have hv0 : xS (redR w) S (2 * redR w + n + 3) = 0 := by
      rw [show 2 * redR w + n + 3 = 2 * redR w + 2 + (n + 1) by omega, xS_ge,
        zS_ge _ _ (by omega)]
    have hW : ∑ k ∈ Finset.range n, (wAt w k : ℤ) * xS (redR w) S (2 * redR w + 2 + k) =
        (t : ℤ) := by
      have e : ∑ k ∈ Finset.range n, (wAt w k : ℤ) * xS (redR w) S (2 * redR w + 2 + k) =
          ∑ k ∈ Finset.range n, (wAt w k : ℤ) * zS S k :=
        Finset.sum_congr rfl (fun k _ => by rw [xS_ge])
      rw [e, W_eq w (zS S) (zS_01 S), filter_zS, hS]
    have hmem : (fun i : Fin (redN w) => (xS (redR w) S i.val : ℝ)) ∈
        knapsackSet (redA w t) (redB w t) := by
      refine ⟨fun i => ?_, ?_⟩
      · rcases xS_01 (redR w) S i.val with h | h
        · left; simp [h]
        · right; simp [h]
      · rw [realA w t (xS (redR w) S) _ (fun i => rfl), ← Int.cast_natCast (R := ℝ) (redB w t)]
        have hc : ∑ j ∈ Finset.range (redN w), (aCoef w t (j + 1) : ℤ) * xS (redR w) S j ≤
            (redB w t : ℤ) := by
          rw [sumA, hB_eq, hF, hy1, hu0, hv0, hW]
          apply le_of_eq
          ring
        exact Int.cast_le.mpr hc
    have h := hv _ (subset_convexHull ℝ _ hmem)
    rw [realB w t (xS (redR w) S) _ (fun i => rfl)] at h
    have h' := Int.cast_le.mp h
    rw [sumB, hBeta_eq, hF, hy1, hu0, hW] at h'
    linarith

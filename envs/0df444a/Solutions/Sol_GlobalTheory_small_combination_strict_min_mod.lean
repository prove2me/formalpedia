-- Prove2me | solution 1 for GlobalTheory.small_combination_strict_min_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:51.665809+00:00
-- url     : https://prove2.me/submissions/b5b870ff-ef98-4cc9-8e27-d3610ae9d079

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SmallCombinationStrictMinMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_zero' (hQ : ∀ x, 2 * Q x = Bf x x) : Q 0 = 0 := by
  have h := hQ 0
  simp only [map_zero, AddMonoidHom.zero_apply] at h
  omega
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_nonneg_of_pos (hQ : ∀ x, 2 * Q x = Bf x x) (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x)
    (x : X) : 0 ≤ Q x := by
  by_cases hx : x = 0
  · subst hx
    rw [quad_zero' hQ]
  · linarith [hpos x hx]
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_add_eq_add_add_bilin (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (x y : X) : Q (x + y) = Q x + Q y + Bf x y := by
  have h := hQ (x + y)
  simp only [map_add, AddMonoidHom.add_apply] at h
  linarith [hQ x, hQ y, hsym y x]
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_zsmul' (hQ : ∀ x, 2 * Q x = Bf x x) (k : ℤ) (x : X) :
    Q (k • x) = k ^ 2 * Q x := by
  have h := hQ (k • x)
  simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_eq_mul, zsmul_eq_mul] at h
  have h2 : 2 * Q (k • x) = 2 * (k ^ 2 * Q x) := by rw [h, ← hQ x]; ring
  exact mul_left_cancel₀ two_ne_zero h2
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma bilin_sq_le_four_mul_quad (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x) (x y : X) : Bf x y ^ 2 ≤ 4 * Q x * Q y := by
  by_cases hx : x = 0
  · subst hx
    rw [quad_zero' hQ]
    simp
  · have hx1 := hpos x hx
    have hw := quad_nonneg_of_pos hQ hpos (Bf x y • x + (-(2 * Q x)) • y)
    rw [quad_add_eq_add_add_bilin hsym hQ, quad_zsmul' hQ, quad_zsmul' hQ] at hw
    simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_eq_mul, zsmul_eq_mul] at hw
    nlinarith
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_add_le_add_sq_mul (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x) {x y : X} {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : 0 ≤ C) (hx : (Q x : ℝ) ≤ a ^ 2 * C) (hy : (Q y : ℝ) ≤ b ^ 2 * C) :
    (Q (x + y) : ℝ) ≤ (a + b) ^ 2 * C := by
  have hcs : (Bf x y : ℝ) ^ 2 ≤ 4 * (Q x : ℝ) * Q y := by
    exact_mod_cast bilin_sq_le_four_mul_quad hsym hQ hpos x y
  have hx0 : (0 : ℝ) ≤ Q x := by exact_mod_cast quad_nonneg_of_pos hQ hpos x
  have hy0 : (0 : ℝ) ≤ Q y := by exact_mod_cast quad_nonneg_of_pos hQ hpos y
  have hprod : (Q x : ℝ) * Q y ≤ (a ^ 2 * C) * (b ^ 2 * C) :=
    mul_le_mul hx hy hy0 (by positivity)
  have hB : (Bf x y : ℝ) ≤ 2 * a * b * C := by
    have h2 : (Bf x y : ℝ) ^ 2 ≤ (2 * a * b * C) ^ 2 := by nlinarith
    exact (abs_le_of_sq_le_sq' h2 (by positivity)).2
  have hadd : (Q (x + y) : ℝ) = Q x + Q y + Bf x y := by
    exact_mod_cast quad_add_eq_add_add_bilin hsym hQ x y
  rw [hadd]
  nlinarith
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_nsmul' (hQ : ∀ x, 2 * Q x = Bf x x) (m : ℕ) (x : X) :
    Q (m • x) = (m : ℤ) ^ 2 * Q x := by
  have h := quad_zsmul' hQ (m : ℤ) x
  rwa [natCast_zsmul] at h
end GlobalTheory
end

set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (X : Type) [AddCommGroup X] (Bf : X →+ X →+ ℤ) (Q : X → ℤ), (∀ x y, Bf x y = Bf y x) →
    (∀ x, 2 * Q x = Bf x x) → (∀ x, x ≠ 0 → 1 ≤ Q x) →
    ∀ (n D q : ℕ) (b : Fin n → X) (Cc M₀ : ℝ), 0 ≤ Cc → 0 ≤ M₀ → (∀ j, (Q (b j) : ℝ) ≤ Cc) →
    (∀ j z, |(Bf (b j) z : ℝ)| ≤ M₀ * Q z) → (D : ℝ) * M₀ < q →
    ∀ e : Fin n → ℕ, ∑ j, e j ≤ D →
    ((Q (∑ j, e j • b j) : ℝ) ≤ (D : ℝ) ^ 2 * Cc) ∧
      ∀ z, z ≠ 0 → Q (∑ j, e j • b j) < Q (∑ j, e j • b j + q • z) := by
  intro X _ Bf Q hsym hQ hpos n D q b Cc M₀ hCc hM₀ hb hBb hq e he
  have hsumR : (∑ j, (e j : ℝ)) ≤ D := by exact_mod_cast he
  have hsum0 : (0 : ℝ) ≤ ∑ j, (e j : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  constructor
  · have key : ∀ s : Finset (Fin n),
        (Q (∑ j ∈ s, e j • b j) : ℝ) ≤ (∑ j ∈ s, (e j : ℝ)) ^ 2 * Cc := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp [quad_zero' hQ]
      · intro j s hj ih
        rw [Finset.sum_insert hj, Finset.sum_insert hj]
        refine quad_add_le_add_sq_mul hsym hQ hpos (Nat.cast_nonneg _)
          (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hCc ?_ ih
        rw [quad_nsmul' hQ]
        push_cast
        exact mul_le_mul_of_nonneg_left (hb j) (by positivity)
    calc (Q (∑ j, e j • b j) : ℝ) ≤ (∑ j, (e j : ℝ)) ^ 2 * Cc := key Finset.univ
      _ ≤ (D : ℝ) ^ 2 * Cc :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hsum0 hsumR 2) hCc
  · intro z hz
    have hz1 : (1 : ℝ) ≤ Q z := by exact_mod_cast hpos z hz
    have hBv : Bf (∑ j, e j • b j) z = ∑ j, (e j : ℤ) * Bf (b j) z := by
      simp [map_sum, map_nsmul, nsmul_eq_mul]
    have hBvR : (Bf (∑ j, e j • b j) z : ℝ) = ∑ j, (e j : ℝ) * Bf (b j) z := by
      rw [hBv]; push_cast; rfl
    have hMz : (0 : ℝ) ≤ M₀ * Q z := mul_nonneg hM₀ (by linarith)
    have habs : |(Bf (∑ j, e j • b j) z : ℝ)| ≤ (∑ j, (e j : ℝ)) * (M₀ * Q z) := by
      rw [hBvR, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hBb j z) (Nat.cast_nonneg _)
    have h2 : (∑ j, (e j : ℝ)) * (M₀ * Q z) ≤ D * (M₀ * Q z) :=
      mul_le_mul_of_nonneg_right hsumR hMz
    have hlow := neg_abs_le (Bf (∑ j, e j • b j) z : ℝ)
    have hbound : -((D : ℝ) * M₀ * Q z) ≤ (Bf (∑ j, e j • b j) z : ℝ) := by nlinarith
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) hM₀) hq
    have hadd : (Q (∑ j, e j • b j + q • z) : ℝ)
        = Q (∑ j, e j • b j) + (q : ℝ) ^ 2 * Q z + q * Bf (∑ j, e j • b j) z := by
      rw [quad_add_eq_add_add_bilin hsym hQ, quad_nsmul' hQ, map_nsmul, nsmul_eq_mul]
      push_cast
      ring
    have hfin : (Q (∑ j, e j • b j) : ℝ) < Q (∑ j, e j • b j + q • z) := by
      rw [hadd]
      nlinarith [mul_pos hq0 (mul_pos (show (0 : ℝ) < q - D * M₀ by linarith)
        (show (0 : ℝ) < Q z by linarith)),
        mul_nonneg hq0.le (show (0 : ℝ) ≤ Bf (∑ j, e j • b j) z + D * M₀ * Q z by linarith)]
    exact_mod_cast hfin
end _root_.GlobalTheory
end GlobalTheory

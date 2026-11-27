-- Prove2me | solution 1 for GlobalTheory.torsion_points_distinct_mod_maximal_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:43:30.475217+00:00
-- url     : https://prove2.me/submissions/2dadf320-b69b-4c76-9040-47631fa435d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TorsionPointsDistinctModMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine
namespace TorsionUnit
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end TorsionUnit
open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma short_negY_eq (A B x y : K) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).negY x y = -y := by
  simp [Affine.negY]
open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma short_addX_eq (A B x₁ x₂ l : K) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).addX x₁ x₂ l = l ^ 2 - x₁ - x₂ := by
  simp [Affine.addX]
open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_add_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_le_one_of_norm_sq_sub_le_one {l s : K} (h : ‖l ^ 2 - s‖ ≤ 1) (hs : ‖s‖ ≤ 1) :
    ‖l‖ ≤ 1 := by
  have hsq : ‖l ^ 2‖ ≤ 1 := by
    have := norm_add_le_one_of_le_one h hs
    rwa [sub_add_cancel] at this
  rw [norm_pow] at hsq
  exact (pow_le_one_iff_of_nonneg (norm_nonneg l) two_ne_zero).mp hsq
open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_mul_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb
open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma short_equation_of_nonsingular {A B x y : K}
    (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + A * x + B := by
  have := h.1
  simp [Affine.equation_iff] at this
  linear_combination this
open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_sub_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact norm_add_le_one_of_le_one ha (by rwa [norm_neg])
open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  exact_mod_cast IsUltrametricDist.norm_natCast_le_one K n
open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_y_eq_one_of_nsmul_eq_zero [DecidableEq K] {A B : K} {N : ℕ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (h2 : ‖(2 : K)‖ = 1) (hD : ‖4 * A ^ 3 + 27 * B ^ 2‖ = 1) (hN : Odd N)
    (hT : ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1)
    {x y : K} (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y)
    (hP : N • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖y‖ = 1 := by
  have hx := hT _ _ h hP
  have h2ne : (2 : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h2
    exact zero_ne_one h2
  have hy : y ≠ ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).negY x y := by
    intro hyy
    have hneg : -Point.some x y h = Point.some x y h := by
      rw [Point.neg_some]
      congr 1
      exact hyy.symm
    obtain ⟨k, rfl⟩ := hN
    have hPP : Point.some x y h + Point.some x y h = 0 := by
      nth_rewrite 1 [← hneg]
      exact neg_add_cancel _
    rw [add_smul, one_smul, mul_comm, mul_smul, two_smul, hPP, smul_zero, zero_add] at hP
    simp at hP
  have hy0 : y ≠ 0 := by
    intro h0
    apply hy
    rw [short_negY_eq, h0, neg_zero]
  have hdbl := Point.add_of_Y_ne (h₁ := h) (h₂ := h) hy
  have h3 := hT _ _ _ (by rw [← hdbl, smul_add, hP, add_zero])
  rw [short_addX_eq] at h3
  set l := ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).slope x x y y with hl
  have hlrel : l * (2 * y) = 3 * x ^ 2 + A := by
    rw [hl, slope_of_Y_ne rfl hy, short_negY_eq, sub_neg_eq_add, ← two_mul,
      div_mul_cancel₀ _ (mul_ne_zero h2ne hy0)]
    simp
  have hlle : ‖l‖ ≤ 1 :=
    norm_le_one_of_norm_sq_sub_le_one (s := x + x) (by rw [← sub_sub]; exact h3)
      (norm_add_le_one_of_le_one hx hx)
  have hder : ‖3 * x ^ 2 + A‖ ≤ ‖y‖ := by
    rw [← hlrel, norm_mul, norm_mul, h2, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hlle
  have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hx3 : ‖x ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hf : ‖x ^ 3 + A * x + B‖ ≤ 1 :=
    norm_add_le_one_of_le_one (norm_add_le_one_of_le_one hx3 (norm_mul_le_one_of_le_one hA hx)) hB
  have hyeq := short_equation_of_nonsingular h
  have hyle : ‖y‖ ≤ 1 := by
    have : ‖y‖ ^ 2 ≤ 1 := by rw [← norm_pow, hyeq]; exact hf
    exact (pow_le_one_iff_of_nonneg (norm_nonneg y) two_ne_zero).mp this
  refine le_antisymm hyle (not_lt.mp fun hlt => ?_)
  have hflt : ‖x ^ 3 + A * x + B‖ < 1 := by
    rw [← hyeq, norm_pow]
    nlinarith [norm_nonneg y]
  have hderlt : ‖3 * x ^ 2 + A‖ < 1 := hder.trans_lt hlt
  have ha : ‖27 * B - 18 * A * x‖ ≤ 1 :=
    norm_sub_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 27) hB)
      (norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 18) hA) hx)
  have hb : ‖6 * A * x ^ 2 - 9 * B * x + 4 * A ^ 2‖ ≤ 1 := by
    refine norm_add_le_one_of_le_one (norm_sub_le_one_of_le_one ?_ ?_) ?_
    · exact norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 6) hA) hx2
    · exact norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 9) hB) hx
    · refine norm_mul_le_one_of_le_one (norm_ofNat_le_one 4) ?_
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hA
  have hid : 4 * A ^ 3 + 27 * B ^ 2 = (27 * B - 18 * A * x) * (x ^ 3 + A * x + B) +
      (6 * A * x ^ 2 - 9 * B * x + 4 * A ^ 2) * (3 * x ^ 2 + A) := by ring
  have hlt1 : ‖4 * A ^ 3 + 27 * B ^ 2‖ < 1 := by
    rw [hid]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans_lt hflt
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans_lt hderlt
  rw [hD] at hlt1
  exact lt_irrefl _ hlt1
open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_sub_y_le_norm_sub_x_of_torsion [DecidableEq K] {A B : K} {N : ℕ}
    (hT : ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1)
    {x₁ y₁ x₂ y₂ : K} (h₁ : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x₁ y₁)
    (h₂ : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x₂ y₂)
    (hP : N • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0)
    (hQ : N • (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0) (hx : x₁ ≠ x₂) :
    ‖y₁ - y₂‖ ≤ ‖x₁ - x₂‖ := by
  have hsum := Point.add_of_X_ne (h₁ := h₁) (h₂ := h₂) hx
  have h3 := hT _ _ _ (by rw [← hsum, smul_add, hP, hQ, add_zero])
  rw [short_addX_eq, slope_of_X_ne hx] at h3
  have hl : ‖(y₁ - y₂) / (x₁ - x₂)‖ ≤ 1 :=
    norm_le_one_of_norm_sq_sub_le_one (s := x₁ + x₂) (by rw [← sub_sub]; exact h3)
      (norm_add_le_one_of_le_one (hT _ _ h₁ hP) (hT _ _ h₂ hQ))
  have hne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have : y₁ - y₂ = (y₁ - y₂) / (x₁ - x₂) * (x₁ - x₂) := by field_simp
  rw [this, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hl
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (A B : K) (N : ℕ), ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖(2 : K)‖ = 1 → ‖4 * A ^ 3 + 27 * B ^ 2‖ = 1 → Odd N → (∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y), N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1) → ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y), N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x ^ 3 + A * x + B‖ = 1 ∧ ∀ (x' y' : K) (h' : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x' y'), N • (WeierstrassCurve.Affine.Point.some x' y' h') = 0 → x ≠ x' → ‖x - x'‖ = 1 := by
  intro K _ _ _ A B N hA hB h2 hD hN hT x y h hP
  have hy1 := norm_y_eq_one_of_nsmul_eq_zero hA hB h2 hD hN hT h hP
  refine ⟨?_, ?_⟩
  · rw [← short_equation_of_nonsingular h, norm_pow, hy1, one_pow]
  · intro x' y' h' hP' hx
    have hxx : ‖x - x'‖ ≤ 1 := norm_sub_le_one_of_le_one (hT _ _ h hP) (hT _ _ h' hP')
    refine le_antisymm hxx (not_lt.mp fun hlt => ?_)
    have hsub := norm_sub_y_le_norm_sub_x_of_torsion hT h h' hP hP' hx
    have hnegP : N • Point.some x' _
        (((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.nonsingular_neg x' y').mpr h') = 0 := by
      rw [← Point.neg_some h', smul_neg, hP', neg_zero]
    have hadd := norm_sub_y_le_norm_sub_x_of_torsion hT h _ hP hnegP hx
    rw [short_negY_eq, sub_neg_eq_add] at hadd
    have h2y : ‖2 * y‖ < 1 := by
      have : 2 * y = (y - y') + (y + y') := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hsub.trans_lt hlt) (hadd.trans_lt hlt))
    rw [norm_mul, h2, hy1, one_mul] at h2y
    exact lt_irrefl _ h2y
end _root_.GlobalTheory
end GlobalTheory

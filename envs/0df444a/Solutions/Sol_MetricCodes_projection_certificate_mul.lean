-- Prove2me | solution 1 for MetricCodes.projection_certificate_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/aaffc6a9-68e1-40b6-bf6b-488e90a77ac3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_ProjectionFamily_overlap_nonneg
import Theorems.Thm_MetricCodes_ProjectionFamily_card_mul_rank_sq_le_dimension_mul_sum_overlap
import Theorems.Thm_MetricCodes_gram_double_sum_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
variable {X E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D d : ℕ}
namespace MetricCodes
theorem _root_.solution
    (P : ProjectionFamily X D d)
    (C : Finset X)
    (t : X → X → ℝ)
    (q : X → E)
    {s lam : ℝ}
    (hd : 0 < d)
    (hs : s < 1)
    (hgap : s < lam)
    (hdiag : ∀ x ∈ C, t x x = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → t x y ≤ s)
    (hgram : ∀ x ∈ C, ∀ y ∈ C,
      ⟪q x, q y⟫_ℝ = (t x y - lam) * P.overlap x y) :
    (C.card : ℝ) * (lam - s) * (d : ℝ) ≤
      (1 - s) * (D : ℝ) := by
  classical
  let f : X → X → ℝ :=
    fun x y => (t x y - s) * P.overlap x y
  have hfeature (x : X) (hx : x ∈ C)
      (y : X) (hy : y ∈ C) :
      f x y =
        (lam - s) * P.overlap x y + ⟪q x, q y⟫_ℝ := by
    dsimp [f]
    rw [hgram x hx y hy]
    ring
  have hgram_nonneg :
      0 ≤ ∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ :=
    gram_double_sum_nonneg C q
  have hfeature_sum :
      (∑ x ∈ C, ∑ y ∈ C, f x y) =
        (lam - s) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) +
          (∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ) := by
    calc
      (∑ x ∈ C, ∑ y ∈ C, f x y) =
          ∑ x ∈ C, ∑ y ∈ C,
            ((lam - s) * P.overlap x y + ⟪q x, q y⟫_ℝ) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              exact hfeature x hx y hy
      _ = (lam - s) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) +
          (∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hlower :
      (lam - s) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) ≤
        ∑ x ∈ C, ∑ y ∈ C, f x y := by
    rw [hfeature_sum]
    exact le_add_of_nonneg_right hgram_nonneg
  have hrow (x : X) (hx : x ∈ C) :
      (∑ y ∈ C, f x y) ≤ (1 - s) * (d : ℝ) := by
    calc
      (∑ y ∈ C, f x y) ≤
          ∑ y ∈ C, if y = x then f x x else 0 := by
            apply Finset.sum_le_sum
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp
            · have hnonpos : f x y ≤ 0 := by
                exact mul_nonpos_of_nonpos_of_nonneg
                  (sub_nonpos.mpr
                    (hsep x hx y hy (Ne.symm hyx)))
                  (P.overlap_nonneg x y)
              simpa [hyx] using hnonpos
      _ = f x x := by simp [hx]
      _ = (1 - s) * (d : ℝ) := by
        dsimp [f]
        rw [hdiag x hx, P.overlap_self x]
  have hupper :
      (∑ x ∈ C, ∑ y ∈ C, f x y) ≤
        (C.card : ℝ) * (1 - s) * (d : ℝ) := by
    calc
      (∑ x ∈ C, ∑ y ∈ C, f x y) ≤
          ∑ x ∈ C, (1 - s) * (d : ℝ) :=
            Finset.sum_le_sum (fun x hx => hrow x hx)
      _ = (C.card : ℝ) * (1 - s) * (d : ℝ) := by
        simp
        ring
  have hoverlap :
      ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
        (D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) :=
    P.card_mul_rank_sq_le_dimension_mul_sum_overlap C
  have hD : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hgap_pos : 0 < lam - s := sub_pos.mpr hgap
  have hmain :
      (lam - s) * ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
        (D : ℝ) * ((C.card : ℝ) * (1 - s) * (d : ℝ)) := by
    calc
      (lam - s) * ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
          (lam - s) *
            ((D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y)) :=
              mul_le_mul_of_nonneg_left hoverlap hgap_pos.le
      _ = (D : ℝ) *
          ((lam - s) *
            (∑ x ∈ C, ∑ y ∈ C, P.overlap x y)) := by ring
      _ ≤ (D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, f x y) :=
        mul_le_mul_of_nonneg_left hlower hD
      _ ≤ (D : ℝ) *
          ((C.card : ℝ) * (1 - s) * (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hupper hD
  by_cases hC : C.Nonempty
  · have hcard : 0 < (C.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hC
    have hrank : 0 < (d : ℝ) := by exact_mod_cast hd
    have hcancel :
        ((C.card : ℝ) * (d : ℝ)) *
            ((C.card : ℝ) * (lam - s) * (d : ℝ)) ≤
          ((C.card : ℝ) * (d : ℝ)) *
            ((1 - s) * (D : ℝ)) := by
      calc
        ((C.card : ℝ) * (d : ℝ)) *
            ((C.card : ℝ) * (lam - s) * (d : ℝ)) =
            (lam - s) * ((C.card : ℝ) * (d : ℝ)) ^ 2 := by ring
        _ ≤ (D : ℝ) *
            ((C.card : ℝ) * (1 - s) * (d : ℝ)) := hmain
        _ = ((C.card : ℝ) * (d : ℝ)) *
            ((1 - s) * (D : ℝ)) := by ring
    exact le_of_mul_le_mul_left hcancel (mul_pos hcard hrank)
  · have hempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    subst C
    simpa using
      (mul_nonneg (sub_nonneg.mpr hs.le) (Nat.cast_nonneg D))
end MetricCodes

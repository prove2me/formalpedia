-- Prove2me | solution 1 for ModularCurve.FifteenA1.deltaPairHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f401196a-685d-5da9-b5b1-75f4bcc061c2

import Definitions.Def_EllipticCurve_FifteenA1
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FifteenA1_deltaPairHom

set_option autoImplicit false

namespace M4cP2
namespace Hom

p2m_open "WeierstrassCurve Affine WeierstrassCurve.Affine ModularCurve.FifteenA1"

theorem equation_shortW_iff (X Y : ℚ) :
    shortW.Equation X Y ↔ Y ^ 2 = (X - 12) * (X + 4) * (X + 13) := by
  rw [equation_iff]
  simp only [shortW_a₁, shortW_a₂, shortW_a₃, shortW_a₄, shortW_a₆]
  constructor <;> intro h <;> linear_combination h

theorem negY_shortW (X Y : ℚ) : shortW.negY X Y = -Y := by
  simp [WeierstrassCurve.Affine.negY]

theorem isSqClass_self (a : ℚ) : IsSqClass a a := ⟨1, one_ne_zero, by ring⟩

theorem isSqClass_symm {d a : ℚ} (_hd : d ≠ 0) (h : IsSqClass d a) : IsSqClass a d := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, mul_one]

theorem isSqClass_trans {d a b : ℚ} (hab : IsSqClass d a) (hbc : IsSqClass a b) :
    IsSqClass d b := by
  obtain ⟨c₁, hc₁, rfl⟩ := hab
  obtain ⟨c₂, hc₂, rfl⟩ := hbc
  exact ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, by ring⟩

theorem isSqClass_one_mul_self {a : ℚ} (ha : a ≠ 0) : IsSqClass 1 (a * a) :=
  ⟨a, ha, by ring⟩

theorem isSqClass_mul_of_mul₃_eq_sq {a b c s : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a * b * c = s ^ 2) : IsSqClass (a * b) c := by
  have hs : s ≠ 0 := by
    rintro rfl
    rw [show (0 : ℚ) ^ 2 = 0 by norm_num] at h
    exact mul_ne_zero (mul_ne_zero ha hb) hc h
  refine ⟨c / s, div_ne_zero hc hs, ?_⟩
  rw [div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero 2 hs)]
  linear_combination -c * h

structure ChordVieta (x₁ x₂ x₃ L M : ℚ) : Prop where
  e₁ : x₁ + x₂ + x₃ = L ^ 2 - 5
  e₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = -(152 + 2 * L * M)
  e₃ : x₁ * x₂ * x₃ = 624 + M ^ 2

namespace ChordVieta

variable {x₁ x₂ x₃ L M : ℚ}

theorem perm₁ (h : ChordVieta x₁ x₂ x₃ L M) : ChordVieta x₂ x₃ x₁ L M :=
  ⟨by linear_combination h.e₁, by linear_combination h.e₂, by linear_combination h.e₃⟩

theorem perm₂ (h : ChordVieta x₁ x₂ x₃ L M) : ChordVieta x₃ x₁ x₂ L M :=
  h.perm₁.perm₁

theorem prod_sub_twelve (h : ChordVieta x₁ x₂ x₃ L M) :
    (x₁ - 12) * (x₂ - 12) * (x₃ - 12) = (12 * L + M) ^ 2 := by
  linear_combination h.e₃ - 12 * h.e₂ + 144 * h.e₁

theorem prod_add_four (h : ChordVieta x₁ x₂ x₃ L M) :
    (x₁ + 4) * (x₂ + 4) * (x₃ + 4) = (M - 4 * L) ^ 2 := by
  linear_combination h.e₃ + 4 * h.e₂ + 16 * h.e₁

theorem line_vanish_of_twelve (h : ChordVieta x₁ x₂ x₃ L M) (hx₃ : x₃ = 12) :
    12 * L + M = 0 := by
  have h12 := h.prod_sub_twelve
  rw [hx₃] at h12
  exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith [h12])

theorem line_vanish_of_neg_four (h : ChordVieta x₁ x₂ x₃ L M) (hx₃ : x₃ = -4) :
    M - 4 * L = 0 := by
  have h4 := h.prod_add_four
  rw [hx₃] at h4
  exact pow_eq_zero_iff two_ne_zero |>.mp (by linarith [h4])

theorem prod_pair_of_twelve (h : ChordVieta x₁ x₂ x₃ L M) (hx₃ : x₃ = 12) :
    (x₁ - 12) * (x₂ - 12) = 400 := by
  have hLM := h.line_vanish_of_twelve hx₃
  subst hx₃
  linear_combination h.e₂ - 24 * h.e₁ - 2 * L * hLM

theorem prod_pair_of_neg_four (h : ChordVieta x₁ x₂ x₃ L M) (hx₃ : x₃ = -4) :
    (x₁ + 4) * (x₂ + 4) = -144 := by
  have hLM := h.line_vanish_of_neg_four hx₃
  subst hx₃
  linear_combination h.e₂ + 8 * h.e₁ - 2 * L * hLM

end ChordVieta

theorem chordVieta_of_secant {x₁ y₁ x₂ y₂ L M : ℚ} (hE₁ : shortW.Equation x₁ y₁)
    (hE₂ : shortW.Equation x₂ y₂) (hx : x₁ ≠ x₂) (hy₁ : y₁ = L * x₁ + M)
    (hy₂ : y₂ = L * x₂ + M) :
    ChordVieta x₁ x₂ (L ^ 2 - 5 - x₁ - x₂) L M := by
  rw [equation_shortW_iff] at hE₁ hE₂
  subst hy₁; subst hy₂
  have hsub : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  refine ⟨by ring, ?_, ?_⟩
  · refine mul_right_cancel₀ hsub ?_
    linear_combination hE₁ - hE₂
  · refine mul_right_cancel₀ hsub ?_
    linear_combination x₂ * hE₁ - x₁ * hE₂

theorem chordVieta_of_tangent {x₁ y₁ L M : ℚ} (hE₁ : shortW.Equation x₁ y₁)
    (hL : L * (2 * y₁) = 3 * x₁ ^ 2 + 10 * x₁ - 152) (hM : M = y₁ - L * x₁) :
    ChordVieta x₁ x₁ (L ^ 2 - 5 - 2 * x₁) L M := by
  rw [equation_shortW_iff] at hE₁
  subst hM
  exact ⟨by ring, by linear_combination hL, by linear_combination -hE₁ + x₁ * hL⟩

theorem addX_shortW (x₁ x₂ ℓ : ℚ) : shortW.addX x₁ x₂ ℓ = ℓ ^ 2 - 5 - x₁ - x₂ := by
  simp only [addX, shortW_a₁, shortW_a₂]
  ring

theorem slope_tangent_eq {x y : ℚ} (hy : y ≠ shortW.negY x y) :
    shortW.slope x x y y * (2 * y) = 3 * x ^ 2 + 10 * x - 152 := by
  have h2y : y - shortW.negY x y = 2 * y := by rw [negY_shortW]; ring
  have h2y' : (2 : ℚ) * y ≠ 0 := by rw [← h2y]; exact sub_ne_zero.mpr hy
  rw [slope_of_Y_ne rfl hy, h2y, div_mul_cancel₀ _ h2y']
  simp only [shortW_a₁, shortW_a₂, shortW_a₄]
  ring

theorem chordVieta_secant_addX {x₁ y₁ x₂ y₂ : ℚ} (hE₁ : shortW.Equation x₁ y₁)
    (hE₂ : shortW.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    ChordVieta x₁ x₂ (shortW.addX x₁ x₂ (shortW.slope x₁ x₂ y₁ y₂))
      (shortW.slope x₁ x₂ y₁ y₂) (y₁ - shortW.slope x₁ x₂ y₁ y₂ * x₁) := by
  have hsub : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hy₂ : y₂ = shortW.slope x₁ x₂ y₁ y₂ * x₂ + (y₁ - shortW.slope x₁ x₂ y₁ y₂ * x₁) := by
    rw [slope_of_X_ne hx]
    field_simp
    ring
  rw [addX_shortW]
  exact chordVieta_of_secant hE₁ hE₂ hx (by ring) hy₂

theorem chordVieta_tangent_addX {x₁ y₁ : ℚ} (hE₁ : shortW.Equation x₁ y₁)
    (hy : y₁ ≠ shortW.negY x₁ y₁) :
    ChordVieta x₁ x₁ (shortW.addX x₁ x₁ (shortW.slope x₁ x₁ y₁ y₁))
      (shortW.slope x₁ x₁ y₁ y₁) (y₁ - shortW.slope x₁ x₁ y₁ y₁ * x₁) := by
  rw [addX_shortW, show shortW.slope x₁ x₁ y₁ y₁ ^ 2 - 5 - x₁ - x₁ =
    shortW.slope x₁ x₁ y₁ y₁ ^ 2 - 5 - 2 * x₁ by ring]
  exact chordVieta_of_tangent hE₁ (slope_tangent_eq hy) rfl

theorem chordVieta_of_add {x₁ y₁ x₂ y₂ : ℚ} (h₁ : shortW.Nonsingular x₁ y₁)
    (h₂ : shortW.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = shortW.negY x₂ y₂)) :
    ChordVieta x₁ x₂ (shortW.addX x₁ x₂ (shortW.slope x₁ x₂ y₁ y₂))
      (shortW.slope x₁ x₂ y₁ y₂) (y₁ - shortW.slope x₁ x₂ y₁ y₂ * x₁) := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ shortW.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    have hy' : y₁ = y₂ := Y_eq_of_Y_ne h₁.1 h₂.1 hx hy
    subst hx
    subst hy'
    exact chordVieta_tangent_addX h₁.1 hy
  · exact chordVieta_secant_addX h₁.1 h₂.1 hx

def dFst (X : ℚ) : ℚ := if X = 12 then 400 else X - 12

def dSnd (X : ℚ) : ℚ := if X = -4 then -144 else X + 4

theorem dFst_of_eq {X : ℚ} (h : X = 12) : dFst X = 400 := if_pos h
theorem dFst_of_ne {X : ℚ} (h : X ≠ 12) : dFst X = X - 12 := if_neg h
theorem dSnd_of_eq {X : ℚ} (h : X = -4) : dSnd X = -144 := if_pos h
theorem dSnd_of_ne {X : ℚ} (h : X ≠ -4) : dSnd X = X + 4 := if_neg h

theorem dFst_ne_zero (X : ℚ) : dFst X ≠ 0 := by
  unfold dFst
  split
  · norm_num
  · exact sub_ne_zero.mpr ‹_›

theorem dSnd_ne_zero (X : ℚ) : dSnd X ≠ 0 := by
  unfold dSnd
  split
  · norm_num
  · rename_i hX
    intro h0
    exact hX (by linarith)

theorem deltaPair_some_fst {X Y : ℚ} {h : shortW.Nonsingular X Y} :
    (deltaPair (.some X Y h)).1 = dFst X := rfl

theorem deltaPair_some_snd {X Y : ℚ} {h : shortW.Nonsingular X Y} :
    (deltaPair (.some X Y h)).2 = dSnd X := rfl

theorem deltaPair_zero_fst : (deltaPair (0 : shortW.Point)).1 = 1 := rfl

theorem deltaPair_zero_snd : (deltaPair (0 : shortW.Point)).2 = 1 := rfl

namespace ChordVieta

variable {x₁ x₂ x₃ L M : ℚ}

theorem exists_dFst_prod_eq_sq (h : ChordVieta x₁ x₂ x₃ L M) :
    ∃ s : ℚ, dFst x₁ * dFst x₂ * dFst x₃ = s ^ 2 := by
  by_cases h1 : x₁ = 12 <;> by_cases h2 : x₂ = 12 <;> by_cases h3 : x₃ = 12
  · exact absurd (h.perm₁.prod_pair_of_twelve h1) (by rw [h2]; norm_num)
  · exact absurd (h.perm₁.prod_pair_of_twelve h1) (by rw [h2]; norm_num)
  · exact absurd (h.prod_pair_of_twelve h3) (by rw [h1]; norm_num)
  · rw [dFst_of_eq h1, dFst_of_ne h2, dFst_of_ne h3]
    exact ⟨400, by linear_combination (400 : ℚ) * h.perm₁.prod_pair_of_twelve h1⟩
  · exact absurd (h.prod_pair_of_twelve h3) (by rw [h2]; norm_num)
  · rw [dFst_of_ne h1, dFst_of_eq h2, dFst_of_ne h3]
    exact ⟨400, by linear_combination (400 : ℚ) * h.perm₂.prod_pair_of_twelve h2⟩
  · rw [dFst_of_ne h1, dFst_of_ne h2, dFst_of_eq h3]
    exact ⟨400, by linear_combination (400 : ℚ) * h.prod_pair_of_twelve h3⟩
  · rw [dFst_of_ne h1, dFst_of_ne h2, dFst_of_ne h3]
    exact ⟨12 * L + M, h.prod_sub_twelve⟩

theorem exists_dSnd_prod_eq_sq (h : ChordVieta x₁ x₂ x₃ L M) :
    ∃ s : ℚ, dSnd x₁ * dSnd x₂ * dSnd x₃ = s ^ 2 := by
  by_cases h1 : x₁ = -4 <;> by_cases h2 : x₂ = -4 <;> by_cases h3 : x₃ = -4
  · exact absurd (h.perm₁.prod_pair_of_neg_four h1) (by rw [h2]; norm_num)
  · exact absurd (h.perm₁.prod_pair_of_neg_four h1) (by rw [h2]; norm_num)
  · exact absurd (h.prod_pair_of_neg_four h3) (by rw [h1]; norm_num)
  · rw [dSnd_of_eq h1, dSnd_of_ne h2, dSnd_of_ne h3]
    exact ⟨144, by linear_combination (-144 : ℚ) * h.perm₁.prod_pair_of_neg_four h1⟩
  · exact absurd (h.prod_pair_of_neg_four h3) (by rw [h2]; norm_num)
  · rw [dSnd_of_ne h1, dSnd_of_eq h2, dSnd_of_ne h3]
    exact ⟨144, by linear_combination (-144 : ℚ) * h.perm₂.prod_pair_of_neg_four h2⟩
  · rw [dSnd_of_ne h1, dSnd_of_ne h2, dSnd_of_eq h3]
    exact ⟨144, by linear_combination (-144 : ℚ) * h.prod_pair_of_neg_four h3⟩
  · rw [dSnd_of_ne h1, dSnd_of_ne h2, dSnd_of_ne h3]
    exact ⟨M - 4 * L, h.prod_add_four⟩

theorem isSqClass_dFst (h : ChordVieta x₁ x₂ x₃ L M) :
    IsSqClass (dFst x₁ * dFst x₂) (dFst x₃) := by
  obtain ⟨s, hs⟩ := h.exists_dFst_prod_eq_sq
  exact isSqClass_mul_of_mul₃_eq_sq (dFst_ne_zero x₁) (dFst_ne_zero x₂) (dFst_ne_zero x₃) hs

theorem isSqClass_dSnd (h : ChordVieta x₁ x₂ x₃ L M) :
    IsSqClass (dSnd x₁ * dSnd x₂) (dSnd x₃) := by
  obtain ⟨s, hs⟩ := h.exists_dSnd_prod_eq_sq
  exact isSqClass_mul_of_mul₃_eq_sq (dSnd_ne_zero x₁) (dSnd_ne_zero x₂) (dSnd_ne_zero x₃) hs

end ChordVieta

theorem deltaPairHom (P Q : shortW.Point) :
    IsSqClass ((deltaPair P).1 * (deltaPair Q).1) (deltaPair (P + Q)).1 ∧
      IsSqClass ((deltaPair P).2 * (deltaPair Q).2) (deltaPair (P + Q)).2 := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero]
    rw [deltaPair_zero_fst, deltaPair_zero_snd]
    exact ⟨by rw [one_mul]; exact isSqClass_self _, by rw [one_mul]; exact isSqClass_self _⟩
  · rw [← Point.zero_def, zero_add]
    rw [deltaPair_zero_fst, deltaPair_zero_snd]
    exact ⟨by rw [one_mul]; exact isSqClass_self _, by rw [one_mul]; exact isSqClass_self _⟩
  · rw [← Point.zero_def, add_zero]
    rw [deltaPair_zero_fst, deltaPair_zero_snd]
    exact ⟨by rw [mul_one]; exact isSqClass_self _, by rw [mul_one]; exact isSqClass_self _⟩
  · by_cases hxy : x₁ = x₂ ∧ y₁ = shortW.negY x₂ y₂
    · obtain ⟨rfl, hy⟩ := hxy
      rw [Point.add_of_Y_eq rfl hy]
      rw [deltaPair_zero_fst, deltaPair_zero_snd, deltaPair_some_fst, deltaPair_some_fst,
        deltaPair_some_snd, deltaPair_some_snd]
      exact ⟨isSqClass_symm one_ne_zero (isSqClass_one_mul_self (dFst_ne_zero x₁)),
        isSqClass_symm one_ne_zero (isSqClass_one_mul_self (dSnd_ne_zero x₁))⟩
    · rw [Point.add_some hxy]
      rw [deltaPair_some_fst, deltaPair_some_fst, deltaPair_some_fst,
        deltaPair_some_snd, deltaPair_some_snd, deltaPair_some_snd]
      exact ⟨(chordVieta_of_add h₁ h₂ hxy).isSqClass_dFst,
        (chordVieta_of_add h₁ h₂ hxy).isSqClass_dSnd⟩

end M4cP2.Hom

open ModularCurve.FifteenA1

theorem solution (P Q : shortW.Point) : IsSqClass ((deltaPair P).1 * (deltaPair Q).1) (deltaPair (P + Q)).1 ∧ IsSqClass ((deltaPair P).2 * (deltaPair Q).2) (deltaPair (P + Q)).2 :=
  M4cP2.Hom.deltaPairHom P Q

end S_ModularCurve_FifteenA1_deltaPairHom
end P2MW
export P2MW.S_ModularCurve_FifteenA1_deltaPairHom (solution)

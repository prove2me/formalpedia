-- Prove2me | solution 1 for LL_DensitySlope517.leaf_two_variation_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:46:30.404513+00:00
-- url     : https://prove2.me/submissions/0fdf9ae2-4efa-4892-852a-49fe931d9ff7

import Mathlib
import Definitions.Def_LL_DensitySlope517_lowerTwoDiscarded

open Classical LL_DensitySlope517 MeasureTheory Set

private noncomputable def F_poly (a b : ℝ) : ℝ :=
  if 1 ≤ a + 3 * b then 1 / (a * b * (99 / 100 - a - b) * (1 - a - b))
  else if 99 / 100 ≤ a + 3 * b then (107 / 200) / (a * b ^ 3)
  else (7 / 200) / (a * b ^ 3)

private noncomputable def G_poly (ε a b : ℝ) : ℝ :=
  if lowerTwoDiscarded ε a b then F_poly a b else 0

private lemma lowerTwoDiscarded_mono {ε : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) {a b : ℝ} :
    lowerTwoDiscarded ε a b → lowerTwoDiscarded (1 / 10 ^ 8) a b := by
  dsimp only [lowerTwoDiscarded, upperPairRegion]
  rintro ⟨h1, h2, h3, h4, hnot⟩
  refine ⟨by linarith, h2, h3, h4, ?_⟩
  intro hor
  apply hnot
  rcases hor with hA | hB | hC | hD
  · left; linarith
  · right; left; exact ⟨by linarith [hB.1], by linarith [hB.2]⟩
  · right; right; left; exact ⟨by linarith [hC.1], by linarith [hC.2.1], by linarith [hC.2.2]⟩
  · right; right; right
    rcases hD with ⟨hn1, hn2, _, hn4, hdisj⟩
    refine ⟨hn1, hn2, h1, by linarith, ?_⟩
    rcases hdisj with hR | hP1 | hP2
    · left; exact ⟨by linarith [hR.1], by linarith [hR.2]⟩
    · right; left; rw [abs_le] at hP1 ⊢; constructor <;> linarith
    · right; right; rw [abs_le] at hP2 ⊢; constructor <;> linarith

private lemma F_poly_nonneg_and_le {a b : ℝ} (h : lowerTwoDiscarded (1 / 10 ^ 8) a b) :
    0 ≤ F_poly a b ∧ F_poly a b ≤ 10 ^ 6 := by
  dsimp only [lowerTwoDiscarded] at h
  rcases h with ⟨hb_lo, hba, ha_hi, hab2, _⟩
  have hb10 : (1 / 10 : ℝ) ≤ b := by linarith
  have ha10 : (1 / 10 : ℝ) ≤ a := by linarith
  have h99 : (9 / 100 : ℝ) ≤ 99 / 100 - a - b := by linarith
  have h1ab : (1 / 10 : ℝ) ≤ 1 - a - b := by linarith
  dsimp only [F_poly]
  split_ifs
  · constructor
    · positivity
    · have hd : (1 / 10 : ℝ) * (1 / 10) * (9 / 100) * (1 / 10) ≤ a * b * (99 / 100 - a - b) * (1 - a - b) := by
        gcongr
      rw [div_le_iff₀ (by positivity)]
      linarith
  · constructor
    · positivity
    · have hd : (1 / 10 : ℝ) * (1 / 10) ^ 3 ≤ a * b ^ 3 := by gcongr
      rw [div_le_iff₀ (by positivity)]
      linarith
  · constructor
    · positivity
    · have hd : (1 / 10 : ℝ) * (1 / 10) ^ 3 ≤ a * b ^ 3 := by gcongr
      rw [div_le_iff₀ (by positivity)]
      linarith

private lemma measurable_G_poly (ε : ℝ) : Measurable (fun p : ℝ × ℝ => G_poly ε p.1 p.2) := by
  have m_le : ∀ {f g : ℝ × ℝ → ℝ}, Continuous f → Continuous g →
      MeasurableSet {p : ℝ × ℝ | f p ≤ g p} := fun hf hg => (isClosed_le hf hg).measurableSet
  have h_upper : MeasurableSet {p : ℝ × ℝ | upperPairRegion ε p.1 p.2} := by
    unfold upperPairRegion
    refine (m_le continuous_snd continuous_fst).inter ?_
    refine (m_le continuous_fst continuous_const).inter ?_
    refine (m_le continuous_const continuous_snd).inter ?_
    refine (m_le continuous_snd continuous_const).inter ?_
    refine ((m_le (by fun_prop) continuous_fst).inter (m_le continuous_fst continuous_const)).union ?_
    refine (m_le (by fun_prop) continuous_const).union ?_
    exact m_le (by fun_prop) continuous_const
  have h_lower : MeasurableSet {p : ℝ × ℝ | lowerTwoDiscarded ε p.1 p.2} := by
    unfold lowerTwoDiscarded
    refine (m_le continuous_const continuous_snd).inter ?_
    refine (m_le continuous_snd continuous_fst).inter ?_
    refine (m_le continuous_fst continuous_const).inter ?_
    refine (m_le (by fun_prop) continuous_const).inter ?_
    refine MeasurableSet.compl ?_
    refine (m_le (by fun_prop) continuous_const).union ?_
    refine ((m_le (by fun_prop) continuous_const).inter (m_le continuous_const (by fun_prop))).union ?_
    refine ((m_le continuous_snd continuous_const).inter ((m_le (by fun_prop) continuous_const).inter (m_le continuous_const (by fun_prop)))).union ?_
    exact h_upper
  have h_F : Measurable (fun p : ℝ × ℝ => F_poly p.1 p.2) := by
    unfold F_poly
    refine Measurable.ite (m_le continuous_const (by fun_prop)) (by fun_prop) ?_
    exact Measurable.ite (m_le continuous_const (by fun_prop)) (by fun_prop) (by fun_prop)
  exact Measurable.ite h_lower h_F measurable_const

private inductive RT
  | z : RT
  | l (u : Nat) : RT
  | a (x y : RT) : RT
  | b (x y : RT) : RT

private def S_scale : Int := 5242880

private def outI (xa0 xa1 xb0 xb1 : Int) : Bool :=
  300000000 * xb1 < 37497197 * S_scale ||
  xa1 < xb0 ||
  2 * xa0 > S_scale ||
  xa0 + 2 * xb0 > S_scale ||
  150000000 * (xa1 + 2 * xb1) ≤ 84373897 * S_scale ||
  (100000000 * (4 * xa1 + 7 * xb1) ≤ 212497999 * S_scale && 150004807 * S_scale ≤ 400000000 * (xa0 + xb0)) ||
  (1100000000 * xb1 ≤ 249927989 * S_scale && 100000000 * (4 * xa1 + 5 * xb1) ≤ 212497999 * S_scale && 105001763 * S_scale ≤ 240000000 * (xa0 + xb0)) ||
  (xb1 ≤ xa0 && 2 * xa1 ≤ S_scale && 37497197 * S_scale ≤ 300000000 * xb0 && 1100000000 * xb1 ≤ 249927989 * S_scale &&
    ((100000000 * (2 * xb1 - xa0) + (-12497999) * S_scale ≤ 0 && 1100000000 * xa1 ≤ 249927989 * S_scale) ||
     (-12497999 * S_scale ≤ 100000000 * (4 * xa0 + 3 * xb0 - 2 * S_scale) && 100000000 * (4 * xa1 + 3 * xb1 - 2 * S_scale) ≤ 12497999 * S_scale) ||
     (-12497999 * S_scale ≤ 100000000 * (4 * xa0 + xb0 - 2 * S_scale) && 100000000 * (4 * xa1 + xb1 - 2 * S_scale) ≤ 12497999 * S_scale)))

private def leafI (xa0 xa1 xb0 xb1 : Int) (u : Nat) : Bool :=
  let ui : Int := (u : Int)
  let xd3 : Int := max (99 * S_scale - 100 * xa1 - 100 * xb1) (100 * xb0 - S_scale)
  let xd4 : Int := max (S_scale - xa1 - xb1) xb0
  let ok1 := !(xa1 + 3 * xb1 ≥ S_scale) ||
    (0 < xa0 && 0 < xb0 && 0 < xd3 && 0 < xd4 &&
     1000 * 100 * S_scale^4 ≤ ui * xa0 * xb0 * xd3 * xd4)
  let ok2 := !(100 * (xa1 + 3 * xb1) ≥ 99 * S_scale && xa0 + 3 * xb0 < S_scale) ||
    (0 < xa0 && 0 < xb0 && 1000 * 107 * S_scale^4 ≤ 200 * ui * xa0 * xb0^3)
  let ok3 := !(100 * (xa0 + 3 * xb0) < 99 * S_scale) ||
    (0 < xa0 && 0 < xb0 && 1000 * 7 * S_scale^4 ≤ 200 * ui * xa0 * xb0^3)
  ok1 && ok2 && ok3

private def checkI : RT → Int → Int → Int → Int → Bool
  | .z, xa0, xa1, xb0, xb1 => outI xa0 xa1 xb0 xb1
  | .l u, xa0, xa1, xb0, xb1 => leafI xa0 xa1 xb0 xb1 u
  | .a l r, xa0, xa1, xb0, xb1 =>
    let xam := (xa0 + xa1) / 2
    (xa0 + xa1) % 2 == 0 && checkI l xa0 xam xb0 xb1 && checkI r xam xa1 xb0 xb1
  | .b l r, xa0, xa1, xb0, xb1 =>
    let xbm := (xb0 + xb1) / 2
    (xb0 + xb1) % 2 == 0 && checkI l xa0 xa1 xb0 xbm && checkI r xa0 xa1 xbm xb1

private def sumI : RT → Int → Int → Int → Int → Int
  | .z, _, _, _, _ => 0
  | .l u, xa0, xa1, xb0, xb1 => (u : Int) * (xa1 - xa0) * (xb1 - xb0)
  | .a l r, xa0, xa1, xb0, xb1 =>
    let xam := (xa0 + xa1) / 2
    sumI l xa0 xam xb0 xb1 + sumI r xam xa1 xb0 xb1
  | .b l r, xa0, xa1, xb0, xb1 =>
    let xbm := (xb0 + xb1) / 2
    sumI l xa0 xa1 xb0 xbm + sumI r xa0 xa1 xbm xb1

private lemma outI_sound {xa0 xa1 xb0 xb1 : Int} (hout : outI xa0 xa1 xb0 xb1 = true)
    {a b : ℝ} (ha0 : (xa0 : ℝ) / S_scale ≤ a) (ha1 : a ≤ (xa1 : ℝ) / S_scale)
    (hb0 : (xb0 : ℝ) / S_scale ≤ b) (hb1 : b ≤ (xb1 : ℝ) / S_scale) :
    ¬ lowerTwoDiscarded (1 / 10 ^ 8) a b := by
  have hS : (0 : ℝ) < (S_scale : ℝ) := by norm_num [S_scale]
  have ha0' : (xa0 : ℝ) ≤ a * S_scale := (div_le_iff₀ hS).mp ha0
  have ha1' : a * S_scale ≤ (xa1 : ℝ) := (le_div_iff₀ hS).mp ha1
  have hb0' : (xb0 : ℝ) ≤ b * S_scale := (div_le_iff₀ hS).mp hb0
  have hb1' : b * S_scale ≤ (xb1 : ℝ) := (le_div_iff₀ hS).mp hb1
  dsimp only [outI] at hout
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hout
  intro hlow
  dsimp only [lowerTwoDiscarded, upperPairRegion] at hlow
  rcases hlow with ⟨h1, h2, h3, h4, hnot⟩
  rcases hout with ((((((c1 | c2) | c3) | c4) | c5) | ⟨c6a, c6b⟩) | ⟨⟨c7a, c7b⟩, c7c⟩) | ⟨⟨⟨⟨c8a, c8b⟩, c8c⟩, c8d⟩, c8e⟩
  · have h_1 : (300000000 * xb1 : ℝ) < 37497197 * S_scale := by
      have := Int.cast_lt (R := ℝ).mpr c1; push_cast at this; exact this
    nlinarith
  · have h_2 : (xa1 : ℝ) < xb0 := Int.cast_lt (R := ℝ).mpr c2
    nlinarith
  · have h_3 : (2 * xa0 : ℝ) > S_scale := by
      have := Int.cast_lt (R := ℝ).mpr c3; push_cast at this; exact this
    nlinarith
  · have h_4 : (xa0 + 2 * xb0 : ℝ) > S_scale := by
      have := Int.cast_lt (R := ℝ).mpr c4; push_cast at this; exact this
    nlinarith
  · have h_5 : (150000000 * (xa1 + 2 * xb1) : ℝ) ≤ 84373897 * S_scale := by
      have := Int.cast_le (R := ℝ).mpr c5; push_cast at this; exact this
    apply hnot; left; nlinarith
  · have h6a : (100000000 * (4 * xa1 + 7 * xb1) : ℝ) ≤ 212497999 * S_scale := by
      have := Int.cast_le (R := ℝ).mpr c6a; push_cast at this; exact this
    have h6b : (150004807 * S_scale : ℝ) ≤ 400000000 * (xa0 + xb0) := by
      have := Int.cast_le (R := ℝ).mpr c6b; push_cast at this; exact this
    apply hnot; right; left; constructor <;> nlinarith
  · have h7a : (1100000000 * xb1 : ℝ) ≤ 249927989 * S_scale := by
      have := Int.cast_le (R := ℝ).mpr c7a; push_cast at this; exact this
    have h7b : (100000000 * (4 * xa1 + 5 * xb1) : ℝ) ≤ 212497999 * S_scale := by
      have := Int.cast_le (R := ℝ).mpr c7b; push_cast at this; exact this
    have h7c : (105001763 * S_scale : ℝ) ≤ 240000000 * (xa0 + xb0) := by
      have := Int.cast_le (R := ℝ).mpr c7c; push_cast at this; exact this
    apply hnot; right; right; left; exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · apply hnot; right; right; right
    have h8a : (xb1 : ℝ) ≤ xa0 := Int.cast_le (R := ℝ).mpr c8a
    have h8b : (2 * xa1 : ℝ) ≤ S_scale := by
      have := Int.cast_le (R := ℝ).mpr c8b; push_cast at this; exact this
    have h8c : (37497197 * S_scale : ℝ) ≤ 300000000 * xb0 := by
      have := Int.cast_le (R := ℝ).mpr c8c; push_cast at this; exact this
    have h8d : (1100000000 * xb1 : ℝ) ≤ 249927989 * S_scale := by
      have := Int.cast_le (R := ℝ).mpr c8d; push_cast at this; exact this
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, ?_⟩
    rcases c8e with (⟨d1, d2⟩ | ⟨d1, d2⟩) | ⟨d1, d2⟩
    · have hd1 : (100000000 * (2 * xb1 - xa0) + (-12497999) * S_scale : ℝ) ≤ 0 := by
        have := Int.cast_le (R := ℝ).mpr d1; push_cast at this; exact this
      have hd2 : (1100000000 * xa1 : ℝ) ≤ 249927989 * S_scale := by
        have := Int.cast_le (R := ℝ).mpr d2; push_cast at this; exact this
      left; constructor <;> nlinarith
    · have hd1 : (-12497999 * S_scale : ℝ) ≤ 100000000 * (4 * xa0 + 3 * xb0 - 2 * S_scale) := by
        have := Int.cast_le (R := ℝ).mpr d1; push_cast at this; exact this
      have hd2 : (100000000 * (4 * xa1 + 3 * xb1 - 2 * S_scale) : ℝ) ≤ 12497999 * S_scale := by
        have := Int.cast_le (R := ℝ).mpr d2; push_cast at this; exact this
      right; left; rw [abs_le]; constructor <;> nlinarith
    · have hd1 : (-12497999 * S_scale : ℝ) ≤ 100000000 * (4 * xa0 + xb0 - 2 * S_scale) := by
        have := Int.cast_le (R := ℝ).mpr d1; push_cast at this; exact this
      have hd2 : (100000000 * (4 * xa1 + xb1 - 2 * S_scale) : ℝ) ≤ 12497999 * S_scale := by
        have := Int.cast_le (R := ℝ).mpr d2; push_cast at this; exact this
      right; right; rw [abs_le]; constructor <;> nlinarith

private lemma leafI_sound {xa0 xa1 xb0 xb1 : Int} {u : Nat} (hleaf : leafI xa0 xa1 xb0 xb1 u = true)
    {a b : ℝ} (ha0 : (xa0 : ℝ) / S_scale ≤ a) (ha1 : a ≤ (xa1 : ℝ) / S_scale)
    (hb0 : (xb0 : ℝ) / S_scale ≤ b) (hb1 : b ≤ (xb1 : ℝ) / S_scale)
    (hlow : lowerTwoDiscarded (1 / 10 ^ 8) a b) :
    F_poly a b ≤ (u : ℝ) / 1000 := by
  have hS : (0 : ℝ) < (S_scale : ℝ) := by norm_num [S_scale]
  have ha0' : (xa0 : ℝ) ≤ a * S_scale := (div_le_iff₀ hS).mp ha0
  have ha1' : a * S_scale ≤ (xa1 : ℝ) := (le_div_iff₀ hS).mp ha1
  have hb0' : (xb0 : ℝ) ≤ b * S_scale := (div_le_iff₀ hS).mp hb0
  have hb1' : b * S_scale ≤ (xb1 : ℝ) := (le_div_iff₀ hS).mp hb1
  dsimp only [lowerTwoDiscarded] at hlow
  have hab2 : a + 2 * b ≤ 1 := hlow.2.2.2.1
  dsimp only [leafI] at hleaf
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, not_le, not_lt] at hleaf
  rcases hleaf with ⟨⟨hok1, hok2⟩, hok3⟩
  dsimp only [F_poly]
  split_ifs with hbr1 hbr2
  · have hcond : S_scale ≤ xa1 + 3 * xb1 := by
      rw [← Int.cast_le (R := ℝ)]
      push_cast; nlinarith
    rcases hok1 with _ | ⟨⟨⟨⟨hxa0, hxb0⟩, hxd3⟩, hxd4⟩, hineq⟩
    · exact False.elim (by omega)
    · have hxa0R : (0 : ℝ) < xa0 := Int.cast_pos.mpr hxa0
      have hxb0R : (0 : ℝ) < xb0 := Int.cast_pos.mpr hxb0
      set xd3 : Int := max (99 * S_scale - 100 * xa1 - 100 * xb1) (100 * xb0 - S_scale)
      set xd4 : Int := max (S_scale - xa1 - xb1) xb0
      have hxd3R : (0 : ℝ) < xd3 := Int.cast_pos.mpr hxd3
      have hxd4R : (0 : ℝ) < xd4 := Int.cast_pos.mpr hxd4
      have hineqR : (1000 * 100 * (S_scale : ℝ) ^ 4) ≤ (u : ℝ) * xa0 * xb0 * xd3 * xd4 := by
        have := Int.cast_le (R := ℝ).mpr hineq; push_cast at this; linarith
      have hd3_ge : (xd3 : ℝ) / (100 * S_scale) ≤ 99 / 100 - a - b := by
        rw [div_le_iff₀ (by positivity)]
        have : (xd3 : ℝ) = max ((99 * S_scale - 100 * xa1 - 100 * xb1 : Int) : ℝ) ((100 * xb0 - S_scale : Int) : ℝ) := by
          push_cast [xd3]; rfl
        rw [this, max_le_iff]
        push_cast
        constructor <;> nlinarith
      have hd4_ge : (xd4 : ℝ) / S_scale ≤ 1 - a - b := by
        rw [div_le_iff₀ hS]
        have : (xd4 : ℝ) = max ((S_scale - xa1 - xb1 : Int) : ℝ) (xb0 : ℝ) := by
          push_cast [xd4]; rfl
        rw [this, max_le_iff]
        push_cast
        constructor <;> nlinarith
      have ha_pos : 0 < a := lt_of_lt_of_le (div_pos hxa0R hS) ha0
      have hb_pos : 0 < b := lt_of_lt_of_le (div_pos hxb0R hS) hb0
      have hd3_pos : 0 < (xd3 : ℝ) / (100 * S_scale) := div_pos hxd3R (by positivity)
      have hd4_pos : 0 < (xd4 : ℝ) / S_scale := div_pos hxd4R hS
      have h99_pos : 0 < 99 / 100 - a - b := lt_of_lt_of_le hd3_pos hd3_ge
      have h1_pos : 0 < 1 - a - b := lt_of_lt_of_le hd4_pos hd4_ge
      have hden_le : (xa0 : ℝ) / S_scale * ((xb0 : ℝ) / S_scale) * ((xd3 : ℝ) / (100 * S_scale)) * ((xd4 : ℝ) / S_scale) ≤
          a * b * (99 / 100 - a - b) * (1 - a - b) := by
        have h12 : (xa0 : ℝ) / S_scale * ((xb0 : ℝ) / S_scale) ≤ a * b :=
          mul_le_mul ha0 hb0 (div_nonneg hxb0R.le hS.le) ha_pos.le
        have h123 : (xa0 : ℝ) / S_scale * ((xb0 : ℝ) / S_scale) * ((xd3 : ℝ) / (100 * S_scale)) ≤
            a * b * (99 / 100 - a - b) :=
          mul_le_mul h12 hd3_ge hd3_pos.le (mul_nonneg ha_pos.le hb_pos.le)
        exact mul_le_mul h123 hd4_ge hd4_pos.le (mul_nonneg (mul_nonneg ha_pos.le hb_pos.le) h99_pos.le)
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hmul : (1000 : ℝ) ≤ (u : ℝ) * ((xa0 : ℝ) / S_scale * ((xb0 : ℝ) / S_scale) * ((xd3 : ℝ) / (100 * S_scale)) * ((xd4 : ℝ) / S_scale)) := by
        rw [← sub_nonneg]
        have : (u : ℝ) * ((xa0 : ℝ) / S_scale * ((xb0 : ℝ) / S_scale) * ((xd3 : ℝ) / (100 * S_scale)) * ((xd4 : ℝ) / S_scale)) - 1000 =
            ((u : ℝ) * xa0 * xb0 * xd3 * xd4 - 1000 * 100 * S_scale ^ 4) / (100 * S_scale ^ 4) := by
          field_simp
        rw [this]
        exact div_nonneg (by linarith) (by positivity)
      nlinarith
  · have hcond1 : 99 * S_scale ≤ 100 * (xa1 + 3 * xb1) := by
      rw [← Int.cast_le (R := ℝ)]
      push_cast; nlinarith
    have hcond2 : xa0 + 3 * xb0 < S_scale := by
      rw [← Int.cast_lt (R := ℝ)]
      push_cast; nlinarith
    rcases hok2 with h_absurd | ⟨⟨hxa0, hxb0⟩, hineq⟩
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le, not_lt] at h_absurd
      omega
    · have hxa0R : (0 : ℝ) < xa0 := Int.cast_pos.mpr hxa0
      have hxb0R : (0 : ℝ) < xb0 := Int.cast_pos.mpr hxb0
      have ha_pos : 0 < a := lt_of_lt_of_le (div_pos hxa0R hS) ha0
      have hb_pos : 0 < b := lt_of_lt_of_le (div_pos hxb0R hS) hb0
      have hineqR : (1000 * 107 * (S_scale : ℝ) ^ 4) ≤ 200 * (u : ℝ) * xa0 * xb0 ^ 3 := by
        have := Int.cast_le (R := ℝ).mpr hineq; push_cast at this; linarith
      have hden_le : (xa0 : ℝ) / S_scale * ((xb0 : ℝ) / S_scale) ^ 3 ≤ a * b ^ 3 := by
        have hb3 : ((xb0 : ℝ) / S_scale) ^ 3 ≤ b ^ 3 :=
          pow_le_pow_left₀ (div_nonneg hxb0R.le hS.le) hb0 3
        exact mul_le_mul ha0 hb3 (pow_nonneg (div_nonneg hxb0R.le hS.le) 3) ha_pos.le
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hmul : (1000 : ℝ) * (107 / 200) ≤ (u : ℝ) * ((xa0 : ℝ) / S_scale * ((xb0 : ℝ) / S_scale) ^ 3) := by
        rw [← sub_nonneg]
        have : (u : ℝ) * ((xa0 : ℝ) / S_scale * ((xb0 : ℝ) / S_scale) ^ 3) - 1000 * (107 / 200) =
            (200 * (u : ℝ) * xa0 * xb0 ^ 3 - 1000 * 107 * S_scale ^ 4) / (200 * S_scale ^ 4) := by
          field_simp
        rw [this]
        exact div_nonneg (by linarith) (by positivity)
      nlinarith
  · have hcond : 100 * (xa0 + 3 * xb0) < 99 * S_scale := by
      rw [← Int.cast_lt (R := ℝ)]
      push_cast; nlinarith
    rcases hok3 with _ | ⟨⟨hxa0, hxb0⟩, hineq⟩
    · exact False.elim (by omega)
    · have hxa0R : (0 : ℝ) < xa0 := Int.cast_pos.mpr hxa0
      have hxb0R : (0 : ℝ) < xb0 := Int.cast_pos.mpr hxb0
      have ha_pos : 0 < a := lt_of_lt_of_le (div_pos hxa0R hS) ha0
      have hb_pos : 0 < b := lt_of_lt_of_le (div_pos hxb0R hS) hb0
      have hineqR : (1000 * 7 * (S_scale : ℝ) ^ 4) ≤ 200 * (u : ℝ) * xa0 * xb0 ^ 3 := by
        have := Int.cast_le (R := ℝ).mpr hineq; push_cast at this; linarith
      have hden_le : (xa0 : ℝ) / S_scale * ((xb0 : ℝ) / S_scale) ^ 3 ≤ a * b ^ 3 := by
        have hb3 : ((xb0 : ℝ) / S_scale) ^ 3 ≤ b ^ 3 :=
          pow_le_pow_left₀ (div_nonneg hxb0R.le hS.le) hb0 3
        exact mul_le_mul ha0 hb3 (pow_nonneg (div_nonneg hxb0R.le hS.le) 3) ha_pos.le
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hmul : (1000 : ℝ) * (7 / 200) ≤ (u : ℝ) * ((xa0 : ℝ) / S_scale * ((xb0 : ℝ) / S_scale) ^ 3) := by
        rw [← sub_nonneg]
        have : (u : ℝ) * ((xa0 : ℝ) / S_scale * ((xb0 : ℝ) / S_scale) ^ 3) - 1000 * (7 / 200) =
            (200 * (u : ℝ) * xa0 * xb0 ^ 3 - 1000 * 7 * S_scale ^ 4) / (200 * S_scale ^ 4) := by
          field_simp
        rw [this]
        exact div_nonneg (by linarith) (by positivity)
      nlinarith

private lemma integral_le_sumI (ε : ℝ) (hε8 : ε ≤ 1 / 10 ^ 8) (t : RT) :
    ∀ (xa0 xa1 xb0 xb1 : Int), xa0 ≤ xa1 → xb0 ≤ xb1 →
      checkI t xa0 xa1 xb0 xb1 = true →
      IntegrableOn (fun p : ℝ × ℝ => G_poly ε p.1 p.2)
        (Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale)) →
      ∫ p in Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale),
        G_poly ε p.1 p.2 ≤ ((sumI t xa0 xa1 xb0 xb1 : ℝ) / (1000 * (S_scale : ℝ) ^ 2)) := by
  have hS : (0 : ℝ) < S_scale := by norm_num [S_scale]
  induction t with
  | z =>
    intro xa0 xa1 xb0 xb1 _ _ hchk _
    dsimp only [sumI]
    simp only [Int.cast_zero, zero_div]
    have hzero : ∀ p ∈ Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale),
        G_poly ε p.1 p.2 = 0 := by
      rintro ⟨a, b⟩ ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩
      have hnot := outI_sound hchk ha0.le ha1 hb0.le hb1
      dsimp only [G_poly]
      rw [if_neg]
      exact fun h => hnot (lowerTwoDiscarded_mono hε8 h)
    rw [setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioc) hzero]
    simp
  | l u =>
    intro xa0 xa1 xb0 xb1 hxa hxb hchk hint
    have haR : (xa0 : ℝ) / S_scale ≤ (xa1 : ℝ) / S_scale := by gcongr
    have hbR : (xb0 : ℝ) / S_scale ≤ (xb1 : ℝ) / S_scale := by gcongr
    have hle : ∀ p ∈ Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale),
        G_poly ε p.1 p.2 ≤ (u : ℝ) / 1000 := by
      rintro ⟨a, b⟩ ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩
      dsimp only [G_poly]
      split_ifs with h
      · exact leafI_sound hchk ha0.le ha1 hb0.le hb1 (lowerTwoDiscarded_mono hε8 h)
      · positivity
    have hconst_int : IntegrableOn (fun _ : ℝ × ℝ => (u : ℝ) / 1000)
        (Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale)) :=
      integrableOn_const (by rw [Measure.volume_eq_prod, Measure.prod_prod]; exact (ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top).ne)
    calc ∫ p in Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale),
          G_poly ε p.1 p.2
      _ ≤ ∫ _ in Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale),
          ((u : ℝ) / 1000) := setIntegral_mono_on hint hconst_int (measurableSet_Ioc.prod measurableSet_Ioc) hle
      _ = ((sumI (.l u) xa0 xa1 xb0 xb1 : Int) : ℝ) / (1000 * (S_scale : ℝ) ^ 2) := by
          dsimp only [sumI]
          rw [setIntegral_const, smul_eq_mul, Measure.volume_eq_prod, Measure.real_def, Measure.prod_prod,
            ENNReal.toReal_mul, ← Measure.real_def, ← Measure.real_def,
            Real.volume_real_Ioc_of_le haR, Real.volume_real_Ioc_of_le hbR]
          push_cast
          field_simp
  | a l r ihl ihr =>
    intro xa0 xa1 xb0 xb1 hxa hxb hchk hint
    dsimp only [checkI, sumI] at hchk ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    rcases hchk with ⟨⟨hmod, hl⟩, hr⟩
    set xam := (xa0 + xa1) / 2
    have hxa0m : xa0 ≤ xam := by omega
    have hxam1 : xam ≤ xa1 := by omega
    have hsplit : Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) =
        Ioc ((xa0 : ℝ) / S_scale) ((xam : ℝ) / S_scale) ∪ Ioc ((xam : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) :=
      (Ioc_union_Ioc_eq_Ioc (by gcongr) (by gcongr)).symm
    have hprod : Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale) =
        (Ioc ((xa0 : ℝ) / S_scale) ((xam : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale)) ∪
        (Ioc ((xam : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale)) := by
      rw [hsplit, union_prod]
    have hdisj : Disjoint
        (Ioc ((xa0 : ℝ) / S_scale) ((xam : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale))
        (Ioc ((xam : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale)) := by
      rw [Set.disjoint_iff]
      rintro ⟨a, _⟩ ⟨⟨⟨_, ha1⟩, _⟩, ⟨⟨ha2, _⟩, _⟩⟩
      linarith
    have hintl : IntegrableOn (fun p : ℝ × ℝ => G_poly ε p.1 p.2)
        (Ioc ((xa0 : ℝ) / S_scale) ((xam : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale)) :=
      hint.mono_set (hprod ▸ subset_union_left)
    have hintr : IntegrableOn (fun p : ℝ × ℝ => G_poly ε p.1 p.2)
        (Ioc ((xam : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale)) :=
      hint.mono_set (hprod ▸ subset_union_right)
    rw [hprod, setIntegral_union hdisj (measurableSet_Ioc.prod measurableSet_Ioc) hintl hintr]
    have h1 := ihl xa0 xam xb0 xb1 hxa0m hxb hl hintl
    have h2 := ihr xam xa1 xb0 xb1 hxam1 hxb hr hintr
    rw [Int.cast_add, add_div]
    exact add_le_add h1 h2
  | b l r ihl ihr =>
    intro xa0 xa1 xb0 xb1 hxa hxb hchk hint
    dsimp only [checkI, sumI] at hchk ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    rcases hchk with ⟨⟨hmod, hl⟩, hr⟩
    set xbm := (xb0 + xb1) / 2
    have hxb0m : xb0 ≤ xbm := by omega
    have hxbm1 : xbm ≤ xb1 := by omega
    have hsplit : Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale) =
        Ioc ((xb0 : ℝ) / S_scale) ((xbm : ℝ) / S_scale) ∪ Ioc ((xbm : ℝ) / S_scale) ((xb1 : ℝ) / S_scale) :=
      (Ioc_union_Ioc_eq_Ioc (by gcongr) (by gcongr)).symm
    have hprod : Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xb1 : ℝ) / S_scale) =
        (Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xbm : ℝ) / S_scale)) ∪
        (Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xbm : ℝ) / S_scale) ((xb1 : ℝ) / S_scale)) := by
      rw [hsplit, prod_union]
    have hdisj : Disjoint
        (Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xbm : ℝ) / S_scale))
        (Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xbm : ℝ) / S_scale) ((xb1 : ℝ) / S_scale)) := by
      rw [Set.disjoint_iff]
      rintro ⟨_, b⟩ ⟨⟨_, ⟨_, hb1⟩⟩, ⟨_, ⟨hb2, _⟩⟩⟩
      linarith
    have hintl : IntegrableOn (fun p : ℝ × ℝ => G_poly ε p.1 p.2)
        (Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xb0 : ℝ) / S_scale) ((xbm : ℝ) / S_scale)) :=
      hint.mono_set (hprod ▸ subset_union_left)
    have hintr : IntegrableOn (fun p : ℝ × ℝ => G_poly ε p.1 p.2)
        (Ioc ((xa0 : ℝ) / S_scale) ((xa1 : ℝ) / S_scale) ×ˢ Ioc ((xbm : ℝ) / S_scale) ((xb1 : ℝ) / S_scale)) :=
      hint.mono_set (hprod ▸ subset_union_right)
    rw [hprod, setIntegral_union hdisj (measurableSet_Ioc.prod measurableSet_Ioc) hintl hintr]
    have h1 := ihl xa0 xa1 xb0 xbm hxa hxb0m hl hintl
    have h2 := ihr xa0 xa1 xbm xb1 hxa hxbm1 hr hintr
    rw [Int.cast_add, add_div]
    exact add_le_add h1 h2

private def certTree : RT := (.b (.b (.b (.a (.a .z (.b .z (.a .z (.b (.a .z (.b .z (.a .z (.b (.a .z (.l 52698)) (.b (.l 50174) (.l 48464)))))) (.b (.a .z (.b (.a (.b .z (.a .z (.a .z (.l 45767)))) (.l 46830)) (.a (.l 45767) (.l 43777)))) (.a (.a .z (.b (.b .z (.a .z (.b .z (.a .z (.a .z (.l 41051)))))) (.l 42082))) (.b (.a (.l 42847) (.l 40984)) (.a (.l 40170) (.a (.l 38423) .z))))))))) (.b (.b .z (.b .z (.b .z (.b .z (.b .z (.b .z (.b .z (.b .z (.b .z (.b .z (.b .z (.l 59751)))))))))))) (.a (.b (.a (.a (.b (.b (.a (.a .z (.l 58515)) (.a (.a (.a (.a (.a (.a (.l 57344) .z) .z) .z) .z) .z) .z)) (.a (.b (.l 55469) (.l 53488)) .z)) (.a (.b (.b (.l 51600) (.a (.l 49801) .z)) (.a (.l 48083) .z)) .z)) .z) (.b (.b (.a (.a .z (.a .z (.l 48597))) (.a (.a (.a (.a (.a (.a (.l 47787) .z) .z) .z) .z) .z) .z)) (.a (.a .z (.b (.a .z (.l 45127)) (.l 44266))) .z)) (.a (.b (.a .z (.l 42704)) (.a (.a .z (.l 40491)) (.a (.l 39793) .z))) .z))) (.a (.b (.a (.a (.a (.a (.a (.a (.a (.a (.l 44879) .z) .z) .z) .z) .z) .z) .z) .z) (.a .z (.a .z (.b (.a .z (.a .z (.l 33969))) (.l 32731))))) (.a (.b (.b (.a (.l 38468) (.a (.l 37141) .z)) (.a (.l 35960) (.a (.a (.a (.b (.l 34720) .z) .z) .z) .z))) (.a (.b (.l 33665) (.l 31562)) .z)) .z))) (.b (.b (.a (.a .z (.b (.b (.l 42165) (.a (.a .z (.a .z (.l 39746))) .z)) (.a (.a .z (.l 38587)) .z))) (.a .z (.a .z (.a .z (.a .z (.l 36066)))))) (.a (.a .z (.a (.b (.l 36424) (.l 33941)) .z)) (.a .z (.a .z (.a .z (.b (.a .z (.l 31155)) (.l 29215))))))) (.b (.a (.b (.a .z (.a (.l 31679) .z)) (.a (.a .z (.a .z (.a .z (.l 29833)))) (.a (.l 29614) .z))) (.a .z (.a .z (.a .z (.b (.l 27268) (.l 25491)))))) (.a (.b (.a (.a .z (.a .z (.l 28138))) (.a (.l 27724) .z)) (.a (.a .z (.l 26780)) (.a (.l 25992) .z))) (.a .z (.a .z (.b (.a .z (.l 23864)) (.l 22660)))))))))) (.a (.a (.b .z (.a .z (.b (.a .z (.b (.a .z (.b .z (.a .z (.b .z (.a .z .z))))) (.a (.b .z (.a .z (.b .z (.a .z (.b .z (.a .z (.l 28916))))))) (.b (.l 31350) (.a (.l 29783) .z))))) (.a .z (.b (.a (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.l 28348))))))) (.b (.l 28319) (.l 26949))) (.a .z (.b (.l 25666) (.a .z (.l 23674))))))))) (.b (.b (.a (.a .z (.b (.a .z .z) (.b .z (.a .z (.a .z (.l 35471)))))) (.b (.a (.b (.a .z (.l 39507)) (.a (.a .z (.l 38043)) (.l 37137))) (.b (.a (.l 37711) (.a (.a (.a (.a (.a (.l 36071) .z) .z) .z) .z) .z)) (.a (.l 35449) .z))) (.a (.b (.a (.l 36701) (.l 34953)) (.a (.l 34584) (.l 32937))) (.a (.b (.l 33364) (.a (.l 31440) .z)) .z)))) (.a (.a (.b (.a .z (.a .z .z)) (.a (.b .z (.a .z .z)) (.b .z (.a .z (.b .z (.a .z (.b .z (.a .z (.l 29623))))))))) (.b (.b (.a .z (.l 34344)) (.a (.b .z (.a .z (.a .z (.l 31956)))) (.l 32436))) (.b (.a (.l 32371) (.l 30668)) (.a (.l 30638) (.l 29025))))) (.b (.a (.b (.a (.l 32627) (.l 31073)) (.a (.l 30815) (.l 29347))) (.a (.a (.a (.a (.a (.a (.a (.l 29661) .z) .z) .z) .z) .z) .z) .z)) (.a (.b (.a (.l 29134) (.l 27747)) (.a (.l 27574) (.a (.l 26261) .z))) .z)))) (.a (.b (.a (.b (.a (.a (.a (.b .z .z) .z) .z) (.b (.a .z (.l 29855)) (.l 29144))) (.a (.b (.a .z (.l 28500)) (.l 27922)) (.b (.l 27662) (.l 26279)))) (.b (.a (.b (.l 29025) (.l 27524)) (.b (.l 27498) (.l 26076))) (.a (.b (.l 26125) (.l 24819)) (.b (.l 24750) (.l 23513))))) (.a (.b (.a (.b (.l 26549) (.l 25264)) (.b (.l 24987) (.l 23778))) (.a (.b (.l 24061) (.l 22934)) (.b (.l 22646) (.l 21585)))) (.b (.a (.b (.l 23599) (.l 22457)) (.b (.l 22357) (.l 21275))) (.a (.b (.l 21388) (.l 20386)) (.b (.l 20262) (.a (.l 19313) .z)))))) (.b (.b (.a (.b (.a (.l 26123) (.a (.a (.a (.a (.l 24879) .z) .z) .z) .z)) (.a (.l 24772) .z)) .z) (.a (.a (.b (.l 23513) (.a (.l 22337) .z)) .z) (.b .z (.a .z (.a .z (.l 19011)))))) (.b (.a (.a (.a (.a (.a (.a (.a (.l 21239) .z) .z) .z) .z) .z) .z) (.a .z (.b (.l 18469) (.l 17575)))) (.a .z (.b (.l 17499) (.l 16679)))))))) (.b (.a (.b (.a (.a .z (.b (.b (.a .z (.l 30728)) (.a (.b .z (.a .z (.a .z (.l 28280)))) (.l 28884))) (.b (.a (.a .z (.l 27699)) (.l 27186)) (.a (.l 26603) (.l 25618))))) (.a (.a (.b (.b (.l 29630) (.a (.l 27853) .z)) (.a (.a (.b (.l 26215) .z) .z) .z)) .z) .z)) (.a (.b (.a (.a .z (.a .z (.l 25590))) (.b (.a (.l 25098) (.l 24168)) (.a (.l 23704) (.l 22826)))) (.a (.b (.a .z (.l 23308)) (.a (.b .z (.a .z (.b .z (.a .z (.l 21395))))) (.l 22059))) (.b (.a (.l 22411) (.a (.l 21581) .z)) (.l 21211)))) (.b .z (.a .z (.b .z (.a .z (.b .z (.a .z (.b .z (.a .z (.l 16678))))))))))) (.b (.b (.a (.b (.a (.a .z (.l 25141)) (.a (.l 24401) .z)) (.a (.a .z (.l 23633)) (.a (.a (.l 22938) .z) .z))) (.a .z (.a .z (.b (.l 21273) (.l 19997))))) (.a (.a (.b (.l 22938) (.l 21615)) (.a (.a (.l 21589) .z) .z)) (.a .z (.a .z (.b (.l 18821) (.l 17736)))))) (.a (.b (.a (.b (.l 20392) (.l 19259)) (.a (.a (.l 19192) .z) .z)) (.a (.b (.l 18209) (.l 17234)) (.a (.a (.a (.l 17138) .z) .z) .z))) (.a .z (.b (.a .z (.b (.b (.b (.l 16732) (.a (.l 16493) (.a (.l 16284) (.l 247342)))) (.b (.a (.l 16258) (.l 245369)) (.l 244998))) (.b (.b (.l 241547) (.l 238161)) (.l 234838)))) (.b (.a .z (.a (.b (.l 228375) (.a (.b (.a (.a .z (.b (.l 221792) (.l 107029))) (.l 108110)) (.l 108470)) (.l 110338))) (.l 114978))) (.a (.b .z (.a .z (.a .z (.b .z (.a .z (.b .z (.a .z (.l 106456)))))))) (.a (.l 112154) (.l 115103))))))))) (.a (.b (.a (.b (.a (.b (.a (.a .z (.l 21325)) (.l 20898)) (.a (.l 20643) (.l 19818))) (.b (.l 20095) (.a (.l 19056) .z))) (.a (.b (.l 19594) (.l 18615)) (.a (.b (.l 18087) (.a (.l 17183) .z)) .z))) (.a .z (.a .z (.b (.a .z (.l 16586)) (.l 15170))))) (.a (.b (.a (.b (.l 17699) (.l 16843)) (.a (.a (.l 16338) .z) .z)) (.a (.b (.l 16041) (.l 15289)) .z)) (.a .z (.b (.b (.a .z (.l 13703)) (.l 13475)) (.a (.l 12833) (.b (.b (.l 12419) (.a (.l 12123) (.b (.l 11931) (.a (.l 11789) (.b (.l 11696) (.a (.l 11626) (.a (.l 11581) (.l 176669)))))))) (.b (.a (.l 11837) (.l 178059)) (.l 176690)))))))) (.b (.a (.a (.b (.b (.l 16327) (.l 15483)) (.b (.l 14696) (.l 13961))) (.a (.b (.a (.a (.a (.a (.a (.l 15367) .z) .z) .z) .z) .z) .z) .z)) (.a .z (.a (.a .z (.b (.a .z (.b (.a .z (.l 108418)) (.l 108917))) (.b (.a .z (.l 109120)) (.l 110087)))) (.b (.a (.b (.l 112293) (.l 112489)) (.b (.l 115289) (.l 115535))) (.a (.b (.l 112741) (.l 113049)) (.b (.l 115839) (.l 116203))))))) (.a (.a (.b (.b (.a (.l 13275) (.b (.a (.l 12872) (.b (.l 12680) (.a (.l 12523) .z))) (.l 191918))) (.a (.b (.l 12632) (.a (.l 12327) (.l 185518))) (.b (.l 187237) (.l 182707)))) (.b (.a (.b (.l 183895) (.l 179517)) (.a (.b (.l 178322) (.a (.b (.a (.l 174077) (.l 84187)) (.l 84514)) (.l 85607))) (.a (.l 87082) .z))) (.a (.b (.l 175276) (.a (.l 171168) (.l 84800))) (.a (.l 86998) (.a (.a (.l 86416) .z) .z))))) .z) (.a .z (.a (.b (.a .z (.b (.l 110398) (.l 110763))) (.a (.b .z (.b .z (.a .z (.b .z (.a .z (.b .z (.a .z (.l 105949)))))))) (.b (.l 111181) (.l 111652)))) (.b (.a (.b (.l 113414) (.l 113834)) (.b (.l 116625) (.l 117106))) (.a (.b (.l 114310) (.l 114842)) (.b (.l 117646) (.l 118246)))))))))))) (.a (.a (.b (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.l 21881)))))))))))) .z) (.b (.b (.a (.b (.a (.b (.a (.b (.l 21875) (.l 20881)) (.b (.l 20589) (.l 19653))) (.a (.b (.l 19947) (.a .z (.l 18489))) (.b (.l 18773) (.l 17945)))) (.b (.a (.b (.l 19445) (.l 18561)) (.a (.a (.a (.a (.a (.l 18422) .z) .z) .z) .z) .z)) (.a (.l 17730) .z))) (.a (.b (.a (.a .z (.a .z (.a .z (.a .z (.a .z (.l 17197)))))) (.l 17165)) (.a .z (.l 15735))) (.b (.a (.a (.a (.a (.a (.a (.l 16211) .z) .z) .z) .z) .z) .z) (.a .z (.b .z (.a .z (.b .z (.a .z (.l 12710))))))))) (.b (.a (.a .z (.b (.b .z (.a .z (.b .z (.a .z (.l 15012))))) (.l 15197))) (.b (.b (.l 15910) (.l 15187)) (.b (.l 14507) (.l 13867)))) (.a (.b (.a (.a .z (.l 14235)) (.l 13896)) (.a (.l 13375) (.l 12738))) (.b (.a (.l 13264) (.l 12687)) (.a (.l 12159) (.l 11631)))))) (.a (.b (.a (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.l 13669)))))))) (.b (.a (.l 13657) (.l 12938)) (.a (.l 12579) (.l 11917)))) (.a .z (.b (.a (.a .z (.a .z (.a .z (.a .z (.l 11037))))) (.l 11001)) (.a .z (.b (.a (.a .z (.a .z (.l 9979))) (.b (.l 9915) (.a (.l 9727) (.b (.l 9604) (.a (.l 9513) (.b (.l 9453) (.a (.l 9408) (.l 143353)))))))) (.a .z (.l 145874))))))) (.b (.a (.b (.a (.l 12291) (.l 11706)) (.a (.l 11321) (.l 10782))) (.b (.a (.l 11174) (.b (.l 10688) (.a (.l 10255) (.b (.l 10037) (.l 150302))))) (.a (.b (.a (.l 10292) (.b (.l 10064) (.a (.l 9862) (.b (.l 9754) (.a (.l 9656) (.b (.l 9604) (.a (.l 9556) (.l 145659)))))))) (.a (.b (.l 9886) (.l 148126)) (.l 147750))) (.b (.a (.l 150478) (.l 147276)) (.a (.l 144539) (.a (.b (.l 141463) (.l 68012)) (.l 68673))))))) (.a (.b (.a (.b (.l 10451) (.a (.l 10049) (.b (.l 9804) (.l 146973)))) (.b (.a (.b (.l 9953) (.a (.l 9759) (.b (.l 9645) (.a (.l 9551) (.b (.l 9495) (.a (.l 9449) (.l 144001))))))) (.l 148599)) (.a (.l 146286) (.l 142884)))) (.a (.b (.a (.l 147768) (.l 144164)) (.a (.l 142228) (.a (.b (.l 138759) (.l 66614)) (.l 67089)))) (.a (.b (.l 140732) (.l 68042)) (.b (.l 68204) (.l 68239))))) (.a (.b (.b (.a (.l 145222) (.l 141995)) (.a (.a (.b (.l 139637) (.l 67083)) (.l 67651)) (.l 68715))) (.a (.b (.l 68450) (.l 68498)) (.b (.l 68758) (.l 68818)))) (.b (.a (.b (.l 69033) (.l 69071)) (.b (.l 69436) (.l 69487))) (.a (.b (.l 69126) (.l 69200)) (.b (.l 69556) (.l 69644))))))))) (.a (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.l 136964)))))))))))))) (.a (.b (.a (.b (.a (.b (.a (.l 67853) (.l 67886)) (.b (.a .z (.b (.a .z (.b (.a .z (.l 65836)) .z)) .z)) .z)) (.b (.b (.l 67935) (.l 67980)) (.a (.l 68041) (.l 68118)))) (.b (.a .z (.b (.a .z (.b (.a .z (.b (.a .z (.l 66121)) .z)) .z)) .z)) .z)) (.b (.b (.a (.b (.l 68082) (.l 68138)) (.b (.l 68291) (.l 68360))) (.a (.b (.l 68212) (.l 68301)) (.b (.l 68446) (.l 68548)))) (.a (.b (.a (.l 68407) (.l 68529)) (.b (.a .z (.b (.a .z (.b (.a .z (.l 66577)) .z)) .z)) .z)) (.b (.b (.l 68667) (.l 68803)) (.a (.l 68954) (.l 69123)))))) (.b (.a .z (.b (.a .z (.b (.a .z (.b (.a .z (.b (.a .z (.l 67210)) .z)) .z)) .z)) .z)) .z)) (.b (.b (.a (.b (.a (.b (.l 68562) (.l 68644)) (.b (.l 68896) (.l 68991))) (.a (.b (.l 68743) (.l 68859)) (.b (.l 69104) (.l 69234)))) (.b (.a (.b (.l 69292) (.l 69401)) (.b (.l 69750) (.l 69873))) (.a (.b (.l 69528) (.l 69672)) (.b (.l 70015) (.l 70175))))) (.a (.b (.a (.b (.l 68992) (.l 69141)) (.b (.l 69381) (.l 69545))) (.a (.b (.l 69307) (.l 69490)) (.b (.l 69726) (.l 69924)))) (.b (.a (.b (.l 69834) (.l 70014)) (.b (.l 70353) (.l 70548))) (.a (.b (.l 70211) (.l 70425)) (.b (.l 70762) (.l 70994)))))) (.a (.b (.a (.b (.a (.l 69690) (.l 69906)) (.b (.a .z (.b (.a .z (.b (.a .z (.l 68027)) .z)) .z)) .z)) (.b (.b (.l 70140) (.l 70372)) (.a (.l 70622) (.l 70890)))) (.b (.a .z (.b (.a .z (.b (.a .z (.b (.a .z (.l 69038)) .z)) .z)) .z)) .z)) (.b (.b (.a (.b (.l 70657) (.l 70907)) (.b (.l 71243) (.l 71511))) (.a (.b (.l 71174) (.l 71460)) (.b (.l 71797) (.l 72101)))) (.a (.b (.a (.l 71763) (.l 72085)) (.b (.a .z (.b (.a .z (.b (.a .z (.l 70256)) .z)) .z)) .z)) (.b (.b (.l 72424) (.l 72766)) (.a (.l 73127) (.l 73507))))))))))) (.b (.a (.b (.b (.a (.a (.b (.b (.l 14584) (.l 13921)) (.b (.l 13298) (.a (.l 12711) .z))) .z) (.b (.a .z (.b (.a (.b (.a (.a .z (.l 11571)) (.b (.l 11476) (.a (.l 11342) (.l 171961)))) (.l 174219)) (.b (.l 172581) (.l 168599))) (.a (.b (.l 170229) (.l 166360)) (.a (.a (.b (.l 164738) (.l 79555)) (.l 80789)) (.l 82747))))) (.a (.a .z (.a .z (.b (.b .z (.a .z (.a .z (.l 159633)))) (.a (.b .z (.a .z (.b .z (.a .z (.l 75498))))) (.l 77355))))) (.a (.a (.b (.b (.l 162608) (.a (.a (.b (.l 158968) (.l 76411)) (.l 76967)) (.l 77838))) (.l 79120)) (.b (.l 80247) (.l 80305))) (.a (.b (.l 81492) (.l 81571)) (.b (.l 82819) (.l 82922))))))) (.a (.a (.a (.b (.l 12159) (.a (.l 11146) .z)) .z) .z) (.a (.a (.b .z (.a .z (.b .z (.a .z (.b .z (.a .z (.b .z (.a .z (.l 74263))))))))) (.b (.a (.b .z (.a .z (.l 76397))) (.b (.l 78057) (.l 78128))) (.a (.b (.l 77134) (.l 77237)) (.b (.l 78226) (.l 78350))))) (.a (.b (.a (.b (.l 79185) (.l 79277)) (.b (.l 80391) (.l 80505))) (.a (.b (.l 79396) (.l 79542)) (.b (.l 80647) (.l 80816)))) (.b (.a (.b (.l 81680) (.l 81817)) (.b (.l 83054) (.l 83216))) (.a (.b (.l 81982) (.l 82176)) (.b (.l 83407) (.l 83628)))))))) (.a (.a (.b (.b (.b (.a (.b (.a (.a (.l 10243) .z) .z) (.l 153345)) (.b .z (.l 147211))) (.a (.a (.l 150216) (.l 147150)) (.a (.a (.b (.l 144207) (.l 69386)) (.l 70145)) (.l 71450)))) (.a (.a (.b (.l 144208) (.l 69854)) (.b (.l 70324) (.l 70364))) (.a (.b (.l 70881) (.l 70936)) (.b (.l 71499) (.l 71569))))) (.a (.b (.a (.b (.l 69899) (.l 69964)) (.b (.l 70424) (.l 70503))) (.a (.b (.l 70048) (.l 70150)) (.b (.l 70602) (.l 70719)))) (.b (.a (.b (.l 71010) (.l 71105)) (.b (.l 71660) (.l 71770))) (.a (.b (.l 71219) (.l 71352)) (.b (.l 71900) (.l 72051)))))) (.b (.a (.b (.a (.b (.b .z (.l 71575)) (.l 72116)) (.b (.b .z (.l 72284)) (.l 72846))) (.a (.b (.l 72181) (.l 72267)) (.b (.l 72927) (.l 73030)))) (.b (.a (.b (.b .z (.l 73057)) (.l 73641)) (.b (.b .z (.l 73896)) (.l 74503))) (.a (.b (.l 73739) (.l 73859)) (.b (.l 74619) (.l 74758))))) (.a (.b (.a (.b (.l 72373) (.l 72501)) (.b (.l 73153) (.l 73298))) (.a (.b (.l 72648) (.l 72817)) (.b (.l 73464) (.l 73651)))) (.b (.a (.b (.l 74001) (.l 74165)) (.b (.l 74919) (.l 75103))) (.a (.b (.l 74350) (.l 74557)) (.b (.l 75309) (.l 75537))))))) (.a (.b (.a (.b (.a (.b (.b .z (.l 74803)) (.l 75435)) (.b (.l 76307) (.l 76439))) (.a (.b (.l 75570) (.l 75729)) (.b (.l 76594) (.l 76774)))) (.b (.a (.b (.l 77365) (.l 77517)) (.b (.l 78499) (.l 78674))) (.a (.b (.l 77694) (.l 77896)) (.b (.l 78874) (.l 79099))))) (.a (.b (.a (.b (.l 75910) (.l 76115)) (.b (.l 76977) (.l 77204))) (.a (.b (.l 76342) (.l 76593)) (.b (.l 77454) (.l 77729)))) (.b (.a (.b (.l 78122) (.l 78373)) (.b (.l 79350) (.l 79626))) (.a (.b (.l 78648) (.l 78948)) (.b (.l 79927) (.l 80255)))))) (.b (.a (.b (.a (.b (.l 79713) (.l 79912)) (.b (.l 81012) (.l 81235))) (.a (.b (.l 80136) (.l 80387)) (.b (.l 81486) (.l 81763)))) (.b (.a (.b (.l 82398) (.l 82648)) (.b (.l 83877) (.l 84156))) (.a (.b (.l 82927) (.l 83233)) (.b (.l 84464) (.l 84802))))) (.a (.b (.a (.b (.l 80664) (.l 80967)) (.b (.l 82068) (.l 82400))) (.a (.b (.l 81296) (.l 81653)) (.b (.l 82760) (.l 83147)))) (.b (.a (.b (.l 83568) (.l 83931)) (.b (.l 85168) (.l 85565))) (.a (.b (.l 84323) (.l 84744)) (.b (.l 85992) (.l 86449))))))))) (.a (.b (.a (.b (.a (.b (.a (.b (.l 84073) (.l 84138)) (.b (.l 85530) (.l 85619))) (.a (.b (.l 84234) (.l 84361)) (.b (.l 85740) (.l 85893)))) (.b (.a (.b (.l 87080) (.l 87195)) (.a (.b (.a (.b (.a (.b (.l 85066) .z) .z) .z) .z) .z) .z)) (.a (.b (.l 87343) (.l 87525)) .z))) (.a (.b (.a (.b (.l 84519) (.l 84707)) (.b (.l 86078) (.l 86295))) (.a (.b (.l 84926) (.l 85175)) (.b (.l 86543) (.l 86823)))) (.a (.b (.b (.l 87739) (.a (.l 86467) .z)) (.a (.l 88265) .z)) .z))) .z) (.a (.b (.a (.b (.a (.b (.l 85454) (.l 85764)) (.b (.l 87134) (.l 87477))) (.a (.b (.l 86104) (.l 86474)) (.b (.l 87851) (.l 88257)))) (.b (.a (.b (.l 88923) (.l 89301)) (.b (.b .z (.l 90202)) (.l 91245))) (.a (.b (.l 89713) (.l 90158)) (.b (.l 91697) (.l 92183))))) (.a (.b (.a (.b (.l 86876) (.l 87308)) (.b (.l 88696) (.l 89167))) (.a (.b (.l 87772) (.l 88268)) (.b (.l 89671) (.l 90208)))) (.b (.a (.b (.l 90636) (.l 91149)) (.b (.l 92705) (.l 93263))) (.a (.b (.l 91696) (.l 92279)) (.b (.l 93857) (.l 94488)))))) (.b (.a (.b (.a (.b (.b .z (.l 92217)) (.l 93316)) (.b (.b .z (.l 94363)) (.l 95522))) (.a (.b (.l 93810) (.l 94342)) (.b (.l 96063) (.l 96642)))) (.b (.a (.b (.b .z (.l 96649)) (.l 97872)) (.b (.b .z (.l 99085)) (.l 100377))) (.a (.b (.l 98463) (.l 99096)) (.b (.l 101023) (.l 101713))))) (.a (.b (.a (.b (.l 94910) (.l 95517)) (.b (.l 97262) (.l 97921))) (.a (.b (.l 96161) (.l 96845)) (.b (.l 98621) (.l 99362)))) (.b (.a (.b (.l 99770) (.l 100487)) (.b (.l 102447) (.l 103226))) (.a (.b (.l 101246) (.l 102050)) (.b (.l 104051) (.l 104922)))))))) (.b (.a (.b .z (.b .z (.a .z (.b .z (.a .z (.b .z (.a .z (.b .z (.a .z (.b .z (.a .z (.l 107914)))))))))))) (.b (.a (.b (.a (.a .z (.b (.a .z (.l 108057)) (.l 108924))) (.b (.l 112176) (.l 112754))) (.a (.b (.a .z (.l 109488)) (.l 110828)) (.b (.l 113387) (.l 114074)))) (.b (.a (.b (.l 115431) (.l 116077)) (.b (.l 118905) (.a (.l 117075) (.l 118871)))) (.a (.b (.l 116780) (.l 117541)) (.b (.a (.l 117811) (.l 119647)) (.a (.l 118607) (.l 120484)))))) (.a (.b (.a (.b (.l 111500) (.l 112225)) (.b (.l 114817) (.l 115616))) (.a (.b (.l 113004) (.l 113838)) (.b (.l 116473) (.a (.l 114832) (.l 116630))))) (.b (.a (.b (.a (.l 115812) (.l 117607)) (.a (.l 116646) (.l 118482))) (.b (.a (.l 119463) (.l 121384)) (.a (.l 120381) (.l 122347)))) (.a (.b (.a (.l 117538) (.l 119418)) (.a (.l 118490) (.l 120415))) (.b (.a (.l 121362) (.l 123376)) (.a (.l 122408) (.l 124471)))))))) (.a (.b (.a (.b (.a (.b (.b .z (.l 101681)) (.l 103048)) (.b (.b .z (.l 104450)) (.l 105899))) (.a (.b (.l 103755) (.l 104507)) (.b (.l 106670) (.l 107490)))) (.b (.a (.b (.b .z (.l 107406)) (.l 108943)) (.b (.l 111330) (.l 112195))) (.a (.b (.l 109785) (.l 110679)) (.b (.l 113115) (.l 114090))))) (.a (.b (.a (.b (.l 105306) (.l 106152)) (.b (.l 108360) (.l 109281))) (.a (.b (.l 107048) (.l 107994)) (.b (.l 110254) (.l 111281)))) (.b (.a (.b (.l 111626) (.l 112629)) (.b (.a (.l 112589) (.l 114360)) (.a (.l 113628) (.l 115444)))) (.a (.b (.l 113687) (.a (.l 112248) (.l 114032))) (.b (.a (.l 114724) (.l 116588)) (.a (.l 115879) (.l 117793))))))) (.b (.a (.b (.a (.b (.l 114727) (.l 115674)) (.b (.a (.l 115757) (.l 117598)) (.a (.l 116741) (.l 118627)))) (.a (.b (.a (.l 114111) (.l 115916)) (.a (.l 115123) (.l 116973))) (.b (.a (.l 117784) (.l 119718)) (.a (.l 118889) (.l 120873))))) (.b (.a (.b (.a (.l 119504) (.l 121476)) (.a (.l 120580) (.l 122603))) (.b (.a (.l 123519) (.l 125634)) (.a (.l 124698) (.l 126868)))) (.a (.b (.a (.l 121721) (.l 123796)) (.a (.l 122928) (.l 125058))) (.b (.a (.l 125946) (.l 128174)) (.a (.l 127266) (.l 129555)))))) (.a (.b (.a (.b (.a (.l 116194) (.l 118092)) (.a (.l 117325) (.l 119273))) (.b (.a (.l 120057) (.l 122094)) (.a (.l 121291) (.l 123382)))) (.a (.b (.a (.l 118518) (.l 120518)) (.a (.l 119775) (.l 121830))) (.b (.a (.l 122591) (.l 124739)) (.a (.l 123960) (.l 126169))))) (.b (.a (.b (.a (.l 124204) (.l 126391)) (.a (.l 125549) (.l 127797))) (.b (.a (.l 128659) (.l 131012)) (.a (.l 130129) (.l 132548)))) (.a (.b (.a (.l 126967) (.l 129279)) (.a (.l 128460) (.l 130838))) (.b (.a (.l 131677) (.l 134167)) (.a (.l 133307) (.l 135871))))))))))) (.a (.a (.b (.a (.b (.a (.b (.a (.b (.l 70271) (.l 70410)) (.b (.l 70855) (.l 71011))) (.a (.b (.l 70567) (.l 70743)) (.b (.l 71185) (.l 71378)))) (.b (.a (.b (.l 71505) (.l 71677)) (.b (.l 72221) (.l 72411))) (.a (.b (.l 71869) (.l 72080)) (.b (.l 72621) (.l 72851))))) (.a (.b (.a (.b (.l 70937) (.l 71150)) (.b (.l 71589) (.l 71820))) (.a (.b (.l 71381) (.l 71631)) (.b (.l 72070) (.l 72338)))) (.b (.a (.b (.l 72310) (.l 72559)) (.b (.l 73101) (.l 73370))) (.a (.b (.l 72829) (.l 73117)) (.b (.l 73660) (.l 73971)))))) (.b (.a (.b (.a (.b (.l 73005) (.l 73214)) (.b (.l 73859) (.l 74088))) (.a (.b (.l 73444) (.l 73693)) (.b (.l 74338) (.l 74610)))) (.b (.a (.b (.l 74786) (.l 75036)) (.b (.l 75787) (.l 76060))) (.a (.b (.l 75308) (.l 75602)) (.b (.l 76355) (.l 76673))))) (.a (.b (.a (.b (.l 73964) (.l 74255)) (.b (.l 74902) (.l 75216))) (.a (.b (.l 74567) (.l 74900)) (.b (.l 75551) (.l 75908)))) (.b (.a (.b (.l 75918) (.l 76256)) (.b (.l 77014) (.l 77378))) (.a (.b (.l 76616) (.l 76999)) (.b (.l 77764) (.l 78175))))))) (.a (.b (.a (.b (.a (.b (.l 71899) (.l 72186)) (.b (.l 72626) (.l 72933))) (.a (.b (.l 72491) (.l 72816)) (.b (.l 73259) (.l 73606)))) (.b (.a (.b (.l 73426) (.l 73754)) (.b (.l 74301) (.l 74652))) (.a (.b (.l 74103) (.l 74472)) (.b (.l 75024) (.l 75418))))) (.a (.b (.a (.b (.l 73160) (.l 73523)) (.b (.l 73972) (.l 74358))) (.a (.b (.l 73906) (.l 74309)) (.b (.l 74764) (.l 75191)))) (.b (.a (.b (.l 74861) (.l 75272)) (.b (.l 75832) (.l 76268))) (.a (.b (.l 75703) (.l 76156)) (.b (.l 76726) (.l 77207)))))) (.b (.a (.b (.a (.b (.l 75254) (.l 75629)) (.b (.l 76287) (.l 76689))) (.a (.b (.l 76026) (.l 76445)) (.b (.l 77112) (.l 77559)))) (.b (.a (.b (.l 77404) (.l 77833)) (.b (.l 78609) (.l 79067))) (.a (.b (.l 78285) (.l 78761)) (.b (.l 79550) (.l 80057))))) (.a (.b (.a (.b (.l 76887) (.l 77350)) (.b (.l 78029) (.l 78522))) (.a (.b (.l 77837) (.l 78347)) (.b (.l 79039) (.l 79580)))) (.b (.a (.b (.l 79262) (.l 79786)) (.b (.l 80590) (.l 81149))) (.a (.b (.l 80336) (.l 80912)) (.b (.l 81734) (.l 82345)))))))) (.b (.a (.b (.a (.b (.a (.b (.l 76867) (.l 77163)) (.b (.l 78027) (.l 78350))) (.a (.b (.l 77483) (.l 77827)) (.b (.l 78696) (.l 79067)))) (.b (.a (.b (.l 79273) (.l 79622)) (.b (.l 80607) (.l 80986))) (.a (.b (.l 79997) (.l 80398)) (.b (.l 81391) (.l 81823))))) (.a (.b (.a (.b (.l 78194) (.l 78585)) (.b (.l 79463) (.l 79883))) (.a (.b (.l 79001) (.l 79440)) (.b (.l 80329) (.l 80800)))) (.b (.a (.b (.l 80823) (.l 81275)) (.b (.l 82281) (.l 82767))) (.a (.b (.l 81754) (.l 82258)) (.b (.l 83280) (.l 83821)))))) (.b (.a (.b (.a (.b (.l 82036) (.l 82446)) (.b (.l 83563) (.l 84007))) (.a (.b (.l 82883) (.l 83349)) (.b (.l 84479) (.l 84980)))) (.b (.a (.b (.l 85194) (.l 85674)) (.b (.l 86936) (.l 87455))) (.a (.b (.l 86184) (.l 86724)) (.b (.l 88005) (.l 88587))))) (.a (.b (.a (.b (.l 83842) (.l 84364)) (.b (.l 85511) (.l 86072))) (.a (.b (.l 84914) (.l 85494)) (.b (.l 86663) (.l 87285)))) (.b (.a (.b (.l 87295) (.l 87898)) (.b (.l 89201) (.l 89849))) (.a (.b (.l 88532) (.l 89200)) (.b (.l 90531) (.l 91247))))))) (.a (.b (.a (.b (.a (.b (.l 79905) (.l 80395)) (.b (.l 81297) (.l 81821))) (.a (.b (.l 80910) (.l 81451)) (.b (.l 82371) (.l 82949)))) (.b (.a (.b (.l 82791) (.l 83350)) (.b (.l 84391) (.l 84990))) (.a (.b (.l 83938) (.l 84555)) (.b (.l 85618) (.l 86277))))) (.a (.b (.a (.b (.l 82019) (.l 82614)) (.b (.l 83554) (.l 84188))) (.a (.b (.l 83237) (.l 83887)) (.b (.l 84851) (.l 85544)))) (.b (.a (.b (.l 85201) (.l 85877)) (.b (.l 86966) (.l 87688))) (.a (.b (.l 86584) (.l 87322)) (.b (.l 88441) (.l 89228)))))) (.b (.a (.b (.a (.b (.l 86105) (.l 86745)) (.b (.l 87938) (.l 88624))) (.a (.b (.l 87417) (.l 88121)) (.b (.l 89343) (.l 90096)))) (.b (.a (.b (.l 89900) (.l 90635)) (.b (.l 91999) (.l 92786))) (.a (.b (.l 91405) (.l 92211)) (.b (.l 93611) (.l 94475))))) (.a (.b (.a (.b (.l 88858) (.l 89628)) (.b (.l 90884) (.l 91707))) (.a (.b (.l 90433) (.l 91273)) (.b (.l 92567) (.l 93464)))) (.b (.a (.b (.l 93053) (.l 93934)) (.b (.l 95377) (.l 96320))) (.a (.b (.l 94853) (.l 95813)) (.b (.l 97304) (.l 98331))))))))) (.b (.a (.a (.b (.a (.b (.a (.b (.l 88795) (.l 89356)) (.b (.l 90780) (.l 91385))) (.a (.b (.l 89949) (.l 90576)) (.b (.l 92025) (.l 92702)))) (.b (.a (.b (.l 92897) (.l 93551)) (.b (.l 95157) (.l 95864))) (.a (.b (.l 94242) (.l 94971)) (.b (.l 96610) (.l 97397))))) (.a (.b (.a (.b (.l 91238) (.l 91935)) (.b (.l 93414) (.l 94164))) (.a (.b (.l 92667) (.l 93436)) (.b (.l 94951) (.l 95778)))) (.b (.a (.b (.l 95739) (.l 96546)) (.b (.l 98224) (.l 99093))) (.a (.b (.l 97393) (.l 98282)) (.b (.l 100006) (.l 100962)))))) (.b (.a (.b (.a (.b (.l 97569) (.l 98334)) (.b (.l 100146) (.l 100973))) (.a (.b (.l 99140) (.l 99989)) (.b (.l 101844) (.l 102760)))) (.b (.a (.b (.l 102899) (.l 103793)) (.b (.l 105842) (.l 106811))) (.a (.b (.l 104735) (.l 105726)) (.b (.l 107830) (.l 108902))))) (.a (.b (.a (.b (.l 100881) (.l 101818)) (.b (.l 103724) (.l 104735))) (.a (.b (.l 102801) (.l 103832)) (.b (.l 105795) (.l 106906)))) (.b (.a (.b (.l 106767) (.l 107858)) (.b (.l 110027) (.l 111207))) (.a (.b (.l 109003) (.l 110203)) (.b (.a (.l 109914) (.l 111658)) (.a (.l 111152) (.l 112945)))))))) (.b (.a (.a (.b (.a (.b (.l 108991) (.l 110041)) (.b (.l 112363) (.a (.l 110976) (.l 112729)))) (.a (.b (.l 111145) (.l 112305)) (.b (.a (.l 112117) (.l 113918)) (.a (.l 113317) (.l 115167))))) (.b (.a (.b (.a (.l 113367) (.l 115199)) (.a (.l 114545) (.l 116427))) (.b (.a (.l 117096) (.l 119062)) (.a (.l 118376) (.l 120396)))) (.a (.b (.a (.l 115784) (.l 117717)) (.a (.l 117084) (.l 119072))) (.b (.a (.l 119720) (.l 121798)) (.a (.l 121132) (.l 123270)))))) (.b (.a (.a (.b (.a (.l 121099) (.l 123211)) (.a (.l 122490) (.l 124662))) (.b (.a (.l 125401) (.l 127673)) (.a (.l 126916) (.l 129254)))) (.b (.a (.a (.l 130031) (.l 132479)) (.l 135022)) (.b (.l 131682) (.a (.l 129241) .z)))) (.b (.a (.a (.a (.l 123952) (.l 126187)) (.l 128507)) (.a (.a (.a (.a (.a (.a (.a (.l 126860) .z) .z) .z) .z) .z) .z) .z)) (.a (.b (.l 125487) (.a (.l 123217) .z)) .z)))) (.b (.a (.a (.a (.b (.a (.l 110968) (.l 112740)) (.a (.l 112187) (.l 114008))) (.b (.a (.l 114575) (.l 116477)) (.a (.l 115896) (.l 117852)))) (.b (.a (.a (.l 118449) (.l 120494)) (.l 122614)) (.b (.l 119881) (.a (.l 117763) .z)))) (.a (.a (.a (.a (.a (.a (.a (.a (.a (.l 121001) .z) .z) .z) .z) .z) .z) .z) .z) .z)) (.a (.b (.a (.a (.a (.l 113465) (.l 115338)) (.l 117279)) (.a (.a (.a (.a (.a (.a (.a (.l 115695) .z) .z) .z) .z) .z) .z) .z)) (.a (.b (.l 114804) (.a (.l 112822) .z)) .z)) .z)))) (.b (.a (.a (.a (.b (.a (.b (.l 94243) (.l 95088)) (.b (.l 96644) (.l 97552))) (.a (.b (.l 95973) (.l 96898)) (.b (.l 98501) (.l 99494)))) (.b (.a (.b (.l 99214) (.l 100189)) (.b (.l 101964) (.l 103013))) (.a (.b (.l 101209) (.l 102276)) (.b (.l 104111) (.l 105258))))) (.b (.a (.a (.b (.l 104911) (.l 106041)) (.b (.l 108070) (.l 109288))) (.b (.a (.a (.l 108950) (.l 110668)) (.l 112448)) (.b (.l 110206) (.a (.l 108347) .z)))) (.b (.a (.a (.l 107222) (.l 108073)) (.a (.a (.a (.a (.a (.a (.a (.l 106529) .z) .z) .z) .z) .z) .z) .z)) (.a (.b (.l 106044) (.a (.l 104294) .z)) .z)))) (.a (.a (.a (.a (.a (.a (.a (.a (.a (.a (.a (.l 110886) .z) .z) .z) .z) .z) .z) .z) .z) .z) .z) .z)) (.a (.b (.a (.a (.a (.b (.l 97866) (.l 98876)) (.b (.l 100532) (.l 101616))) (.b (.a (.l 103391) (.l 104114)) (.b (.l 102279) (.a (.l 100628) .z)))) (.a (.a (.a (.a (.a (.a (.a (.a (.l 102583) .z) .z) .z) .z) .z) .z) .z) .z)) (.a (.b (.a (.a (.l 99930) (.l 100535)) (.a (.a (.a (.a (.a (.a (.l 99012) .z) .z) .z) .z) .z) .z)) (.a (.l 98879) .z)) .z)) .z))))))) (.a (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.a .z (.l 127715)))))))))))))))))) (.b (.b (.a (.b (.a (.a (.a (.b (.a (.b (.a (.l 74731) (.l 75175)) (.b (.a .z (.b (.a .z (.b (.a .z (.l 73375)) .z)) .z)) .z)) (.b (.b (.l 75639) (.l 76108)) (.a (.l 76598) (.l 77111)))) (.b (.a .z (.b (.a .z (.b (.a .z (.b (.a .z (.l 75319)) .z)) .z)) .z)) .z)) (.b (.b (.a (.b (.l 76630) (.l 77127)) (.b (.l 77710) (.l 78236))) (.a (.b (.l 77646) (.l 78189)) (.b (.l 78786) (.l 79360)))) (.a (.b (.a (.l 78754) (.l 79344)) (.b (.a .z (.b (.a .z (.b (.a .z (.l 77554)) .z)) .z)) .z)) (.b (.b (.l 79958) (.l 80582)) (.a (.l 81231) (.l 81906)))))) (.b (.a (.b (.a (.b (.l 78881) (.l 79438)) (.b (.l 80147) (.l 80738))) (.a (.b (.l 80021) (.l 80629)) (.b (.l 81356) (.l 82000)))) (.b (.a (.b (.l 81513) (.l 82141)) (.b (.l 82984) (.l 83652))) (.a (.b (.l 82796) (.l 83479)) (.b (.l 84347) (.l 85073))))) (.a (.b (.a (.b (.l 81262) (.l 81922)) (.b (.l 82671) (.l 83370))) (.a (.b (.l 82609) (.l 83324)) (.b (.l 84098) (.l 84854)))) (.b (.a (.b (.l 84191) (.l 84932)) (.b (.l 85828) (.l 86614))) (.a (.b (.l 85703) (.l 86505)) (.b (.l 87432) (.l 88283))))))) (.b (.a (.a (.b (.a (.b (.l 84567) (.l 85276)) (.b (.l 86267) (.l 87022))) (.a (.b (.l 86016) (.l 86786)) (.b (.l 87808) (.l 88627)))) (.b (.a (.b (.l 88092) (.l 88895)) (.b (.l 90050) (.l 90906))) (.a (.b (.l 89733) (.l 90605)) (.b (.l 91798) (.l 92728))))) (.b (.a (.a (.b (.l 92149) (.l 93062)) (.b (.l 94400) (.l 95375))) (.b (.a (.l 96813) (.l 97306)) (.l 95815))) (.a (.b (.a (.l 94014) (.l 94402)) (.l 93065)) (.a (.a (.a (.a (.a (.a (.a (.l 92880) .z) .z) .z) .z) .z) .z) .z)))) (.a (.b (.a (.a (.b (.l 87589) (.l 88424)) (.b (.l 89481) (.l 90369))) (.b (.a (.l 91513) (.l 91800)) (.l 90607))) (.a (.b (.a (.l 89293) (.l 89483)) (.l 88426)) (.a (.a (.a (.a (.a (.a (.a (.l 87940) .z) .z) .z) .z) .z) .z) .z))) (.a (.a (.a (.a (.a (.a (.a (.a (.a (.l 90270) .z) .z) .z) .z) .z) .z) .z) .z) .z)))) (.a (.b (.a (.a .z (.b (.a .z (.b (.a .z (.b (.a .z (.b (.a .z (.l 80113)) .z)) .z)) .z)) .z)) (.b (.a (.a (.a (.l 84067) (.l 84839)) (.b (.l 85641) (.l 86459))) (.b (.a (.l 87339) (.l 87434)) (.l 86507))) (.a (.b (.a (.a .z (.b (.a .z (.b (.a .z (.l 83038)) .z)) .z)) (.l 85643)) (.a .z (.a (.a .z .z) .z))) (.a (.a (.a (.a (.a (.a (.a (.l 84057) .z) .z) .z) .z) .z) .z) .z)))) (.a .z (.a (.a .z .z) .z))) (.a (.a (.a (.a (.a (.a (.a (.a (.a (.a (.a (.l 85873) .z) .z) .z) .z) .z) .z) .z) .z) .z) .z) .z))) (.a (.a (.a (.a (.a (.a (.a (.a (.a (.a (.a (.a (.a (.l 95786) .z) .z) .z) .z) .z) .z) .z) .z) .z) .z) .z) .z) .z)) (.a (.a (.a .z .z) .z) .z)) .z)))

private lemma cert_valid :
    checkI certTree (S_scale / 10) (S_scale / 2) (S_scale / 10) (S_scale / 2) = true := by
  decide

private lemma cert_sum_le :
    sumI certTree (S_scale / 10) (S_scale / 2) (S_scale / 10) (S_scale / 2) ≤ 2 * 1000 * S_scale ^ 2 := by
  decide

theorem solution {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if lowerTwoDiscarded ε a b then
        (if 1 ≤ a+3*b then 1/(a*b*(99/100-a-b)*(1-a-b))
          else if 99/100 ≤ a+3*b then (107/200)/(a*b^3) else (7/200)/(a*b^3))
      else 0)) ≤ 2 := by
  have _ := hε
  change (∫ a in (1 / 10 : ℝ)..(1 / 2 : ℝ), ∫ b in (1 / 10 : ℝ)..(1 / 2 : ℝ), G_poly ε a b) ≤ 2
  have ha_eq : ((S_scale / 10 : Int) : ℝ) / S_scale = 1 / 10 := by norm_num [S_scale]
  have hb_eq : ((S_scale / 2 : Int) : ℝ) / S_scale = 1 / 2 := by norm_num [S_scale]
  have hS : (0 : ℝ) < S_scale := by norm_num [S_scale]
  have h_meas : Measurable (fun p : ℝ × ℝ => G_poly ε p.1 p.2) := measurable_G_poly ε
  have h_bound : ∀ p : ℝ × ℝ, ‖G_poly ε p.1 p.2‖ ≤ 10 ^ 6 := by
    intro ⟨a, b⟩
    dsimp only [G_poly]
    split_ifs with h
    · have hfb := F_poly_nonneg_and_le (lowerTwoDiscarded_mono hε8 h)
      rw [Real.norm_of_nonneg hfb.1]
      exact hfb.2
    · norm_num
  have h_vol : volume (Ioc (1 / 10 : ℝ) (1 / 2) ×ˢ Ioc (1 / 10 : ℝ) (1 / 2)) < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
  have h_int : IntegrableOn (fun p : ℝ × ℝ => G_poly ε p.1 p.2)
      (Ioc (1 / 10 : ℝ) (1 / 2) ×ˢ Ioc (1 / 10 : ℝ) (1 / 2)) :=
    IntegrableOn.of_bound h_vol h_meas.aestronglyMeasurable (10 ^ 6) (ae_of_all _ h_bound)
  have h_fubini : (∫ a in (1 / 10 : ℝ)..(1 / 2 : ℝ), ∫ b in (1 / 10 : ℝ)..(1 / 2 : ℝ), G_poly ε a b) =
      ∫ p in Ioc (1 / 10 : ℝ) (1 / 2) ×ˢ Ioc (1 / 10 : ℝ) (1 / 2), G_poly ε p.1 p.2 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    simp_rw [intervalIntegral.integral_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 2)]
    exact (MeasureTheory.setIntegral_prod (fun p : ℝ × ℝ => G_poly ε p.1 p.2) h_int).symm
  rw [h_fubini, ← ha_eq, ← hb_eq]
  have h_int' : IntegrableOn (fun p : ℝ × ℝ => G_poly ε p.1 p.2)
      (Ioc (((S_scale / 10 : Int) : ℝ) / S_scale) (((S_scale / 2 : Int) : ℝ) / S_scale) ×ˢ
       Ioc (((S_scale / 10 : Int) : ℝ) / S_scale) (((S_scale / 2 : Int) : ℝ) / S_scale)) := by
    simpa only [ha_eq, hb_eq] using h_int
  have h_tree := integral_le_sumI ε hε8 certTree (S_scale / 10) (S_scale / 2) (S_scale / 10) (S_scale / 2)
    (by decide) (by decide) cert_valid h_int'
  have h_sumR : ((sumI certTree (S_scale / 10) (S_scale / 2) (S_scale / 10) (S_scale / 2) : Int) : ℝ) ≤
      2 * 1000 * (S_scale : ℝ) ^ 2 := by
    have := Int.cast_le (R := ℝ).mpr cert_sum_le
    push_cast at this
    linarith
  calc ∫ p in Ioc (((S_scale / 10 : Int) : ℝ) / S_scale) (((S_scale / 2 : Int) : ℝ) / S_scale) ×ˢ
          Ioc (((S_scale / 10 : Int) : ℝ) / S_scale) (((S_scale / 2 : Int) : ℝ) / S_scale),
        G_poly ε p.1 p.2
    _ ≤ ((sumI certTree (S_scale / 10) (S_scale / 2) (S_scale / 10) (S_scale / 2) : Int) : ℝ) / (1000 * (S_scale : ℝ) ^ 2) := h_tree
    _ ≤ (2 * 1000 * (S_scale : ℝ) ^ 2) / (1000 * (S_scale : ℝ) ^ 2) := by gcongr
    _ = 2 := by field_simp

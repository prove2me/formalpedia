-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_first_transition_corner_excluded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:44:17.041481+00:00
-- url     : https://prove2.me/submissions/c2bf9c01-e632-45c7-8662-274df6fe2fe0

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_four_corner_necessary_data

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalMeasureCoordinatePermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace CubicTorus

private lemma firstCornerPolynomial0_piece0 {d : ℝ}
    (hlo : (0 : ℝ) ≤ d) (hhi : d ≤ (1/4 : ℝ)) :
    0 ≤ (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 := by
  have hl : 0 ≤ d-(0 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1/4 : ℝ)-d := sub_nonneg.mpr hhi
  have he : (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 =
      (6144/5 : ℝ)*(d-(0 : ℝ))^0*((1/4 : ℝ)-d)^6 +
        (321536/45 : ℝ)*(d-(0 : ℝ))^1*((1/4 : ℝ)-d)^5 +
        (153344/9 : ℝ)*(d-(0 : ℝ))^2*((1/4 : ℝ)-d)^4 +
        (191488/9 : ℝ)*(d-(0 : ℝ))^3*((1/4 : ℝ)-d)^3 +
        (131872/9 : ℝ)*(d-(0 : ℝ))^4*((1/4 : ℝ)-d)^2 +
        (237376/45 : ℝ)*(d-(0 : ℝ))^5*((1/4 : ℝ)-d)^1 +
        (34931/45 : ℝ)*(d-(0 : ℝ))^6*((1/4 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial0_piece1 {d : ℝ}
    (hlo : (1/4 : ℝ) ≤ d) (hhi : d ≤ (1/2 : ℝ)) :
    0 ≤ (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 := by
  have hl : 0 ≤ d-(1/4 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1/2 : ℝ)-d := sub_nonneg.mpr hhi
  have he : (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 =
      (34931/45 : ℝ)*(d-(1/4 : ℝ))^0*((1/2 : ℝ)-d)^6 +
        (181796/45 : ℝ)*(d-(1/4 : ℝ))^1*((1/2 : ℝ)-d)^5 +
        (76292/9 : ℝ)*(d-(1/4 : ℝ))^2*((1/2 : ℝ)-d)^4 +
        (27424/3 : ℝ)*(d-(1/4 : ℝ))^3*((1/2 : ℝ)-d)^3 +
        (48016/9 : ℝ)*(d-(1/4 : ℝ))^4*((1/2 : ℝ)-d)^2 +
        (72256/45 : ℝ)*(d-(1/4 : ℝ))^5*((1/2 : ℝ)-d)^1 +
        (8896/45 : ℝ)*(d-(1/4 : ℝ))^6*((1/2 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial0_piece2 {d : ℝ}
    (hlo : (1/2 : ℝ) ≤ d) (hhi : d ≤ (3/4 : ℝ)) :
    0 ≤ (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 := by
  have hl : 0 ≤ d-(1/2 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (3/4 : ℝ)-d := sub_nonneg.mpr hhi
  have he : (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 =
      (8896/45 : ℝ)*(d-(1/2 : ℝ))^0*((3/4 : ℝ)-d)^6 +
        (34496/45 : ℝ)*(d-(1/2 : ℝ))^1*((3/4 : ℝ)-d)^5 +
        (10256/9 : ℝ)*(d-(1/2 : ℝ))^2*((3/4 : ℝ)-d)^4 +
        (8480/9 : ℝ)*(d-(1/2 : ℝ))^3*((3/4 : ℝ)-d)^3 +
        (5956/9 : ℝ)*(d-(1/2 : ℝ))^4*((3/4 : ℝ)-d)^2 +
        (17836/45 : ℝ)*(d-(1/2 : ℝ))^5*((3/4 : ℝ)-d)^1 +
        (1577/15 : ℝ)*(d-(1/2 : ℝ))^6*((3/4 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial0_piece3 {d : ℝ}
    (hlo : (3/4 : ℝ) ≤ d) (hhi : d ≤ (1 : ℝ)) :
    0 ≤ (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 := by
  have hl : 0 ≤ d-(3/4 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1 : ℝ)-d := sub_nonneg.mpr hhi
  have he : (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 =
      (1577/15 : ℝ)*(d-(3/4 : ℝ))^0*((1 : ℝ)-d)^6 +
        (38936/45 : ℝ)*(d-(3/4 : ℝ))^1*((1 : ℝ)-d)^5 +
        (27056/9 : ℝ)*(d-(3/4 : ℝ))^2*((1 : ℝ)-d)^4 +
        (47872/9 : ℝ)*(d-(3/4 : ℝ))^3*((1 : ℝ)-d)^3 +
        (44032/9 : ℝ)*(d-(3/4 : ℝ))^4*((1 : ℝ)-d)^2 +
        (96256/45 : ℝ)*(d-(3/4 : ℝ))^5*((1 : ℝ)-d)^1 +
        (14336/45 : ℝ)*(d-(3/4 : ℝ))^6*((1 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

lemma firstCornerPolynomial0_nonneg {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    0 ≤ (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 := by
  by_cases h1 : d ≤ 1/4
  · exact firstCornerPolynomial0_piece0 hd0 h1
  by_cases h2 : d ≤ 1/2
  · exact firstCornerPolynomial0_piece1 (by linarith) h2
  by_cases h3 : d ≤ 3/4
  · exact firstCornerPolynomial0_piece2 (by linarith) h3
  exact firstCornerPolynomial0_piece3 (by linarith) hd1

private lemma firstCornerPolynomial1_piece0 {d : ℝ}
    (hlo : (0 : ℝ) ≤ d) (hhi : d ≤ (1/4 : ℝ)) :
    0 ≤ ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 := by
  have hl : 0 ≤ d-(0 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1/4 : ℝ)-d := sub_nonneg.mpr hhi
  have he : ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 =
      (21364736/405 : ℝ)*(d-(0 : ℝ))^0*((1/4 : ℝ)-d)^8 +
        (159121408/405 : ℝ)*(d-(0 : ℝ))^1*((1/4 : ℝ)-d)^7 +
        (513953792/405 : ℝ)*(d-(0 : ℝ))^2*((1/4 : ℝ)-d)^6 +
        (187977728/81 : ℝ)*(d-(0 : ℝ))^3*((1/4 : ℝ)-d)^5 +
        (1063959424/405 : ℝ)*(d-(0 : ℝ))^4*((1/4 : ℝ)-d)^4 +
        (254383744/135 : ℝ)*(d-(0 : ℝ))^5*((1/4 : ℝ)-d)^3 +
        (338610992/405 : ℝ)*(d-(0 : ℝ))^6*((1/4 : ℝ)-d)^2 +
        (28318096/135 : ℝ)*(d-(0 : ℝ))^7*((1/4 : ℝ)-d)^1 +
        (1025176/45 : ℝ)*(d-(0 : ℝ))^8*((1/4 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial1_piece1 {d : ℝ}
    (hlo : (1/4 : ℝ) ≤ d) (hhi : d ≤ (1/2 : ℝ)) :
    0 ≤ ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 := by
  have hl : 0 ≤ d-(1/4 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1/2 : ℝ)-d := sub_nonneg.mpr hhi
  have he : ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 =
      (1025176/45 : ℝ)*(d-(1/4 : ℝ))^0*((1/2 : ℝ)-d)^8 +
        (20890352/135 : ℝ)*(d-(1/4 : ℝ))^1*((1/2 : ℝ)-d)^7 +
        (182628368/405 : ℝ)*(d-(1/4 : ℝ))^2*((1/2 : ℝ)-d)^6 +
        (99176704/135 : ℝ)*(d-(1/4 : ℝ))^3*((1/2 : ℝ)-d)^5 +
        (295680064/405 : ℝ)*(d-(1/4 : ℝ))^4*((1/2 : ℝ)-d)^4 +
        (1356544/3 : ℝ)*(d-(1/4 : ℝ))^5*((1/2 : ℝ)-d)^3 +
        (13788928/81 : ℝ)*(d-(1/4 : ℝ))^6*((1/2 : ℝ)-d)^2 +
        (4814848/135 : ℝ)*(d-(1/4 : ℝ))^7*((1/2 : ℝ)-d)^1 +
        (48128/15 : ℝ)*(d-(1/4 : ℝ))^8*((1/2 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial1_piece2 {d : ℝ}
    (hlo : (1/2 : ℝ) ≤ d) (hhi : d ≤ (3/4 : ℝ)) :
    0 ≤ ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 := by
  have hl : 0 ≤ d-(1/2 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (3/4 : ℝ)-d := sub_nonneg.mpr hhi
  have he : ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 =
      (48128/15 : ℝ)*(d-(1/2 : ℝ))^0*((3/4 : ℝ)-d)^8 +
        (2115584/135 : ℝ)*(d-(1/2 : ℝ))^1*((3/4 : ℝ)-d)^7 +
        (12260096/405 : ℝ)*(d-(1/2 : ℝ))^2*((3/4 : ℝ)-d)^6 +
        (4338944/135 : ℝ)*(d-(1/2 : ℝ))^3*((3/4 : ℝ)-d)^5 +
        (11942464/405 : ℝ)*(d-(1/2 : ℝ))^4*((3/4 : ℝ)-d)^4 +
        (13395712/405 : ℝ)*(d-(1/2 : ℝ))^5*((3/4 : ℝ)-d)^3 +
        (11699216/405 : ℝ)*(d-(1/2 : ℝ))^6*((3/4 : ℝ)-d)^2 +
        (5426032/405 : ℝ)*(d-(1/2 : ℝ))^7*((3/4 : ℝ)-d)^1 +
        (984056/405 : ℝ)*(d-(1/2 : ℝ))^8*((3/4 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial1_piece3 {d : ℝ}
    (hlo : (3/4 : ℝ) ≤ d) (hhi : d ≤ (1 : ℝ)) :
    0 ≤ ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 := by
  have hl : 0 ≤ d-(3/4 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1 : ℝ)-d := sub_nonneg.mpr hhi
  have he : ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 =
      (984056/405 : ℝ)*(d-(3/4 : ℝ))^0*((1 : ℝ)-d)^8 +
        (10318864/405 : ℝ)*(d-(3/4 : ℝ))^1*((1 : ℝ)-d)^7 +
        (9189808/81 : ℝ)*(d-(3/4 : ℝ))^2*((1 : ℝ)-d)^6 +
        (22413056/81 : ℝ)*(d-(3/4 : ℝ))^3*((1 : ℝ)-d)^5 +
        (162792064/405 : ℝ)*(d-(3/4 : ℝ))^4*((1 : ℝ)-d)^4 +
        (15935488/45 : ℝ)*(d-(3/4 : ℝ))^5*((1 : ℝ)-d)^3 +
        (74067968/405 : ℝ)*(d-(3/4 : ℝ))^6*((1 : ℝ)-d)^2 +
        (2228224/45 : ℝ)*(d-(3/4 : ℝ))^7*((1 : ℝ)-d)^1 +
        (229376/45 : ℝ)*(d-(3/4 : ℝ))^8*((1 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

lemma firstCornerPolynomial1_nonneg {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    0 ≤ ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 := by
  by_cases h1 : d ≤ 1/4
  · exact firstCornerPolynomial1_piece0 hd0 h1
  by_cases h2 : d ≤ 1/2
  · exact firstCornerPolynomial1_piece1 (by linarith) h2
  by_cases h3 : d ≤ 3/4
  · exact firstCornerPolynomial1_piece2 (by linarith) h3
  exact firstCornerPolynomial1_piece3 (by linarith) hd1

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlanarRadialArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace CubicTorus

lemma square_below_nonnegative_chord {q c e y : ℝ}
    (hl0 : 0≤q) (hl1 : q≤1) (hc : 0 ≤ c) (he : 0≤e) (hy : 0≤y)
    (hch : y≤(1-q)*c+q*e) : y^2≤(1-q)*c^2+q*e^2 := by
  have hl : 0≤1-q := by linarith
  have hh := (sq_le_sq₀ hy (add_nonneg (mul_nonneg hl hc) (mul_nonneg hl0 he))).mpr hch
  have hv := mul_nonneg (mul_nonneg hl0 hl) (sq_nonneg (c-e))
  nlinarith only [hh,hv]

lemma firstCorner_chord_endpoint_bound {d : ℝ} (hd0 : 0≤d) (hd1 : d≤1) :
    (2/9 : ℝ)*d+(4/81)*(1-d^2)^2+
      ((2/9)*(1-d^2)+d*(1-d^2)/(1+(1-d^2)))^2≤3/10 := by
  let b := 1-d^2
  have hb : 0≤b := by dsimp [b]; nlinarith
  have hden : 0<1+b := by linarith
  have hp := firstCornerPolynomial1_nonneg hd0 hd1
  change 0≤(3/10-(2/9)*d-(4/81)*b^2)*(1+b)^2-b^2*((2/9)*(1+b)+d)^2 at hp
  change (2/9)*d+(4/81)*b^2+((2/9)*b+d*b/(1+b))^2≤3/10
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hden)).mp
  have he : ((2/9)*d+(4/81)*b^2+((2/9)*b+d*b/(1+b))^2)*(1+b)^2=
      ((2/9)*d+(4/81)*b^2)*(1+b)^2+b^2*((2/9)*(1+b)+d)^2 := by
    field_simp
  rw [he]
  nlinarith only [hp]

theorem firstCorner_dimensionless_bound {t d : ℝ} (ht0 : 0≤t) (ht1 : t<1)
    (hd0 : 0≤d) (htd : t+d^2≤1) :
    (2/9 : ℝ)*d+(4/81)*t^2+
      ((2/9)*t+d*(1-t-d^2)/(1-t^2))^2≤3/10 := by
  have hd1 : d≤1 := by nlinarith
  let b := 1-d^2
  have hb : 0≤b := by dsimp [b]; nlinarith
  have htb : t≤b := by dsimp [b]; linarith
  have hb1 : b≤1 := by dsimp [b]; nlinarith [sq_nonneg d]
  have htden : 0<1+t := by linarith
  have hbden : 0<1+b := by linarith
  have htden2 : 0<1-t^2 := by nlinarith
  by_cases hbz : b=0
  · have htz : t=0 := by linarith
    have hdz : d=1 := by dsimp [b] at hbz; nlinarith
    rw [htz,hdz]
    norm_num
  have hbpos : 0<b := lt_of_le_of_ne hb (Ne.symm hbz)
  let c := d*b
  let e := (2/9 : ℝ)*b+c/(1+b)
  let q := t/b
  let y := (2/9 : ℝ)*t+d*(b-t)/(1-t^2)
  have hc : 0 ≤ c := mul_nonneg hd0 hb
  have he : 0≤e := by dsimp [e]; positivity
  have hy : 0≤y := by dsimp [y]; positivity
  have hl0 : 0≤q := div_nonneg ht0 hb
  have hl1 : q≤1 := (div_le_one hbpos).mpr htb
  have hlt : q*b=t := div_mul_cancel₀ _ hbz
  have hch : y≤(1-q)*c+q*e := by
    have h1 : d*(b-t)/(1-t^2) ≤ c/(1+t) := by
      dsimp only [c]
      apply (div_le_div_iff₀ htden2 htden).mpr
      have hh := mul_nonneg (mul_nonneg hd0 ht0) (sub_nonneg.mpr hb1)
      have hh' := mul_nonneg hh htden.le
      nlinarith only [hh']
    have h2 : (2/9 : ℝ)*t+c/(1+t)≤(1-q)*c+q*e := by
      have hid : (1-q)*c+q*e-((2/9 : ℝ)*t+c/(1+t))=
          c*t*(b-t)/((1+b)*(1+t)) := by
        dsimp only [q,e]
        field_simp
        ring
      have hh : 0 ≤ c*t*(b-t)/((1+b)*(1+t)) := by positivity
      rw [← hid] at hh
      linarith
    exact le_trans (add_le_add le_rfl h1) h2
  have hysq := square_below_nonnegative_chord hl0 hl1 hc he hy hch
  have htsq : t^2≤q*b^2 := by
    rw [← hlt]
    have hl2 := mul_nonneg hl0 (sub_nonneg.mpr hl1)
    have hh := mul_nonneg hl2 (sq_nonneg b)
    nlinarith only [hh]
  have h0 := firstCornerPolynomial0_nonneg hd0 hd1
  have h1 := firstCorner_chord_endpoint_bound hd0 hd1
  have h0' : (2/9 : ℝ)*d+c^2≤3/10 := by dsimp [c,b]; nlinarith only [h0]
  have h1' : (2/9 : ℝ)*d+(4/81)*b^2+e^2≤3/10 := h1
  have hK0 := mul_le_mul_of_nonneg_left h0' (sub_nonneg.mpr hl1)
  have hK1 := mul_le_mul_of_nonneg_left h1' hl0
  have hydef : ((2/9 : ℝ)*t+d*(1-t-d^2)/(1-t^2))=y := by
    dsimp [y,b]; congr 1; congr 1; ring
  rw [hydef]
  nlinarith only [hysq,htsq,hK0,hK1]

theorem firstCorner_scaled_strict_bound {t d x : ℝ} (ht0 : 0≤t) (ht1 : t<1)
    (hd0 : 0≤d) (htd : t+d^2≤1)
    (hx : x=Real.pi*(1-t-d^2)/(1-t^2)) :
    (2*Real.pi/9)*d+
      ((2*Real.pi/9)^2*t^2+((2*Real.pi/9)*t+x*d)^2)/Real.pi<1 := by
  have hh := firstCorner_dimensionless_bound ht0 ht1 hd0 htd
  have hp := mul_le_mul_of_nonneg_left hh Real.pi_pos.le
  have he : (2*Real.pi/9)*d+
      ((2*Real.pi/9)^2*t^2+((2*Real.pi/9)*t+x*d)^2)/Real.pi=
      Real.pi*((2/9)*d+(4/81)*t^2+((2/9)*t+d*(1-t-d^2)/(1-t^2))^2) := by
    rw [hx]
    field_simp
    ring
  rw [he]
  nlinarith only [hp,Real.pi_lt_d2]

end CubicTorus

end
end

section

noncomputable section
open Set
namespace CubicTorus

theorem firstCorner_endpoint_contradiction {A h b r s : ℝ}
    (hA0 : 0<A) (hA : A≤2*Real.pi/9) (hh : 0≤h)
    (hb0 : 0≤b) (hb1 : b<1) (hr0 : 0 ≤ r) (hr1 : r≤4*Real.pi/81)
    (hs1 : s≤1)
    (htop : Real.sqrt (Real.pi*r)≤A*b-h*(4*Real.pi/81-r))
    (hbottom : Real.sqrt (Real.pi*(1-s))≤A*b+h*(s-4*Real.pi/81))
    (hdrop : s-r≤A*Real.sqrt (1-b)) : False := by
  let a := 2*Real.pi/9
  let x := h*A
  let d := Real.sqrt (1-b)
  let w := Real.sqrt (Real.pi*r)/a
  have ha : 0<a := by dsimp [a]; positivity
  have hp : Real.pi≠0 := Real.pi_pos.ne'
  have hva : 4*Real.pi/81=a^2/Real.pi := by dsimp [a]; field_simp; ring
  have haA : A≤a := hA
  have hx0 : 0≤x := mul_nonneg hh hA0.le
  have hd0 : 0≤d := Real.sqrt_nonneg _
  have hd2 : d^2=1-b := Real.sq_sqrt (by linarith)
  have hw0 : 0≤w := div_nonneg (Real.sqrt_nonneg _) ha.le
  have haw : a*w=Real.sqrt (Real.pi*r) := by dsimp only [w]; field_simp
  have hrw : r=a^2*w^2/Real.pi := by
    have hz := Real.sq_sqrt (mul_nonneg Real.pi_pos.le hr0)
    rw [← haw,mul_pow] at hz
    apply (eq_div_iff hp).mpr
    nlinarith only [hz]
  have hw1 : w≤1 := by
    rw [hva,hrw] at hr1
    have hz := (div_le_div_iff_of_pos_right Real.pi_pos).mp hr1
    have ha2 := sq_pos_of_pos ha
    have hw2' : w^2≤1 := (mul_le_mul_iff_right₀ ha2).mp (by simpa only [mul_one] using hz)
    nlinarith only [hw2',hw0]
  have hw2 : 0≤1-w^2 := by nlinarith
  have hxn : x≤h*a := mul_le_mul_of_nonneg_left haA hh
  have hnorm : w+x/Real.pi*(1-w^2)≤b := by
    have hleft := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hxn Real.pi_pos.le) hw2
    have hleft' := mul_le_mul_of_nonneg_left (add_le_add (le_refl w) hleft) ha.le
    have ht : a*(w+h*a/Real.pi*(1-w^2))≤A*b := by
      have hid : a*(w+h*a/Real.pi*(1-w^2))=a*w+h*(4*Real.pi/81-r) := by
        rw [hva,hrw]
        ring
      rw [hid,haw]
      linarith only [htop]
    have hright := mul_le_mul_of_nonneg_right haA hb0
    exact (mul_le_mul_iff_right₀ ha).mp (hleft'.trans (ht.trans hright))
  let f : ℝ → ℝ := fun t => t+x/Real.pi*(1-t^2)
  have hf : Continuous f := by fun_prop
  have hf1 : f 1=1 := by dsimp [f]; ring
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc hw1 hf.continuousOn
    (show b∈Icc (f w) (f 1) from ⟨hnorm,by rw [hf1]; exact hb1.le⟩)
  have ht0 : 0≤t := hw0.trans ht.1
  have ht1 : t<1 := by
    by_contra hn
    have he : t=1 := le_antisymm ht.2 (le_of_not_gt hn)
    rw [he,hf1] at hft
    linarith
  have htden : 0<1-t^2 := by nlinarith
  have hroot : t+x/Real.pi*(1-t^2)=b := hft
  have hxterm : 0≤x/Real.pi*(1-t^2) := by positivity
  have htd : t+d^2≤1 := by linarith only [hroot,hxterm,hd2]
  have hxroot : x=Real.pi*(1-t-d^2)/(1-t^2) := by
    apply (eq_div_iff htden.ne').mpr
    have he := congrArg (fun y : ℝ => y*Real.pi) hroot
    field_simp at he
    rw [show 1-t-d^2=b-t by linarith only [hd2]]
    nlinarith only [he]
  have hwtsq : w^2≤t^2 := (sq_le_sq₀ hw0 ht0).mpr ht.1
  have hrbound : r≤a^2*t^2/Real.pi := by
    rw [hrw]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwtsq (sq_nonneg a)) Real.pi_pos.le
  have hEt : A*b-h*(4*Real.pi/81-a^2*t^2/Real.pi)≤a*t := by
    have he : A*b-h*(4*Real.pi/81-a^2*t^2/Real.pi)=
        A*t+(h/Real.pi)*(A^2-a^2)*(1-t^2) := by
      rw [hva,← hroot]
      dsimp only [x]
      ring
    have hA2 : A^2≤a^2 := (sq_le_sq₀ hA0.le ha.le).mpr haA
    have hcorr : (h/Real.pi)*(A^2-a^2)*(1-t^2)≤0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hh Real.pi_pos.le) (sub_nonpos.mpr hA2)) htden.le
    rw [he]
    have hat := mul_le_mul_of_nonneg_right haA ht0
    linarith only [hcorr,hat]
  have hsb : s≤a^2*t^2/Real.pi+a*d := by
    have hAd := mul_le_mul_of_nonneg_right haA hd0
    linarith only [hdrop,hrbound,hAd]
  have hbottom' : Real.sqrt (Real.pi*(1-s))≤a*t+x*d := by
    have hdiff := mul_le_mul_of_nonneg_left hdrop hh
    have hrr := mul_le_mul_of_nonneg_left hrbound hh
    have hxd : h*(A*d)=x*d := by dsimp [x]; ring
    rw [hxd] at hdiff
    linarith only [hbottom,hdiff,hrr,hEt]
  have hbsq : Real.pi*(1-s)≤(a*t+x*d)^2 := by
    have hy : 0≤a*t+x*d := by positivity
    have hh' := (sq_le_sq₀ (Real.sqrt_nonneg (Real.pi*(1-s))) hy).mpr hbottom'
    rwa [Real.sq_sqrt (mul_nonneg Real.pi_pos.le (by linarith : 0≤1-s))] at hh'
  have hnec : 1≤a*d+(a^2*t^2+(a*t+x*d)^2)/Real.pi := by
    have hh' := mul_le_mul_of_nonneg_left hsb Real.pi_pos.le
    have hcancel : Real.pi*(a^2*t^2/Real.pi+a*d)=a^2*t^2+Real.pi*a*d := by field_simp
    rw [hcancel] at hh'
    have hh2 : 1≤((a*d)*Real.pi+(a^2*t^2+(a*t+x*d)^2))/Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by nlinarith only [hh',hbsq])
    simpa only [add_div,mul_div_cancel_right₀ _ hp] using hh2
  exact (not_lt_of_ge hnec) (firstCorner_scaled_strict_bound ht0 ht1 hd0 htd hxroot)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_MinimizerFirstTransitionTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma firstTransition_mem_Ioo_half : 4*Real.pi/81∈Ioo (0 : ℝ) (1/2) := by
  constructor
  · positivity
  · linarith [Real.pi_lt_four]

theorem isMinimizerAt_first_transition_corner_excluded_oai
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt (4*Real.pi/81) E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (hw : axialFluxWeight μ 0<1)
    (ht1 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=1)))∉openRepresentative E)
    (ht2 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=2)))∉openRepresentative E)
    (hb1 : quotientMap (chamberVertex c (fun j => decide (j=1)))∈openRepresentative E)
    (hb2 : quotientMap (chamberVertex c (fun j => decide (j=2)))∈openRepresentative E) : False := by
  obtain ⟨hA,hAc,_,hh,hr0,hrV,_,hs1,hb0,_,ht,hb,hd⟩ :=
    isMinimizerAt_four_corner_necessary_data firstTransition_mem_Ioo_half hE hm hμ hN hp ha hs hsg hH ht1 ht2 hb1 hb2
  have hrad : Real.sqrt (Real.pi*(4*Real.pi/81))=2*Real.pi/9 := by
    have hsqrt := Real.sq_sqrt (show 0≤Real.pi*(4*Real.pi/81) by positivity)
    have hnon := Real.sqrt_nonneg (Real.pi*(4*Real.pi/81))
    have hp := Real.pi_pos
    nlinarith only [hsqrt,hnon,hp]
  rw [hrad] at hAc
  exact firstCorner_endpoint_contradiction hA hAc hh hb0 hw hr0 hrV hs1 ht hb hd

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_first_transition_corner_excluded_oai := @OAI.CubicTorus.isMinimizerAt_first_transition_corner_excluded_oai

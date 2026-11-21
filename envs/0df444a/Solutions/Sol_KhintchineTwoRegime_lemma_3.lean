-- Prove2me | solution 1 for KhintchineTwoRegime.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:44:50.609963+00:00
-- url     : https://prove2.me/submissions/b12402da-4e5d-4299-8de4-99abe20c98f8

import Mathlib
import Definitions.Def_KhintchineTwoRegime_J
import Definitions.Def_KhintchineTwoRegime_H

namespace KhintchineTwoRegime

private noncomputable def K3 : ℝ := (7423 : ℝ) / 10000

private noncomputable def CL : ℝ := (7978845 : ℝ) / 10000000

private noncomputable def Q3 (x y : ℝ) : ℝ :=
  1 - 2 * x * y - 2 * (2 * K3 - x - y) ^ 2

private def GoodRow (l u t A B : ℝ) : Prop :=
  u ≤ K3 ∧
    u ≤ 1 ∧
      0 ≤ A ∧
        (1 : ℝ) / 2 ≤ A ^ 2 ∧
          0 ≤ B ∧
            (1 : ℝ) / 2 ≤ B ^ 2 ∧
              A ≤ B ∧
                A ^ 2 * (8 + 8 * u ^ 2 + 3 * u ^ 4) < 8 + 4 * u ^ 2 ∧
                  B ^ 2 * (8 + 8 * t ^ 2 + 3 * t ^ 4) < 8 + 4 * t ^ 2 ∧
                    0 < Q3 l t ∧
                      K3 < CL * (u ^ 2 * A + (1 - u ^ 2) * B)

private lemma sq_le_sq_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := hx.trans hxy
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx hy)]

private lemma lt_sqrt_of_sq_lt {A z : ℝ} (hA : 0 ≤ A) (hz : 0 ≤ z)
    (h : A ^ 2 < z) : A < Real.sqrt z := by
  have hs : 0 ≤ Real.sqrt z := Real.sqrt_nonneg z
  have hsq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz
  by_contra hlt
  have hle : Real.sqrt z ≤ A := le_of_not_gt hlt
  have hp : 0 ≤ (A - Real.sqrt z) * (A + Real.sqrt z) :=
    mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hA hs)
  nlinarith

private lemma rFun_lower {x u A : ℝ} (hx0 : 0 ≤ x) (hxu : x ≤ u)
    (hA0 : 0 ≤ A) (hA2 : (1 : ℝ) / 2 ≤ A ^ 2)
    (hrow : A ^ 2 * (8 + 8 * u ^ 2 + 3 * u ^ 4) < 8 + 4 * u ^ 2) :
    A < rFun x := by
  have hu0 : 0 ≤ u := hx0.trans hxu
  have hx2 : x ^ 2 ≤ u ^ 2 := sq_le_sq_of_nonneg hx0 hxu
  have hx4 : x ^ 4 ≤ u ^ 4 := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ ≤ (u ^ 2) ^ 2 := sq_le_sq_of_nonneg (sq_nonneg x) hx2
      _ = u ^ 4 := by ring
  have hcoef : 0 ≤ 8 * A ^ 2 - 4 := by
    nlinarith
  have h3A : 0 ≤ 3 * A ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg A)
  have hp :
      (8 * A ^ 2 - 4) * x ^ 2 + 3 * A ^ 2 * x ^ 4 + 8 * A ^ 2 ≤
        (8 * A ^ 2 - 4) * u ^ 2 + 3 * A ^ 2 * u ^ 4 + 8 * A ^ 2 := by
    have h₁ := mul_nonneg hcoef (sub_nonneg.mpr hx2)
    have h₂ := mul_nonneg h3A (sub_nonneg.mpr hx4)
    nlinarith
  have hpu :
      (8 * A ^ 2 - 4) * u ^ 2 + 3 * A ^ 2 * u ^ 4 + 8 * A ^ 2 < 8 := by
    nlinarith [hrow]
  have hpx :
      (8 * A ^ 2 - 4) * x ^ 2 + 3 * A ^ 2 * x ^ 4 + 8 * A ^ 2 < 8 :=
    hp.trans_lt hpu
  have hrowx : A ^ 2 * (8 + 8 * x ^ 2 + 3 * x ^ 4) < 8 + 4 * x ^ 2 := by
    nlinarith [hpx]
  have hD : 0 < 8 + 8 * x ^ 2 + 3 * x ^ 4 := by
    positivity
  have hN : 0 < 8 + 4 * x ^ 2 := by
    positivity
  have hfrac : A ^ 2 < (8 + 4 * x ^ 2) / (8 + 8 * x ^ 2 + 3 * x ^ 4) :=
    (lt_div_iff₀ hD).2 hrowx
  have hz : 0 ≤ (8 + 4 * x ^ 2) / (8 + 8 * x ^ 2 + 3 * x ^ 4) :=
    (div_pos hN hD).le
  unfold rFun
  exact lt_sqrt_of_sq_lt hA0 hz hfrac

private lemma CL_lt_Cconst : CL < Cconst := by
  have hclpos : 0 < CL ^ 2 := by
    norm_num [CL]
  have hnum : CL ^ 2 * (3.14159265358979323847 : ℝ) < 2 := by
    norm_num [CL]
  have hmul : CL ^ 2 * Real.pi < CL ^ 2 * (3.14159265358979323847 : ℝ) :=
    mul_lt_mul_of_pos_left Real.pi_lt_d20 hclpos
  have hsq : CL ^ 2 < 2 / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).2
    linarith
  have hcl0 : 0 ≤ CL := by
    norm_num [CL]
  have hz : 0 ≤ (2 : ℝ) / Real.pi :=
    (div_pos (by norm_num) Real.pi_pos).le
  unfold Cconst
  exact lt_sqrt_of_sq_lt hcl0 hz hsq

private lemma Q3_mono {l t a b : ℝ} (hla : l ≤ a) (htb : t ≤ b)
    (haK : a ≤ K3) (hbK : b ≤ K3) (hsum : a + b ≤ 1) :
    Q3 l t ≤ Q3 a b := by
  have hk : 0 ≤ 6 * K3 - 4 := by
    norm_num [K3]
  have hfy : 0 ≤ 8 * K3 - 6 * l - 2 * b - 2 * t := by
    nlinarith
  have hfx : 0 ≤ 8 * K3 - 2 * a - 2 * l - 6 * b := by
    nlinarith
  have hmy : 0 ≤ (b - t) * (8 * K3 - 6 * l - 2 * b - 2 * t) :=
    mul_nonneg (sub_nonneg.mpr htb) hfy
  have hmx : 0 ≤ (a - l) * (8 * K3 - 2 * a - 2 * l - 6 * b) :=
    mul_nonneg (sub_nonneg.mpr hla) hfx
  have hstep_y : Q3 l t ≤ Q3 l b := by
    unfold Q3
    nlinarith [hmy]
  have hstep_x : Q3 l b ≤ Q3 a b := by
    unfold Q3
    nlinarith [hmx]
  exact hstep_y.trans hstep_x

private lemma K3_lt_J_of_Q {a b : ℝ} (hQ : 0 < Q3 a b)
    (hs : 0 ≤ 2 * K3 - a - b) : K3 < J a b := by
  have hq : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsquare :
      (Real.sqrt 2 * (2 * K3 - a - b)) ^ 2 < 1 - 2 * a * b := by
    calc
      (Real.sqrt 2 * (2 * K3 - a - b)) ^ 2 =
          2 * (2 * K3 - a - b) ^ 2 := by
        rw [mul_pow, hq2]
      _ < 1 - 2 * a * b := by
        unfold Q3 at hQ
        nlinarith
  have hrad : 0 ≤ 1 - 2 * a * b := by
    nlinarith [sq_nonneg (Real.sqrt 2 * (2 * K3 - a - b))]
  have hlt :
      Real.sqrt 2 * (2 * K3 - a - b) < Real.sqrt (1 - 2 * a * b) :=
    lt_sqrt_of_sq_lt (mul_nonneg hq.le hs) hrad hsquare
  have hden : 0 < 2 * Real.sqrt 2 := mul_pos (by norm_num) hq
  have hrepr :
      (a + b) / 2 + Real.sqrt (1 - 2 * a * b) / (2 * Real.sqrt 2) - K3 =
        (Real.sqrt (1 - 2 * a * b) - Real.sqrt 2 * (2 * K3 - a - b)) /
          (2 * Real.sqrt 2) := by
    field_simp [ne_of_gt hq]
    <;> ring
  have hpos :
      0 < (a + b) / 2 + Real.sqrt (1 - 2 * a * b) / (2 * Real.sqrt 2) - K3 := by
    rw [hrepr]
    exact div_pos (sub_pos.mpr hlt) hden
  unfold J
  linarith

private lemma row_bound {l u t A B a b : ℝ} (hrow : GoodRow l u t A B)
    (hla : l ≤ a) (hau : a ≤ u) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hba : b ≤ a) (hsum : a + b ≤ 1) (hCL : CL < Cconst) :
    K3 < max (J a b) (H a b) := by
  rcases hrow with
    ⟨huK, hu1, hA0, hA2, hB0, hB2, hAB, hrA, hrB, hQ, hnum⟩
  have hc0 : 0 < CL := by
    norm_num [CL]
  have hC0 : 0 < Cconst := hc0.trans hCL
  by_cases htb : t ≤ b
  · have haK : a ≤ K3 := hau.trans huK
    have hbK : b ≤ K3 := hba.trans haK
    have hQle : Q3 l t ≤ Q3 a b := Q3_mono hla htb haK hbK hsum
    have hQpos : 0 < Q3 a b := hQ.trans_le hQle
    have hKs : (1 : ℝ) ≤ 2 * K3 := by
      norm_num [K3]
    have hs : 0 ≤ 2 * K3 - a - b := by
      linarith
    have hj : K3 < J a b := K3_lt_J_of_Q hQpos hs
    exact hj.trans_le (le_max_left _ _)
  · have hbt : b ≤ t := (lt_of_not_ge htb).le
    have hra : A < rFun a := rFun_lower ha0 hau hA0 hA2 hrA
    have hrb : B < rFun b := rFun_lower hb0 hbt hB0 hB2 hrB
    have ha2u : a ^ 2 ≤ u ^ 2 := sq_le_sq_of_nonneg ha0 hau
    have ha2one : a ^ 2 ≤ 1 := by
      calc
        a ^ 2 ≤ (1 : ℝ) ^ 2 := sq_le_sq_of_nonneg ha0 (hau.trans hu1)
        _ = 1 := by norm_num
    have hwb : 0 ≤ 1 - a ^ 2 := sub_nonneg.mpr ha2one
    have hFa :
        u ^ 2 * A + (1 - u ^ 2) * B ≤ a ^ 2 * A + (1 - a ^ 2) * B := by
      have hp : 0 ≤ (u ^ 2 - a ^ 2) * (B - A) :=
        mul_nonneg (sub_nonneg.mpr ha2u) (sub_nonneg.mpr hAB)
      nlinarith [hp]
    have hweighted :
        a ^ 2 * A + (1 - a ^ 2) * B ≤
          a ^ 2 * rFun a + (1 - a ^ 2) * rFun b :=
      add_le_add
        (mul_le_mul_of_nonneg_left hra.le (sq_nonneg a))
        (mul_le_mul_of_nonneg_left hrb.le hwb)
    have hF :
        u ^ 2 * A + (1 - u ^ 2) * B ≤
          a ^ 2 * rFun a + (1 - a ^ 2) * rFun b :=
      hFa.trans hweighted
    have hk0 : 0 < K3 := by
      norm_num [K3]
    have hFu : 0 < u ^ 2 * A + (1 - u ^ 2) * B := by
      by_contra h
      have hle : u ^ 2 * A + (1 - u ^ 2) * B ≤ 0 := le_of_not_gt h
      have hm : CL * (u ^ 2 * A + (1 - u ^ 2) * B) ≤ 0 := by
        have hm' := mul_le_mul_of_nonneg_left hle hc0.le
        simpa using hm'
      linarith
    have hcF :
        CL * (u ^ 2 * A + (1 - u ^ 2) * B) <
          Cconst * (u ^ 2 * A + (1 - u ^ 2) * B) :=
      mul_lt_mul_of_pos_right hCL hFu
    have hend : K3 < Cconst * (u ^ 2 * A + (1 - u ^ 2) * B) :=
      hnum.trans hcF
    have hCF :
        Cconst * (u ^ 2 * A + (1 - u ^ 2) * B) ≤
          Cconst * (a ^ 2 * rFun a + (1 - a ^ 2) * rFun b) :=
      mul_le_mul_of_nonneg_left hF hC0.le
    have hh : K3 < H a b := by
      unfold H
      exact hend.trans_le hCF
    exact hh.trans_le (le_max_right _ _)

theorem _root_.solution (a b : ℝ) (ha₁ : 1 / 2 ≤ a) (ha₂ : a ≤ 7423 / 10000)
    (hb₀ : 0 ≤ b) (hba : b ≤ a) (hab : a + b ≤ 1) :
    (7423 : ℝ) / 10000 < max (J a b) (H a b) := by
  have ha0 : 0 ≤ a := by
    linarith
  have haK : a ≤ K3 := by
    simpa [K3] using ha₂
  have hC : CL < Cconst := CL_lt_Cconst
  suffices h : K3 < max (J a b) (H a b) by
    simpa [K3] using h
  by_cases h₁ : a ≤ (63 : ℝ) / 100
  · exact row_bound
      (l := (1 : ℝ) / 2) (u := (63 : ℝ) / 100) (t := (47 : ℝ) / 100)
      (A := (907263 : ℝ) / 1000000) (B := (946627 : ℝ) / 1000000)
      (a := a) (b := b)
      (by norm_num [GoodRow, Q3, K3, CL]) ha₁ h₁ ha0 hb₀ hba hab hC
  by_cases h₂ : a ≤ (71 : ℝ) / 100
  · have hl : (63 : ℝ) / 100 ≤ a := by
      linarith
    exact row_bound
      (l := (63 : ℝ) / 100) (u := (71 : ℝ) / 100) (t := (294 : ℝ) / 1000)
      (A := (884775 : ℝ) / 1000000) (B := (978647 : ℝ) / 1000000)
      (a := a) (b := b)
      (by norm_num [GoodRow, Q3, K3, CL]) hl h₂ ha0 hb₀ hba hab hC
  by_cases h₃ : a ≤ (738 : ℝ) / 1000
  · have hl : (71 : ℝ) / 100 ≤ a := by
      linarith
    exact row_bound
      (l := (71 : ℝ) / 100) (u := (738 : ℝ) / 1000) (t := (144 : ℝ) / 1000)
      (A := (876564 : ℝ) / 1000000) (B := (994829 : ℝ) / 1000000)
      (a := a) (b := b)
      (by norm_num [GoodRow, Q3, K3, CL]) hl h₃ ha0 hb₀ hba hab hC
  · have hl : (738 : ℝ) / 1000 ≤ a := by
      linarith
    exact row_bound
      (l := (738 : ℝ) / 1000) (u := (7423 : ℝ) / 10000) (t := (86 : ℝ) / 1000)
      (A := (875289 : ℝ) / 1000000) (B := (998152 : ℝ) / 1000000)
      (a := a) (b := b)
      (by norm_num [GoodRow, Q3, K3, CL]) hl haK ha0 hb₀ hba hab hC

end KhintchineTwoRegime

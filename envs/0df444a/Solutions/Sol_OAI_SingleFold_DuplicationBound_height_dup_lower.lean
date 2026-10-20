-- Prove2me | solution 1 for OAI.SingleFold.DuplicationBound.height_dup_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:13:31.478332+00:00
-- url     : https://prove2.me/submissions/29556efb-ccbb-4689-aa99-c2d9982db911

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Duplication.lean:L55-L97
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.DuplicationBound.height_dup_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication

-- ---- from OAI.NumberTheory.SingleFold.Duplication ----
namespace OAI

namespace SingleFold.DuplicationBound

lemma gcd_numerator_divides (a b : ℤ) (h : IsCoprime a b) :
    gcd ((a^2+25*b^2)^2) (4*a*b*(a^2-25*b^2)) ∣ (6250000:ℤ) := by
  let N := (a^2+25*b^2)^2
  have ht : IsCoprime (a^2+25*b^2) b := by
    have hh := (h.pow_left (m:=2)).add_mul_right_left (25*b)
    simpa only [pow_two,mul_assoc] using hh
  have hs : IsCoprime (a^2-25*b^2) b := by
    have hh := (h.pow_left (m:=2)).add_mul_right_left (-25*b)
    simpa only [pow_two,mul_assoc,neg_mul,sub_eq_add_neg] using hh
  have h4 : gcd N 4 ∣ (4:ℤ) := gcd_dvd_right _ _
  have ha : gcd N a ∣ (625:ℤ) := by
    have hcop : IsCoprime (gcd N a) (b^4) :=
      (h.of_isCoprime_of_dvd_left (gcd_dvd_right N a)).pow_right
    apply hcop.dvd_of_dvd_mul_right
    have hh := dvd_sub (gcd_dvd_left N a)
      (dvd_mul_of_dvd_left (gcd_dvd_right N a) (a^3+50*a*b^2))
    convert hh using 1; dsimp [N]; ring
  have hb : gcd N b ∣ (1:ℤ) :=
    ((ht.pow_left (m:=2)).isUnit_of_dvd' (gcd_dvd_left N b) (gcd_dvd_right N b)).dvd
  have hc : gcd N (a^2-25*b^2) ∣ (2500:ℤ) := by
    have hcop : IsCoprime (gcd N (a^2-25*b^2)) (b^4) :=
      (hs.of_isCoprime_of_dvd_left (gcd_dvd_right N _)).pow_right
    apply hcop.dvd_of_dvd_mul_right
    have hh := dvd_sub (gcd_dvd_left N (a^2-25*b^2))
      (dvd_mul_of_dvd_left (gcd_dvd_right N (a^2-25*b^2)) (a^2+75*b^2))
    convert hh using 1; dsimp [N]; ring
  have hh := gcd_mul_dvd_mul_gcd N (4*a*b) (a^2-25*b^2)
  have h₁ := gcd_mul_dvd_mul_gcd N (4*a) b
  have h₂ := gcd_mul_dvd_mul_gcd N 4 a
  exact hh.trans ((mul_dvd_mul
    (h₁.trans (mul_dvd_mul (h₂.trans (mul_dvd_mul h4 ha)) hb)) hc) |>.trans (by norm_num))

lemma common_divisor_bound (a b c : ℤ) (h : IsCoprime a b)
    (hN : c ∣ (a^2+25*b^2)^2) (hD : c ∣ 4*a*b*(a^2-25*b^2)) : c ∣ (6250000:ℤ) :=
  (dvd_gcd hN hD).trans (gcd_numerator_divides a b h)

lemma dupX_fraction (x : ℚ) : dupX x =
    (((x.num:ℤ)^2+25*(x.den:ℤ)^2)^2 : ℤ) / (4*x.num*x.den*(x.num^2-25*(x.den:ℤ)^2) : ℤ) := by
  have hb : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  conv_lhs => rw [←x.num_div_den]
  unfold dupX
  push_cast
  field_simp

lemma height_dup_lower (x : ℚ) (hx : x ≠ 0) (hs : x^2-25 ≠ 0) :
    height x ^ 4 ≤ 6250000 * height (dupX x) := by
  let a := x.num
  let b : ℤ := x.den
  let N := (a^2+25*b^2)^2
  let D := 4*a*b*(a^2-25*b^2)
  have hb : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have ha : a ≠ 0 := Rat.num_ne_zero.mpr hx
  have hsn : a^2-25*b^2 ≠ 0 := by
    intro hh
    apply hs
    rw [←x.num_div_den]
    dsimp [a,b] at hh
    have hh' : (x.num:ℚ)^2-25*(x.den:ℚ)^2=0 := by exact_mod_cast hh
    field_simp
    nlinarith only [hh']
  have hD : D ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha)
    (by dsimp [b]; exact_mod_cast x.den_ne_zero)) hsn
  have hf : dupX x = Rat.divInt N D := by
    rw [Rat.divInt_eq_div]
    exact dupX_fraction x
  obtain ⟨c,hNc,hDc⟩ := Rat.num_den_mk hD hf
  have hc : c ∣ (6250000:ℤ) := common_divisor_bound a b c x.isCoprime_num_den
    ⟨_,hNc⟩ ⟨_,hDc⟩
  have hc' : c.natAbs ≤ 6250000 := Nat.le_of_dvd (by norm_num) (Int.natAbs_dvd_natAbs.mpr hc)
  have hN : N.natAbs ≤ 6250000 * height (dupX x) := by
    rw [hNc,Int.natAbs_mul]
    exact Nat.mul_le_mul hc' (le_max_left _ _)
  apply le_trans _ hN
  have hN' : (N.natAbs:ℤ)=N := Int.natAbs_of_nonneg (sq_nonneg _)
  have ha' : (a.natAbs:ℤ)^2=a^2 := by rw [Int.natCast_natAbs,sq_abs]
  apply Int.ofNat_le.mp
  rw [hN']
  push_cast
  unfold height
  rcases le_total x.num.natAbs x.den with hl|hl
  · rw [max_eq_right hl]
    change (b^4:ℤ) ≤ (a^2+25*b^2)^2
    nlinarith [sq_nonneg (a^2),sq_nonneg (b^2),mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  · rw [max_eq_left hl]
    change (a.natAbs:ℤ)^4 ≤ (a^2+25*b^2)^2
    rw [show (a.natAbs:ℤ)^4=((a.natAbs:ℤ)^2)^2 by ring,ha']
    nlinarith [sq_nonneg (b^2),mul_nonneg (sq_nonneg a) (sq_nonneg b)]

end SingleFold.DuplicationBound

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.DuplicationBound


theorem solution : type_of% @_root_.OAI.SingleFold.DuplicationBound.height_dup_lower := @_root_.OAI.SingleFold.DuplicationBound.height_dup_lower

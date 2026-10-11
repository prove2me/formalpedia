-- Prove2me | solution 1 for IntMul.CarryProduct.logarithmic_coefficient_precision
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T15:44:45.238978+00:00
-- url     : https://prove2.me/submissions/4c893928-13f0-4dfa-847b-0819eefa6b1d

import Definitions.Def_IntMul_CarryProduct
import Theorems.Thm_IntMul_CarryNormalization_product_recovery
import Mathlib.Tactic
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace IntMul.CarryProduct

private theorem block_count_le (B : ℕ) (x : List Bool) (hB : 0<B) :
    DigitConvolution.blockCount B x≤x.length := by
  unfold DigitConvolution.blockCount
  by_cases hx : x.length=0
  · rw [hx,Nat.zero_add]
    rw [Nat.div_eq_of_lt (by omega : B-1<B)]
  · have hn : 1≤x.length := by omega
    have hm : (x.length-1)*1≤(x.length-1)*B := Nat.mul_le_mul_left _ (by omega : 1≤B)
    simp only [Nat.mul_one] at hm
    have he : x.length-1+1=x.length := by omega
    have h : x.length+B-1≤B*x.length := by
      calc
        x.length+B-1=(x.length-1)+B := by omega
        _≤(x.length-1)*B+B := Nat.add_le_add_right hm B
        _=((x.length-1)+1)*B := by ring
        _=B*x.length := by rw [he];ring
    exact Nat.div_le_of_le_mul h

private theorem precision_bound (B : ℕ) (x y : List Bool) (hb : lg (x.length+y.length)≤B) :
    coefficientWidth B x y≤3*B := by
  have hlg : 1≤lg (x.length+y.length) := Nat.le_max_right _ _
  have hB : 0<B := by omega
  have hx := block_count_le B x hB
  have hm : min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)≤x.length+y.length := by
    have h := Nat.min_le_left (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)
    omega
  have hc : Nat.clog 2 (x.length+y.length)≤B :=
    (Nat.le_max_left _ _).trans hb
  have hp : x.length+y.length≤2^B :=
    (Nat.le_pow_clog (by decide : 1<2) _).trans (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hc)
  have hcp : Nat.clog 2 (min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y))≤B :=
    Nat.clog_le_of_le_pow (hm.trans hp)
  unfold coefficientWidth
  omega

/-- A logarithmic block size admits a uniform three-block-bit coefficient
precision, including every coefficient-plus-carry sum during normalization. -/
private theorem logarithmic_coefficient_precision (B : ℕ) (x y : List Bool)
    (hb : lg (x.length+y.length)≤B) :
    coefficientWidth B x y≤3*B ∧
      ∀ a ∈ CarryNormalization.coefficients B x y, ∀ j : ℕ,
        a+CarryNormalization.carryAt (2^B) (CarryNormalization.coefficients B x y) 0 j<2^(3*B) := by
  have hN := precision_bound B x y hb
  have hlg : 1≤lg (x.length+y.length) := Nat.le_max_right _ _
  have hB : 0<B := by omega
  have h := (CarryNormalization.product_recovery B hB x y).2.2.2.2
  refine ⟨hN,?_⟩
  intro a ha j
  have ha' := h a ha j
  exact lt_of_lt_of_le ha' (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hN)
end IntMul.CarryProduct

open IntMul IntMul.CarryProduct

theorem solution (B : ℕ) (x y : List Bool)
    (hb : lg (x.length+y.length)≤B) :
    coefficientWidth B x y≤3*B ∧
      ∀ a ∈ CarryNormalization.coefficients B x y, ∀ j : ℕ,
        a+CarryNormalization.carryAt (2^B) (CarryNormalization.coefficients B x y) 0 j<2^(3*B) :=
  IntMul.CarryProduct.logarithmic_coefficient_precision B x y hb

#print axioms solution

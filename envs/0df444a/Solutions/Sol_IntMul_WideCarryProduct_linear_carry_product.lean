-- Prove2me | solution 1 for IntMul.WideCarryProduct.linear_carry_product
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T16:17:07.584301+00:00
-- url     : https://prove2.me/submissions/a1bc3005-1ac6-4176-93fa-18c365192d0f

import Definitions.Def_IntMul_WideCarryProduct
import Theorems.Thm_IntMul_WideCarryProduct_wide_carry_product
import Theorems.Thm_IntMul_CarryProduct_logarithmic_coefficient_precision
import Mathlib.Tactic
namespace IntMul.WideCarryProduct

private theorem lg_le_width (W : ℕ) (hW : 0< W) : lg W≤ W := by
  have hc : Nat.clog 2 W≤ W := Nat.clog_le_of_le_pow (Nat.le_of_lt W.lt_two_pow_self)
  exact max_le hc (by omega)

private theorem block_volume (B : ℕ) (x : List Bool) :
    DigitConvolution.blockCount B x*B≤ x.length+B := by
  have h := Nat.div_mul_le_self (x.length+B-1) B
  unfold DigitConvolution.blockCount
  omega

/-- The prepared physical carry/output product recovery stage has linear
actual transition cost at logarithmic block size and three-block precision. -/
private theorem linear_carry_product (pre x y z l : List Bool)
    (hW : 0< x.length+y.length)
    (hB : CarryStep.blockSize z=lg (x.length+y.length))
    (hN : val l+1=3*CarryStep.blockSize z)
    (hz : z.length≤ CarryStep.blockSize z)
    (hl : l.length≤ 3*CarryStep.blockSize z) :
    ∃ t : ℕ,
      t ≤ 909*(x.length+y.length)+21 ∧
      machine.step^[t] (initialFrame pre x y z l)=finalFrame pre x y z l ∧
      (machine.step^[t] (initialFrame pre x y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 1=
        machine.tapeOf ((bin (CarryStep.blockSize z*
          (DigitConvolution.blockCount (CarryStep.blockSize z) x+
            DigitConvolution.blockCount (CarryStep.blockSize z) y)) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 12=
        machine.tapeOf ((bin ((val l+1)) 0).map machine.bitSym) := by
  have hp := (CarryProduct.logarithmic_coefficient_precision (CarryStep.blockSize z) x y (by rw [hB])).1
  have hprec : CarryProduct.coefficientWidth (CarryStep.blockSize z) x y≤ val l+1 := by rw [hN];exact hp
  obtain ⟨t,ht,he,hh,hout,hcarry⟩ := wide_carry_product pre x y z l hprec
  have hBpos : 1≤ CarryStep.blockSize z := by simp [CarryStep.blockSize]
  have hBW : CarryStep.blockSize z≤ x.length+y.length := by rw [hB];exact lg_le_width _ hW
  have hx := block_volume (CarryStep.blockSize z) x
  have hy := block_volume (CarryStep.blockSize z) y
  have hm : (DigitConvolution.blockCount (CarryStep.blockSize z) x+
      DigitConvolution.blockCount (CarryStep.blockSize z) y)*CarryStep.blockSize z≤ 3*(x.length+y.length) := by
    rw [Nat.add_mul];omega
  have hper : 41*(val l+1)+21*CarryStep.blockSize z+21*z.length+4*l.length+126≤ 303*CarryStep.blockSize z := by
    rw [hN];omega
  refine ⟨t,le_trans ht ?_,he,hh,hout,hcarry⟩
  calc
    (DigitConvolution.blockCount (CarryStep.blockSize z) x+
      DigitConvolution.blockCount (CarryStep.blockSize z) y)*
      (41*(val l+1)+21*CarryStep.blockSize z+21*z.length+4*l.length+126)+21
      ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
          DigitConvolution.blockCount (CarryStep.blockSize z) y)*(303*CarryStep.blockSize z)+21 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hper) _
    _=303*((DigitConvolution.blockCount (CarryStep.blockSize z) x+
          DigitConvolution.blockCount (CarryStep.blockSize z) y)*CarryStep.blockSize z)+21 := by ring
    _≤ 303*(3*(x.length+y.length))+21 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hm) _
    _=909*(x.length+y.length)+21 := by ring
end IntMul.WideCarryProduct

open IntMul IntMul.WideCarryProduct

theorem solution (pre x y z l : List Bool)
    (hW : 0< x.length+y.length)
    (hB : CarryStep.blockSize z=lg (x.length+y.length))
    (hN : val l+1=3*CarryStep.blockSize z)
    (hz : z.length≤ CarryStep.blockSize z)
    (hl : l.length≤ 3*CarryStep.blockSize z) :
    ∃ t : ℕ,
      t ≤ 909*(x.length+y.length)+21 ∧
      machine.step^[t] (initialFrame pre x y z l)=finalFrame pre x y z l ∧
      (machine.step^[t] (initialFrame pre x y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 1=
        machine.tapeOf ((bin (CarryStep.blockSize z*
          (DigitConvolution.blockCount (CarryStep.blockSize z) x+
            DigitConvolution.blockCount (CarryStep.blockSize z) y)) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame pre x y z l)).cells 12=
        machine.tapeOf ((bin ((val l+1)) 0).map machine.bitSym) :=
  IntMul.WideCarryProduct.linear_carry_product pre x y z l hW hB hN hz hl

#print axioms solution

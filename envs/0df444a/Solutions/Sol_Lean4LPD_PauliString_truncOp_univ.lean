-- Prove2me | solution 1 for Lean4LPD.PauliString.truncOp_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:33:55.503997+00:00
-- url     : https://prove2.me/submissions/36d3f515-1766-403d-9a4b-05a7e6ca6118

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Theorems.Thm_Lean4LPD_PauliString_sum_norm_coeff_sq


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n ko kh : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (O : Matrix (Bits n) (Bits n) ℂ) : truncOp univ O = O := by
  have hsub : ∀ (A B : Matrix (Bits n) (Bits n) ℂ) (q : PauliIndex n),
      coeff (A - B) q = coeff A q - coeff B q := by
    intro A B q
    rw [coeff, coeff, coeff, Matrix.mul_sub, Matrix.trace_sub, mul_sub]
  have hcoeff : ∀ q : PauliIndex n, coeff (truncOp univ O - O) q = 0 := by
    intro q
    rw [hsub, coeff_truncOp, if_pos (Finset.mem_univ q), sub_self]
  have hnorm : pauliNormSq (truncOp univ O - O) = 0 := by
    rw [← sum_norm_coeff_sq]
    exact Finset.sum_eq_zero fun q _ => by rw [hcoeff q, norm_zero]; norm_num
  have hsum : ∑ a : Bits n, ∑ b : Bits n, ‖(truncOp univ O - O) a b‖ ^ 2 = 0 := by
    rw [pauliNormSq] at hnorm
    exact (mul_eq_zero.1 hnorm).resolve_left (by positivity)
  refine sub_eq_zero.1 (Matrix.ext fun a b => ?_)
  have ha := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => Finset.sum_nonneg fun b _ => by positivity)).1 hsum a (Finset.mem_univ a)
  have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).1 ha b
    (Finset.mem_univ b)
  exact norm_eq_zero.1 ((pow_eq_zero_iff (n := 2) (by norm_num)).1 hb)
end Lean4LPD.PauliString

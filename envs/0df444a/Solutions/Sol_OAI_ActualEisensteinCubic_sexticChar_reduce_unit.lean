-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sexticChar_reduce_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:00.450973+00:00
-- url     : https://prove2.me/submissions/72d1cbe6-477d-4f7d-9188-545036cbfa0a

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_reduce

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (u : (O ⧸ P)ˣ) :
    (Ideal.Quotient.mk P) (sexticChar P hgood (u : O ⧸ P)) =
      (u : O ⧸ P) ^ ((Nat.card (O ⧸ P) - 1) / 6) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let N := Fintype.card (O ⧸ P)
  let m := (N - 1) / 6
  have hthree : 3 ∣ N - 1 := by
    simpa only [N, Nat.card_eq_fintype_card] using card_sub_one_div_three P hgood
  have hodd : N % 2 = 1 := FiniteField.odd_card_of_char_ne_two hchar
  have hN : 1 < N := Fintype.one_lt_card
  have hsix : 6 ∣ N - 1 := by omega
  have hsize : N - 1 = 6 * m := by
    dsimp [m]
    exact (Nat.mul_div_cancel_left' hsix).symm
  have hthird : (N - 1) / 3 = 2 * m := by omega
  have hhalf : N / 2 = 3 * m := by omega
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hquad : ρ (quadraticCharO P (u : O ⧸ P)) =
      (u : O ⧸ P) ^ (N / 2) := by
    change (quadraticChar (O ⧸ P) (u : O ⧸ P) : O ⧸ P) = _
    exact quadraticChar_eq_pow_of_char_ne_two' hchar (u : O ⧸ P)
  have hcub : ρ (cubicChar P hgood (u : O ⧸ P)) =
      (u : O ⧸ P) ^ ((N - 1) / 3) := by
    simpa only [N, Nat.card_eq_fintype_card] using cubicChar_reduce P hgood (u : O ⧸ P)
  have hfermat : (u : O ⧸ P) ^ (N - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero u)
  change ρ ((cubicChar P hgood ^ 2 * quadraticCharO P) (u : O ⧸ P)) = _
  rw [MulChar.mul_apply, MulChar.pow_apply', map_mul, map_pow, hcub, hquad]
  rw [hthird, hhalf]
  simpa only [Nat.card_eq_fintype_card, N, m] using
    (show ((u : O ⧸ P) ^ (2 * m)) ^ 2 * (u : O ⧸ P) ^ (3 * m) =
      (u : O ⧸ P) ^ m by
      calc
        ((u : O ⧸ P) ^ (2 * m)) ^ 2 * (u : O ⧸ P) ^ (3 * m) =
            (u : O ⧸ P) ^ (7 * m) := by
              rw [← pow_mul, ← pow_add]
              congr 1
              omega
        _ = (u : O ⧸ P) ^ m * (u : O ⧸ P) ^ (N - 1) := by
          rw [hsize, ← pow_add]; congr 1; omega
        _ = (u : O ⧸ P) ^ m := by rw [hfermat, mul_one])
  all_goals norm_num
end OAI.ActualEisensteinCubic

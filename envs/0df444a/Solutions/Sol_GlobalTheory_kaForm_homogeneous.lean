-- Prove2me | solution 1 for GlobalTheory.kaForm_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:35.816986+00:00
-- url     : https://prove2.me/submissions/db65b6fc-c256-47b7-ac2b-8d72b433faac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_AlternatingSumChooseMulSubPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KaFormHomogeneous
import Theorems.Thm_GlobalTheory_tComb_rescale
import Theorems.Thm_GlobalTheory_tComb_mul_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
open Finset GlobalTheory.KeyKa
private theorem kaForm_monomial_eq_of_exponent_relations {G : Type} [CommGroup G] (X X' J u dl a : G) (N k : ℕ)
    (z1 z2 z3 α e1 e2 e3 : ℤ) (hu : z1 * N * e1 + z2 * N * e2 + z3 * e3 = 0)
    (hdl : 2 * N * e1 + 2 * N * e2 + 2 * e3 = 0) (ha : α * e1 + α * e2 + k = 0) :
    (X * (u ^ z1) ^ N * (dl ^ 2) ^ N * a ^ α) ^ e1 * (X' * (u ^ z2) ^ N * (dl ^ 2) ^ N * a ^ α) ^ e2 *
      (J * u ^ z3 * dl ^ 2) ^ e3 * a ^ k = X ^ e1 * X' ^ e2 * J ^ e3 := by
  have eU : u ^ (z1 * N * e1) * u ^ (z2 * N * e2) * u ^ (z3 * e3) = 1 := by
    rw [← zpow_add, ← zpow_add, hu, zpow_zero]
  have eD : dl ^ (2 * N * e1) * dl ^ (2 * N * e2) * dl ^ (2 * e3) = 1 := by
    rw [← zpow_add, ← zpow_add, hdl, zpow_zero]
  have eA : a ^ (α * e1) * a ^ (α * e2) * a ^ (k : ℤ) = 1 := by
    rw [← zpow_add, ← zpow_add, ha, zpow_zero]
  simp only [mul_zpow, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat]
  calc _ = X ^ e1 * X' ^ e2 * J ^ e3 * (u ^ (z1 * N * e1) * u ^ (z2 * N * e2) * u ^ (z3 * e3)) *
        (dl ^ (2 * N * e1) * dl ^ (2 * N * e2) * dl ^ (2 * e3)) *
        (a ^ (α * e1) * a ^ (α * e2) * a ^ (k : ℤ)) := by simp only [mul_comm, mul_assoc, mul_left_comm]
    _ = _ := by rw [eU, eD, eA, mul_one, mul_one, mul_one]
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open Finset GlobalTheory.KeyKa
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (g n l l' : ℕ) (t t' J u a dl : Rˣ) (lam lam' be be' : ℕ → Rˣ), g * n < l → l < l' → kaForm g n l l' (t * u ^ (-2 * (l : ℤ)) * dl ^ 2 * ∏ j ∈ Finset.range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) (t' * u ^ (-2 * (l' : ℤ)) * dl ^ 2 * ∏ j ∈ Finset.range (g + 1), be' j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) (fun j => lam j * be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ) * a ^ (8 * (l - j * n) ^ (4 * g + 2))) (fun j => lam' j * be' j ^ (-8 * ((l' - j * n) ^ (3 * g + 2) : ℕ) : ℤ) * a ^ (8 * (l' - j * n) ^ (4 * g + 2))) (J * u ^ (-((g * n : ℕ) : ℤ)) * dl ^ 2) * a ^ (8 * kaExp g n l l') = kaForm g n l l' t t' lam lam' J := by
  intro R _ g n l l' t t' J u a dl lam lam' be be' hl hl'
  have hd : ∀ j ∈ range (g + 1), (l - j * n) ∣ degProd g n l l' := fun j hj =>
    (dvd_mul_right _ _).trans (dvd_prod_of_mem (fun j => (l - j * n) * (l' - j * n)) hj)
  have hd' : ∀ j ∈ range (g + 1), (l' - j * n) ∣ degProd g n l l' := fun j hj =>
    (dvd_mul_left _ _).trans (dvd_prod_of_mem (fun j => (l - j * n) * (l' - j * n)) hj)
  unfold kaForm
  rw [tComb_rescale g n l _ _ a lam be hl hd, tComb_rescale g n l' _ _ a lam' be' (hl.trans hl') hd',
    tComb_mul_left, tComb_mul_left, tComb_mul_left, tComb_mul_left]
  refine kaForm_monomial_eq_of_exponent_relations _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
  all_goals
    try unfold kaExp
    push_cast [Nat.cast_sub hl'.le]
    ring
end GlobalTheory

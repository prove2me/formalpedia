-- Prove2me | solution 1 for GlobalTheory.tComb_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:58.39004+00:00
-- url     : https://prove2.me/submissions/ebc586de-9897-4576-a27c-d13254536b28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_AlternatingSumChooseMulSubPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KaFormHomogeneous
import Theorems.Thm_GlobalTheory_alternating_sum_choose_mul_sub_pow

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
private theorem kaForm_prod_zpow {G : Type} [CommGroup G] (a : G) (s : Finset ℕ) (f : ℕ → ℤ) :
    ∏ j ∈ s, a ^ f j = a ^ ∑ j ∈ s, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [prod_insert hj, sum_insert hj, ih, zpow_add]
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open Finset GlobalTheory.KeyKa
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] (g n l Pr : ℕ) (t a : Rˣ) (lam be : ℕ → Rˣ)
    (hl : g * n < l) (hd : ∀ j ∈ range (g + 1), (l - j * n) ∣ Pr) :
    tComb g n l Pr (t * ∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ)))
      (fun j => lam j * be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ) *
        a ^ (8 * (l - j * n) ^ (4 * g + 2)))
      = tComb g n l Pr t lam *
        a ^ (8 * ((Pr ^ (3 * g + 2) : ℕ) : ℤ) * ((g.factorial * n ^ g : ℕ) : ℤ)) := by
  unfold tComb
  rw [mul_pow]
  simp only [mul_zpow, prod_mul_distrib]
  have hB : (∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) ^ (4 * Pr ^ (3 * g + 2)) *
      ∏ j ∈ range (g + 1), (be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ)) ^
        ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) = 1 := by
    rw [← prod_pow, ← prod_mul_distrib]
    refine prod_eq_one fun j hj => ?_
    rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    convert zpow_zero (be j) using 2
    have key : Pr / (l - j * n) * (l - j * n) = Pr := Nat.div_mul_cancel (hd j hj)
    generalize Pr / (l - j * n) = q at key ⊢
    generalize l - j * n = d at key ⊢
    subst key
    push_cast
    ring
  have hA : ∏ j ∈ range (g + 1), (a ^ (8 * (l - j * n) ^ (4 * g + 2))) ^
        ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) =
      a ^ (8 * ((Pr ^ (3 * g + 2) : ℕ) : ℤ) * ((g.factorial * n ^ g : ℕ) : ℤ)) := by
    rw [prod_congr rfl fun j _ => by rw [← zpow_natCast, ← zpow_mul], kaForm_prod_zpow,
      ← alternating_sum_choose_mul_sub_pow g n l hl.le, mul_sum]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have key : Pr / (l - j * n) * (l - j * n) = Pr := Nat.div_mul_cancel (hd j hj)
    generalize Pr / (l - j * n) = q at key ⊢
    generalize l - j * n = d at key ⊢
    subst key
    push_cast
    ring
  calc _ = t ^ (4 * Pr ^ (3 * g + 2)) *
        (∏ j ∈ range (g + 1), lam j ^ ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ))) *
        ((∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) ^ (4 * Pr ^ (3 * g + 2)) *
          ∏ j ∈ range (g + 1), (be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ)) ^
            ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ))) *
        ∏ j ∈ range (g + 1), (a ^ (8 * (l - j * n) ^ (4 * g + 2))) ^
          ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) := by ac_rfl
    _ = _ := by rw [hB, hA, mul_one]
end GlobalTheory

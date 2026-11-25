-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassLaurentCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:27.204482+00:00
-- url     : https://prove2.me/submissions/554e2c08-d2f3-4138-898f-4d33cd4d233e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_one
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_two
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_add_three
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassLaurentCoeff_recursion
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassLaurentCoeff_two_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_one
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_two

set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair Nat
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (n : ℕ) (hn : n ≠ 0) :
    weierstrassLaurentCoeff L (2 * n) = weierstrassCoeff L.g₂ L.g₃ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih, hn with
    | 1, _, _ =>
      rw [weierstrassLaurentCoeff_two_mul one_ne_zero, weierstrassCoeff_one, Rat.smul_def,
        PeriodPair.g₂]
      push_cast
      ring
    | 2, _, _ =>
      rw [weierstrassLaurentCoeff_two_mul two_ne_zero, weierstrassCoeff_two, Rat.smul_def,
        PeriodPair.g₃]
      push_cast
      ring
    | n + 3, ih, _ =>
      have hrec := weierstrassLaurentCoeff_recursion (L := L) n
      have hsum : ∑ i : Fin (n + 1), weierstrassLaurentCoeff L (2 * ((i : ℕ) + 1)) *
          weierstrassLaurentCoeff L (2 * (n + 1 - i)) = ∑ i : Fin (n + 1),
            weierstrassCoeff L.g₂ L.g₃ ((i : ℕ) + 1) * weierstrassCoeff L.g₂ L.g₃ (n + 1 - i) :=
        Finset.sum_congr rfl fun i _ ↦ by
          have := i.isLt
          rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      rw [hsum] at hrec
      rw [weierstrassCoeff_add_three, Rat.smul_def, show 2 * (n + 3) = 2 * n + 6 by ring]
      have hK : ((2 * n + 6 : ℂ) * (2 * n + 5) - 12) ≠ 0 := by
        have : ((2 * n + 6 : ℂ) * (2 * n + 5) - 12) = 2 * (2 * n + 9) * (n + 1) := by ring
        rw [this]
        have : ((2 * (2 * n + 9) * (n + 1) : ℕ) : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.2 (by positivity)
        exact_mod_cast this
      apply mul_left_cancel₀ hK
      rw [hrec]
      have h1 : (2 * ((n : ℂ) + 3) + 3) ≠ 0 := by
        have : ((2 * (n + 3) + 3 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
        exact_mod_cast this
      have h2 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      push_cast
      field_simp
      ring
end GroundTheory.Global.Elliptic

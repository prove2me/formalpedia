-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassCoeff_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:27.161547+00:00
-- url     : https://prove2.me/submissions/cd0f7dd4-293b-49ac-8a25-920789f85216

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_one
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_two
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_add_three
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_zero
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_one
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_two

set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair Nat
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (t a b : R) (n : ℕ) :
    weierstrassCoeff (t ^ 4 * a) (t ^ 6 * b) n = t ^ (2 * n + 2) * weierstrassCoeff a b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | 2, _ => simp
    | n + 3, ih =>
      rw [weierstrassCoeff_add_three, weierstrassCoeff_add_three, mul_smul_comm, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi := i.isLt
      rw [ih _ (by omega), ih _ (by omega)]
      have : t ^ (2 * (n + 3) + 2) = t ^ (2 * ((i : ℕ) + 1) + 2) * t ^ (2 * (n + 1 - i) + 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [this]
      ring
end GroundTheory.Global.Elliptic

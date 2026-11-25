-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassCoeff_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:59:13.351154+00:00
-- url     : https://prove2.me/submissions/2b767fb3-5b0b-4616-b6e7-0a9d82fe3b9b

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
theorem _root_.solution (f : R →ₐ[ℚ] S) (a b : R) (n : ℕ) :
    f (weierstrassCoeff a b n) = weierstrassCoeff (f a) (f b) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp [map_smul]
    | 2, _ => simp [map_smul]
    | n + 3, ih =>
      rw [weierstrassCoeff_add_three, weierstrassCoeff_add_three, map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_mul, ih _ (by have := i.isLt; omega), ih _ (by omega)]
end GroundTheory.Global.Elliptic

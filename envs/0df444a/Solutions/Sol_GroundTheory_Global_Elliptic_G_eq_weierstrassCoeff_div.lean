-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.G_eq_weierstrassCoeff_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:40.371365+00:00
-- url     : https://prove2.me/submissions/b0bc14b6-7aa8-448b-9809-e9e439679c02

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_mul_G_eq_weierstrassCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair Nat
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) :
    L.G (2 * n + 2) = weierstrassCoeff L.g₂ L.g₃ n / (2 * n + 1) := by
  have h : (2 * (n : ℂ) + 1) ≠ 0 := by
    have : ((2 * n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    exact_mod_cast this
  rw [← mul_G_eq_weierstrassCoeff hn, mul_div_cancel_left₀ _ h]
end GroundTheory.Global.Elliptic

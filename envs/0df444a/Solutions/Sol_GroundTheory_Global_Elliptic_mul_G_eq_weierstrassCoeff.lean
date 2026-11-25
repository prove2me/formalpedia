-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.mul_G_eq_weierstrassCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:47:46.812638+00:00
-- url     : https://prove2.me/submissions/e9170588-9760-4830-a30b-a30fd4f6a4b1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassLaurentCoeff_two_mul
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassLaurentCoeff_eq

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
    (2 * n + 1) * L.G (2 * n + 2) = weierstrassCoeff L.g₂ L.g₃ n := by
  rw [← weierstrassLaurentCoeff_two_mul hn, weierstrassLaurentCoeff_eq n hn]
end GroundTheory.Global.Elliptic

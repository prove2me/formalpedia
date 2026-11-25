-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassLaurentCoeff_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:06.005404+00:00
-- url     : https://prove2.me/submissions/a2a93354-2fc1-4c73-b63f-e85425ad7b4e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein

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
    weierstrassLaurentCoeff L (2 * n) = (2 * n + 1) * L.G (2 * n + 2) := by
  rw [weierstrassLaurentCoeff, if_neg (by omega)]
  push_cast
  ring
end GroundTheory.Global.Elliptic

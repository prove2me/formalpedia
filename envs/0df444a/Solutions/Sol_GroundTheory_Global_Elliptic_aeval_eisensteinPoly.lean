-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.aeval_eisensteinPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:09:32.772419+00:00
-- url     : https://prove2.me/submissions/078ae7fa-8927-4865-89ef-b3dcb4006ace

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_map

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
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (x : Fin 2 → ℂ) (n : ℕ) :
    MvPolynomial.aeval x (eisensteinPoly n) =
      weierstrassCoeff (x 0) (x 1) n / (2 * n + 1) := by
  rw [eisensteinPoly, map_smul, weierstrassCoeff_map, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
    Rat.smul_def]
  push_cast
  ring
end GroundTheory.Global.Elliptic

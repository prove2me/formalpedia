-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.G_eq_aeval_eisensteinPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:54.983254+00:00
-- url     : https://prove2.me/submissions/c10f3148-ed15-4429-a854-dba963311642

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_aeval_eisensteinPoly
import Theorems.Thm_GroundTheory_Global_Elliptic_G_eq_weierstrassCoeff_div

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
    L.G (2 * n + 2) = MvPolynomial.aeval ![L.g₂, L.g₃] (eisensteinPoly n) := by
  rw [aeval_eisensteinPoly, G_eq_weierstrassCoeff_div hn]
  rfl
end GroundTheory.Global.Elliptic

-- Prove2me | solution 1 for GlobalTheory.SatakeFlip.invRevT_invRevT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:00.410075+00:00
-- url     : https://prove2.me/submissions/582ea5b4-76e2-4111-9ce9-75e275a0ae98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Matrix
open GlobalTheory GlobalTheory.SatakeFlip
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.SatakeFlip
theorem _root_.solution (g : GL (Fin n) R) : invRevT (invRevT g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invRevT_apply, ← map_inv, invRevT_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]
end GlobalTheory.SatakeFlip

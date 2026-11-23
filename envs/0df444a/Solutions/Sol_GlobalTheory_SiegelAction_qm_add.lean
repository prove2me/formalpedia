-- Prove2me | solution 1 for GlobalTheory.SiegelAction.qm_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:04.429857+00:00
-- url     : https://prove2.me/submissions/b5af668f-3195-48f0-b871-185d810ce31c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SiegelAction
theorem _root_.solution {α β : Type} (A B : Matrix α β ℚ) : qm (A + B) = qm A + qm B := by
  ext i j; simp [qm]
end GlobalTheory.SiegelAction

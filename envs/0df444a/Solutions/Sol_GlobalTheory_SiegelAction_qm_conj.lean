-- Prove2me | solution 1 for GlobalTheory.SiegelAction.qm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:14.63873+00:00
-- url     : https://prove2.me/submissions/9fb999f6-6ea8-4c62-8b9e-47d855e3c4c8

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
theorem _root_.solution {α β : Type} (A : Matrix α β ℚ) : (qm A).map conj = qm A := by
  ext i j; simp [qm]
end GlobalTheory.SiegelAction

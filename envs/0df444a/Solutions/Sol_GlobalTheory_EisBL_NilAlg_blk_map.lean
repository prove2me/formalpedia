-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.blk_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:44.068426+00:00
-- url     : https://prove2.me/submissions/cc24e9cc-dc4c-4311-bb74-acb12d2e3263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.EisBL.NilAlg
theorem _root_.solution (c : B →+* B) (X : Matrix n n B) : (blk X).map c = blk (X.map c) := by
  have e : ∀ M : Matrix n n B, M.map c = c.mapMatrix M := fun _ => rfl
  simp only [blk, fromBlocks_map, e, map_add, map_sub, map_neg, map_one]
end GlobalTheory.EisBL.NilAlg

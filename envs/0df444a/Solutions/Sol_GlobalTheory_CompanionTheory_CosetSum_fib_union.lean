-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CosetSum.fib_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:14.256817+00:00
-- url     : https://prove2.me/submissions/1fb0d07f-ce13-4ab5-a302-0cb1a1c34386

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetIntegralUnramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetSum
variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
namespace GlobalTheory.CompanionTheory.CosetSum
theorem _root_.solution (H : AddSubgroup G) : ⋃ c, fib H c = univ :=
  eq_univ_of_forall fun x => mem_iUnion.mpr ⟨(x : G ⧸ H), rfl⟩
end GlobalTheory.CompanionTheory.CosetSum

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CosetSum.fib_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:09.190095+00:00
-- url     : https://prove2.me/submissions/97f76dfa-2e2e-41aa-9158-a431e0bbcc85

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
theorem _root_.solution (H : AddSubgroup G) (g : G) :
    fib H (g : G ⧸ H) = {x | x - g ∈ H} := by
  ext x
  simp only [fib, mem_preimage, mem_singleton_iff]
  exact QuotientAddGroup.eq_iff_sub_mem
end GlobalTheory.CompanionTheory.CosetSum

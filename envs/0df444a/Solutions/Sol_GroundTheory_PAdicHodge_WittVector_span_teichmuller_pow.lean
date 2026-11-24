-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.span_teichmuller_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:20.634799+00:00
-- url     : https://prove2.me/submissions/75d25ecb-29df-4abc-8093-51f58b5322d6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
variable [CharP R p]
omit [CharP R p]
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (b : R) (N : ℕ) :
    Ideal.span {teichmuller p b} ^ N = Ideal.span {teichmuller p (b ^ N)} := by
  rw [Ideal.span_singleton_pow, map_pow]
end WittVector
end GroundTheory.PAdicHodge

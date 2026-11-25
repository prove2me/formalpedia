-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.mem_span_teichmuller_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:50:03.706491+00:00
-- url     : https://prove2.me/submissions/3f773f00-12e6-4165-b175-d1e5b722b3cc

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_mem_span_teichmuller_iff
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_span_teichmuller_pow

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
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (b : R) (N : ℕ) (y : WittVector p R) :
    y ∈ Ideal.span {teichmuller p b} ^ N ↔ ∀ n, b ^ (N * p ^ n) ∣ y.coeff n := by
  rw [WittVector.span_teichmuller_pow, WittVector.mem_span_teichmuller_iff]
  simp only [← pow_mul]
end WittVector
end GroundTheory.PAdicHodge

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.teich_sub_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:28:43.944553+00:00
-- url     : https://prove2.me/submissions/ea5d947b-ceed-4164-bc55-171c9751d82b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_quotEquiv_symm

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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution (a : L) (n : ℕ) (z : Γ)
    (hz : T.red z = (((frobeniusEquiv L p).symm : L →+* L))^[n] a) :
    T.teich a - z ^ p ^ n ∈ Ideal.span {T.π ^ (n + 1)} := by
  haveI := T.isAdicComplete
  have h : Ideal.Quotient.mk T.I z = Perfection.coeff (Γ ⧸ T.I) p n (T.toPerfection p a) := by
    rw [coeff_toPerfection]
    exact (T.quotEquiv_symm _ z hz).symm
  have := Perfection.teichmuller₀_sModEq (p := p) (I := T.I) h
  rw [SModEq.sub_mem, T.I_pow] at this
  exact this
end GroundTheory.PAdicHodge.TeichLift

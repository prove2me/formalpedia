-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ringEquiv_symm_pow_apply_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:12.61857+00:00
-- url     : https://prove2.me/submissions/c9a68944-7a1e-45bc-89bc-00f59e381582

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
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
omit [CharP R p] [PerfectRing R p]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {S : Type*} [Semiring S] (f : S ≃+* S) (n : ℕ)
    (y : S) : (f.symm ^ n) ((f ^ n) y) = y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ', RingAut.mul_apply, RingAut.mul_apply, RingEquiv.symm_apply_apply, ih]
end GroundTheory.PAdicHodge

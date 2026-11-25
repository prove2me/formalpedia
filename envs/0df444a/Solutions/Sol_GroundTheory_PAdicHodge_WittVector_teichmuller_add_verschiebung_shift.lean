-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.teichmuller_add_verschiebung_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:19.916486+00:00
-- url     : https://prove2.me/submissions/bc446e5e-0cb2-41a4-931f-248e9a81eec2

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
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (x : WittVector p R) :
    teichmuller p (x.coeff 0) + verschiebung (x.shift 1) = x := by
  ext n
  rw [coeff_add_of_disjoint n _ _ fun m => ?_]
  · rcases n with _ | n
    · rw [teichmuller_coeff_zero, verschiebung_coeff_zero, add_zero]
    · rw [teichmuller_coeff_pos p _ _ n.succ_pos, verschiebung_coeff_succ, shift_coeff, zero_add,
        add_comm]
  · rcases m with _ | m
    · exact Or.inr (verschiebung_coeff_zero _)
    · exact Or.inl (teichmuller_coeff_pos p _ _ m.succ_pos)
end WittVector
end GroundTheory.PAdicHodge

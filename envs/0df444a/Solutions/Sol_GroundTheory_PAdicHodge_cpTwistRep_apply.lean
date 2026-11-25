-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cpTwistRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:39:56.840296+00:00
-- url     : https://prove2.me/submissions/81f7f7a0-a5e7-4bf1-9b29-0dafe1527de8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open UniformSpace
variable {p : ℕ} [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace GroundTheory.PAdicHodge
theorem _root_.solution (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    cpTwistRep K j σ x = twistScalar K j σ * (σ • x) := rfl
end GroundTheory.PAdicHodge

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cycloChar_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:39:57.634157+00:00
-- url     : https://prove2.me/submissions/c83f35c9-b546-4cff-a852-1d28dac6bc75

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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ p ^ n = 1) :
    σ ζ = ζ ^ ((cycloChar K σ : ℤ_[p]).toZModPow n).val :=
  cyclotomicCharacter.spec p (MulSemiringAction.toRingAut Gal(PadicAlgCl p/K) (PadicAlgCl p) σ) ζ hζ
end GroundTheory.PAdicHodge

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.irreducible_wittToBDeRhamPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:16.33815+00:00
-- url     : https://prove2.me/submissions/b410b892-2675-44d1-a21f-1cf074584d91

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus

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
open Ideal WittVector IsLocalRing
variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
local notation "𝕎R♭" => WittVector p (PreTilt R p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt R p))
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) (hξ0 : ξ ∈ nonZeroDivisors 𝕎R♭)
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    Irreducible (wittToBDeRhamPlus R p ξ) := by
  have := isAdicComplete_bDeRhamPlus hξ
  have := hK.nontrivial
  exact (isDiscreteValuationRing_of_isAdicComplete
    (ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK)
    (pow_wittToBDeRhamPlus_ne_zero hξ hξ0)).2
end GroundTheory.PAdicHodge

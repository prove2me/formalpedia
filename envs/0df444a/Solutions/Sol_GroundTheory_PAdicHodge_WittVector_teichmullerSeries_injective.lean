-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.teichmullerSeries_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:46.364093+00:00
-- url     : https://prove2.me/submissions/ae342c82-bf6a-41a1-8606-6554ac28dd5a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmullerSeries_coeff
import Theorems.Thm_GroundTheory_PAdicHodge_frobeniusEquiv_pow_apply

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
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution :
    Function.Injective (WittVector.teichmullerSeries (p := p) (R := R)) := by
  intro a b h
  funext n
  have := congrArg (fun x => x.coeff n) h
  simp only [WittVector.teichmullerSeries_coeff, ← frobeniusEquiv_pow_apply] at this
  exact (_root_.frobeniusEquiv R p ^ n).injective this
end WittVector
end GroundTheory.PAdicHodge

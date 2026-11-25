-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.not_iso_mu_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:08:29.725609+00:00
-- url     : https://prove2.me/submissions/27d4ffad-9af9-448a-98cf-4438957ef381

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.PDivGroup.Test
open PDiv
variable {p : ℕ} {O : Type} [CommRing O]
namespace GlobalTheory.PDivGroup.Test
theorem _root_.solution [Fact p.Prime] (hp : ¬ IsUnit (p : O)) :
    IsEmpty (mu p O ≅ const p O) := ⟨fun e => dlogT_ne_zero p O hp <| by
  have h := LinearMap.congr_fun (omegaMap_comp e.hom e.inv) (dlogT p O)
  rw [e.hom_inv_id, omegaMap_id, LinearMap.id_apply, LinearMap.comp_apply,
    Subsingleton.elim (omegaMap (const p O) (mu p O) e.inv (dlogT p O)) 0, map_zero] at h
  exact h⟩
end GlobalTheory.PDivGroup.Test

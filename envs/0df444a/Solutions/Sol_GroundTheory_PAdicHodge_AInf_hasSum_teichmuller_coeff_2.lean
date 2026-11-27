-- Prove2me | solution 2 for GroundTheory.PAdicHodge.AInf.hasSum_teichmuller_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:51:14.202277+00:00
-- url     : https://prove2.me/submissions/87ef85cf-4fd2-4728-9484-d1b06498a04a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_hasSum_teichmullerSeries
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmullerSeries_coeff_eq


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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (x : AInf K p) :
    @HasSum (AInf K p) ℕ _ (pAdicTopology K p)
      (fun n => teichmuller p (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n)) *
        (p : AInf K p) ^ n) x (SummationFilter.unconditional ℕ) := by
  have := hasSum_teichmullerSeries (K := K)
    (fun n => ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n))
  rwa [WittVector.teichmullerSeries_coeff_eq] at this
end GroundTheory.PAdicHodge.AInf

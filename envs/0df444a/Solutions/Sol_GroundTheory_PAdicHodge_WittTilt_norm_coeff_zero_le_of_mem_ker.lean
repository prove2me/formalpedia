-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.norm_coeff_zero_le_of_mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:59:53.848055+00:00
-- url     : https://prove2.me/submissions/12a2b4f5-d520-49df-9462-c9d5a29d2136

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_teichmuller_add_mul_p


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
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable {ρ : ℝ}
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution {x : AInf K p} (hx : x ∈ RingHom.ker θ) :
    ‖x.coeff 0‖ ≤ ‖(p : K)‖ := by
  obtain ⟨v, hv⟩ := exists_eq_teichmuller_add_mul_p x
  have h := congrArg θ hv
  rw [RingHom.mem_ker.1 hx, map_add, map_mul, map_natCast, fontaineTheta_teichmuller] at h
  have h' : ((PreTilt.untilt (x.coeff 0) : 𝒪) : K) = -((θ v : 𝒪) : K) * p := by
    have := congrArg (fun y : 𝒪 => (y : K)) h
    push_cast at this
    linear_combination -this
  rw [preTilt_norm_def, h', norm_mul, norm_neg]
  exact mul_le_of_le_one_left (norm_nonneg _) (mem_normInteger.1 (θ v).2)
end GroundTheory.PAdicHodge.WittTilt

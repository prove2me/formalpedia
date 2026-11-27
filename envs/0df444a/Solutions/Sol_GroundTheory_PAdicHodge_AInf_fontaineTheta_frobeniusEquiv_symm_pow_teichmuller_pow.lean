-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.fontaineTheta_frobeniusEquiv_symm_pow_teichmuller_pow
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-27T02:59:58.512841+00:00
-- url     : https://prove2.me/submissions/137c319d-85fa-4115-a57d-49ec0996a3ba

import Mathlib
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
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
theorem solution (x : 𝒪♭) (n : ℕ) :
    θ (((φ).symm ^ n) (teichmuller p x)) ^ p ^ n = PreTilt.untilt x := by
  have key : ∀ m : ℕ, (((φ).symm ^ m) (teichmuller p x)) =
      teichmuller p ((_root_.frobeniusEquiv 𝒪♭ p).symm^[m] x) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ']
      change (φ).symm (((φ).symm ^ m) (teichmuller p x)) = _
      rw [ih, Function.iterate_succ_apply',
        WittVector.frobeniusEquiv_symm_apply, WittVector.map_teichmuller]
      rfl
  rw [key, fontaineTheta_teichmuller, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]

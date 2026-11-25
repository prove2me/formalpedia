-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.fontaineTheta_frobeniusEquiv_symm_pow_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:26.590802+00:00
-- url     : https://prove2.me/submissions/d054a779-3e82-428d-845a-f6ffeeb118f1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_symm_pow_teichmuller

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
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (x : 𝒪♭) (n : ℕ) :
    θ (((φ).symm ^ n) (teichmuller p x)) =
      PreTilt.untilt (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) x) := by
  rw [WittVector.frobeniusEquiv_symm_pow_teichmuller, fontaineTheta_teichmuller]
end GroundTheory.PAdicHodge.AInf

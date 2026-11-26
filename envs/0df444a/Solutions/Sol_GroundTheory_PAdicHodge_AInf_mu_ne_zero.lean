-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.mu_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T15:22:13.393308+00:00
-- url     : https://prove2.me/submissions/98539433-8afa-4659-a2de-dbfacf2e674e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

open GroundTheory.PAdicHodge.AInf in
theorem solution {ε : 𝒪♭}
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    mu ε ≠ 0 := by
  intro h0
  have hε : teichmuller p ε = 1 := sub_eq_zero.mp (by simpa [mu] using h0)
  have hcoeff : (ε : 𝒪♭) = 1 := by
    simpa [teichmuller_coeff_zero, one_coeff_zero] using
      congrArg (fun w : AInf K p => w.coeff 0) hε
  have : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) = 1 := by
    rw [hcoeff, map_one, map_one]
  exact hζ this

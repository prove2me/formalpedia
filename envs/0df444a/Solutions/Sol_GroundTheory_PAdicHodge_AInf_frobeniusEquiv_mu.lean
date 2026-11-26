-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.frobeniusEquiv_mu
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T15:24:18.306722+00:00
-- url     : https://prove2.me/submissions/b5065e87-16b0-4706-b630-af3f71b3de36

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
theorem solution (ε : 𝒪♭) :
    φ (mu ε) = mu ε * ∑ i ∈ Finset.range p, teichmuller p ε ^ i := by
  have hφ : φ (teichmuller p ε) = teichmuller p ε ^ p := by
    change WittVector.frobenius (teichmuller p ε) = teichmuller p ε ^ p
    rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def, map_pow]
  have hgeom :
      (∑ i ∈ Finset.range p, teichmuller p ε ^ i) * (teichmuller p ε - 1) =
        teichmuller p ε ^ p - 1 :=
    geom_sum_mul (teichmuller p ε) p
  simp [mu, map_sub, map_one, hφ, mul_comm, hgeom]

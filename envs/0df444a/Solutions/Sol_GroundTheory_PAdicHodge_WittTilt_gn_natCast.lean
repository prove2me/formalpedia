-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.gn_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:07.206316+00:00
-- url     : https://prove2.me/submissions/4588fff7-2349-4a64-8f0d-82563e87264e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_mul
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_pow
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_natCast_p
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_unit

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
theorem _root_.solution (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {m : ℕ} (hm : m ≠ 0) :
    gn K p ρ (m : 𝔸) = ρ ^ (m.factorization p) := by
  have e : (m : 𝔸) = (p : 𝔸) ^ (m.factorization p) * ((ordCompl[p] m : ℕ) : 𝔸) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  rw [e, gn_mul hρ0 hρ1, gn_pow hρ0 hρ1, gn_natCast_p hρ0,
    ← map_natCast (algebraMap (AInf K p) 𝔸) (ordCompl[p] m),
    gn_unit hρ0 hρ1 (WittVector.isUnit_natCast_of_coprime ((Nat.coprime_ordCompl hp.out hm).symm)),
    mul_one]
end GroundTheory.PAdicHodge.WittTilt

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.gn_dpow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:26:09.977863+00:00
-- url     : https://prove2.me/submissions/3b1da57e-e2c0-44af-a6c1-ac55ba685b1f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_mul
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_pow
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_natCast
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_ker_le

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
theorem _root_.solution (hp0 : ‖(p : K)‖ ≤ ρ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : AInf K p}
    (hx : x ∈ RingHom.ker θ) (n : ℕ) : gn K p ρ (ACris.dpow n x) ≤ 1 := by
  have h := congrArg (gn K p ρ) (ACris.factorial_mul_dpow n x)
  rw [gn_mul hρ0 hρ1, gn_pow hρ0 hρ1, gn_natCast hρ0 hρ1 (Nat.factorial_ne_zero n)] at h
  have hv := ACris.factorization_factorial_le (p := p) n
  have hxn : gn K p ρ (algebraMap (AInf K p) 𝔸 x) ^ n ≤ ρ ^ n :=
    pow_le_pow_left₀ (gn_nonneg hρ0 _) (gn_ker_le hp0 hρ0 hρ1 hx) n
  have h2 : ρ ^ n ≤ ρ ^ (n.factorial.factorization p) := pow_le_pow_of_le_one hρ0.le hρ1.le hv
  have hpos : 0 < ρ ^ (n.factorial.factorization p) := pow_pos hρ0 _
  by_contra hc
  push_neg at hc
  have := mul_lt_mul_of_pos_left hc hpos
  linarith
end GroundTheory.PAdicHodge.WittTilt

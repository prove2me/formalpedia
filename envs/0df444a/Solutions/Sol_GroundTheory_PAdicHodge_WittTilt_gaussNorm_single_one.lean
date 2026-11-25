-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.gaussNorm_single_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:49.199204+00:00
-- url     : https://prove2.me/submissions/06e90915-1928-4110-bcc9-b2cd6d27a94f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_le_gaussNorm
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_le
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem
attribute [local simp] P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
attribute [local simp] P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65



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
theorem _root_.solution (hρ0 : 0 < ρ) :
    gaussNorm (Pi.single (1 : ℤ) (1 : K♭)) ρ = ρ := by
  refine le_antisymm (gaussNorm_le fun n => ?_) ?_
  · by_cases hn : n = 1
    · subst hn; simp
    · rw [Pi.single_eq_of_ne hn, norm_zero, zero_mul]; exact hρ0.le
  · have := (TeichLift.convergesAt_pi_single (1 : ℤ) (1 : K♭) ρ).le_gaussNorm 1
    simpa using this
end GroundTheory.PAdicHodge.WittTilt

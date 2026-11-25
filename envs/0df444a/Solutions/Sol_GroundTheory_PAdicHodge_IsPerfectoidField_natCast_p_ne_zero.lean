-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.natCast_p_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:34.268152+00:00
-- url     : https://prove2.me/submissions/4e1bd705-cd51-43d6-a412-c32f8c0b8c46

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice

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
open Ideal WittVector IsLocalRing
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
omit [IsPerfectoidField K p]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution : (p : 𝒪) ≠ 0 := by
  intro h
  have h2 : ((p : 𝒪) : K) = 0 := by rw [h]; rfl
  rw [Subring.coe_natCast] at h2
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h2
end GroundTheory.PAdicHodge.IsPerfectoidField

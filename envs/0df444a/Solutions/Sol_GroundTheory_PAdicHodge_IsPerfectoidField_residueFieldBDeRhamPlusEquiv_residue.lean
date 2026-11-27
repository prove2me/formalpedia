-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.residueFieldBDeRhamPlusEquiv_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:31.754209+00:00
-- url     : https://prove2.me/submissions/eb363a3a-0dfb-4c4d-a7e6-ff7a0cb5422b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus

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
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p
variable {p}
variable [CharZero K]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (x : 𝔹) :
    residueFieldBDeRhamPlusEquiv (residue 𝔹 x) = thetaBDeRhamPlusField p x :=
  rfl
end GroundTheory.PAdicHodge.IsPerfectoidField

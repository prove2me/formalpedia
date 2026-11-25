-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.grEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:36.401091+00:00
-- url     : https://prove2.me/submissions/2dc32738-652b-4d53-9a56-9a33d999a3ca

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Ideal WittVector IsLocalRing
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "𝔹dR" => BDeRham (normInteger K) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger K) p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (x : fil K p i) :
    grEquiv hπ i (Submodule.Quotient.mk x) = grMap hπ i x := rfl
end GroundTheory.PAdicHodge.IsPerfectoidField

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.grMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:06:37.905806+00:00
-- url     : https://prove2.me/submissions/d65266fe-2117-4417-a263-05e2ce4a3ffd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRField
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_filEquiv_mk

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
theorem _root_.solution {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (b : 𝔹)
    (h : algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR b ∈ fil K p i) :
    grMap hπ i ⟨algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR b, h⟩ = thetaBDeRhamPlusField p b := by
  rw [grMap_apply, filEquiv_mk]
end GroundTheory.PAdicHodge.IsPerfectoidField

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.grMap_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:53.749403+00:00
-- url     : https://prove2.me/submissions/3fe27180-e11a-4722-a6d1-093f548a466f

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
theorem _root_.solution {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (c : 𝔹) (x : fil K p i) :
    grMap hπ i (c • x) = thetaBDeRhamPlusField p c * grMap hπ i x := by
  rw [grMap_apply, grMap_apply, map_smul, smul_eq_mul, map_mul]
end GroundTheory.PAdicHodge.IsPerfectoidField

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.map_mem_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:07:37.064184+00:00
-- url     : https://prove2.me/submissions/e94528e9-95b7-47b3-af76-6581a77c48f2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois

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
open Ideal WittVector IsLocalRing
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger K) p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {F : 𝔹 →+* 𝔹} (hF : ∀ x ∈ maximalIdeal 𝔹, F x ∈ maximalIdeal 𝔹)
    {x : 𝔹} {n : ℕ} (hx : x ∈ maximalIdeal 𝔹 ^ n) : F x ∈ maximalIdeal 𝔹 ^ n := by
  have h1 : (maximalIdeal 𝔹).map F ≤ maximalIdeal 𝔹 := Ideal.map_le_iff_le_comap.2 hF
  have h2 : (maximalIdeal 𝔹 ^ n).map F ≤ maximalIdeal 𝔹 ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h1 n
  exact h2 (Ideal.mem_map_of_mem F hx)
end GroundTheory.PAdicHodge.IsPerfectoidField

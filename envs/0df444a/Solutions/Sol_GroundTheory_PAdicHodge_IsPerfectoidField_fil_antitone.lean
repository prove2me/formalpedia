-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.fil_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:43.245216+00:00
-- url     : https://prove2.me/submissions/e44201b5-edf3-4390-bd3d-0733e6b10893

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
variable (K p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution : Antitone (fil K p) := by
  intro i j hij
  have hϖ := maximalIdeal_eq_span_varpi K p
  change Submodule.span 𝔹 {algebraMap 𝔹 𝔹dR (varpi K p) ^ j} ≤ fil K p i
  rw [Submodule.span_singleton_le_iff_mem, mem_fil_iff hϖ]
  refine ⟨varpi K p ^ (j - i).toNat, ?_⟩
  rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
    ← zpow_add₀ (algebraMap_ne_zero_of_maximalIdeal_eq_span hϖ), add_sub_cancel]
end GroundTheory.PAdicHodge.IsPerfectoidField

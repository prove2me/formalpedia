-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_toBDeRhamPlus_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:24.861203+00:00
-- url     : https://prove2.me/submissions/74b20432-e785-4505-9290-44ab6ea508cc

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_evalB_toBDeRhamPlus
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_ker_evalB

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
theorem _root_.solution (x : 𝔹) (n : ℕ) :
    ∃ a : 𝔸, x - toBDeRhamPlus 𝒪 p a ∈ maximalIdeal 𝔹 ^ n := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalB K p n x)
  refine ⟨a, ?_⟩
  rw [← ker_evalB, RingHom.mem_ker, map_sub, evalB_toBDeRhamPlus, ha, sub_self]
end GroundTheory.PAdicHodge.IsPerfectoidField

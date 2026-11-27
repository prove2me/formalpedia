-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.ringHom_ext_bDeRhamPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:33.799796+00:00
-- url     : https://prove2.me/submissions/582a2498-3968-4af5-a1da-6956dc148418

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_toBDeRhamPlus_sub_mem
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_map_mem_maximalIdeal_pow
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_eq_zero_of_forall_mem_maximalIdeal_pow

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
theorem _root_.solution {F G : 𝔹 →+* 𝔹}
    (h : ∀ w : 𝕎𝒪♭, F (wittToBDeRhamPlus 𝒪 p w) = G (wittToBDeRhamPlus 𝒪 p w))
    (hF : ∀ x ∈ maximalIdeal 𝔹, F x ∈ maximalIdeal 𝔹)
    (hG : ∀ x ∈ maximalIdeal 𝔹, G x ∈ maximalIdeal 𝔹) : F = G := by
  have hA : F.comp (toBDeRhamPlus 𝒪 p) = G.comp (toBDeRhamPlus 𝒪 p) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : 𝕎𝒪♭)) (RingHom.ext fun w => h w)
  ext x
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_maximalIdeal_pow fun n => ?_
  obtain ⟨a, ha⟩ := exists_toBDeRhamPlus_sub_mem x n
  have hFG : F (toBDeRhamPlus 𝒪 p a) = G (toBDeRhamPlus 𝒪 p a) := RingHom.congr_fun hA a
  have e : F x - G x = F (x - toBDeRhamPlus 𝒪 p a) - G (x - toBDeRhamPlus 𝒪 p a) := by
    rw [map_sub, map_sub, hFG]
    ring
  rw [e]
  exact Ideal.sub_mem _ (map_mem_maximalIdeal_pow hF ha) (map_mem_maximalIdeal_pow hG ha)
end GroundTheory.PAdicHodge.IsPerfectoidField

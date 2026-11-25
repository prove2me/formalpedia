-- Prove2me | solution 1 for GroundTheory.PAdicHodge.thetaBDeRhamPlus_eq_zero_of_evalB_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:29.574531+00:00
-- url     : https://prove2.me/submissions/78c00ea2-dece-4900-8125-2e8b97e9c6d4

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_ker_evalB
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Ideal WittVector IsLocalRing
open GroundTheory GroundTheory.PAdicHodge
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝒪" => normInteger ℂ_[p]
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger ℂ_[p]) p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger ℂ_[p]) p))
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger ℂ_[p]) p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {y : 𝔹}
    (hy : IsPerfectoidField.evalB ℂ_[p] p 1 y = 0) : thetaBDeRhamPlus 𝒪 p y = 0 := by
  have hmem : y ∈ maximalIdeal 𝔹 := by
    have h : y ∈ maximalIdeal 𝔹 ^ 1 := by
      rw [← IsPerfectoidField.ker_evalB (K := ℂ_[p]) (p := p) 1, RingHom.mem_ker]
      exact hy
    rwa [pow_one] at h
  rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker,
    IsPerfectoidField.thetaBDeRhamPlusField] at hmem
  simp only [RingHom.comp_apply] at hmem
  exact (map_eq_zero_iff _ (IsPerfectoidField.awayEquiv (K := ℂ_[p]) p).injective).1 hmem
end GroundTheory.PAdicHodge

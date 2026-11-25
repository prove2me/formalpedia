-- Prove2me | solution 1 for GroundTheory.LocalField.coprime_card_lowerRamificationGroup_zero_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:23:31.609276+00:00
-- url     : https://prove2.me/submissions/f91dc516-2441-4519-b5a3-a2293c14fef3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Theorems.Thm_GroundTheory_LocalField_card_lowerRamificationGroup_zero_quotient_dvd
import Theorems.Thm_GroundTheory_LocalField_coprime_card_residueField_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ
omit hϖ
variable (K L)
variable {K L}
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution :
    Nat.Coprime (Nat.card (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0))) (ringChar 𝓀[K]) := by
  rw [Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  exact Nat.Coprime.coprime_dvd_left (card_lowerRamificationGroup_zero_quotient_dvd K L)
    coprime_card_residueField_sub_one
end GroundTheory.LocalField

-- Prove2me | solution 1 for GroundTheory.LocalField.existsUnique_isUnramifiedSubextension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:18.649672+00:00
-- url     : https://prove2.me/submissions/74701f40-803a-4197-86dc-80557a7b6799

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Theorems.Thm_GroundTheory_LocalField_exists_isPrimitiveRoot_card_pow_sub_one
import Theorems.Thm_GroundTheory_LocalField_isUnramifiedSubextension_adjoin
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_eq_adjoin

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
open ValuativeRel IntermediateField
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]
namespace GroundTheory.LocalField
theorem _root_.solution [IsSepClosed Ksep] {n : ℕ} (hn : n ≠ 0) :
    ∃! E : IntermediateField K Ksep, IsUnramifiedSubextension E ∧ Module.finrank K E = n := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ksep) hn
  exact ⟨K⟮ζ⟯, isUnramifiedSubextension_adjoin hn hζ,
    fun E ⟨hE, hEn⟩ ↦ hE.eq_adjoin hEn hn hζ⟩
end GroundTheory.LocalField

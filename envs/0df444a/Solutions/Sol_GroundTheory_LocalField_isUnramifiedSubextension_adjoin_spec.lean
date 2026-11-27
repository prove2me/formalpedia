-- Prove2me | solution 1 for GroundTheory.LocalField.isUnramifiedSubextension_adjoin_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:59.930987+00:00
-- url     : https://prove2.me/submissions/8146cc0a-5e79-419b-ac52-c78113d3cbdf

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_isGalois
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_isCyclic
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_card_algEquiv
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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    IsUnramifiedSubextension K⟮ζ⟯ ∧ Module.finrank K K⟮ζ⟯ = n ∧ IsGalois K K⟮ζ⟯ ∧
      IsCyclic (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) ∧ Nat.card (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) = n ∧
      ∀ E : IntermediateField K Ksep, IsUnramifiedSubextension E → Module.finrank K E = n →
        E = K⟮ζ⟯ := by
  obtain ⟨hE, hEn⟩ := isUnramifiedSubextension_adjoin hn hζ
  exact ⟨hE, hEn, hE.isGalois, hE.isCyclic, hE.card_algEquiv.trans hEn,
    fun E hE' hE'n ↦ hE'.eq_adjoin hE'n hn hζ⟩
end GroundTheory.LocalField

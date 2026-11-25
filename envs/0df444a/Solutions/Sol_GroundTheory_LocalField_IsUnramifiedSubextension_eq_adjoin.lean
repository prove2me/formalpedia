-- Prove2me | solution 1 for GroundTheory.LocalField.IsUnramifiedSubextension.eq_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:11.839242+00:00
-- url     : https://prove2.me/submissions/061359ff-dcf4-48c5-95a6-aba33373b62f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Theorems.Thm_GroundTheory_LocalField_card_residueField_of_unramified
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_ramificationIndex_eq_one
import Theorems.Thm_GroundTheory_LocalField_isUnramifiedSubextension_adjoin
import Theorems.Thm_GroundTheory_LocalField_finiteExtensionStructure_isNonarchimedeanLocalField
import Theorems.Thm_GroundTheory_LocalField_finiteExtensionStructure_valuativeExtension


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
namespace IsUnramifiedSubextension
theorem _root_.solution {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) {n : ℕ} (hEn : Module.finrank K E = n) (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : E = K⟮ζ⟯ := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  have h := hE.ramificationIndex_eq_one
  obtain ⟨ξ, hξ, -⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K E h
  rw [card_residueField_of_unramified K E h, hEn] at hξ
  have hξ' : IsPrimitiveRoot (ξ : Ksep) (Nat.card 𝓀[K] ^ n - 1) :=
    hξ.map_of_injective (f := E.val) Subtype.val_injective
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) := ⟨by
    have := Nat.one_lt_pow hn (one_lt_card_residueField K)
    omega⟩
  obtain ⟨i, -, hi⟩ := hξ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hζE : ζ ∈ E := hi ▸ pow_mem ξ.2 i
  have hle : K⟮ζ⟯ ≤ E := adjoin_simple_le_iff.mpr hζE
  refine (eq_of_le_of_finrank_eq hle ?_).symm
  rw [(isUnramifiedSubextension_adjoin hn hζ).2, hEn]
end IsUnramifiedSubextension
end GroundTheory.LocalField

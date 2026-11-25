-- Prove2me | solution 1 for GroundTheory.LocalField.directed_isUnramifiedSubextension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:12.941422+00:00
-- url     : https://prove2.me/submissions/4fda71c4-cfb2-45ea-957a-4b9bb13fc846

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_le_adjoin
import Theorems.Thm_GroundTheory_LocalField_isUnramifiedSubextension_adjoin


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
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]
variable [HasUnramifiedRoots K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution :
    Directed (· ≤ ·) (fun E : {E : IntermediateField K Ω // IsUnramifiedSubextension E} ↦ E.1) := by
  rintro ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
  have := h₁.1
  have := h₂.1
  have hn : Module.finrank K E₁ * Module.finrank K E₂ ≠ 0 :=
    mul_ne_zero Module.finrank_pos.ne' Module.finrank_pos.ne'
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hn
  exact ⟨⟨K⟮ζ⟯, (isUnramifiedSubextension_adjoin hn hζ).1⟩,
    h₁.le_adjoin hn (dvd_mul_right _ _) hζ, h₂.le_adjoin hn (dvd_mul_left _ _) hζ⟩
end GroundTheory.LocalField

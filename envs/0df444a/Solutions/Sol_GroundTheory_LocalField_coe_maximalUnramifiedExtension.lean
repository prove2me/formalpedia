-- Prove2me | solution 1 for GroundTheory.LocalField.coe_maximalUnramifiedExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:39.91658+00:00
-- url     : https://prove2.me/submissions/0bf80bcb-0a0f-4cf1-a9c2-1c311d168766

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
import Theorems.Thm_GroundTheory_LocalField_directed_isUnramifiedSubextension
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
theorem _root_.solution : (maximalUnramifiedExtension K Ω : Set Ω) =
    ⋃ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, (E.1 : Set Ω) := by
  have : Nonempty {E : IntermediateField K Ω // IsUnramifiedSubextension E} := by
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) 1 one_ne_zero
    exact ⟨⟨K⟮ζ⟯, (isUnramifiedSubextension_adjoin one_ne_zero hζ).1⟩⟩
  exact coe_iSup_of_directed directed_isUnramifiedSubextension
end GroundTheory.LocalField

-- Prove2me | solution 1 for GroundTheory.LocalField.eq_maximalUnramifiedExtensionFrobenius_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:50.971801+00:00
-- url     : https://prove2.me/submissions/fa5eeaf2-f149-4a66-b0c1-0a91c05f951d

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
import Theorems.Thm_GroundTheory_LocalField_unramifiedDegree_eq_ofAdd_one_iff
import Theorems.Thm_GroundTheory_LocalField_unramifiedDegree_maximalUnramifiedExtensionFrobenius

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
variable [IsGalois K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution (ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) :
    ρ = maximalUnramifiedExtensionFrobenius K Ω ↔
      ∀ ξ ∈ unramifiedRoots K (maximalUnramifiedExtension K Ω), ρ ξ = ξ ^ Nat.card 𝓀[K] := by
  rw [← unramifiedDegree_eq_ofAdd_one_iff,
    ← unramifiedDegree_maximalUnramifiedExtensionFrobenius (K := K) (Ω := Ω)]
  exact unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm
end GroundTheory.LocalField

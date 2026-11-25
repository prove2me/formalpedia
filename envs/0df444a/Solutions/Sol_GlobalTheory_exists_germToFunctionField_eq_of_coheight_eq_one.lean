-- Prove2me | solution 1 for GlobalTheory.exists_germToFunctionField_eq_of_coheight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:54:24.956925+00:00
-- url     : https://prove2.me/submissions/95443b1a-50b5-4e1a-b99c-861771aed60b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_GlobalTheory_mem_range_algebraMap_iff_forall_height_eq_one
import Theorems.Thm_GlobalTheory_mem_range_algebraMap_iff_mem_primeLocalSubalgebra
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {X Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] (V : X.Opens) [Nonempty V] (t : X.functionField)
    (h : ∀ x ∈ V, Order.coheight x = 1 →
      t ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ s : Γ(X, V), X.germToFunctionField V s = t := by
  refine IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx ↦ ?_
  obtain ⟨_, ⟨(W : X.Opens), hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X W hW
  have := IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨s, hs⟩ : t ∈ (algebraMap Γ(X, W) X.functionField).range := by
    refine (mem_range_algebraMap_iff_forall_height_eq_one t).mpr fun p hp h1 ↦ ?_
    have hy : hW.fromSpec ⟨p, hp⟩ ∈ W := by
      rw [← SetLike.mem_coe, ← hW.range_fromSpec]
      exact ⟨_, rfl⟩
    let y : W := ⟨_, hy⟩
    let : Algebra Γ(X, W) (X.presheaf.stalk y.1) := X.presheaf.algebra_section_stalk y
    have : IsLocalization.AtPrime (X.presheaf.stalk y.1) p := hW.isLocalization_stalk' ⟨p, hp⟩ hy
    have := functionField_isScalarTower X W y
    refine (mem_range_algebraMap_iff_mem_primeLocalSubalgebra p (X.presheaf.stalk y.1) t).mp
      (h _ (hWV hy) ?_)
    have e := IsLocalization.AtPrime.ringKrullDim_eq_height p (X.presheaf.stalk y.1)
    rw [ringKrullDim_stalk_eq_coheight, h1] at e
    exact_mod_cast e
  exact ⟨W, inferInstance, s, hxW, hWV, hs⟩
end GlobalTheory

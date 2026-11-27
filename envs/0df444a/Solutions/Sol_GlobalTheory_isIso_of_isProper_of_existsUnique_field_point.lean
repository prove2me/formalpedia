-- Prove2me | solution 1 for GlobalTheory.isIso_of_isProper_of_existsUnique_field_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:11.527189+00:00
-- url     : https://prove2.me/submissions/0883ec0f-7a83-47ef-b027-9b4682e5c1bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
import Theorems.Thm_GlobalTheory_existsUnique_field_point_morphismRestrict
import Theorems.Thm_GlobalTheory_isIso_of_isProper_of_existsUnique_field_point_of_isIntegral
import Theorems.Thm_GlobalTheory_IsNormalScheme_iff_of_iSup_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (S T : Scheme.{0}) (f : S ⟶ T)
    (hf : IsProper f) (hS : IsReduced S) (hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T)
    (hN : IsLocallyNoetherian T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) : IsIso f := by
  have := GlobalTheory.IsNormalScheme.of_pred hT
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _)
    GlobalTheory.IsNormalScheme.component (GlobalTheory.IsNormalScheme.iSup_component T)).mpr fun Z ↦ ?_
  exact isIso_of_isProper_of_existsUnique_field_point_of_isIntegral
    (f ∣_ GlobalTheory.IsNormalScheme.component Z) (existsUnique_field_point_morphismRestrict f h _)
end GlobalTheory

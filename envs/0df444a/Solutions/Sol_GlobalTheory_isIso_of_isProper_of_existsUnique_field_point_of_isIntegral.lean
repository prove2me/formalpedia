-- Prove2me | solution 1 for GlobalTheory.isIso_of_isProper_of_existsUnique_field_point_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:02.672057+00:00
-- url     : https://prove2.me/submissions/7a5c8d65-c97a-4208-a06b-02c460898cb1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
import Theorems.Thm_GlobalTheory_bijective_of_existsUnique_field_point
import Theorems.Thm_GlobalTheory_isIso_stalkMap_genericPoint_of_lift
import Theorems.Thm_GlobalTheory_isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap


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
theorem _root_.solution {S T : Scheme.{0}} (f : S ⟶ T)
    [IsProper f] [IsReduced S] [IsIntegral T] [GlobalTheory.IsNormalScheme T]
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) : IsIso f := by
  have hb := bijective_of_existsUnique_field_point f h
  have hh : IsHomeomorph f :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨f.continuous, f.isClosedMap, hb⟩
  have : IrreducibleSpace S := hh.homeomorph.symm.irreducibleSpace_iff.mp inferInstance
  have : IsIntegral S := isIntegral_of_irreducibleSpace_of_isReduced S
  have : IsDominant f := ⟨hb.2.denseRange⟩
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    fun t ↦ (Set.finite_singleton t).preimage hb.1.injOn
  obtain ⟨z, hz, -⟩ := h T.functionField (T.fromSpecStalk (genericPoint T))
  have := isIso_stalkMap_genericPoint_of_lift f hb.1 z hz
  exact isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap f fun _ ↦ inferInstance
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.homPair_descends_to_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:39:25.403124+00:00
-- url     : https://prove2.me/submissions/9556e92d-e3c4-4fdc-9700-bb02c745e473

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomPairDescendsToFinite
import Theorems.Thm_GlobalTheory_HomPairDescent_isGrpPullback_bcMap
import Theorems.Thm_GlobalTheory_HomPairDescent_exists_descend
import Theorems.Thm_GlobalTheory_HomPairDescent_comp_eq_pow_of_epi
import Theorems.Thm_GlobalTheory_FieldBaseChange_epi_and_isMonHom_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory
open HomPairDescent Spread
namespace GlobalTheory
theorem _root_.solution : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (A B : Over (Sp K)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (i : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) (r : (Over.pullback (spMap (algebraMap K Ω))).obj B ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj A), IsMonHom i → IsMonHom r → ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (i' : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B) (r' : (Over.pullback (spMap (algebraMap K L))).obj B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A), IsMonHom i' ∧ IsMonHom r' ∧ ∀ m : ℕ, (i ≫ r = 𝟙 _ ^ m → i' ≫ r' = 𝟙 _ ^ m) ∧ (r ≫ i = 𝟙 _ ^ m → r' ≫ i' = 𝟙 _ ^ m) := by
  classical
  intro K Ω _ _ _ _ A B _ _ hA hB i r hi hr
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  obtain ⟨s, hs⟩ := exists_descend A B i
  obtain ⟨t, ht⟩ := exists_descend B A r
  let L : IntermediateField K Ω := IntermediateField.adjoin K ((s ∪ t : Finset Ω) : Set Ω)
  have hL : ((s ∪ t : Finset Ω) : Set Ω) ⊆ L := IntermediateField.subset_adjoin _ _
  obtain ⟨i', hi'⟩ := hs L ((Finset.coe_subset.2 Finset.subset_union_left).trans hL)
  obtain ⟨r', hr'⟩ := ht L ((Finset.coe_subset.2 Finset.subset_union_right).trans hL)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have gA := isGrpPullback_bcMap A L.val
  have gB := isGrpPullback_bcMap B L.val
  obtain ⟨hepi, hmon⟩ := FieldBaseChange.epi_and_isMonHom_iff L Ω L.val.toRingHom
  have eA := (hepi _ _ _ _ _ gA.1).1
  have eB := (hepi _ _ _ _ _ gB.1).1
  exact ⟨L, hfin, i', r', (hmon _ _ _ _ _ _ i' i gA gB hi').1 hi, (hmon _ _ _ _ _ _ r' r gB gA hr').1 hr,
    fun m => ⟨comp_eq_pow_of_epi gA hi' hr' m, comp_eq_pow_of_epi gB hr' hi' m⟩⟩
end GlobalTheory

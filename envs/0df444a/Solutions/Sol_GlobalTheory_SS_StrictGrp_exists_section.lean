-- Prove2me | solution 1 for GlobalTheory.SS.StrictGrp.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:13.236252+00:00
-- url     : https://prove2.me/submissions/bd654666-f0c9-4934-8f36-b47f2efa04f8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnionTranslatesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGrpObjOfStrictBirationalLaw
import Theorems.Thm_GlobalTheory_range_fst_residue
import Theorems.Thm_GlobalTheory_reducePoint_residue_surjective


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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictGrp
variable {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K] {A : Over (Sp K)}
namespace GlobalTheory.SS.StrictGrp
theorem _root_.solution (h : SH R K) (M : Model R A) {S : Set M.Y.left} (hS : IsLocallyClosed S)
    (hne : (S ∩ M.sp).Nonempty) : ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, s.left (IsLocalRing.closedPoint R) ∈ S := by
  obtain ⟨-, hH, hk, -⟩ := h
  have := M.smooth
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  obtain ⟨x, hxS, hx⟩ := hne
  obtain ⟨z, rfl⟩ := (range_fst_residue M.Y.hom).ge hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd M.Y.hom r)
  obtain ⟨c, hcS, hc⟩ := nonempty_inter_closedPoints (Z := pullback.fst M.Y.hom r ⁻¹' S) ⟨z, hxS⟩
    (hS.preimage (pullback.fst M.Y.hom r).continuous)
  obtain ⟨⟨s, hs⟩, e⟩ := reducePoint_residue_surjective M.Y.hom R (𝟙 _)
    ⟨pointOfClosedPoint (pullback.snd M.Y.hom r) c hc ≫ pullback.fst M.Y.hom r, by
      rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩
  refine ⟨Over.homMk s hs, ?_⟩
  have e₁ : r ≫ s = pointOfClosedPoint (pullback.snd M.Y.hom r) c hc ≫ pullback.fst M.Y.hom r := congrArg Subtype.val e
  have e₂ : s (r (IsLocalRing.closedPoint _)) = pullback.fst M.Y.hom r c := by
    rw [← Scheme.Hom.comp_apply, e₁, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  have e₃ : r (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint R := IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  rw [e₃] at e₂
  change s _ ∈ S
  rw [e₂]; exact hcS
end GlobalTheory.SS.StrictGrp

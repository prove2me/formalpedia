-- Prove2me | solution 1 for GlobalTheory.SS.LawDef.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:32.627181+00:00
-- url     : https://prove2.me/submissions/adc653bf-0247-4cdc-9f98-5485ff7386f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslate
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LawDef
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
variable [IsLocalRing R]
namespace GlobalTheory.SS.LawDef
theorem _root_.solution [IsDomain R] (hR : SH R K) (M : Model R A) {C : Set M.Y.left} (hC : IsLocallyClosed C)
    (hne : (C ∩ M.sp).Nonempty) : ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, sp0 s ∈ C := by
  obtain ⟨-, hH, hk, -⟩ := hR
  have := M.smooth
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let i := pullback.fst M.Y.hom r
  let q := pullback.snd M.Y.hom r
  have := LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨y, hy, hy'⟩ := hne
  obtain ⟨w, rfl⟩ : y ∈ Set.range i := by
    rw [range_fst_residue]; exact hy'
  obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := i ⁻¹' C) ⟨w, hy⟩ (hC.preimage i.continuous)
  obtain ⟨⟨x, hx⟩, hx'⟩ := reducePoint_residue_surjective M.Y.hom R (𝟙 _)
    ⟨pointOfClosedPoint q c hc' ≫ i, by
      rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩
  have e : r ≫ x = pointOfClosedPoint q c hc' ≫ i := congrArg Subtype.val hx'
  refine ⟨Over.homMk x hx, ?_⟩
  have e' := congrArg (fun m => m (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) e
  simp only [Scheme.Hom.comp_apply, pointOfClosedPoint_apply] at e'
  have e2 : r (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  rw [e2] at e'
  show x _ ∈ C
  exact e' ▸ hc
end GlobalTheory.SS.LawDef

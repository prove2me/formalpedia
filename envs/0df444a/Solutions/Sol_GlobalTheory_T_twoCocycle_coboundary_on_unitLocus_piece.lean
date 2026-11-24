-- Prove2me | solution 1 for GlobalTheory.T.twoCocycle_coboundary_on_unitLocus_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:49.415794+00:00
-- url     : https://prove2.me/submissions/0fdda3cb-fc99-432a-9cdf-301ec46bb155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoCocycleCoboundaryOnUnitLocusPiece
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovBy
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueCommaOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfUpwardFamilyStandardCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGluedSectionUpwardFamilyStandardCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleUpwardFamilyIsCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleInvertibleLocusIsCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsInvertibleLocusOfBasisFunctorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoCocycleCoboundaryOnUnitLocusPieceStatement
import Theorems.Thm_GlobalTheory_CatCoh_Desc_VandermondeTwoBasis_coboundary_on_piece


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (p : C') (v : T ⟶ G.obj p), (∀ (S : C) (u : T ⟶ S), IsUnit (mp F u e) → Nonempty (G.obj p ⟶ S)) → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece <;> assumption)
end _root_.GlobalTheory.T

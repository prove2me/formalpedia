-- Prove2me | solution 1 for GlobalTheory.TorusImage.exists_finset_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:27:31.983376+00:00
-- url     : https://prove2.me/submissions/d2716c2f-8a9d-47c8-9b5e-5f788314eda6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSumsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusImageFactorQuotientGoodOpen
import Theorems.Thm_GlobalTheory_TorusImage_ext_affineOpen

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
open GlobalTheory GlobalTheory.TorusImage
namespace GlobalTheory.TorusImage
theorem _root_.solution {S : Scheme.{0}} [IsAffine S] (G : Over S) [LocallyOfFiniteType G.hom] {U : G.left.Opens}
    (hU : IsAffineOpen U) : ∃ s : Finset Γ(G.left, U), ∀ (Z : Over S) (g g' : Z ⟶ G) (h : ⊤ ≤ g.left ⁻¹ᵁ U)
      (h' : ⊤ ≤ g'.left ⁻¹ᵁ U), (∀ f ∈ s, (g.left.appLE U ⊤ h).hom f = (g'.left.appLE U ⊤ h').hom f) → g = g' := by
  have hft : (G.hom.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType G.hom inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  let _ := (G.hom.appLE ⊤ U le_top).hom.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType Γ(S, ⊤) Γ(G.left, U) from hft).out
  refine ⟨s, fun Z g g' h h' e => Over.OverMorphism.ext (ext_affineOpen _ _ hU h h' ?_)⟩
  ext f
  have hf : f ∈ Algebra.adjoin Γ(S, ⊤) (s : Set Γ(G.left, U)) := hs ▸ trivial
  have key : ∀ (g : Z ⟶ G) (h : ⊤ ≤ g.left ⁻¹ᵁ U) (c : Γ(S, ⊤)),
      (g.left.appLE U ⊤ h).hom ((G.hom.appLE ⊤ U le_top).hom c) = (Z.hom.appLE ⊤ ⊤ le_top).hom c := by
    intro g h c
    have aux : ∀ q : Z.left ⟶ S, g.left ≫ G.hom = q → ∀ hq, (g.left.appLE U ⊤ h).hom
        ((G.hom.appLE ⊤ U le_top).hom c) = (q.appLE ⊤ ⊤ hq).hom c := by
      rintro _ rfl hq
      exact congrArg (fun q => q.hom c) (Scheme.Hom.appLE_comp_appLE g.left G.hom ⊤ U ⊤ le_top h)
    exact aux _ (Over.w g) _
  induction hf using Algebra.adjoin_induction with
  | mem x hx => exact e x hx
  | algebraMap c => exact (key g h c).trans (key g' h' c).symm
  | add x y _ _ a b => rw [map_add, map_add, a, b]
  | mul x y _ _ a b => rw [map_mul, map_mul, a, b]
end GlobalTheory.TorusImage

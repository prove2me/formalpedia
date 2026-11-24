-- Prove2me | solution 1 for GlobalTheory.SS.FinUnion.irr_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:53:39.809566+00:00
-- url     : https://prove2.me/submissions/d1ff26ea-a0d6-4647-99e0-76ee00220b35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnionTranslates

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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FinUnion
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.FinUnion
theorem _root_.solution {X I : Type} [TopologicalSpace X] (S : Set X) (U : I → Set X) (i₀ : I) (hU : ∀ i, IsOpen (U i))
    (hI : ∀ i, IsPreirreducible (S ∩ U i)) (hc : ∀ x ∈ S, ∃ i, x ∈ U i) (hm : ∀ i, (S ∩ U i ∩ U i₀).Nonempty) :
    IsIrreducible S := by
  refine ⟨(hm i₀).mono fun x hx => hx.1.1, ?_⟩
  have hs : S ⊆ closure (S ∩ U i₀) := fun x hx => by
    obtain ⟨i, hi⟩ := hc x hx
    exact closure_mono (show S ∩ U i ∩ U i₀ ⊆ S ∩ U i₀ from fun y hy => ⟨hy.1.1, hy.2⟩)
      (subset_closure_inter_of_isPreirreducible_of_isOpen (hI i) (hU i₀) (hm i) ⟨hx, hi⟩)
  have e : closure S = closure (S ∩ U i₀) :=
    subset_antisymm (closure_minimal hs isClosed_closure) (closure_mono Set.inter_subset_left)
  rw [← isPreirreducible_iff_closure, e]
  exact (hI i₀).closure
end GlobalTheory.SS.FinUnion

-- Prove2me | solution 1 for GlobalTheory.SpreadScheme.lfp_of_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:06:55.13783+00:00
-- url     : https://prove2.me/submissions/1967497a-46ab-4356-9878-09c5ba130c50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra

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
open GlobalTheory GlobalTheory.SpreadScheme
open GlobalTheory.Spread GlobalTheory.GlueModels
attribute [instance] PairModel.lfp PairModel.qs PairModel.qc PairModel.opn PairModel.qca
variable {S S₁ S₀ U T : Scheme.{0}} {f : S ⟶ S₀} {p : U ⟶ S} {a : T ⟶ U}
namespace GlobalTheory.SpreadScheme
theorem _root_.solution {X W : Scheme.{0}} {u : U ⟶ X} {v : W ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (q : X ⟶ S) (hu : LocallyOfFinitePresentation (u ≫ q)) (hv : LocallyOfFinitePresentation (v ≫ q)) :
    LocallyOfFinitePresentation q := by
  let Y : Bool → Scheme.{0} := fun i => Bool.rec U W i
  let t : ∀ i, Y i ⟶ X := fun i => Bool.rec (motive := fun i => Y i ⟶ X) u v i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool Y t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{0})
    (Q := @RingHom.FinitePresentation)
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation.{0}) 𝒰 ?_
  rintro (_ | _)
  · exact hu
  · exact hv
end GlobalTheory.SpreadScheme

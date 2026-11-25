-- Prove2me | solution 1 for GlobalTheory.SpreadScheme.exists_common_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:12:01.605585+00:00
-- url     : https://prove2.me/submissions/de1cc179-ec34-4450-b68f-8f397289d00e

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
variable {V : Type} [CommRing V]
namespace GlobalTheory.SpreadScheme
theorem _root_.solution {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (f₁ : R₁ →+* V) (f₂ : R₂ →+* V)
    (h₁ : Algebra.FiniteType ℤ R₁) (h₂ : Algebra.FiniteType ℤ R₂) :
    ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (g₁ : R₁ →+* R) (g₂ : R₂ →+* R), Algebra.FiniteType ℤ R ∧
      spMap f ≫ spMap g₁ = spMap f₁ ∧ spMap f ≫ spMap g₂ = spMap f₂ := by
  let R : Subalgebra ℤ V := f₁.toIntAlgHom.range ⊔ f₂.toIntAlgHom.range
  have hR : R.FG := by
    refine Subalgebra.FG.sup ?_ ?_ <;> rw [← Algebra.map_top]
    · exact h₁.out.map _
    · exact h₂.out.map _
  refine ⟨R, inferInstance, R.val.toRingHom,
    f₁.codRestrict R fun x => (le_sup_left : _ ≤ R) ⟨x, rfl⟩,
    f₂.codRestrict R fun x => (le_sup_right : _ ≤ R) ⟨x, rfl⟩, (Subalgebra.fg_iff_finiteType R).1 hR, ?_, ?_⟩ <;>
  · rw [← Spec.map_comp]
    rfl
end GlobalTheory.SpreadScheme

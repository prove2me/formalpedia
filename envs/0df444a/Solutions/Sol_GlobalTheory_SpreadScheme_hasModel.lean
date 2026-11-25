-- Prove2me | solution 1 for GlobalTheory.SpreadScheme.hasModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:07.649801+00:00
-- url     : https://prove2.me/submissions/bd520712-9c49-48a6-b8ec-df0d78d46745

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
import Theorems.Thm_GlobalTheory_SpreadScheme_hasModel_of_two
import Theorems.Thm_GlobalTheory_SpreadScheme_hasModel_of_isAffine

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
theorem _root_.solution {X : Scheme.{0}} (q : X ⟶ Sp V) [LocallyOfFinitePresentation q] [QuasiSeparated q]
    [QuasiCompact q] : HasModel q := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have key : HasModel ((⊤ : X.Opens).ι ≫ q) := by
    refine compact_open_induction_on (P := fun S => HasModel (S.ι ≫ q)) ⊤ isCompact_univ ?_ ?_
    · have : IsAffine (⊥ : X.Opens) := isAffineOpen_bot X
      exact hasModel_of_isAffine _
    · intro S hS W h
      have : CompactSpace S := isCompact_iff_compactSpace.1 hS
      have : IsAffine W.1 := W.2
      refine hasModel_of_two _ (X.homOfLE (le_sup_left : S ≤ S ⊔ W.1)) (X.homOfLE (le_sup_right : W.1 ≤ S ⊔ W.1))
        ?_ ?_ ?_
      · rintro ⟨x, hx | hx⟩
        · exact Or.inl ⟨⟨x, hx⟩, Subtype.ext (by simp)⟩
        · exact Or.inr ⟨⟨x, hx⟩, Subtype.ext (by simp)⟩
      · rwa [Scheme.homOfLE_ι_assoc]
      · exact hasModel_of_isAffine _
  obtain ⟨R, _, f, X₀, p₀, φ, h₁, h₂, h₃, h₄, hφ⟩ := key
  refine ⟨R, _, f, X₀, p₀, X.topIso.inv ≫ φ, h₁, h₂, h₃, h₄, ?_⟩
  exact hφ.of_iso X.topIso (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
end GlobalTheory.SpreadScheme

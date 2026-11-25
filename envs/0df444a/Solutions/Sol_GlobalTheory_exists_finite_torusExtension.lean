-- Prove2me | solution 1 for GlobalTheory.exists_finite_torusExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:49.351127+00:00
-- url     : https://prove2.me/submissions/5c971587-a386-431d-98b8-8e49e478231f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomDescendsToSubfieldContainingFinsetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFinsetModelOfIsAffineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescendsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescendsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Theorems.Thm_GlobalTheory_FieldModel_exists_finite_torusExtension_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (G : Over (Sp k)) [GrpObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → IsSeparated G.hom →
    Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap k K))).obj G)) →
    ∃ k' : IntermediateField k K, FiniteDimensional k k' ∧
      Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap k k'))).obj G)) := by
  intro k K _ _ _ _ G _ _ _ _ ⟨T⟩
  obtain ⟨s, hs, h⟩ := FieldModel.exists_finite_torusExtension_range (algebraMap k K) G T
  have := hs.to_subtype
  refine ⟨IntermediateField.adjoin k s, IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  exact h _ _ (algebraMap (IntermediateField.adjoin k s) K) rfl
    fun x hx => ⟨⟨x, IntermediateField.subset_adjoin k s hx⟩, rfl⟩
end GlobalTheory

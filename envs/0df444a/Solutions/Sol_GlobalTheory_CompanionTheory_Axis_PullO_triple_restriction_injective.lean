-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.PullO.triple_restriction_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:58:22.213799+00:00
-- url     : https://prove2.me/submissions/8083755f-1e12-4a69-b39f-6af8bb51ed91

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverComp
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_PullO_restrict_pull1_bijective_of_basis
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_PullO_triple_restriction_pair_restriction
import Theorems.Thm_GlobalTheory_CechDR_exists_triple_below_two
import Theorems.Thm_GlobalTheory_CechDR_triple_cover_affine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis GlobalTheory.CompanionTheory.Axis.PullO
variable {R'' : Type} [CommRing R''] {X X' X'' : Scheme.{0}}
variable (ψ : X'' ⟶ X') (φ : X' ⟶ X)
namespace GlobalTheory.CompanionTheory.Axis.PullO
theorem _root_.solution (s'' : X'' ⟶ Sp R'') : Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 x
  obtain ⟨y', rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 y
  rw [triple_restriction_pair_restriction, triple_restriction_pair_restriction] at hxy
  rw [(restrict_pull1_bijective_of_basis s'' (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))
    (triple_cover_affine ψ φ s'') (exists_triple_below_two ψ φ s'')).1 hxy]
end GlobalTheory.CompanionTheory.Axis.PullO

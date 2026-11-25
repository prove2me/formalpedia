-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.PullO.isPullO_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:17:45.975561+00:00
-- url     : https://prove2.me/submissions/94d3977d-7b2d-41b3-a547-550da967b2e5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverComp
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_PullO_triple_restriction_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_PullO_tri_pull_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_PullO_tri_res_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_PullO_tri_res_res
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


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
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}
namespace GlobalTheory.CompanionTheory.Axis.PullO
theorem _root_.solution (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) (b : HO1 s') (c : HO1 s'') :
    IsPullO h a b → IsPullO h' b c → IsPullO h'' a c := by
  intro hab hbc
  apply triple_restriction_injective ψ φ s''
  unfold IsPullO at hab hbc
  rw [tri_pull_pull h h' h'' a, hab, tri_res_pull h' b, hbc, tri_res_res (φ := φ) c]
end GlobalTheory.CompanionTheory.Axis.PullO

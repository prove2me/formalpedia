-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.PullO.tri_pull_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:05.289588+00:00
-- url     : https://prove2.me/submissions/3d410f88-7743-4a61-8a41-11a8653a2052

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverComp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_comp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_eq_of_natTrans
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
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) :
    (cechTripleRestrictComposite ψ φ s'').pull1 ((pairPull h'').pull1 a) =
      (cechTriplePullbackSecond h').pull1 ((pairPull h).pull1 a) := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp, ← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
    ((pairPull h).comp (cechTriplePullbackSecond h')) { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ a
  intro T b
  erw [GlobalTheory.CatCoh.mp_id]
  show (CommRingCat.Hom.hom (Scheme.Hom.appLE φ _ _ _ ≫ Scheme.Hom.appLE ψ _ _ _)) b =
    CommRingCat.Hom.hom (Scheme.Hom.appLE (ψ ≫ φ) _ _ _) b
  exact congrArg (fun k => CommRingCat.Hom.hom k b) (Scheme.Hom.appLE_comp_appLE ψ φ _ _ _ _ _)
end GlobalTheory.CompanionTheory.Axis.PullO

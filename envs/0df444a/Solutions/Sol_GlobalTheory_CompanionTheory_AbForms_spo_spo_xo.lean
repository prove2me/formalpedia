-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AbForms.spo_spo_xo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:26:08.179602+00:00
-- url     : https://prove2.me/submissions/8baaeaef-3529-42d8-8402-ae1864271553

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
variable {A : Over (Sp R)} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
variable {M : Type} [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
  (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M']
namespace GlobalTheory.CompanionTheory.AbForms
theorem _root_.solution (x' : Sp B' ⟶ A.left) (hx' : x' ≫ A.hom = spMap (algebraMap R B'))
    (α : B →+* B') (hxx : x' = spMap α ≫ x)
    {T T' : Type} [CommRing T] [CommRing T'] {f : R →+* T} {f' : R →+* T'} (ψ : T →+* T')
    (hψ : ψ.comp f = f') (τ : B →+* T) (hτ : τ.comp (algebraMap R B) = f)
    (τ' : B' →+* T') (hτ' : τ'.comp (algebraMap R B') = f') (e : ψ.comp τ = τ'.comp α) :
    spo ψ hψ ≫ spo τ hτ ≫ xo x hx = spo τ' hτ' ≫ xo x' hx' := by
  refine Over.OverMorphism.ext ?_
  change spMap ψ ≫ spMap τ ≫ x = spMap τ' ≫ x'
  rw [hxx, ← Category.assoc, ← spMap_comp, e, spMap_comp, Category.assoc]
end GlobalTheory.CompanionTheory.AbForms

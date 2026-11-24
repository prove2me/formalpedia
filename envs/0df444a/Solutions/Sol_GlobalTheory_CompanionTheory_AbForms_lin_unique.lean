-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AbForms.lin_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:23.281812+00:00
-- url     : https://prove2.me/submissions/6c5ff5d6-96ff-43ff-8785-5e08ee7bc7e9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_Zp_sg
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_spMap_inj
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_sg_snd

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
variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
  [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ A.left} (hy : IsCot A.hom η[A].left W y₀)
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M']
variable (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))
variable [IsOpenImmersion x]
namespace GlobalTheory.CompanionTheory.AbForms
theorem _root_.solution (f f' : Ω[B⁄R] →ₗ[B] M)
    (h : (f.restrictScalars R) ∘ₗ uOf hy x hx = (f'.restrictScalars R) ∘ₗ uOf hy x hx) : f = f' := by
  have h1 : Zp x hx (sg f) (sg_w f) = Zp x hx (sg f') (sg_w f') := by
    rw [Zp_sg hy, Zp_sg hy, h]
  have h2 : spo (sg f) (sg_w f) ≫ xo x hx = spo (sg f') (sg_w f') ≫ xo x hx := mul_right_cancel h1
  have h3 : spMap (sg f) ≫ x = spMap (sg f') ≫ x := congrArg (fun t ↦ t.left) h2
  have h4 : sg f = sg f' := spMap_inj ((cancel_mono x).1 h3)
  refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b ↦ ?_)
  have h5 := congrArg (fun t ↦ (t b).snd) h4
  exact (sg_snd f b).symm.trans (h5.trans (sg_snd f' b))
end GlobalTheory.CompanionTheory.AbForms

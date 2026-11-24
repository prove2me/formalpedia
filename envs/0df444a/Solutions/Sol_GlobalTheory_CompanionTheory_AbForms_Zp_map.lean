-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AbForms.Zp_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:38:08.508967+00:00
-- url     : https://prove2.me/submissions/4d323873-34f8-4b0b-87a3-b7d89e7a8550

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_spo_spo_xo
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



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
    (α : B →+* B') (hxx : x' = spMap α ≫ x) (hα : α.comp (algebraMap R B) = algebraMap R B')
    (f : M →+ M') (hf : ∀ b m, f (b • m) = α b • f m)
    (σ : B →+* TrivSqZeroExt B M) (hσ : σ.comp (algebraMap R B) = sz B M)
    (σ' : B' →+* TrivSqZeroExt B' M') (hσ' : σ'.comp (algebraMap R B') = sz B' M')
    (e : (tmap α f hf).comp σ = σ'.comp α) (h : (tmap α f hf).comp (sz (R := R) B M) = sz B' M') :
    spo (tmap α f hf) h ≫ Zp x hx σ hσ = Zp x' hx' σ' hσ' := by
  rw [Zp, MonObj.comp_mul, GrpObj.comp_inv, spo_spo_xo x hx x' hx' α hxx _ h σ hσ σ' hσ' e,
    spo_spo_xo x hx x' hx' α hxx _ h (TrivSqZeroExt.inlHom B M) rfl (TrivSqZeroExt.inlHom B' M') rfl
      (RingHom.ext fun b ↦ by ext <;> simp)]
  rfl
end GlobalTheory.CompanionTheory.AbForms

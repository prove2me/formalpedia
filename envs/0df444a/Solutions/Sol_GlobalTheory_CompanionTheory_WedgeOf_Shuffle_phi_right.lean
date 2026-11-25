-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.Shuffle.phi_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:40.168583+00:00
-- url     : https://prove2.me/submissions/f63189df-774f-4717-9537-be40a1f32f84

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishing
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf GlobalTheory.CompanionTheory.WedgeOf.Shuffle
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
namespace GlobalTheory.CompanionTheory.WedgeOf.Shuffle
theorem _root_.solution (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2)
    (Φ₁ : C1 F ⊗[R] C0 F ≃ₗ[R] ∀ x : Ar C × C, F.obj x.1.2.1 ⊗[R] F.obj x.2)
    (hΦ₁ : ∀ f g x, Φ₁ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g x.2) (u : C1 F ⊗[R] C0 F) (x y : Ar C) :
    Φ (TensorProduct.map LinearMap.id (d0 F) u) (x, y) =
      Φ₁ u (x, y.2.1) - TensorProduct.map LinearMap.id (mp F y.2.2).toLinearMap (Φ₁ u (x, y.1)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, hΦ, hΦ₁, amitsur_d0_apply, TensorProduct.tmul_sub]
    rfl
  | add u v hu hv =>
    simp only [map_add, Pi.add_apply, hu, hv]
    abel
end GlobalTheory.CompanionTheory.WedgeOf.Shuffle

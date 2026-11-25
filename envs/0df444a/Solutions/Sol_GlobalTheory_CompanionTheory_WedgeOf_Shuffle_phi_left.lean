-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.Shuffle.phi_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:38.674035+00:00
-- url     : https://prove2.me/submissions/12303b1f-e91d-4cea-8515-3cc88c9b9e6d

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
    (Φ₂ : C0 F ⊗[R] C1 F ≃ₗ[R] ∀ x : C × Ar C, F.obj x.1 ⊗[R] F.obj x.2.2.1)
    (hΦ₂ : ∀ f g x, Φ₂ (f ⊗ₜ g) x = f x.1 ⊗ₜ g _ _ x.2.2.2) (v : C0 F ⊗[R] C1 F) (x y : Ar C) :
    Φ (TensorProduct.map (d0 F) LinearMap.id v) (x, y) =
      Φ₂ v (x.2.1, y) - TensorProduct.map (mp F x.2.2).toLinearMap LinearMap.id (Φ₂ v (x.1, y)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, hΦ, hΦ₂, amitsur_d0_apply, TensorProduct.sub_tmul]
    rfl
  | add u v hu hv =>
    simp only [map_add, Pi.add_apply, hu, hv]
    abel
end GlobalTheory.CompanionTheory.WedgeOf.Shuffle

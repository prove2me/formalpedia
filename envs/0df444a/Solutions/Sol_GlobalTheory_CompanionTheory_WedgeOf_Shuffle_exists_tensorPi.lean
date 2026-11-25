-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.Shuffle.exists_tensorPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:00:08.391928+00:00
-- url     : https://prove2.me/submissions/b6f60fad-8136-414b-a7b9-719c19bf30f7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishing
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
namespace GlobalTheory.CompanionTheory.WedgeOf.Shuffle
theorem _root_.solution (R : Type) [CommRing R] (I J : Type) [Finite I] [Finite J] (A : I → Type) (B : J → Type)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)] :
    ∃ Φ : (∀ i, A i) ⊗[R] (∀ j, B j) ≃ₗ[R] ∀ x : I × J, A x.1 ⊗[R] B x.2,
      ∀ (f : ∀ i, A i) (g : ∀ j, B j) (x : I × J), Φ (f ⊗ₜ g) x = f x.1 ⊗ₜ g x.2 := by
  classical
  haveI := Fintype.ofFinite I
  haveI := Fintype.ofFinite J
  let e : (∀ j, ∀ i, A i ⊗[R] B j) ≃ₗ[R] ∀ x : I × J, A x.1 ⊗[R] B x.2 :=
    { toFun := fun g x ↦ g x.2 x.1
      invFun := fun h j i ↦ h (i, j)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine ⟨(TensorProduct.piRight R R (∀ i, A i) B) ≪≫ₗ
    (LinearEquiv.piCongrRight fun j ↦ (TensorProduct.comm R _ _) ≪≫ₗ (TensorProduct.piRight R R (B j) A) ≪≫ₗ
      (LinearEquiv.piCongrRight fun i ↦ TensorProduct.comm R _ _)) ≪≫ₗ e, fun f g x ↦ ?_⟩
  simp [e]
end GlobalTheory.CompanionTheory.WedgeOf.Shuffle

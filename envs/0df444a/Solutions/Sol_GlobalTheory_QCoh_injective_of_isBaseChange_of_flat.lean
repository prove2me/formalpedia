-- Prove2me | solution 1 for GlobalTheory.QCoh.injective_of_isBaseChange_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:01:57.513659+00:00
-- url     : https://prove2.me/submissions/bad194f6-eb40-4ffa-8e28-b2e66a5f5e2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
import Theorems.Thm_GlobalTheory_QCoh_homAppLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


attribute [local simp] GlobalTheory.QCoh.homAppLinear_apply

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X Y : Scheme.{u}} {F F' : X.Modules}
variable (f : X ⟶ Y)
namespace GlobalTheory.QCoh
theorem _root_.solution {A B M M' N N' : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] [AddCommGroup N']
    [Module A N'] [Module B N'] [IsScalarTower A B N'] {l : M →ₗ[A] N} {l' : M' →ₗ[A] N'}
    (hl : IsBaseChange B l) (hl' : IsBaseChange B l') (a : M →ₗ[A] M') (b : N →ₗ[B] N')
    (hab : ∀ m, b (l m) = l' (a m)) (ha : Function.Injective a) : Function.Injective b := by
  have : b ∘ₗ hl.equiv.toLinearMap = hl'.equiv.toLinearMap ∘ₗ a.baseChange B := by
    ext m
    simp [hab]
  have h : Function.Injective (b ∘ₗ hl.equiv.toLinearMap) := by
    rw [this]
    exact hl'.equiv.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap a ha)
  exact Function.Injective.of_comp_right h hl.equiv.surjective
end GlobalTheory.QCoh

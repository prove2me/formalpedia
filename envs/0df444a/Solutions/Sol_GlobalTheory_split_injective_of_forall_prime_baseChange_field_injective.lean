-- Prove2me | solution 1 for GlobalTheory.split_injective_of_forall_prime_baseChange_field_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:21.423135+00:00
-- url     : https://prove2.me/submissions/98a1a841-112f-46e8-b897-7b332bbb25e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitInjectiveOfForallPrimeBaseChangeFieldInject
import Theorems.Thm_GlobalTheory_split_injective_of_forall_lTensor_residueField_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Projective R M] (N : Type 1) [AddCommGroup N] [Module R N] [Module.Finite R N]
      [Module.Projective R N] (f : M →ₗ[R] N),
      (∀ P : PrimeSpectrum R, ∃ (k : Type) (_ : Field k) (_ : Algebra R k),
        RingHom.ker (algebraMap R k) = P.asIdeal ∧ Function.Injective (f.baseChange k)) →
      ∃ g : N →ₗ[R] M, g ∘ₗ f = LinearMap.id := by
  intro R _ M _ _ _ _ N _ _ _ _ f h
  refine split_injective_of_forall_lTensor_residueField_injective f fun m hm => ?_
  obtain ⟨k, _, _, hk, hinj⟩ := h ⟨m, hm.isPrime⟩
  simp only at hk
  let φ : m.ResidueField →ₐ[R] k := Ideal.ResidueField.liftₐ m (Algebra.ofId R k) hk.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hk ▸ h0))
  letI : Algebra m.ResidueField k := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R m.ResidueField k :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have e : (AlgebraTensorModule.cancelBaseChange R m.ResidueField m.ResidueField k N) ∘
        ((f.baseChange m.ResidueField).lTensor k) =
      (f.lTensor k) ∘ (AlgebraTensorModule.cancelBaseChange R
        m.ResidueField m.ResidueField k M) := by
    funext x
    exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
      m.ResidueField m.ResidueField (M := k) f) x).symm
  have h1 : Function.Injective ((f.baseChange m.ResidueField).lTensor k) :=
    Function.Injective.of_comp (e ▸ (hinj.comp (LinearEquiv.injective _)))
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective m.ResidueField k _).1 h1
end GlobalTheory

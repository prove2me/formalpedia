-- Prove2me | solution 1 for GlobalTheory.bijective_algHom_comp_of_etale_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:52.811718+00:00
-- url     : https://prove2.me/submissions/11421cb3-85e7-4e34-ab4a-cc5804b7c605

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_algHom_ext_of_sub_mem_jacobson
import Theorems.Thm_GlobalTheory_exists_algHom_lift_of_etale_of_henselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution (R : Type*) {k A B C : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing k] [CommRing A] [CommRing B] [CommRing C] [Algebra R B]
    [Module.Finite R B] [Algebra k A] [Algebra k B] [Algebra k C] [Algebra.Etale k A]
    (π : B →ₐ[k] C) (hπ : Function.Surjective π)
    (hker : RingHom.ker π ≤ (⊥ : Ideal B).jacobson) :
    Function.Bijective fun ψ : A →ₐ[k] B ↦ π.comp ψ := by
  refine ⟨fun f g h ↦ algHom_ext_of_sub_mem_jacobson fun a ↦ hker ?_, fun φ ↦ ?_⟩
  · rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact congr($h a)
  · let ε := Ideal.quotientKerAlgEquivOfSurjective hπ
    obtain ⟨ψ, hψ⟩ := exists_algHom_lift_of_etale_of_henselian R _ hker (ε.symm.toAlgHom.comp φ)
    refine ⟨ψ, AlgHom.ext fun a ↦ ?_⟩
    have := congr(ε $(hψ a))
    simpa [ε] using this
end GlobalTheory

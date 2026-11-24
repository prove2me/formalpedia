-- Prove2me | solution 1 for GlobalTheory.flat_comap_map_of_one_tmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:42.656718+00:00
-- url     : https://prove2.me/submissions/1a29fe45-3741-4ad6-9615-135046914efc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatComapMapOfOneTmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {B C R : Type} [CommRing B] [CommRing C] [CommRing R]
    [Algebra B C] [Algebra B R] [Module.Flat B R] (J : Ideal C) (r : R)
    (h : (1 : C) ⊗ₜ[B] r ∈ J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R)) :
    r ∈ (J.comap (algebraMap B C)).map (algebraMap B R) := by
  let f : B →ₗ[B] C ⧸ J := (Ideal.Quotient.mkₐ B J).toLinearMap ∘ₗ Algebra.linearMap B C
  have hex := Module.Flat.rTensor_exact R (LinearMap.exact_subtype_ker_map f)
  let φ : C ⊗[B] R →ₐ[B] (C ⧸ J) ⊗[B] R :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B J) (AlgHom.id B R)
  have hle : J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R) ≤
      RingHom.ker φ.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro j hj
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    show φ (j ⊗ₜ[B] (1 : R)) = 0
    simp [φ, Algebra.TensorProduct.map_tmul, (Ideal.Quotient.eq_zero_iff_mem).2 hj]
  have h0 : LinearMap.rTensor R f ((1 : B) ⊗ₜ[B] r) = 0 := by
    have := hle h
    rw [RingHom.mem_ker] at this
    simpa [f, φ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul] using this
  obtain ⟨x, hx⟩ := (hex ((1 : B) ⊗ₜ[B] r)).1 h0
  have key : ∀ y : (LinearMap.ker f) ⊗[B] R,
      TensorProduct.lid B R (LinearMap.rTensor R (LinearMap.ker f).subtype y) ∈
        (J.comap (algebraMap B C)).map (algebraMap B R) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul i s =>
      simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype, TensorProduct.lid_tmul]
      rw [Algebra.smul_def]
      apply Ideal.mul_mem_right
      apply Ideal.mem_map_of_mem
      have hi := i.2
      rw [LinearMap.mem_ker] at hi
      simp only [f, LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
        AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hi
      exact hi
    | add a b ha hb => simpa [map_add] using Ideal.add_mem _ ha hb
  have := key x
  rwa [hx, TensorProduct.lid_tmul, one_smul] at this
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.mem_map_ker_of_one_tmul_eq_zero_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:25.034316+00:00
-- url     : https://prove2.me/submissions/63db6a78-e7a1-4066-8dc0-85baa3eab557

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemMapKerOfOneTmulEqZeroOfFlat

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
theorem _root_.solution (B C k : Type) [CommRing B] [CommRing C]
    [Algebra B C] [Module.Flat B C] [Field k] [Algebra B k] (c : C)
    (h : (1 : k) ⊗ₜ[B] c = 0) :
    c ∈ (RingHom.ker (algebraMap B k)).map (algebraMap B C) := by
  classical
  set I : Ideal B := RingHom.ker (algebraMap B k) with hI
  let f : (B ⧸ I) →ₗ[B] k :=
    Submodule.liftQ I (Algebra.linearMap B k) (fun a ha => by simpa [hI] using ha)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun a ha => by simpa [hI] using ha)
  have hinj : Function.Injective (f.rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hx : (Ideal.Quotient.mk I 1) ⊗ₜ[B] c = 0 := by
    apply hinj
    have h1 : f (Ideal.Quotient.mk I 1) = 1 := by
      show Submodule.liftQ I (Algebra.linearMap B k) _ (Submodule.Quotient.mk 1) = 1
      rw [Submodule.liftQ_apply, Algebra.linearMap_apply, map_one]
    rw [LinearMap.rTensor_tmul, map_zero, h1]
    exact h
  have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul C I) hx
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, map_zero, one_smul,
    Submodule.Quotient.mk_eq_zero] at hq
  rw [Ideal.smul_top_eq_map] at hq
  exact hq
end GlobalTheory

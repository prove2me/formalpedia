-- Prove2me | solution 1 for GlobalTheory.EigenLine.finrank_ker_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:10.488277+00:00
-- url     : https://prove2.me/submissions/6bb7899a-c769-4d6f-b767-d92792d69c0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LineHyperplaneCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.EigenLine
variable {K : Type} [Field K] {O : Type} [CommRing O] {L : Type} [AddCommGroup L] [Module K L]
namespace GlobalTheory.EigenLine
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] K) (hf : f ≠ 0) :
    Module.finrank K (LinearMap.ker f) + 1 = Module.finrank K V := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext h)
  have htop : LinearMap.range f = ⊤ := by
    refine LinearMap.range_eq_top.2 fun k => ⟨(k / f y) • y, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [htop, finrank_top, Module.finrank_self] at h
  omega
end GlobalTheory.EigenLine

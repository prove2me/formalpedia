-- Prove2me | solution 1 for GlobalTheory.SpanQuotientTensor.span_mkQ_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:53:36.182639+00:00
-- url     : https://prove2.me/submissions/beba5cb5-beea-455f-a17f-75b224f3a9a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SpanMkQOneTmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanQuotientTensor
namespace GlobalTheory.SpanQuotientTensor
theorem _root_.solution {K D : Type} [Field K] [AddCommGroup D] [Module K D]
    (F : Type) [Field F] [Algebra K F] (N : Submodule F (TensorProduct K F D)) :
    Submodule.span F (Set.range (fun x : D => N.mkQ ((1 : F) ⊗ₜ[K] x))) = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  obtain ⟨y, rfl⟩ := N.mkQ_surjective q
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h : (a ⊗ₜ[K] x : TensorProduct K F D) = a • ((1 : F) ⊗ₜ[K] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add y z hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz
end GlobalTheory.SpanQuotientTensor

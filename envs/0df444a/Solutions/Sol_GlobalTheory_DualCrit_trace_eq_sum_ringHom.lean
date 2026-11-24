-- Prove2me | solution 1 for GlobalTheory.DualCrit.trace_eq_sum_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:24:51.344974+00:00
-- url     : https://prove2.me/submissions/9190e3da-54a1-4a84-b30d-1ee45e7cb797

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfTraceDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DualCrit
namespace GlobalTheory.DualCrit
theorem _root_.solution {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]
    [Fintype (E →+* K)] (hcard : Fintype.card (E →+* K) = Module.finrank ℚ E) (x : E) :
    algebraMap ℚ K (Algebra.trace ℚ E x) = ∑ σ : E →+* K, σ x := by
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  apply ι.injective
  rw [map_sum]
  have hq : ι.comp (algebraMap ℚ K) = algebraMap ℚ (AlgebraicClosure K) := RingHom.ext_rat _ _
  rw [← RingHom.comp_apply, hq, trace_eq_sum_embeddings (AlgebraicClosure K)]
  let f : (E →+* K) → (E →ₐ[ℚ] AlgebraicClosure K) := fun σ => (ι.comp σ).toRatAlgHom
  have hinj : Function.Injective f := by
    intro σ σ' h
    ext y
    apply ι.injective
    exact congrArg (fun g : E →ₐ[ℚ] AlgebraicClosure K => g y) h
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [hcard, AlgHom.card]
  exact (Fintype.sum_bijective f hbij (fun σ => ι (σ x)) (fun τ => τ x) (fun σ => rfl)).symm
end GlobalTheory.DualCrit

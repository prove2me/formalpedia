-- Prove2me | solution 1 for GlobalTheory.ColengthDifferent.sum_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:16:01.514669+00:00
-- url     : https://prove2.me/submissions/01b40657-b536-418e-adec-aa575f18f14b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.ColengthDifferent
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.ColengthDifferent
theorem _root_.solution {F : Type} [Field F] [CharZero F] {ι : Type} [Fintype ι]
    (σ : ι → (E →+* F)) (hσ : Function.Injective σ) (hc : Fintype.card ι = Module.finrank ℚ E) (x : E) :
    ∑ i, σ i x = algebraMap ℚ F (Algebra.trace ℚ E x) := by
  classical
  let K := AlgebraicClosure F
  let φ : ι → (E →ₐ[ℚ] K) := fun i => ((algebraMap F K).comp (σ i)).toRatAlgHom
  have hφ : Function.Injective φ := by
    intro i j h
    apply hσ
    ext y
    exact (algebraMap F K).injective (congrArg (fun f : E →ₐ[ℚ] K => f y) h)
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hφ, by rw [hc, AlgHom.card]⟩
  apply (algebraMap F K).injective
  rw [map_sum, ← IsScalarTower.algebraMap_apply ℚ F K, trace_eq_sum_embeddings K]
  exact hbij.sum_comp (fun f : E →ₐ[ℚ] K => f x)
end GlobalTheory.ColengthDifferent

-- Prove2me | solution 1 for GlobalTheory.LatExpSum.trace_eq_sum_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:37:29.538873+00:00
-- url     : https://prove2.me/submissions/8c1d0868-436e-401c-afcc-086dc67be7ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableExpNegTraceTotallyPositiveFractionalIdea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
noncomputable section
open GlobalTheory GlobalTheory.LatExpSum
namespace GlobalTheory.LatExpSum
theorem _root_.solution (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ τ : Emb F, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (E := ℂ) (x := x)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [eq_ratCast] at h
  have h2 : ∑ φ : F →+* ℂ, φ x = ∑ τ : Emb F, ((τ x : ℝ) : ℂ) := by
    refine (Fintype.sum_bijective (fun τ : Emb F => (ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩ _ _ (fun _ => rfl)).symm
    · intro τ τ' hτ
      ext y
      have := DFunLike.congr_fun hτ y
      simpa using this
    · intro φ
      have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
      exact ⟨hr.embedding, by ext y; simp⟩
  rw [h2, ← ofReal_sum] at h
  exact_mod_cast h
end GlobalTheory.LatExpSum

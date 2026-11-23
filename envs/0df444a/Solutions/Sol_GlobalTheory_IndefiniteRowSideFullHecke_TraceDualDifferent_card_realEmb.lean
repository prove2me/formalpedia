-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:52.210898+00:00
-- url     : https://prove2.me/submissions/1ffa0bb8-1ed4-4219-97f9-db513ea102eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
open NumberField nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
theorem _root_.solution [IsTotallyReal F] :
    Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
  classical
  rw [IsTotallyReal.finrank, ← InfinitePlace.card_real_embeddings]
  convert Fintype.card_congr
    { toFun := fun φ => ⟨Complex.ofRealHom.comp φ, ?_⟩
      invFun := fun φ => φ.2.embedding
      left_inv := ?_
      right_inv := ?_ : (F →+* ℝ) ≃ { φ : F →+* ℂ // ComplexEmbedding.IsReal φ } }
  · rw [ComplexEmbedding.isReal_iff]; ext x; simp [ComplexEmbedding.conjugate]
  · intro φ; ext x
    simpa using ComplexEmbedding.IsReal.coe_embedding_apply (φ := Complex.ofRealHom.comp φ) _ x
  · intro φ; ext x; simp [ComplexEmbedding.IsReal.coe_embedding_apply]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
end GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

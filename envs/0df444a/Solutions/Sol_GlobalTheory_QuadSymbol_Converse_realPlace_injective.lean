-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Converse.realPlace_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:48:21.773003+00:00
-- url     : https://prove2.me/submissions/de1da0d5-a2b7-475a-8610-a2efe4baa224

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEverywhereNormDivOfEtaProdEqOne
import Theorems.Thm_GlobalTheory_QuadSymbol_Converse_embedding_realPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex
noncomputable section
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.HilbertRecip
open GlobalTheory.QuadSymbol.Converse
variable {K : Type} [Field K]
namespace GlobalTheory.QuadSymbol.Converse
theorem _root_.solution : Function.Injective (realPlace (K := K)) := by
  intro σ τ h
  have H : ∀ (w w' : InfinitePlace K) (h : w.IsReal) (h' : w'.IsReal), w = w' →
      InfinitePlace.embedding_of_isReal h = InfinitePlace.embedding_of_isReal h' := by
    rintro w _ h h' rfl
    rfl
  rw [← embedding_realPlace σ, ← embedding_realPlace τ]
  exact H _ _ _ _ h
end GlobalTheory.QuadSymbol.Converse

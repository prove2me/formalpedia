-- Prove2me | solution 1 for GlobalTheory.CMType.sum_univ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:56.532513+00:00
-- url     : https://prove2.me/submissions/001b8351-1bbc-4465-8741-f78ea059f693

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.CMType
variable {E : Type*} [Field E] [NumberField E] (Φ : CMType E)
namespace GlobalTheory.CMType
theorem _root_.solution {M : Type*} [AddCommMonoid M] (g : (E →+* ℂ) → M) :
    ∑ τ, g τ = ∑ τ : Φ, (g τ + g (ComplexEmbedding.conjugate τ.1)) := by
  rw [← Φ.sumEquiv.sum_comp, Fintype.sum_sum_type, Finset.sum_add_distrib]
  rfl
end GlobalTheory.CMType

-- Prove2me | solution 1 for GlobalTheory.UnRep.NormOne.exists_nat_multiple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:56.374457+00:00
-- url     : https://prove2.me/submissions/ed6a32f9-1941-4090-8fa4-af2bc82e44d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.NormOne
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.UnRep.NormOne
theorem _root_.solution (α : 𝓞 E) (h : α ≠ 0) : ∃ n : ℕ, 0 < n ∧ ∃ γ : 𝓞 E, (n : 𝓞 E) = α * γ := by
  refine ⟨Ideal.absNorm (Ideal.span {α}), Nat.pos_of_ne_zero ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact h
  · exact Ideal.mem_span_singleton.mp (Ideal.absNorm_mem _)
end GlobalTheory.UnRep.NormOne

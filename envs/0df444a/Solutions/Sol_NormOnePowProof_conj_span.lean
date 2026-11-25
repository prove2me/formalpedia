-- Prove2me | solution 1 for NormOnePowProof.conj_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:56.420843+00:00
-- url     : https://prove2.me/submissions/88e9c5ac-725a-4e62-adab-00574af34da6

import Definitions.Def_Formalism_PeriodIntegrals_NormOnePow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOnePowerPrincipal_PowPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open NormOnePowProof
variable {E : Type} [Field E] [NumberField E]
namespace NormOnePowProof
theorem _root_.solution (c : E →+* E) (hc : ∀ x, c (c x) = x) {B : Submodule (𝓞 E) E} (a : E)
    (hB : ∀ x, x ∈ B ↔ c x ∈ Submodule.span (𝓞 E) {a}) :
    B = Submodule.span (𝓞 E) {c a} := by
  ext x
  rw [hB, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨σ c r, ?_⟩
    rw [Algebra.smul_def] at hr ⊢
    have := congrArg c hr
    rw [hc, map_mul] at this
    rw [← this]
    rfl
  · rintro ⟨r, rfl⟩
    refine ⟨σ c r, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
    rfl
end NormOnePowProof

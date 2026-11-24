-- Prove2me | solution 1 for GlobalTheory.LengthQuotientValuationDet.length_quotient_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:42:42.84768+00:00
-- url     : https://prove2.me/submissions/2b4bac52-00b4-4b0d-a339-20f672249550

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthQuotientSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthQuotientValuationDet
open Module IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace GlobalTheory.LengthQuotientValuationDet
theorem _root_.solution {x : R} (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({x} : Set R)) = addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq, length_quotient_pow_maximalIdeal, addVal_def' u hϖ]
end GlobalTheory.LengthQuotientValuationDet

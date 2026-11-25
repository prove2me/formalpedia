-- Prove2me | solution 1 for GlobalTheory.exists_monic_sq_eq_of_mul_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:35.591612+00:00
-- url     : https://prove2.me/submissions/c83871af-fe02-44d1-bca7-7b7385ed1b11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMulSqrtNegOddPolynomialIdentity
import Theorems.Thm_GlobalTheory_latticeIsogeny_latticePoint
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticeIsogeny_latticePoint
attribute [local simp] GlobalTheory.latticePointEquiv_mk



set_option autoImplicit false
open Polynomial PeriodPair
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {D G P : ℂ[X]} (hD : D.Monic) (hc : IsCoprime D G)
    (h : D * G = P ^ 2) : ∃ h : ℂ[X], h.Monic ∧ D = h ^ 2 := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hc h
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hD.ne_zero (by simpa using hd.symm)
  refine ⟨normalize d, monic_normalize hd0, ?_⟩
  refine eq_of_monic_of_associated hD ((monic_normalize hd0).pow 2) ?_
  exact hd.symm.trans ((associated_normalize d).pow_pow)
end GlobalTheory

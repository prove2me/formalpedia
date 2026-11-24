-- Prove2me | solution 1 for GlobalTheory.NormEq.mem_span_piO_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:22.109026+00:00
-- url     : https://prove2.me/submissions/371a79e7-4b80-48cf-b5bc-bb3b69e38163

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel
import Theorems.Thm_GlobalTheory_NormEq_mul_ofAdd_one_le_of_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (y : intL L)
    (hy : Valued.v (y : L) < 1) : y ∈ Ideal.span {piO h} := by
  have hϖ : ϖ ≠ 0 := by
    intro h0
    have := h.2.2.2.1
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hc : (y : L) / ϖ ∈ intL L := by
    change Valued.v ((y : L) / ϖ) ≤ 1
    rw [map_div₀, h.2.2.2.1, div_eq_mul_inv, ← WithZero.coe_inv, ← ofAdd_neg, neg_neg]
    exact mul_ofAdd_one_le_of_lt_one hy
  rw [Ideal.mem_span_singleton']
  exact ⟨⟨_, hc⟩, Subtype.ext (by simp [div_mul_cancel₀ _ hϖ])⟩
end GlobalTheory.NormEq

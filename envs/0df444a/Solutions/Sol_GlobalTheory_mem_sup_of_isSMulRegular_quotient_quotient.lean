-- Prove2me | solution 1 for GlobalTheory.mem_sup_of_isSMulRegular_quotient_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:22:37.952652+00:00
-- url     : https://prove2.me/submissions/491521fb-fe22-432f-9b0f-4200ed1dc175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfInjectiveModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegular
import Theorems.Thm_GlobalTheory_mkQ_mem_smul_top_iff_mem_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Type} [CommRing A] (I J : Ideal A) (r : A)
    (h : IsSMulRegular ((A ⧸ I) ⧸ (J • ⊤ : Submodule A (A ⧸ I))) r) (a : A)
    (ha : r * a ∈ J ⊔ I) : a ∈ J ⊔ I := by
  rw [sup_comm, ← mkQ_mem_smul_top_iff_mem_sup, ← Submodule.Quotient.mk_eq_zero] at ha ⊢
  apply h
  simp only [smul_zero]
  exact ha
end GlobalTheory

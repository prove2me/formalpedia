-- Prove2me | solution 1 for GlobalTheory.DerivAtOrigin.term_origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:11:06.945837+00:00
-- url     : https://prove2.me/submissions/736aca92-9d1d-42a7-8d98-f320b580a0e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivFormulaOfSeries
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DerivAtOrigin
namespace GlobalTheory.DerivAtOrigin
theorem _root_.solution {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (x : E) :
    term φ k κ 0 x = ∏ i, ((φ i x)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i x)) ^ κ i) := by
  unfold term
  refine Finset.prod_congr rfl fun i _ => ?_
  simp
end GlobalTheory.DerivAtOrigin

-- Prove2me | solution 1 for GlobalTheory.DeformedSum.dTerm_origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:09:24.446828+00:00
-- url     : https://prove2.me/submissions/c04b4c0f-0df6-49f5-a1e3-a15b32e61119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_DefiningCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
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
noncomputable section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates
open GlobalTheory GlobalTheory.DeformedSum
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.DeformedSum
theorem _root_.solution (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E) :
    dTerm φ k m 0 x = risingFactor k m * ∏ i, ((φ i x)⁻¹ ^ (k + m i) * (starRingEnd ℂ (φ i x)) ^ m i) := by
  unfold dTerm risingFactor
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [defCoord, Pi.zero_apply, zero_mul, add_zero]
  ring
end GlobalTheory.DeformedSum

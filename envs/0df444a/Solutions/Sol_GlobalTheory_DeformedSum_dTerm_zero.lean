-- Prove2me | solution 1 for GlobalTheory.DeformedSum.dTerm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:09:25.343369+00:00
-- url     : https://prove2.me/submissions/4eb87bae-f19e-4563-b5d1-c8676c00e0db

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
theorem _root_.solution (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (x : E) :
    dTerm φ k 0 z x = ∏ i, (defCoord φ z x i)⁻¹ ^ k := by
  simp [dTerm]
end GlobalTheory.DeformedSum

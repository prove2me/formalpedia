-- Prove2me | solution 1 for GlobalTheory.RootEx.FourierJacobiGroup.colE_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:58:49.127892+00:00
-- url     : https://prove2.me/submissions/8e05ebbb-0f3c-468f-829a-cd63ab875ec8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumn
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.FourierJacobiGroup
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.FourierJacobiGroup
theorem _root_.solution (q : ℕ) (β : n → k) (r s : n ⊕ Fin c) (h : lev q r ≠ lev q s) :
    (colE c q β).val r s = 0 := by
  rcases r with r | r <;> rcases s with s | s
  · simp [lev] at h
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at h
    simp [colE, upU, h.symm]
  · simp [colE, upU]
  · have : r ≠ s := by
      rintro rfl
      exact h rfl
    simp [colE, upU, this]
end GlobalTheory.RootEx.FourierJacobiGroup

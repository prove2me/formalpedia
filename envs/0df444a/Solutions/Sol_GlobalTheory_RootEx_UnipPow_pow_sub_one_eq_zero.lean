-- Prove2me | solution 1 for GlobalTheory.RootEx.UnipPow.pow_sub_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:23:18.907836+00:00
-- url     : https://prove2.me/submissions/943d7399-5fce-4f03-b870-29bfa1929f65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhds
import Theorems.Thm_GlobalTheory_RootEx_UnipPow_pow_sub_one_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnipPow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.UnipPow
theorem _root_.solution {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : InN p g) :
    ((g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) K) - 1) ^ (c + p + 1) = 0 := by
  have hb : ∀ t : n ⊕ Fin c, lev p t ≤ c + p := by
    rintro (t | t)
    · show p ≤ c + p
      omega
    · show t.val + 1 ≤ c + p
      have := t.isLt
      omega
  ext r s
  rw [Matrix.zero_apply]
  exact pow_sub_one_apply hg _ r s (by have := hb s; omega)
end GlobalTheory.RootEx.UnipPow

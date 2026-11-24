-- Prove2me | solution 1 for GlobalTheory.RootEx.ParabolicEntries.embX_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:01.816368+00:00
-- url     : https://prove2.me/submissions/c6ba79e0-afae-4b79-9a9f-f397ae3480a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntri
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ParabolicEntries
open GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.ParabolicEntries
theorem _root_.solution (L : ℕ) (b : Fin c → ℕ) (x : GL n k) : embX c x ∈ parGroup k n L b := by
  intro r s hor _
  rw [embX_val]
  rcases r with r | r <;> rcases s with s | s <;> simp_all [Matrix.one_apply]
end GlobalTheory.RootEx.ParabolicEntries

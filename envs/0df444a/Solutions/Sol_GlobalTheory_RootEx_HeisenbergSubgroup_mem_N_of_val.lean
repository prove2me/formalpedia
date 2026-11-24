-- Prove2me | solution 1 for GlobalTheory.RootEx.HeisenbergSubgroup.mem_N_of_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:58:53.851186+00:00
-- url     : https://prove2.me/submissions/88c57636-83de-4132-b912-12b2925466b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsHeisenbergSubgroupFourierJacobiCommutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.HeisenbergSubgroup
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.HeisenbergSubgroup
theorem _root_.solution {g : GL (n ⊕ Fin c) k} {β : n → k} {t : k} (hg : g.val = hM c p 0 β t) :
    g ∈ N k n c p := by
  show g ∈ Subgroup.closure {g | InN p g}
  refine Subgroup.subset_closure ?_
  intro r s hrs
  rw [hg, hM, row_zero]
  rcases r with a | l <;> rcases s with b | i
  · simp [Matrix.one_apply]
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₁₂, ExchangeSupport.colM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · simp
  · simp only [lev, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.add_apply, zM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp [Matrix.one_apply]
end GlobalTheory.RootEx.HeisenbergSubgroup

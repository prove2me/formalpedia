-- Prove2me | solution 1 for GlobalTheory.RootEx.FourierJacobiGroup.uni_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:58:50.507803+00:00
-- url     : https://prove2.me/submissions/5032a735-593e-439e-ac92-76273f7cbf18

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
namespace GlobalTheory.RootEx.FourierJacobiGroup
theorem _root_.solution {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {b : ι → ℕ}
    {A B M : Matrix ι ι k} (hA : ∀ r s, b r ≠ b s → A r s = 0) (hB : ∀ r s, b r ≠ b s → B r s = 0)
    (hAB : A * B = 1) (hM : Radical.Uni b M) : Radical.Uni b (A * M * B) := by
  intro r s hrs
  have : (A * M * B) r s = (A * (1 : Matrix ι ι k) * B) r s := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => ?_
    by_cases h1 : b r = b t
    · by_cases h2 : b u = b s
      · rw [hM t u (by omega)]
      · rw [hB u s h2, mul_zero, mul_zero]
    · simp only [hA r t h1, zero_mul]
  rw [this, Matrix.mul_one, hAB]
end GlobalTheory.RootEx.FourierJacobiGroup

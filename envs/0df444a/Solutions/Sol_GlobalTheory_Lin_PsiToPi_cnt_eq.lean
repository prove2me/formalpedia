-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.cnt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:55.39097+00:00
-- url     : https://prove2.me/submissions/ab890ee2-1a3a-43d0-b135-89ac128937e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
namespace GlobalTheory.Lin.PsiToPi
theorem _root_.solution (P : ℕ → Prop) (u : ℝ) :
    cnt P u = ∑ k ∈ Finset.Ioc 0 ⌊u⌋₊, 1 / Real.log k * wt P k := by
  unfold cnt
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold wt
  split_ifs with h
  · have : 0 < Real.log k := Real.log_pos (by exact_mod_cast h.1.one_lt)
    field_simp; simp
  · simp
end GlobalTheory.Lin.PsiToPi

-- Prove2me | solution 1 for GlobalTheory.SymLevelExists.superSum_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:14:44.461915+00:00
-- url     : https://prove2.me/submissions/17f045c3-300c-4803-94cd-f54a9bcde95e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul_apply_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.SymLevelExists
variable {F : Type} [Field F] {κ l : ℕ}
namespace GlobalTheory.SymLevelExists
theorem _root_.solution {a : Type} [Fintype a] [DecidableEq a] {pos : a → ℕ} {M M' : Matrix a a F}
    (h : IsUpperUnip pos M) (h' : IsUpperUnip pos M') :
    superSum pos (M * M') = superSum pos M + superSum pos M' := by
  simp only [superSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · exact Radical.Uni.mul_apply_succ (b := pos) h h' hij
  · simp
end GlobalTheory.SymLevelExists

-- Prove2me | solution 1 for GlobalTheory.SplitFlip.FourierDepth.pairCols_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:16.807383+00:00
-- url     : https://prove2.me/submissions/75967c8c-c09f-4f99-acf7-9ee23366c31e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.FourierDepth
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type*} [DecidableEq D]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D]
namespace GlobalTheory.SplitFlip.FourierDepth
theorem _root_.solution [Fintype A] (P : Finset D) (Y Z : Matrix A D k) (T : Matrix A P k) :
    pairCols P (Y + Z) T = pairCols P Y T + pairCols P Z T := by
  simp [pairCols, mul_add, Finset.sum_add_distrib]
end GlobalTheory.SplitFlip.FourierDepth

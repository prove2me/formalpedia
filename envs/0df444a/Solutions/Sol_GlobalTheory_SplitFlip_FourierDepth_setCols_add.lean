-- Prove2me | solution 1 for GlobalTheory.SplitFlip.FourierDepth.setCols_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:14.461601+00:00
-- url     : https://prove2.me/submissions/e08f5aad-9ef6-46a4-a328-875e5881159d

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
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip.FourierDepth
theorem _root_.solution (P : Finset D) (Y Z : Matrix A D k) (T : Matrix A P k) :
    setCols P (Y + Z) T = setCols P Y T + setCols P Z 0 := by
  ext i j
  by_cases h : j ∈ P <;> simp [setCols, h]
end GlobalTheory.SplitFlip.FourierDepth

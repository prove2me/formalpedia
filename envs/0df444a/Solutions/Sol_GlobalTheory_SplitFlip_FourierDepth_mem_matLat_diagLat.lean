-- Prove2me | solution 1 for GlobalTheory.SplitFlip.FourierDepth.mem_matLat_diagLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:07.240419+00:00
-- url     : https://prove2.me/submissions/a0caf926-f596-439a-84e4-5ad877715082

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
omit [DecidableEq D]
namespace GlobalTheory.SplitFlip.FourierDepth
theorem _root_.solution {c : D → kˣ} {X : Matrix A D k} :
    X ∈ matLat A (diagLat c) ↔ ∀ i j, valuation k (X i j) ≤ valuation k (c j : k) := Iff.rfl
end GlobalTheory.SplitFlip.FourierDepth

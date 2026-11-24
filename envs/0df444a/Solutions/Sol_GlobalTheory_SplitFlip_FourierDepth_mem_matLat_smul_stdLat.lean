-- Prove2me | solution 1 for GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:16.142801+00:00
-- url     : https://prove2.me/submissions/3646b101-685a-4f8f-85eb-ac07d0f3ef7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_diagLat
import Theorems.Thm_GlobalTheory_SplitFlip_smul_diagLat


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
theorem _root_.solution {c : kˣ} {X : Matrix A D k} :
    X ∈ matLat A (c • stdLat k D) ↔ ∀ i j, valuation k (X i j) ≤ valuation k (c : k) := by
  rw [stdLat, smul_diagLat, mem_matLat_diagLat]
  simp
end GlobalTheory.SplitFlip.FourierDepth

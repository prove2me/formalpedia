-- Prove2me | solution 1 for GlobalTheory.LatClass.zpow_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:14:11.833226+00:00
-- url     : https://prove2.me/submissions/e50dfb91-b072-446e-bf48-a5d6c8ec81d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_LatClass_val_pos
import Theorems.Thm_GlobalTheory_LatClass_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hϖ : valuation k (ϖ : k) = uniformizer k)
include hϖ
namespace GlobalTheory.LatClass
theorem _root_.solution {a b : ℤ} : (ϖ : k) ^ a ∈ powInt ϖ b ↔ b ≤ a := by
  rw [mem_pow, map_zpow₀, zpow_le_zpow_iff_right_of_lt_one₀ (val_pos ϖ) (hϖ ▸ uniformizer_lt_one)]
end GlobalTheory.LatClass

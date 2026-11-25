-- Prove2me | solution 1 for GlobalTheory.LatClass.pow_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:06:56.563688+00:00
-- url     : https://prove2.me/submissions/e5545c5b-2f1f-492e-8b4e-d2094e8a5a3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_LatClass_mem_pow
import Theorems.Thm_GlobalTheory_LatClass_zpow_mem_pow

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
theorem _root_.solution {a b : ℤ} (h : a ≤ b) {s : k} (hs : s ∈ powInt ϖ b) : s ∈ powInt ϖ a := by
  have := (zpow_mem_pow hϖ).2 h
  rw [mem_pow] at hs this ⊢
  rw [map_zpow₀] at this
  exact hs.trans this
end GlobalTheory.LatClass

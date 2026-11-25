-- Prove2me | solution 1 for GlobalTheory.LatClass.zpow_mul_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:19.019211+00:00
-- url     : https://prove2.me/submissions/9d82412f-25cc-4bb8-a49f-a52a60615913

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
namespace GlobalTheory.LatClass
theorem _root_.solution {a b : ℤ} {s : k} : (ϖ : k) ^ a * s ∈ powInt ϖ b ↔ s ∈ powInt ϖ (b - a) := by
  have h := val_pos ϖ
  rw [mem_pow, mem_pow, map_mul, map_zpow₀, zpow_sub₀ h.ne', le_div_iff₀ (zpow_pos h a), mul_comm]
end GlobalTheory.LatClass

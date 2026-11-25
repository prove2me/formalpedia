-- Prove2me | solution 1 for GlobalTheory.LatClass.pow_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:03:05.753218+00:00
-- url     : https://prove2.me/submissions/d92e9556-5549-4635-a08a-80c960e4f733

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
theorem _root_.solution {a b : ℤ} {t s : k} (ht : t ∈ powInt ϖ a) (hs : s ∈ powInt ϖ b) : t * s ∈ powInt ϖ (a + b) := by
  rw [mem_pow] at ht hs ⊢
  rw [map_mul, zpow_add₀ (val_pos ϖ).ne']
  exact mul_le_mul' ht hs
end GlobalTheory.LatClass

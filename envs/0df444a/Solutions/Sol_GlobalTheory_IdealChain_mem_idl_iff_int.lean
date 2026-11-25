-- Prove2me | solution 1 for GlobalTheory.IdealChain.mem_idl_iff_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:24.308464+00:00
-- url     : https://prove2.me/submissions/552f3eea-9ed0-41ef-82f0-971501a6cfde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Theorems.Thm_GlobalTheory_IdealChain_mem_idl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IdealChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IdealChain
theorem _root_.solution {b : kˣ} {x : k} : x ∈ idl b ↔ ((b⁻¹ : kˣ) : k) * x ∈ 𝒪[k] := by
  have hb : 0 < valuation k (b : k) := zero_lt_iff.2 (by simp)
  rw [mem_idl]
  change _ ↔ valuation k _ ≤ 1
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ hb, mul_one]
end GlobalTheory.IdealChain

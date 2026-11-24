-- Prove2me | solution 1 for GlobalTheory.HeisUnit.mul_mem_integer_iff_of_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:26:19.727481+00:00
-- url     : https://prove2.me/submissions/c443c046-ecc1-4d9b-8a4c-59f64e421ad4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCharacterUnitEqOneHeisenberg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.HeisUnit
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.HeisUnit
theorem _root_.solution {u : kˣ} (hu : valuation k (u : k) = 1) (y : k) :
    (u : k) * y ∈ 𝒪[k] ↔ y ∈ 𝒪[k] := by
  simp only [Valuation.mem_integer_iff, map_mul, hu, one_mul]
end GlobalTheory.HeisUnit

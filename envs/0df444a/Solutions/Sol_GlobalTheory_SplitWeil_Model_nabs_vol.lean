-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.nabs_vol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:56:00.500904+00:00
-- url     : https://prove2.me/submissions/bd7df891-b219-499d-9ed9-76d1a6ae8fbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil.Model
theorem _root_.solution (ν : Measure k) (h : IsUnitVol ν) (x : kˣ) :
    ν (x • (𝒪[k] : Set k)) = ENNReal.ofReal (nabs k x) := by
  have := h.1
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  rw [← distribHaarChar_mul ν x, h.2]; simp [nabs]
end GlobalTheory.SplitWeil.Model

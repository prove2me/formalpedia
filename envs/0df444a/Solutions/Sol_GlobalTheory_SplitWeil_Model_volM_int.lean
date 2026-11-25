-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.volM_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:14:57.487488+00:00
-- url     : https://prove2.me/submissions/b516815f-ff8b-4cb7-9983-2b4c8a562c6e

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
theorem _root_.solution (ν : Measure k) (h : IsUnitVol ν) (m n : Type*) [Fintype m] [Fintype n] :
    volM ν m n {x | ∀ i j, x i j ∈ (𝒪[k] : Set k)} = 1 := by
  have := h.1
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have : {x : Matrix m n k | ∀ i j, x i j ∈ (𝒪[k] : Set k)} =
      (Set.univ.pi fun _ : m => Set.univ.pi fun _ : n => (𝒪[k] : Set k) : Set (m → n → k)) :=
    Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
  rw [this]
  erw [Measure.pi_pi]
  simp [Measure.pi_pi, h.2]
end GlobalTheory.SplitWeil.Model

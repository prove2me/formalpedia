-- Prove2me | solution 1 for GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:23:09.983895+00:00
-- url     : https://prove2.me/submissions/ce69918a-13a6-4263-a369-df165ffe60e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralBlockIndicator
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralBlockIndicatorStatement
import Theorems.Thm_GlobalTheory_BlockFubini_integral_block_indicator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [MeasurableSpace k] [Zero k] (ν : Measure k) [SigmaFinite ν] (I : Type) [Fintype I] (P Q R : I → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R], (∀ i, R i ↔ P i ∧ ¬ Q i) → (∀ i, Q i → P i) → ∀ (s : Set k), MeasurableSet s → ν s ≠ ⊤ → ∀ (G : (I → k) → ℂ), (∀ m : I → k, G m = (if ∀ i, Q i → m i ∈ s then (1 : ℂ) else 0) * G (fun i => if Q i then 0 else m i)) → ∫ e : {i // P i} → k, G (fun i => if h : P i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) = (((ν s).toReal ^ Fintype.card {i // Q i} : ℝ) : ℂ) * ∫ e : {i // R i} → k, G (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) := by
  first | exact @GlobalTheory.BlockFubini.integral_block_indicator | exact GlobalTheory.BlockFubini.integral_block_indicator | (intros; apply GlobalTheory.BlockFubini.integral_block_indicator <;> assumption)
end _root_.GlobalTheory.T

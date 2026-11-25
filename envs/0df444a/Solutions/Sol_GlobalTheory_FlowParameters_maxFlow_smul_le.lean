-- Prove2me | solution 1 for GlobalTheory.FlowParameters.maxFlow_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:49:09.328813+00:00
-- url     : https://prove2.me/submissions/d837dc38-8963-4cdf-8eb7-51942b449f9b

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ParametersSmallBound
import Theorems.Thm_GlobalTheory_FlowParameters_flowVal_le_sum
import Theorems.Thm_GlobalTheory_FlowParameters_flowVal_le_maxFlow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.FlowParameters
namespace GlobalTheory.FlowParameters
theorem _root_.solution (l d : ℕ) [NeZero d] (c : ℝ) (hc : 0 ≤ c) (D : ZMod d → ℝ) (hD : 0 ≤ D) :
    maxFlow l d (fun a => c * D a) ≤ c * maxFlow l d D := by
  refine csSup_le ⟨_, fun _ _ => 0, ⟨fun _ _ => le_rfl, fun s => ?_⟩, rfl⟩ ?_
  · simpa using mul_nonneg hc (hD s)
  rintro t ⟨x, hx, rfl⟩
  rcases hc.eq_or_lt with rfl | hc'
  · simpa using flowVal_le_sum l d _ x hx
  · have hz : IsFlow l d D (fun a i => c⁻¹ * x a i) := by
      refine ⟨fun s i => mul_nonneg (by positivity) (hx.1 s i), fun s => ?_⟩
      have h := hx.2 s
      have e : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * (c⁻¹ * x s i)) +
          (∑ i ∈ oddLevels d, c⁻¹ * x (s - (i : ZMod d)) i) =
          c⁻¹ * ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
            (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i)) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, inv_mul_le_iff₀ hc']
      exact h
    have h := flowVal_le_maxFlow l d D _ hz
    have e : flowVal d (fun a i => c⁻¹ * x a i) = c⁻¹ * flowVal d x := by
      simp only [flowVal, Finset.mul_sum]
    rw [e, inv_mul_le_iff₀ hc'] at h
    exact h
end GlobalTheory.FlowParameters

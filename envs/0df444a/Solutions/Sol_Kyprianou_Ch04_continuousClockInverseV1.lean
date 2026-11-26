-- Prove2me | solution 1 for Kyprianou.Ch04.continuousClockInverseV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:37:14.385112+00:00
-- url     : https://prove2.me/submissions/6166cc51-2344-4ac1-9a8e-ce7b0348c216

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A continuous increasing clock dominating time has an attained finite inverse. -/
theorem solution (A : NNReal → ℝ) (hA : Continuous A)
    (hMono : Monotone A) (hLower : ∀ t : NNReal, (t : ℝ) ≤ A t)
    (m t : NNReal) :
    sInf {u : NNReal | (m : ℝ) ≤ A u} ≤ t ↔ (m : ℝ) ≤ A t := by
  let S : Set NNReal := {u | (m : ℝ) ≤ A u}
  have hS : S.Nonempty := ⟨m, hLower m⟩
  have hb : BddBelow S := ⟨0, fun _ _ => zero_le⟩
  have hc : IsClosed S := isClosed_Ici.preimage hA
  have hmem : sInf S ∈ S := hc.csInf_mem hS hb
  change sInf S ≤ t ↔ t ∈ S
  exact ⟨fun h => (show (m : ℝ) ≤ A (sInf S) from hmem).trans (hMono h),
    fun h => csInf_le hb h⟩

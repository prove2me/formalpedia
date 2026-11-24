-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:22:56.500533+00:00
-- url     : https://prove2.me/submissions/7c917c2a-203e-46b0-9599-6775a5b26658

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeOneOfPowerBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Casselman
namespace GlobalTheory.CompanionTheory.Casselman
theorem _root_.solution :
    ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r →
      (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by
  intro δ r hδ hδ1 hr h
  by_contra hlt
  rw [not_le] at hlt
  have hx : 0 < Real.sqrt δ * r := mul_pos (Real.sqrt_pos.mpr hδ) (by linarith)
  have hcont : ContinuousAt (fun ε : ℝ => δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε)) 0 := by
    apply ContinuousAt.mul continuousAt_const
    exact (Real.continuousAt_const_rpow hx.ne').comp
      (continuous_const.add continuous_id).continuousAt
  have h0 : δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0) = r ^ 2 := by
    rw [add_zero, Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le, inv_mul_cancel_left₀ hδ.ne']
  have h1 : (1 : ℝ) < δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0) := by
    rw [h0]
    nlinarith
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 1 < δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) :=
    hcont.eventually (lt_mem_nhds h1)
  obtain ⟨ε, hε1, hε0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[Set.Ioi (0 : ℝ)] 0, x ∈ Set.Ioi (0 : ℝ))).exists
  exact lt_asymm (h ε hε0) hε1
end GlobalTheory.CompanionTheory.Casselman

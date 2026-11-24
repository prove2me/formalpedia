-- Prove2me | solution 1 for GlobalTheory.ExponentialIntegralUnits.exists_isUnit_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:17.035345+00:00
-- url     : https://prove2.me/submissions/fc181e5f-aabe-4dfb-9257-fe4669169756

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsUnitIntegral
import Theorems.Thm_GlobalTheory_ExponentialIntegralUnits_hasDerivAt_primitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NormedSpace Filter Topology
open GlobalTheory GlobalTheory.ExponentialIntegralUnits
universe u_1
variable {𝔸 : Type u_1} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace GlobalTheory.ExponentialIntegralUnits
theorem _root_.solution (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1) :
    ∃ δ : ℝ, IsUnit (∫ s in (0 : ℝ)..δ, M s) := by
  have hd := (hasDerivAt_primitive M hc 0).tendsto_slope_zero
  rw [h0] at hd
  have hev := hd.eventually (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨δ, hδU, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0' : δ ≠ 0 := Set.mem_compl_singleton_iff.1 hδ0
  simp only [zero_add, intervalIntegral.integral_same, sub_zero] at hδU
  refine ⟨δ, ?_⟩
  have e : (∫ s in (0 : ℝ)..δ, M s) = algebraMap ℝ 𝔸 δ * (δ⁻¹ • ∫ s in (0 : ℝ)..δ, M s) := by
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hδ0', one_smul]
  rw [e]
  exact ((isUnit_iff_ne_zero.2 hδ0').map (algebraMap ℝ 𝔸)).mul hδU
end GlobalTheory.ExponentialIntegralUnits

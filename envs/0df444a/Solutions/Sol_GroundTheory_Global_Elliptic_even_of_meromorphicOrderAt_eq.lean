-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.even_of_meromorphicOrderAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:37.21092+00:00
-- url     : https://prove2.me/submissions/41f24743-a7d0-4bf3-b00b-44f50171adf0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (he : ∀ z, f (-z) = f z) {n : ℤ} (hn : meromorphicOrderAt f 0 = n) : Even n := by
  obtain ⟨u, hu, hu0, e⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn
  have hneg : Tendsto (fun z : ℂ ↦ -z) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((continuous_neg.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have e' := hneg.eventually e
  have key : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (-1 : ℂ) ^ n * u (-z) = u z := by
    filter_upwards [e, e', self_mem_nhdsWithin] with z h1 h2 hz
    have hz' : z ≠ 0 := hz
    rw [he z, h1] at h2
    simp only [sub_zero, smul_eq_mul] at h2
    have h3 : z ^ n * u z = z ^ n * ((-1 : ℂ) ^ n * u (-z)) := by
      rw [h2, show -z = (-1 : ℂ) * z by ring, mul_zpow]
      ring
    exact (mul_left_cancel₀ (zpow_ne_zero n hz') h3).symm
  have hc : ContinuousAt (fun z ↦ (-1 : ℂ) ^ n * u (-z)) 0 := by
    have : ContinuousAt u (-0) := by simpa using hu.continuousAt
    exact continuousAt_const.mul (this.comp continuous_neg.continuousAt)
  have t1 : Tendsto u (𝓝[≠] 0) (𝓝 (u 0)) := hu.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 := (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' key
  have heq : (-1 : ℂ) ^ n * u (-0) = u 0 := tendsto_nhds_unique t2 t1
  rw [neg_zero] at heq
  rcases Int.even_or_odd n with h | h
  · exact h
  · exfalso
    rw [h.neg_one_zpow] at heq
    apply hu0
    linear_combination -heq / 2
end GroundTheory.Global.Elliptic

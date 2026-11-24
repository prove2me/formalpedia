-- Prove2me | solution 1 for GlobalTheory.exists_eq_const_of_periodic_of_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:40:18.568472+00:00
-- url     : https://prove2.me/submissions/24167361-a9b1-424f-947c-f4edb5099aa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_exists_eq_add_sq_mul_of_even
import Theorems.Thm_GlobalTheory_eq_const_of_periodic_of_tendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {f N : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (L.lattice : Set ℂ)ᶜ)
    (hper : ∀ z ∉ L.lattice, ∀ w ∈ L.lattice, f (z + w) = f z)
    (hN : AnalyticAt ℂ N 0) (he : ∀ z, N (-z) = N z) (h0 : N 0 = 0)
    (hfN : ∀ z ∉ L.lattice, z ^ 2 * f z = N z) : ∃ c, ∀ z ∉ L.lattice, f z = c := by
  obtain ⟨h, hh, e⟩ := exists_eq_add_sq_mul_of_even hN he
  refine ⟨h 0, fun z hz => eq_const_of_periodic_of_tendsto L hf hper ?_ hz⟩
  refine (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_notMem_lattice L 0, self_mem_nhdsWithin] with x hx (hx0 : x ≠ 0)
  have := e x
  rw [h0, zero_add, ← hfN x hx] at this
  exact (mul_left_cancel₀ (pow_ne_zero 2 hx0) this).symm
end GlobalTheory

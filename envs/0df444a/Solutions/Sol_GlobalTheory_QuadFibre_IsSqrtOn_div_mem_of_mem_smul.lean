-- Prove2me | solution 1 for GlobalTheory.QuadFibre.IsSqrtOn.div_mem_of_mem_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:47:51.210523+00:00
-- url     : https://prove2.me/submissions/afff6aa5-18a5-4663-b5ad-4811af4123b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegrableContinuousOnAveragedFibreIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.QuadFibre
namespace GlobalTheory.QuadFibre
namespace IsSqrtOn
theorem _root_.solution {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {t₀ t y : K} (h0 : t₀ ≠ 0) (ht : t ∈ t₀ • U) (hy : y ∈ t₀ • U) :
    y ≠ 0 ∧ t / y ∈ U := by
  obtain ⟨-, -, -, hmul, hinv, hnorm, -, -⟩ := h
  rw [Set.mem_smul_set] at ht hy
  obtain ⟨a, ha, rfl⟩ := ht
  obtain ⟨b, hb, rfl⟩ := hy
  have hb0 : b ≠ 0 := by
    intro hb0
    have := hnorm b hb
    rw [hb0, norm_zero] at this
    exact zero_ne_one this
  refine ⟨smul_ne_zero h0 hb0, ?_⟩
  simp only [smul_eq_mul]
  rw [mul_div_mul_left a b h0, div_eq_mul_inv]
  exact hmul a ha _ (hinv b hb)
end IsSqrtOn
end GlobalTheory.QuadFibre

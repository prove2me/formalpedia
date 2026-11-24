-- Prove2me | solution 1 for GlobalTheory.QuadFibre.IsSqrtOn.smul_eq_of_mem_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:26.225581+00:00
-- url     : https://prove2.me/submissions/f169c2d2-b30b-40a6-b9de-0239c90515b6

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
    (h : IsSqrtOn U s) {t₀ t : K} (ht : t ∈ t₀ • U) : t • U = t₀ • U := by
  obtain ⟨-, -, -, hmul, hinv, hnorm, -, -⟩ := h
  rw [Set.mem_smul_set] at ht
  obtain ⟨a, ha, rfl⟩ := ht
  have ha0 : a ≠ 0 := by
    intro ha0
    have := hnorm a ha
    rw [ha0, norm_zero] at this
    exact zero_ne_one this
  have haU : a • U = U := by
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hmul a ha b hb
    · intro hx
      refine ⟨a⁻¹ * x, hmul _ (hinv a ha) x hx, ?_⟩
      rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
  rw [smul_eq_mul, mul_smul, haU]
end IsSqrtOn
end GlobalTheory.QuadFibre

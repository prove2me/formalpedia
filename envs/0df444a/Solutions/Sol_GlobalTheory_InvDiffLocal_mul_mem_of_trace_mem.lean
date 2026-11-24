-- Prove2me | solution 1 for GlobalTheory.InvDiffLocal.mul_mem_of_trace_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:53:58.116031+00:00
-- url     : https://prove2.me/submissions/f0900eb0-52b7-4447-a0be-64d4eca1ed8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationMulLeOneOfTraceApproxIdempotentIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open Classical
open GlobalTheory GlobalTheory.InvDiffLocal
namespace GlobalTheory.InvDiffLocal
theorem _root_.solution {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (x : L)
    (hx : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range) :
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∃ c : 𝓞 L, (c : L) = x * (d : L) := by
  intro d hd
  have hxd : x ∈ FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx b
  have hdd : (d : L) ∈ ((differentIdeal (𝓞 K) (𝓞 L) : Ideal (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  rw [coeIdeal_differentIdeal (𝓞 K) K] at hdd
  have hm := FractionalIdeal.mul_mem_mul hxd hdd
  rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero (𝓞 K) K (by simp))] at hm
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  exact ⟨c, hc⟩
end GlobalTheory.InvDiffLocal

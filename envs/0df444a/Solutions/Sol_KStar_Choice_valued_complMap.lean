-- Prove2me | solution 1 for KStar.Choice.valued_complMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:16.025842+00:00
-- url     : https://prove2.me/submissions/5dd101a6-7450-4b61-82e9-c791e964d099

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_TendstoUnderCofinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open KStar KStar.Choice
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K L)
namespace KStar.Choice
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (x : v.adicCompletion K) :
    Valued.v (complMap v w x) = Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  by_cases hx : x = 0
  · subst hx
    have := w.isPrime
    rw [map_zero, map_zero, map_zero, zero_pow (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne']
  have hx' : complMap v w x ≠ 0 := (map_ne_zero _).2 hx
  have h1 : {y | Valued.v y = Valued.v x} ∈ nhds x :=
    Valued.locally_const ((Valuation.ne_zero_iff _).2 hx)
  have h2 : complMap v w ⁻¹' {y | Valued.v y = Valued.v (complMap v w x)} ∈ nhds x :=
    (continuous_complMap v w).continuousAt.preimage_mem_nhds
      (Valued.locally_const ((Valuation.ne_zero_iff _).2 hx'))
  obtain ⟨a, ha1, ha2⟩ := (denseRange_algebraMap K v).mem_nhds (Filter.inter_mem h1 h2)
  have e1 : Valued.v (algebraMap K (v.adicCompletion K) a) = Valued.v x := ha1
  have e2 : Valued.v (complMap v w (algebraMap K (v.adicCompletion K) a)) =
      Valued.v (complMap v w x) := ha2
  have := w.isPrime
  rw [← e2, ← e1, complMap_algebraMap,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  change Valued.v ((algebraMap K L a : L) : w.adicCompletion L) =
    Valued.v ((a : K) : v.adicCompletion K) ^ _
  rw [valuedAdicCompletion_eq_valuation', valuedAdicCompletion_eq_valuation',
    valuation_liesOver L v w]
end KStar.Choice

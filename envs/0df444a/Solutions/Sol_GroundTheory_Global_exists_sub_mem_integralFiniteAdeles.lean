-- Prove2me | solution 1 for GroundTheory.Global.exists_sub_mem_integralFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:22.073249+00:00
-- url     : https://prove2.me/submissions/fb3b4eb2-a243-439b-9a17-b9c11faf3c25

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsValuationSubLeOne
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Theorems.Thm_GroundTheory_Global_exists_valuation_sub_le_one
import Theorems.Thm_GroundTheory_Global_coe_mem_adicCompletionIntegers_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GroundTheory.Global
theorem _root_.solution (a : FiniteAdeleRing R K) :
    ∃ k : K, a - algebraMap K (FiniteAdeleRing R K) k ∈ integralFiniteAdeles R K := by
  classical
  have hS : {v : HeightOneSpectrum R | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2
  have hx : ∀ v : HeightOneSpectrum R, ∃ z : K,
      a v - (z : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    intro v
    have hU : IsOpen {w : v.adicCompletion K | a v - w ∈ v.adicCompletionIntegers K} :=
      (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
        (continuous_const.sub continuous_id)
    obtain ⟨z, hz⟩ := (denseRange_algebraMap (K := K) v).exists_mem_open hU
      ⟨a v, by simp⟩
    exact ⟨z, hz⟩
  choose x hx using hx
  obtain ⟨k, hkS, hkn⟩ := exists_valuation_sub_le_one hS.toFinset x
  refine ⟨k, fun v => ?_⟩
  change a v - (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K
  by_cases hv : v ∈ hS.toFinset
  · have h1 := (coe_mem_adicCompletionIntegers_iff v (k - x v)).mpr (hkS v hv)
    have h2 : a v - (k : v.adicCompletion K) =
        (a v - (x v : v.adicCompletion K)) - ((k - x v : K) : v.adicCompletion K) := by
      have hc : ∀ z : K, (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z :=
        fun z => by simp [algebraMap_adicCompletion]
      rw [hc, hc, hc, map_sub]
      ring
    rw [h2]
    exact Subring.sub_mem _ (hx v) h1
  · have hav : a v ∈ v.adicCompletionIntegers K := by
      simpa using hv
    exact Subring.sub_mem _ hav ((coe_mem_adicCompletionIntegers_iff v k).mpr (hkn v hv))
end GroundTheory.Global

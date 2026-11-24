-- Prove2me | solution 1 for GlobalTheory.addVal_norm_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:10.2078+00:00
-- url     : https://prove2.me/submissions/ce2e1eb1-397a-4d5c-824d-6daa2b9af1ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_length_quot_span_singleton
import Theorems.Thm_GlobalTheory_addVal_norm_ne_top_iff
import Theorems.Thm_GlobalTheory_addVal_norm_eq_sum_length

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]
variable [∀ n, IsDomain (A n)] [∀ n, IsDiscreteValuationRing (A n)]
namespace GlobalTheory
theorem _root_.solution (x : S) :
    addVal R (Algebra.norm R x) = ∑ n : MaximalSpectrum S,
      addVal (A n) (algebraMap S (A n) x) * n.asIdeal.inertiaDeg R := by
  by_cases hx : x ∈ nonZeroDivisors S
  · rw [addVal_norm_eq_sum_length R A hx]
    exact Finset.sum_congr rfl fun n _ => by rw [length_quot_span_singleton]
  · have h1 : addVal R (Algebra.norm R x) = ⊤ := by
      rwa [← addVal_norm_ne_top_iff R, not_not] at hx
    rw [mem_nonZeroDivisors_iff_left] at hx
    push Not at hx
    obtain ⟨y, hxy, hy⟩ := hx
    have hne : LinearMap.ker (LinearMap.toSpanSingleton S S y) ≠ ⊤ := by
      intro h
      have : (1 : S) ∈ LinearMap.ker (LinearMap.toSpanSingleton S S y) := h ▸ Submodule.mem_top
      exact hy (by simpa using this)
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let n : MaximalSpectrum S := ⟨m, hm⟩
    have hy' : algebraMap S (A n) y ≠ 0 := by
      intro h
      obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff n.asIdeal.primeCompl (A n) y).1 h
      exact s.2 (hle (by simpa using hs))
    have hx' : algebraMap S (A n) x = 0 := by
      have := congrArg (algebraMap S (A n)) hxy
      rw [map_mul, map_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hy'
    rw [h1, eq_comm, ENat.sum_eq_top]
    refine ⟨n, Finset.mem_univ _, ?_⟩
    rw [hx', addVal_zero, ENat.top_mul]
    exact_mod_cast (Ideal.inertiaDeg_pos n.asIdeal R).ne'
end GlobalTheory

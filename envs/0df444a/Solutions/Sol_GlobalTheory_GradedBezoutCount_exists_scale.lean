-- Prove2me | solution 1 for GlobalTheory.GradedBezoutCount.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:17:35.744891+00:00
-- url     : https://prove2.me/submissions/59f5befe-1731-49a2-a9a7-fd42f9d61143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientLeOne
import Theorems.Thm_GlobalTheory_GradedBezoutCount_sub_smul_mem
import Theorems.Thm_GlobalTheory_GradedBezoutCount_exists_minimalPrime_le
import Theorems.Thm_GlobalTheory_GradedBezout_exists_ringKrullDim_quotient_eq_succ
import Theorems.Thm_GlobalTheory_GradedBezout_ringKrullDim_quotient_of_mem_minimalPrimes_sup
import Theorems.Thm_GlobalTheory_isHomogeneous_of_mem_minimalPrimes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
open GlobalTheory.GradedBezoutCount
open GradedBezout
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] {𝒜 : ℕ → Submodule K T}
  [GradedAlgebra 𝒜]
variable {ι : Type*} [Finite ι] {x : ι → T} (hx : ∀ i, x i ∈ 𝒜 1)
  (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hx hfin
namespace GlobalTheory.GradedBezoutCount
theorem _root_.solution {P : Ideal T} [P.IsPrime] (hI : P.IsHomogeneous 𝒜)
    (hr : ringKrullDim (T ⧸ P) = (0 + 1 : ℕ)) {φ ψ : T →ₐ[K] K} (hφ : ∀ y ∈ P, φ y = 0)
    (hψ : ∀ y ∈ P, ψ y = 0) {i : ι} (hi : φ (x i) ≠ 0) :
    ∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, ψ y = c ^ e * φ y := by
  have key : ∀ e, ∀ y ∈ 𝒜 e, φ y = 0 → y ∈ P := fun e y hy h0 => by
    by_contra hyP
    obtain ⟨Q, hQ, hle⟩ := exists_minimalPrime_le φ hφ h0
    haveI := hQ.1.1
    have h1 := ringKrullDim_quotient_of_mem_minimalPrimes_sup hfin hr hyP hQ
    obtain ⟨m, h2⟩ := exists_ringKrullDim_quotient_eq_succ hx hfin
      (isHomogeneous_of_mem_minimalPrimes _ (isHomogeneous_sup_span hI hy) hQ)
      (i := i) fun h => hi (hle _ h)
    rw [h2] at h1
    have h3 : m + 1 = 0 := by exact_mod_cast h1
    omega
  refine ⟨ψ (x i) / φ (x i), fun e y hy => ?_⟩
  obtain ⟨h1, h2⟩ := sub_smul_mem φ (hx i) hy
  have h3 := hψ _ (key e _ h1 h2)
  simp only [map_sub, map_smul, map_pow, smul_eq_mul] at h3
  rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero e hi)]
  linear_combination h3
end GlobalTheory.GradedBezoutCount

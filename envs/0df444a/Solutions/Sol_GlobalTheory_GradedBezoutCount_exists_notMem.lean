-- Prove2me | solution 1 for GlobalTheory.GradedBezoutCount.exists_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:27:44.115024+00:00
-- url     : https://prove2.me/submissions/799192db-8564-4327-8f76-ab9048fbfbe2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientLeOne
import Theorems.Thm_GlobalTheory_GradedBezoutCount_ringKrullDim_quotient_le_one
import Theorems.Thm_GlobalTheory_GradedBezoutCount_exists_point

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
theorem _root_.solution [IsAlgClosed K] {F : Set T} {Φ : Set (T →ₐ[K] K)} (hΦ : Φ.Finite)
    (hF : ∀ φ : T →ₐ[K] K, (∃ i, φ (x i) ≠ 0) → (∀ f ∈ F, φ f = 0) →
      ∃ ψ ∈ Φ, ∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ y = c ^ e * ψ y)
    {P : Ideal T} [hP : P.IsPrime] {r : ℕ} (hr : ringKrullDim (T ⧸ P) = (r + 2 : ℕ)) :
    ∃ f ∈ F, f ∉ P := by
  haveI := finiteType hfin
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ : ∃ i, x i ∉ P := by
    by_contra h
    push Not at h
    have := ringKrullDim_quotient_le_zero hfin h
    rw [hr] at this
    exact absurd this (by exact_mod_cast (by omega))
  have key : ∀ ψ : T →ₐ[K] K, ∃ e, ∃ y ∈ 𝒜 e, ψ y = 0 ∧ y ∉ P := fun ψ => by
    by_contra h
    push Not at h
    have := ringKrullDim_quotient_le_one ψ (hx i) hi h
    rw [hr] at this
    exact absurd this (by exact_mod_cast (by omega))
  choose e y hy hψ hyP using key
  have hprod : x i * ∏ ψ ∈ hΦ.toFinset, y ψ ∉ P := by
    rw [hP.mul_mem_iff_mem_or_mem, Ideal.IsPrime.prod_mem_iff]
    push Not
    exact ⟨hi, fun ψ _ => hyP ψ⟩
  obtain ⟨φ, h1, h2⟩ := exists_point (K := K) hprod
  rw [map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at h2
  obtain ⟨ψ, hψΦ, c, hc⟩ := hF φ ⟨i, h2.1⟩ fun f hf => h1 f (hcon f hf)
  exact h2.2 ψ (hΦ.mem_toFinset.2 hψΦ) (by rw [hc _ _ (hy ψ), hψ, mul_zero])
end GlobalTheory.GradedBezoutCount

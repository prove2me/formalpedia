-- Prove2me | solution 1 for GlobalTheory.GradedBezoutCount.exists_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:06:51.383799+00:00
-- url     : https://prove2.me/submissions/01116a01-09c8-45e6-a5be-45bafe8699b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientLeOne

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
omit [GradedAlgebra 𝒜]
namespace GlobalTheory.GradedBezoutCount
theorem _root_.solution [IsAlgClosed K] [Algebra.FiniteType K T] {P : Ideal T} [hP : P.IsPrime]
    {h : T} (hh : h ∉ P) : ∃ φ : T →ₐ[K] K, (∀ y ∈ P, φ y = 0) ∧ φ h ≠ 0 := by
  haveI : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := K)
  rw [← IsJacobsonRing.out' P hP.isRadical, Ideal.jacobson, Ideal.mem_sInf] at hh
  push Not at hh
  obtain ⟨M, ⟨hPM, hM⟩, hhM⟩ := hh
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (T ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (T ⧸ M)
  let e : K ≃ₐ[K] (T ⧸ M) := AlgEquiv.ofBijective (Algebra.ofId K (T ⧸ M))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M), fun y hy => ?_, ?_⟩
  · simp [Ideal.Quotient.eq_zero_iff_mem.2 (hPM hy)]
  · simpa [Ideal.Quotient.eq_zero_iff_mem] using hhM
end GlobalTheory.GradedBezoutCount

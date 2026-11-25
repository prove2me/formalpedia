-- Prove2me | solution 1 for GlobalTheory.GradedBezoutCount.exists_minimalPrime_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:05:03.596952+00:00
-- url     : https://prove2.me/submissions/5569fa58-6f35-491b-a958-54b967491379

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
variable {ι : Type*} [Finite ι] {x : ι → T} (hx : ∀ i, x i ∈ 𝒜 1)
  (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hx hfin
omit hx [GradedAlgebra 𝒜] [Finite ι] hfin
namespace GlobalTheory.GradedBezoutCount
theorem _root_.solution {P : Ideal T} {f : T} (φ : T →ₐ[K] K) (hP : ∀ y ∈ P, φ y = 0)
    (hf : φ f = 0) : ∃ Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes, ∀ y ∈ Q, φ y = 0 := by
  haveI := RingHom.ker_isPrime φ
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_minimalPrimes_le (I := P ⊔ Ideal.span {f})
    (J := RingHom.ker φ) (sup_le hP ((Ideal.span_singleton_le_iff_mem _).2 hf))
  exact ⟨Q, hQ, hle⟩
end GlobalTheory.GradedBezoutCount

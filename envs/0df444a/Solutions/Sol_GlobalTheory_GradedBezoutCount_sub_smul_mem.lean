-- Prove2me | solution 1 for GlobalTheory.GradedBezoutCount.sub_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:07:19.093136+00:00
-- url     : https://prove2.me/submissions/d7d2dde1-4705-4162-a113-8dc0ab137752

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
namespace GlobalTheory.GradedBezoutCount
theorem _root_.solution (φ : T →ₐ[K] K) {t y : T} {e : ℕ} (ht : t ∈ 𝒜 1) (hy : y ∈ 𝒜 e) :
    φ t ^ e • y - φ y • t ^ e ∈ 𝒜 e ∧ φ (φ t ^ e • y - φ y • t ^ e) = 0 := by
  refine ⟨Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ ?_), ?_⟩
  · simpa using SetLike.pow_mem_graded e ht
  · simp [mul_comm]
end GlobalTheory.GradedBezoutCount

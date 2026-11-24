-- Prove2me | solution 1 for GlobalTheory.FixedPoint.mem_range_of_algebraMap_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:54:14.997839+00:00
-- url     : https://prove2.me/submissions/438d1aab-bae5-4f70-ad0b-f290e15c9210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_range_algebraMap_of_forall_algEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.FixedPoint
universe u v w
variable {K₀ : Type u} {K₁ : Type v} {L : Type w} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]
namespace GlobalTheory.FixedPoint
theorem _root_.solution [PerfectField K₀] [IsAlgClosed L] (a : K₁)
    (ha : ∀ s : L ≃ₐ[K₀] L, s (algebraMap K₁ L a) = algebraMap K₁ L a) :
    a ∈ Set.range (algebraMap K₀ K₁) := by
  obtain ⟨k, hk⟩ := GaloisDescent.mem_range_algebraMap_of_forall_algEquiv _ ha
  refine ⟨k, (algebraMap K₁ L).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply, hk]
end GlobalTheory.FixedPoint

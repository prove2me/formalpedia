-- Prove2me | solution 1 for Neutral.B1.cycN_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:12.443166+00:00
-- url     : https://prove2.me/submissions/27b0022b-2f6b-4cc3-8c51-97a6731be5f5

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
  (n : ℕ) [NeZero n]
variable {K L n}
namespace Neutral.B1
theorem _root_.solution (σ : L ≃ₐ[K] L) (ζ : L) (h : ζ ^ n = 1) :
    σ ζ = ζ ^ ((cycN K L n σ : ZMod n)).val := by
  have hz : ζ ≠ 0 := by
    rintro rfl
    simp [NeZero.ne n] at h
  have ht : Units.mk0 ζ hz ∈ rootsOfUnity n L := by
    rw [mem_rootsOfUnity]; ext; simp [h]
  have := modularCyclotomicCharacter.spec L (HasEnoughRootsOfUnity.natCard_rootsOfUnity L n)
    (MulSemiringAction.toRingAut (L ≃ₐ[K] L) L σ) ht
  simpa [cycN] using this
end Neutral.B1

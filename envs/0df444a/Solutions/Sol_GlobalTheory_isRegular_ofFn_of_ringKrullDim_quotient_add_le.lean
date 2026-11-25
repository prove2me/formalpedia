-- Prove2me | solution 1 for GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:21.956136+00:00
-- url     : https://prove2.me/submissions/7dd3dfc7-1781-4c6d-b834-e4f5477c3b32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsRegularOfFnOfRingKrullDimQuotientAddLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (d r : ℕ) (f : Fin r → A),
      ringKrullDim A = d → (∀ i, f i ∈ IsLocalRing.maximalIdeal A) →
      ringKrullDim (A ⧸ Ideal.span (Set.range f)) + r ≤ d →
      RingTheory.Sequence.IsRegular A (List.ofFn f) := by
  intro A _ _ d r f hd hm hq
  have he : Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
    unfold Ideal.ofList
    congr 1
    ext x
    simp [List.mem_ofFn]
  refine isRegular_of_isCM_of_ringKrullDim_quotient_add_length_le
    (isCM_of_isRegularLocalRing A) (fun y hy => ?_) ?_
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact hm i
  · rw [he, List.length_ofFn, hd]
    exact hq
end GlobalTheory

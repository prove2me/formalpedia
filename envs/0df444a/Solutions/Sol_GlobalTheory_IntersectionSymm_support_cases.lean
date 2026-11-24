-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.support_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:08:37.097679+00:00
-- url     : https://prove2.me/submissions/57dbac77-e861-4021-96c9-ffdf3f48b7ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
import Theorems.Thm_GlobalTheory_IntersectionSymm_height_one_or_eq_max

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.IntersectionSymm
namespace GlobalTheory.IntersectionSymm
theorem _root_.solution {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (a : A) (ha : a ≠ 0) (P : Finset (PrimeSpectrum A))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal) :
    ∀ p ∈ Module.support A (A ⧸ Ideal.span {a}), p ∈ P ∨ p.asIdeal = maximalIdeal A := by
  intro p hp
  rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] at hp
  have hap : a ∈ p.asIdeal := hp (Ideal.subset_span rfl)
  have h0 : p.asIdeal ≠ ⊥ := fun h => ha (by rw [h] at hap; exact (Submodule.mem_bot A).1 hap)
  rcases height_one_or_eq_max hA p.asIdeal h0 with h | h
  · exact Or.inl ((hP p).2 ⟨h, hap⟩)
  · exact Or.inr h
end GlobalTheory.IntersectionSymm

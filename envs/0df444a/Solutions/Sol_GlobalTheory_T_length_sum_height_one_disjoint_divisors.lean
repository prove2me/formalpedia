-- Prove2me | solution 1 for GlobalTheory.T.length_sum_height_one_disjoint_divisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:22:09.199878+00:00
-- url     : https://prove2.me/submissions/e8a20f5e-4718-4b32-889b-7d372e1cbb3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisorsStatement
import Theorems.Thm_GlobalTheory_IntersectionSymm_intersection_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A], ringKrullDim A = 2 → ∀ (a b : A), a ≠ 0 → b ≠ 0 → ∀ (P Q : Finset (PrimeSpectrum A)), (∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal) → (∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) → Disjoint P Q → ∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal b})).toNat = ∑ p ∈ Q, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) b})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal a})).toNat := by
  first | exact @GlobalTheory.IntersectionSymm.intersection_symm | exact GlobalTheory.IntersectionSymm.intersection_symm | (intros; apply GlobalTheory.IntersectionSymm.intersection_symm <;> assumption)
end _root_.GlobalTheory.T

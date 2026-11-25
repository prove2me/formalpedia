-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.intersection_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:57.709034+00:00
-- url     : https://prove2.me/submissions/50406497-b827-4e2f-aa51-382de0490531

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
import Theorems.Thm_GlobalTheory_IntersectionSymm_side
import Theorems.Thm_GlobalTheory_IntersectionSymm_terms_ne_top
import Theorems.Thm_GlobalTheory_IntersectionSymm_toNat_sum_mul
import Theorems.Thm_GlobalTheory_T_length_ker_coker_lsmul_quotient_span_swap


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
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A], ringKrullDim A = 2 → ∀ (a b : A), a ≠ 0 → b ≠ 0 → ∀ (P Q : Finset (PrimeSpectrum A)), (∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal) → (∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) → Disjoint P Q → ∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal b})).toNat = ∑ p ∈ Q, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) b})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal a})).toNat := by
  intro A _ _ _ _ hA a b ha hb P Q hP hQ hdis
  obtain ⟨hK, hC⟩ := side hA a b ha P Q hP hQ hdis
  obtain ⟨_, hC'⟩ := side hA b a hb Q P hQ hP hdis.symm
  obtain ⟨hk, hc⟩ := GlobalTheory.T.length_ker_coker_lsmul_quotient_span_swap A a b ha hb
  have hS := hC.symm.trans (hc.trans hC')
  rw [← hk] at hS
  have hS' := WithTop.add_left_cancel hK hS
  refine (toNat_sum_mul P _ _ (terms_ne_top hA a b ha P Q hP hQ hdis)).trans
    ((congrArg ENat.toNat hS').trans
      (toNat_sum_mul Q _ _ (terms_ne_top hA b a hb Q P hQ hP hdis.symm)).symm)
end GlobalTheory.IntersectionSymm

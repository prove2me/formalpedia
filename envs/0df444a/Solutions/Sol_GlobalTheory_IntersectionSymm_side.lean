-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:00:53.65922+00:00
-- url     : https://prove2.me/submissions/b222f9b1-def5-455a-b593-1785ab092f57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
import Theorems.Thm_GlobalTheory_IntersectionSymm_dim_quotient_eq_one
import Theorems.Thm_GlobalTheory_IntersectionSymm_length_localized_quotient
import Theorems.Thm_GlobalTheory_IntersectionSymm_length_quotient_sup
import Theorems.Thm_GlobalTheory_IntersectionSymm_support_cases
import Theorems.Thm_P2M_GlobalTheory_T_length_coker_lsmul_eq_length_ker_add_sum__275061a9a21e


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
theorem _root_.solution {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (a b : A) (ha : a ≠ 0) (P Q : Finset (PrimeSpectrum A))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal)
    (hQ : ∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) (hdis : Disjoint P Q) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤ ∧
    Module.length A ((A ⧸ Ideal.span {a}) ⧸
        LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) +
      ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸
          Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a}) *
        Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal b}) := by
  have hmem : ∀ p ∈ P, p.asIdeal.height = 1 ∧ a ∈ p.asIdeal ∧ b ∉ p.asIdeal := by
    intro p hp
    obtain ⟨h1, h2⟩ := (hP p).1 hp
    exact ⟨h1, h2, fun hb => Finset.disjoint_left.1 hdis hp ((hQ p).2 ⟨h1, hb⟩)⟩
  have key := GlobalTheory.T.length_coker_lsmul_eq_length_ker_add_sum' A b P
    (fun p hp => ⟨dim_quotient_eq_one hA p.asIdeal (hmem p hp).1, (hmem p hp).2.2⟩)
    (A ⧸ Ideal.span {a}) (support_cases hA a ha P hP)
  refine ⟨key.1, key.2.trans ?_⟩
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [length_localized_quotient, length_quotient_sup]
end GlobalTheory.IntersectionSymm

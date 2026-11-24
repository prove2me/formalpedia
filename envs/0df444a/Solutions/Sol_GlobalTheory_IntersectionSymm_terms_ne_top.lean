-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.terms_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:08:37.834232+00:00
-- url     : https://prove2.me/submissions/f31650ee-7441-4e7f-9e7a-9242bcd89aa5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
import Theorems.Thm_GlobalTheory_IntersectionSymm_dim_quotient_eq_one
import Theorems.Thm_GlobalTheory_IntersectionSymm_length_localized_ne_top
import Theorems.Thm_GlobalTheory_IntersectionSymm_length_quotient_ne_top

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
    ∀ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸
          Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a}) *
        Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal b}) ≠ ⊤ := by
  intro p hp
  obtain ⟨h1, _⟩ := (hP p).1 hp
  have hb : b ∉ p.asIdeal := fun hb => Finset.disjoint_left.1 hdis hp ((hQ p).2 ⟨h1, hb⟩)
  exact WithTop.mul_ne_top (length_localized_ne_top p.asIdeal h1 a ha)
    (length_quotient_ne_top p.asIdeal (dim_quotient_eq_one hA p.asIdeal h1) b hb)
end GlobalTheory.IntersectionSymm

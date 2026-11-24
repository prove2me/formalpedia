-- Prove2me | solution 1 for GlobalTheory.Wick.induction_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:02.224116+00:00
-- url     : https://prove2.me/submissions/9e5ee5f0-2715-44f5-86b3-6fffe51df737

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Theorems.Thm_GlobalTheory_Wick_monomial_induction_inl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Wick
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}
namespace GlobalTheory.Wick
theorem _root_.solution {p : MvPolynomial (ι ⊕ κ) R → Prop}
    (h0 : ∀ q : MvPolynomial κ R, p (rename Sum.inr q))
    (hadd : ∀ P Q, p P → p Q → p (P + Q))
    (h : ∀ P (i : ι), p P → p (X (Sum.inl i) * P)) (P : MvPolynomial (ι ⊕ κ) R) : p P := by
  induction P using MvPolynomial.induction_on' with
  | monomial s c => exact monomial_induction_inl c (fun t => h0 _) (fun s i => h _ i) s
  | add P Q hP hQ => exact hadd P Q hP hQ
end GlobalTheory.Wick

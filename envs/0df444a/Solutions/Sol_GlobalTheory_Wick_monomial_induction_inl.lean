-- Prove2me | solution 1 for GlobalTheory.Wick.monomial_induction_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:09.780667+00:00
-- url     : https://prove2.me/submissions/0a21b131-ea20-409e-af5e-cb1314cfca1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Theorems.Thm_GlobalTheory_Wick_finsupp_induction_single

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
theorem _root_.solution {p : MvPolynomial (ι ⊕ κ) R → Prop} (c : R)
    (h0 : ∀ t : κ →₀ ℕ, p (rename Sum.inr (monomial t c)))
    (h : ∀ (s : ι ⊕ κ →₀ ℕ) (i : ι), p (monomial s c) → p (X (Sum.inl i) * monomial s c))
    (s : ι ⊕ κ →₀ ℕ) : p (monomial s c) := by
  suffices H : ∀ t : κ →₀ ℕ, p (monomial (s + t.mapDomain Sum.inr) c) by simpa using H 0
  induction s using finsupp_induction_single with
  | h0 => intro t; simpa [rename_monomial] using h0 t
  | h s v ih =>
    intro t
    rcases v with i | j
    · rw [add_right_comm, monomial_add_single, pow_one, mul_comm]; exact h _ _ (ih t)
    · have := ih (Finsupp.single j 1 + t)
      rwa [Finsupp.mapDomain_add, Finsupp.mapDomain_single, ← add_assoc] at this
end GlobalTheory.Wick

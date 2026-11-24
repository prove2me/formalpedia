-- Prove2me | solution 1 for GlobalTheory.Lyndon.monomial_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:53:24.679039+00:00
-- url     : https://prove2.me/submissions/c9d47b26-e710-4b83-9bf1-ab28284639c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
open ShuffleAlgebra
variable (K : Type) [Field K]
namespace GlobalTheory.Lyndon
theorem _root_.solution {σ : Type} (d : σ →₀ ℕ) :
    (MvPolynomial.monomial d (1 : K)) = ((Finsupp.toMultiset d).map MvPolynomial.X).prod := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Multiset.map_add, Multiset.prod_add, ← hf, ← hg, MvPolynomial.monomial_mul,
      one_mul]
  | single a n =>
    rw [Finsupp.toMultiset_single, ← MvPolynomial.X_pow_eq_monomial]
    simp [Multiset.map_nsmul, Multiset.prod_nsmul]
end GlobalTheory.Lyndon

-- Prove2me | solution 1 for MellinDuality.gcd_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:19.109233+00:00
-- url     : https://prove2.me/submissions/e1dda5b1-9d3a-4670-bf5f-670f5d8f9372

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_sum_pairs_gcd


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) :
    ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, F n n' =
      ∑ ab ∈ coprimePairs N, ∑ r ∈ pairRange N ab, F (ab.1 * r) (ab.2 * r) :=
  sum_pairs_gcd N F
end MellinDuality

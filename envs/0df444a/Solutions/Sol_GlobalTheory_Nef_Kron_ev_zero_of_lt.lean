-- Prove2me | solution 1 for GlobalTheory.Nef.Kron.ev_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:11:42.574232+00:00
-- url     : https://prove2.me/submissions/624a705f-8ab7-4650-b30d-5fa3ff3c55bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
import Theorems.Thm_GlobalTheory_Nef_Kron_ev_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.Kron
open Polynomial
variable {F : Type} [Field F] (c : ℕ → F)
namespace GlobalTheory.Nef.Kron
theorem _root_.solution (q p : F[X]) (s : ℕ) (h : ∀ j < s, ev c (q * X ^ j) = 0)
    (hp : p.natDegree < s) : ev c (q * p) = 0 := by
  rw [ev_expand c q p s hp]
  exact Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero]
end GlobalTheory.Nef.Kron

-- Prove2me | solution 1 for GlobalTheory.MxDet.iterD_linF_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:22:58.294735+00:00
-- url     : https://prove2.me/submissions/fa5d8ce4-d4e9-4c71-ac56-e3cce81b1ef8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReDetRelation
import Theorems.Thm_GlobalTheory_MxDet_pderiv_linF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.MxDet
namespace GlobalTheory.MxDet
theorem _root_.solution {ι : Type} [Fintype ι] (x : ι → ℝ) (N : ℕ) : ∀ (m : ℕ) (a : Fin m → ι),
    iterD m a (linF x ^ N) = MvPolynomial.C ((N.descFactorial m : ℝ) * ∏ j, x (a j)) * linF x ^ (N - m)
  | 0, a => by simp [iterD]
  | m + 1, a => by
    rw [iterD, LinearMap.comp_apply, solution x N m, Derivation.coeFn_coe, MvPolynomial.pderiv_C_mul,
      MvPolynomial.pderiv_pow, pderiv_linF, Nat.descFactorial_succ, Fin.prod_univ_succ, Nat.sub_sub]
    simp only [Fin.tail, Nat.cast_mul, map_mul, map_natCast]
    ring
end GlobalTheory.MxDet

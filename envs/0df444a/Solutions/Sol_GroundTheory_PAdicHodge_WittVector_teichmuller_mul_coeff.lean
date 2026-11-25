-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.teichmuller_mul_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:25.344509+00:00
-- url     : https://prove2.me/submissions/c9d473a9-448c-4ba4-8bf4-2cf6da6f1e71

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmuller_add_verschiebung_shift
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobenius_teichmuller

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
variable [CharP R p]
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (a : R) (x : WittVector p R) (n : ℕ) :
    (teichmuller p a * x).coeff n = a ^ p ^ n * x.coeff n := by
  induction n generalizing a x with
  | zero => rw [mul_coeff_zero, teichmuller_coeff_zero, pow_zero, pow_one]
  | succ n ih =>
    conv_lhs => rw [← WittVector.teichmuller_add_verschiebung_shift x]
    rw [mul_add, ← map_mul, mul_comm (teichmuller p a), ← verschiebung_mul_frobenius,
      WittVector.frobenius_teichmuller]
    rw [coeff_add_of_disjoint (n + 1) _ _ fun m => ?_]
    · rw [teichmuller_coeff_pos p _ _ n.succ_pos, zero_add, verschiebung_coeff_succ, mul_comm,
        ih, shift_coeff, ← pow_mul, ← pow_succ', add_comm 1 n]
    · rcases m with _ | m
      · exact Or.inr (verschiebung_coeff_zero _)
      · exact Or.inl (teichmuller_coeff_pos p _ _ m.succ_pos)
end WittVector
end GroundTheory.PAdicHodge

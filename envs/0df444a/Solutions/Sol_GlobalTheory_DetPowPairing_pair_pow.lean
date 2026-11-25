-- Prove2me | solution 1 for GlobalTheory.DetPowPairing.pair_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:21.408793+00:00
-- url     : https://prove2.me/submissions/fce7f42c-b706-41b5-980e-bf3d89dcd398

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_monomial
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_det
import Theorems.Thm_ReciprocityTheory_PGsh_cayley


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.DetPowPairing
open MvPolynomial
variable {σ : Type} {C : Type} [CommRing C]
namespace GlobalTheory.DetPowPairing
theorem _root_.solution (n x : ℕ) :
    (∏ c ∈ Finset.range n, (c.factorial : C)) * pair (cayDet n C ^ x) (cayDet n C ^ x) =
      ∏ c ∈ Finset.range n, ((x + c).factorial : C) := by
  induction x with
  | zero =>
    have h1 : pair (1 : MvPolynomial (Fin n × Fin n) C) 1 = 1 := by
      rw [show (1 : MvPolynomial (Fin n × Fin n) C) = monomial 0 1 from rfl, pair_monomial]
      simp [wt]
    simp [h1]
  | succ x ih =>
    have hc := cayley n C (x + 1)
    rw [Nat.add_sub_cancel] at hc
    have hp : pair (cayDet n C ^ (x + 1)) (cayDet n C ^ (x + 1)) =
        pair (cayDet n C ^ x) (cayOp n C (cayDet n C ^ (x + 1))) := by
      rw [← pair_det, ← pow_succ]
    rw [hp, hc, map_nsmul, nsmul_eq_mul, Nat.cast_prod, mul_left_comm, ih,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [show x + 1 + c = (x + c) + 1 by ring, Nat.factorial_succ]
    push_cast
    ring
end GlobalTheory.DetPowPairing

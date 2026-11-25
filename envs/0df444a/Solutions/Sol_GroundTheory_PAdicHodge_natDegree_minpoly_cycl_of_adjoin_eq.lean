-- Prove2me | solution 1 for GroundTheory.PAdicHodge.natDegree_minpoly_cycl_of_adjoin_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:05:17.965074+00:00
-- url     : https://prove2.me/submissions/92c032f6-5150-4629-9db8-e9be57c94cad

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_cycl
import Theorems.Thm_GroundTheory_PAdicHodge_totient_prime_pow_succ
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_mono
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_sup_adjoin_simple


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {y : PadicAlgCl p}
    (hy : ℚ_[p]⟮y⟯ = cycl p (k + 1)) : (minpoly (cycl p k) y).natDegree = p := by
  have hint : IsIntegral (cycl p k) y :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top
  have e := finrank_sup_adjoin_simple (cycl p k) hint
  rw [hy, sup_eq_right.2 (cycl_mono (Nat.le_succ k)), finrank_cycl, finrank_cycl,
    totient_prime_pow_succ hk] at e
  have hφ : 0 < Nat.totient (p ^ k) := Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)
  rw [mul_comm p] at e
  exact (Nat.eq_of_mul_eq_mul_left hφ e).symm
end GroundTheory.PAdicHodge

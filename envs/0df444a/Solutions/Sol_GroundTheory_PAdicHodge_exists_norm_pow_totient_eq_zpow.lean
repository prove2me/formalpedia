-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_norm_pow_totient_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:19.288057+00:00
-- url     : https://prove2.me/submissions/ddb6b0fe-fcb3-4912-b535-4862146d7230

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_natDegree_minpoly
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_eq_zpow_of_ne_zero
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_cycl
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_eq_mul_finrank_extendScalars


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
theorem _root_.solution {n : ℕ} {y : PadicAlgCl p} (hy : y ∈ cycl p n)
    (hy0 : y ≠ 0) : ∃ z : ℤ, ‖y‖ ^ Nat.totient (p ^ n) = (p : ℝ) ^ z := by
  have hint : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  have hle : ℚ_[p]⟮y⟯ ≤ cycl p n := by rw [adjoin_simple_le_iff]; exact hy
  have hdvd : (minpoly ℚ_[p] y).natDegree ∣ Nat.totient (p ^ n) := by
    rw [← finrank_cycl, finrank_eq_mul_finrank_extendScalars hle,
      IntermediateField.adjoin.finrank hint]
    exact Dvd.intro _ rfl
  obtain ⟨m, hm⟩ := hdvd
  have hc0 : (minpoly ℚ_[p] y).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hy0
  obtain ⟨z, hz⟩ := exists_norm_eq_zpow_of_ne_zero hc0
  refine ⟨z * m, ?_⟩
  rw [hm, pow_mul, norm_pow_natDegree_minpoly, hz, zpow_mul, zpow_natCast]
end GroundTheory.PAdicHodge

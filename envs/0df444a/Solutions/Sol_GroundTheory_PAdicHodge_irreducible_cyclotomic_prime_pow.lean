-- Prove2me | solution 1 for GroundTheory.PAdicHodge.irreducible_cyclotomic_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:44.569907+00:00
-- url     : https://prove2.me/submissions/e3c5f44d-f7a5-4f01-bff3-63990fef0c11

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_minpoly_eq_cyclotomic_of_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_exists_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (n : ℕ) : Irreducible (cyclotomic (p ^ n) ℚ_[p]) := by
  cases n with
  | zero => simpa using irreducible_X_sub_C (1 : ℚ_[p])
  | succ k =>
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (k + 1)
    rw [← minpoly_eq_cyclotomic_of_isPrimitiveRoot hζ]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral ζ)
end GroundTheory.PAdicHodge

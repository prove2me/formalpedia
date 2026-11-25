-- Prove2me | solution 1 for GroundTheory.PAdicHodge.finrank_cycl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:57:16.699901+00:00
-- url     : https://prove2.me/submissions/58c300f7-bed3-4d3d-98ab-730af2ff9233

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_minpoly_eq_cyclotomic_of_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_eq_adjoin
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
theorem _root_.solution (n : ℕ) : finrank ℚ_[p] (cycl p n) = Nat.totient (p ^ n) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) n
  rw [cycl_eq_adjoin hζ, IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ζ)]
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hζ
    subst hζ
    rw [minpoly.one]
    simpa using natDegree_X_sub_C (1 : ℚ_[p])
  | succ k => rw [minpoly_eq_cyclotomic_of_isPrimitiveRoot hζ, natDegree_cyclotomic]
end GroundTheory.PAdicHodge

-- Prove2me | solution 1 for GlobalTheory.AffineThickening.exists_pow_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:09.631918+00:00
-- url     : https://prove2.me/submissions/5b4c3c36-d308-4673-91b1-e6f9a8337d3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
namespace GlobalTheory.AffineThickening
theorem _root_.solution {Y : Scheme.{u}} {U V : Y.Opens} (hU : IsAffineOpen U)
    (h : V ≤ U) (g a : Γ(Y, U)) (e : V = Y.basicOpen g) (ha : rs h a = 0) :
    ∃ n : ℕ, g ^ n * a = 0 := by
  subst e
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y hU a g ha
end GlobalTheory.AffineThickening

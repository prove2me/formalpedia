-- Prove2me | solution 1 for GlobalTheory.AffineThickening.exists_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:03:22.206254+00:00
-- url     : https://prove2.me/submissions/077453ae-2568-4064-9a41-72aa25255b41

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
    (h : V ≤ U) (g : Γ(Y, U)) (x : Γ(Y, V)) (e : V = Y.basicOpen g) :
    ∃ (n : ℕ) (y : Γ(Y, U)), rs h y = rs h g ^ n * x := by
  subst e
  exact exists_eq_pow_mul_of_isAffineOpen Y U hU g x
end GlobalTheory.AffineThickening

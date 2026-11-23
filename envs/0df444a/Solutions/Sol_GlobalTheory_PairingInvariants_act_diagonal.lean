-- Prove2me | solution 1 for GlobalTheory.PairingInvariants.act_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:12.798369+00:00
-- url     : https://prove2.me/submissions/a902bbcb-bca2-4d6b-87ee-b04555755f0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.PairingInvariants
variable {T : Type} {n N : ℕ}
namespace GlobalTheory.PairingInvariants
theorem _root_.solution (a b : T → Fin n → ℂ) (z : T × Bool × Fin n × Fin N → ℂ) :
    act (fun t => diagonal (a t)) (fun t => diagonal (b t)) z =
      fun v => (if v.2.1 then a v.1 v.2.2.1 else b v.1 v.2.2.1) * z v := by
  funext ⟨t, c, k, j⟩
  cases c <;> simp [act, diagonal_apply]
end GlobalTheory.PairingInvariants

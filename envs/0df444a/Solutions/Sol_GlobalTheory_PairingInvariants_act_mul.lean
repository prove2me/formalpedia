-- Prove2me | solution 1 for GlobalTheory.PairingInvariants.act_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:51.985731+00:00
-- url     : https://prove2.me/submissions/15d1a985-3580-4fed-9ec6-c30f716d79aa

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
theorem _root_.solution (g h g' h' : T → Matrix (Fin n) (Fin n) ℂ) (z : T × Bool × Fin n × Fin N → ℂ) :
    act (fun t => g t * g' t) (fun t => h t * h' t) z = act g h (act g' h' z) := by
  funext ⟨t, b, k, j⟩
  cases b <;>
  · simp only [act, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, if_true, Bool.false_eq_true, if_false, mul_assoc]
    exact Finset.sum_comm
end GlobalTheory.PairingInvariants

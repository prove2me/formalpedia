-- Prove2me | solution 1 for GlobalTheory.T.exists_aeval_pairings_eq_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:37.635805+00:00
-- url     : https://prove2.me/submissions/9ce93d93-fad9-40b3-b745-8efb2fdcb55d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairingsStatement
import Theorems.Thm_GlobalTheory_invariant_polynomial_eq_aeval_pairings


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (T : Type) [Fintype T] [DecidableEq T] (n N : ℕ), N ≤ n → ∀ p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ, (∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ z : T × Bool × Fin n × Fin N → ℂ, MvPolynomial.eval (fun v => ∑ l, (if v.2.1 then u v.1 v.2.2.1 l else conj (u v.1 v.2.2.1 l)) * z (v.1, v.2.1, l, v.2.2.2)) p = MvPolynomial.eval z p) → ∃ s : MvPolynomial (T × Fin N × Fin N) ℂ, p = MvPolynomial.aeval (fun v : T × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)) s := by
  first | exact @GlobalTheory.invariant_polynomial_eq_aeval_pairings | exact GlobalTheory.invariant_polynomial_eq_aeval_pairings | (intros; apply GlobalTheory.invariant_polynomial_eq_aeval_pairings <;> assumption)
end _root_.GlobalTheory.T

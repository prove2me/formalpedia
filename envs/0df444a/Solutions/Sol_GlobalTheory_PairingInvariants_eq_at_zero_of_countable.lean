-- Prove2me | solution 1 for GlobalTheory.PairingInvariants.eq_at_zero_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:32.832217+00:00
-- url     : https://prove2.me/submissions/ec3f914b-224f-4cce-819c-88c8b6ee3ece

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
theorem _root_.solution {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    {S : Set ℂ} (hS : S.Countable) (h : ∀ c ∉ S, F c = G c) : F 0 = G 0 :=
  congrFun (Continuous.ext_on (hS.dense_compl ℂ) hF.continuous hG.continuous h) 0
end GlobalTheory.PairingInvariants

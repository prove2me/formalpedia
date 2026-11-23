-- Prove2me | solution 1 for GlobalTheory.PairingInvariants.differentiable_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:36.094203+00:00
-- url     : https://prove2.me/submissions/e6b85634-442d-469b-b40e-106cb119084e

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
theorem _root_.solution {σ : Type} (p : MvPolynomial σ ℂ) (f : ℂ → σ → ℂ)
    (hf : ∀ v, Differentiable ℂ (fun c => f c v)) :
    Differentiable ℂ (fun c => MvPolynomial.eval (f c) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add]; exact hp.fun_add hq
  | mul_X p v hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.fun_mul (hf v)
end GlobalTheory.PairingInvariants

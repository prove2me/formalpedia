-- Prove2me | solution 1 for GlobalTheory.SW.HeatTerm.diffAt_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:26:09.75779+00:00
-- url     : https://prove2.me/submissions/c461dbec-4238-4a22-89c7-15bb0cbe70c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
import Theorems.Thm_GlobalTheory_SW_HeatTerm_diffAt_det

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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section
namespace GlobalTheory.SW.HeatTerm
theorem _root_.solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {N : ℕ}
    (A : X → Matrix (Fin N) (Fin N) ℂ) (x : X)
    (h : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x) (h0 : (A x).det ≠ 0) (i j : Fin N) :
    DifferentiableAt ℂ (fun y => (A y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  refine ((diffAt_det A x h).fun_inv h0).fun_mul (diffAt_det _ x fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact h a b
end GlobalTheory.SW.HeatTerm

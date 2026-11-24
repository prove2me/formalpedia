-- Prove2me | solution 1 for GlobalTheory.SW.HeatTerm.quad_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:26:13.291031+00:00
-- url     : https://prove2.me/submissions/a5596566-1817-4c20-a4e2-c7683a438c9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero

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
theorem _root_.solution {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (u v : Fin N → ℂ) :
    u ⬝ᵥ (S * Matrix.single a b 1 * S) *ᵥ v = (u ᵥ* S) a * (S *ᵥ v) b := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.single_mulVec]
  simp [dotProduct, Function.update_apply]
end GlobalTheory.SW.HeatTerm

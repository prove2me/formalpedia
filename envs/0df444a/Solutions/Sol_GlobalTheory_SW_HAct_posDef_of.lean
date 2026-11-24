-- Prove2me | solution 1 for GlobalTheory.SW.HAct.posDef_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:07.747733+00:00
-- url     : https://prove2.me/submissions/0bf83062-0933-428f-9d30-6505e946705f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {N : ℕ} {A B C D Z : Matrix (Fin N) (Fin N) ℂ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution {Q Y X : Matrix (Fin N) (Fin N) ℂ} (hQ : Q.det ≠ 0) (h : Qᴴ * Y * Q = X)
    (hX : X.PosDef) : Y.PosDef := by
  have hi : Q * Q⁻¹ = 1 := mul_nonsing_inv Q (Ne.isUnit hQ)
  have e : Y = (Q⁻¹)ᴴ * X * Q⁻¹ := by
    rw [← h]
    calc Y = (Q * Q⁻¹)ᴴ * Y * (Q * Q⁻¹) := by simp [hi]
      _ = _ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e]
  refine hX.conjTranspose_mul_mul_same ?_
  exact Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_nonsing_inv_iff).2
    ((Matrix.isUnit_iff_isUnit_det Q).2 (Ne.isUnit hQ)))
end GlobalTheory.SW.HAct

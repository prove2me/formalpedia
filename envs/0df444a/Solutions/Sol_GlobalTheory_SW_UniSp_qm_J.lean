-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.qm_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:29:40.233656+00:00
-- url     : https://prove2.me/submissions/2267af87-957e-43ff-9f31-04cae04a88a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UniSp
noncomputable section
open Classical
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
variable {Ψ : Finset (E →+* ℂ)} {N : ℕ}
namespace GlobalTheory.SW.UniSp
theorem _root_.solution {α : Type} [DecidableEq α] : qm (Matrix.J α ℚ) = Matrix.J α ℂ := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [qm, Matrix.J, Matrix.one_apply, h]
end GlobalTheory.SW.UniSp

-- Prove2me | solution 1 for GlobalTheory.SW.HAct.ccT_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:37.241385+00:00
-- url     : https://prove2.me/submissions/2d77e4be-d55f-4149-bdaa-aa8abd07c4e8

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution {α : Type} [DecidableEq α] : ccT (1 : Matrix α α E) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [ccT, cc]
  · simp [ccT, cc, Matrix.one_apply, h, Ne.symm h]
end GlobalTheory.SW.HAct

-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.local_num
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:29:38.058798+00:00
-- url     : https://prove2.me/submissions/3c172cfd-08cc-4582-acda-404799736c67

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
variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
  {S : Matrix ι K ℂ} {S' : Matrix K ι ℂ}
variable {m o : Type} [Fintype m] [Fintype o] [DecidableEq o]
variable [DecidableEq m]
namespace GlobalTheory.SW.UniSp
theorem _root_.solution (A B Z : Matrix m m ℂ) :
    dl A * fromBlocks 0 Z Zᵀ 0 + dl B * sw m =
      fromBlocks 0 (A * Z + B) (Z * Aᴴ + Bᴴ)ᵀ 0 := by
  simp [dl, sw, fromBlocks_multiply, fromBlocks_add]
end GlobalTheory.SW.UniSp

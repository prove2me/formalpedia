-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.local_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:29:37.354057+00:00
-- url     : https://prove2.me/submissions/0dbb242b-0fa0-44fb-87f0-f4f6628403e7

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
theorem _root_.solution (C D Z : Matrix m m ℂ) :
    sw m * dl C * fromBlocks 0 Z Zᵀ 0 + sw m * dl D * sw m =
      fromBlocks (Z * Cᴴ + Dᴴ)ᵀ 0 0 (C * Z + D) := by
  simp [dl, sw, fromBlocks_multiply, fromBlocks_add]
end GlobalTheory.SW.UniSp

-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.local_sp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:29:39.49714+00:00
-- url     : https://prove2.me/submissions/346bd678-8c62-42e0-95e5-f73a69cf0890

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
theorem _root_.solution {A B C D : Matrix m m ℂ} (h1 : A * Bᴴ = B * Aᴴ) (h2 : A * Dᴴ = B * Cᴴ + 1)
    (h3 : D * Aᴴ = C * Bᴴ + 1) (h4 : C * Dᴴ = D * Cᴴ) :
    dl B * sw m * (dl A)ᵀ = dl A * (dl B * sw m)ᵀ ∧
    dl A * (sw m * dl D * sw m)ᵀ = dl B * sw m * (sw m * dl C)ᵀ + 1 ∧
    sw m * dl D * sw m * (dl A)ᵀ = sw m * dl C * (dl B * sw m)ᵀ + 1 ∧
    sw m * dl D * sw m * (sw m * dl C)ᵀ = sw m * dl C * (sw m * dl D * sw m)ᵀ := by
  have g1 := congrArg transpose h1
  have g2 := congrArg transpose h2
  have g3 := congrArg transpose h3
  have g4 := congrArg transpose h4
  simp only [transpose_mul, transpose_add, transpose_one] at g1 g2 g3 g4
  rw [← fromBlocks_one]
  simp only [dl, sw, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_add, transpose_zero,
    transpose_transpose, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero,
    zero_add, h1, h2, h3, h4, g1, g2, g3, g4, and_self]
end GlobalTheory.SW.UniSp

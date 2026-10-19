-- Prove2me | solution 1 for MazurTransfer.Order13ActualRationalPicardTorsionNineteen.actual_rational_arithmetic_picard_torsion_card
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T16:29:33.950999+00:00
-- url     : https://prove2.me/submissions/6a45e381-365c-4b10-abab-719f3d8f88a4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual arithmetic Picard torsion subgroup over Q has
exactly nineteen elements, using the Pell infinity class and the same-family
upper bound from reduction at three and five. Named downstream consumer:
the rational Jacobian computation; the rank-zero step remains separate.
-/
import Theorems.Thm_MazurTransfer_Order13InfinityPicardClassOrder_infinityClass_order
import Theorems.Thm_MazurTransfer_Order13ActualRationalArithmeticPicardTorsionBound_actual_rational_arithmetic_picard_torsion_bound
noncomputable section
open AlgebraicCurve MazurTransfer
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityPicardClassOrder
local instance rationalTorsionCardOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
namespace MazurTransfer.RationalPicardTorsionCardProofHelpers20261018

theorem infinityClass_in_torsion : Multiplicative.ofAdd infinityClass ∈
    CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ))) := by
  rw [CommGroup.mem_torsion]
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨19, by decide, ?_⟩
  change Multiplicative.ofAdd ((19 : ℕ) • infinityClass) = Multiplicative.ofAdd 0
  apply congrArg Multiplicative.ofAdd
  simpa only [infinityClass_order] using addOrderOf_nsmul_eq_zero infinityClass

end MazurTransfer.RationalPicardTorsionCardProofHelpers20261018
open MazurTransfer.RationalPicardTorsionCardProofHelpers20261018

theorem solution :
    Finite (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) ∧
    Nat.card (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) = 19 := by
  obtain ⟨hf, hupper⟩ :=
    Order13ActualRationalArithmeticPicardTorsionBound.actual_rational_arithmetic_picard_torsion_bound
  have hlower := (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))).orderOf_dvd_natCard
    infinityClass_in_torsion
  rw [orderOf_ofAdd_eq_addOrderOf, infinityClass_order] at hlower
  exact ⟨hf, Nat.dvd_antisymm hupper hlower⟩

#print axioms solution

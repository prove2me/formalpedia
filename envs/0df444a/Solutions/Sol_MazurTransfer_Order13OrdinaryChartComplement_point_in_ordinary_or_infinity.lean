-- Prove2me | solution 1 for MazurTransfer.Order13OrdinaryChartComplement.point_in_ordinary_or_infinity
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:41:33.904785+00:00
-- url     : https://prove2.me/submissions/1a8f2122-a319-4e3d-b6a0-3b598aafa10b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the complement of the ordinary affine chart consists of
the two literal infinity section points. Named downstream consumer: the
complete support calculation for the Pell principal divisor.
-/
import Definitions.Def_MazurTransfer_Order13ActualInfinityPlaceCenterData
import Definitions.Def_MazurTransfer_Order13PellPolynomialCertificate
import Definitions.Def_MazurTransfer_Order13PellInfinityLocalOrders
import Theorems.Thm_MazurTransfer_Order13IntegralHyperellipticMap_reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen
import Theorems.Thm_MazurTransfer_Order13InfinityEvaluationKernel_evaluation_kernel
noncomputable section
open MazurTransfer
namespace MazurTransfer.OrdinaryChartComplementHelpers20261017
open AlgebraicGeometry CategoryTheory Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13InfinityLocalParameter Order13InfinityEvaluationKernel
open Order13ActualInfinityPlaceCenters
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem chartPoint_eq_of_coordinates (p : PrimeSpectrum (ReciprocalRing ℚ))
    (a : ℚ) (ha : a ^ 2 = 1)
    (hz : zCoordinate ℚ ∈ p.asIdeal)
    (hw : wCoordinate ℚ - algebraMap ℚ (ReciprocalRing ℚ) a ∈ p.asIdeal) :
    p = chartPoint a ha := by
  have Hle : infinityIdeal ℚ a ha ≤ p.asIdeal := by
    unfold infinityIdeal
    rw [evaluation_kernel]
    apply Ideal.span_le.mpr
    intro b hb
    rcases hb with rfl | hb
    · exact hz
    · exact Set.mem_singleton_iff.mp hb ▸ hw
  apply PrimeSpectrum.ext
  exact ((infinityIdeal_isMaximal ℚ a ha).eq_of_le p.isPrime.ne_top Hle).symm

theorem reciprocal_point_with_zero_z (p : PrimeSpectrum (ReciprocalRing ℚ))
    (hz : zCoordinate ℚ ∈ p.asIdeal) :
    p = chartPoint 1 (Order13PellInfinityLocalOrders.positiveProof ℚ) ∨
      p = chartPoint (-1) (Order13PellInfinityLocalOrders.negativeProof ℚ) := by
  have Hw : wCoordinate ℚ ^ 2 = Order13PellChartCertificate.infinitySextic (zCoordinate ℚ) := by
    simpa only [reciprocalPolynomial, Order13PellChartCertificate.infinitySextic,
      map_add, map_mul, map_pow, map_ofNat, map_one, aeval_X,
      add_comm, add_left_comm, add_assoc] using wCoordinate_sq ℚ
  have He : (wCoordinate ℚ - 1) * (wCoordinate ℚ + 1) = zCoordinate ℚ *
      (2 + zCoordinate ℚ + 2 * zCoordinate ℚ ^ 2 + 6 * zCoordinate ℚ ^ 3 +
        4 * zCoordinate ℚ ^ 4 + zCoordinate ℚ ^ 5) := by
    calc
      _ = wCoordinate ℚ ^ 2 - 1 := by ring
      _ = _ := by rw [Hw]; dsimp [Order13PellChartCertificate.infinitySextic]; ring
  have Hp : (wCoordinate ℚ - 1) * (wCoordinate ℚ + 1) ∈ p.asIdeal := by
    rw [He]
    exact p.asIdeal.mul_mem_right _ hz
  rcases p.isPrime.mem_or_mem Hp with h | h
  · left
    apply chartPoint_eq_of_coordinates p 1 (Order13PellInfinityLocalOrders.positiveProof ℚ) hz
    simpa only [map_one] using h
  · right
    apply chartPoint_eq_of_coordinates p (-1) (Order13PellInfinityLocalOrders.negativeProof ℚ) hz
    simpa only [map_neg, map_one, sub_neg_eq_add] using h

end MazurTransfer.OrdinaryChartComplementHelpers20261017
open MazurTransfer.OrdinaryChartComplementHelpers20261017
open AlgebraicGeometry CategoryTheory Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13InfinityLocalParameter MazurTransfer.Order13InfinityEvaluationKernel
open MazurTransfer.Order13ActualInfinityPlaceCenters
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
theorem solution (x : curveScheme ℚ) :
    x ∈ (ordinaryChartMap ℚ).opensRange ∨
      x = center 1 (Order13PellInfinityLocalOrders.positiveProof ℚ) ∨
      x = center (-1) (Order13PellInfinityLocalOrders.negativeProof ℚ) := by
  obtain ⟨i, p, rfl⟩ := (glueData ℚ).ι_jointly_surjective x
  rcases i with (_ | _)
  · exact Or.inl ⟨p, rfl⟩
  · by_cases hz : zCoordinate ℚ ∈ p.asIdeal
    · rcases reciprocal_point_with_zero_z p hz with hp | hp
      · exact Or.inr (Or.inl (congrArg (reciprocalChartMap ℚ) hp))
      · exact Or.inr (Or.inr (congrArg (reciprocalChartMap ℚ) hp))
    · left
      have H := Order13IntegralHyperellipticMap.reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen ℚ
      have Hp : p ∈ (reciprocalChartMap ℚ) ⁻¹ᵁ (ordinaryChartMap ℚ).opensRange := by
        rw [H]
        exact hz
      exact Hp

#print axioms solution

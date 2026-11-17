-- Prove2me | solution 1 for N25.Endgame.frobenius_fixedPlaces_card_eq_finiteField_of_algebra25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:55.857133+00:00
-- url     : https://prove2.me/submissions/94d094ca-d829-41b9-8e51-3455849a79c8

import Theorems.Thm_N25_Endgame_FBaseCoeffMap25_frobenius_iterate
import Theorems.Thm_N25_Endgame_qExpFrobeniusModL_pow_isIntegral25
import Theorems.Thm_N25_Endgame_restrictAlong_qExpFrobeniusModL_pow25
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_N25_Endgame_xH25C_isCurveOver
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_N25_Endgame_xH25C_finitelyGenerated
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_N25_Endgame_FBaseCoeffMap25_generates
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors

/-! Fixed-place counts of prime Frobenius iterates over finite coefficient fields. -/
noncomputable section

namespace N25.Endgame

/-- The degree-one specialization of the fixed-place divisor count. -/
private theorem fixedPlace_card_eq_degreeOne
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hi : φ.toRingHom.IsIntegral)
    (hpow : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hi)) =
      Nat.card {P : AlgebraicCurve.Place k F₀ // P.deg = 1} := by
  have h := AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
    k K F₀ F hfg hgen φ hi hpow 1 Nat.zero_lt_one
  have hc := h.2
  simp only [Function.iterate_one, Nat.divisors_one, Finset.sum_singleton, one_mul] at hc
  exact hc

/-- Restriction along cardinality Frobenius counts degree-one places of the finite form. -/
private theorem frobenius_restrictAlong_card_eq_finiteField25
    (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra k K]
    (n : ℕ) (hk : Nat.card k = p ^ n) :
    Nat.card (Function.fixedPoints
      (AlgebraicCurve.Place.restrictAlong (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n)
        (qExpFrobeniusModL_pow_isIntegral25 p K n))) =
      Nat.card {P : AlgebraicCurve.Place k (ModularCurve.qExpFunctionFieldC k Γ25) //
        P.deg = 1} := by
  let coeffAlgebra : Algebra (FBase k) (FBase K) := (FBaseCoeffMap25 k K).toAlgebra
  let : Algebra (FBase k) (FBase K) := coeffAlgebra
  let : AlgebraicCurve.IsCurveOver k (FBase k) := xH25C_isCurveOver k
  let : AlgebraicCurve.IsCurveOver K (FBase K) := xH25C_isCurveOver K
  have hmap : algebraMap (FBase k) (FBase K) = FBaseCoeffMap25 k K := rfl
  have hgen : IntermediateField.adjoin K
      (Set.range (algebraMap (FBase k) (FBase K))) = ⊤ := by
    rw [hmap]
    exact FBaseCoeffMap25_generates k K
  have hpow : ∀ x : FBase k,
      (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n)
          (algebraMap (FBase k) (FBase K) x) =
        algebraMap (FBase k) (FBase K) (x ^ Nat.card k) := by
    intro x
    rw [hmap]
    exact FBaseCoeffMap25_frobenius_iterate p k K n hk x
  exact fixedPlace_card_eq_degreeOne
    k K (FBase k) (FBase K)
    (xH25C_finitelyGenerated k) hgen
    (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n)
    (qExpFrobeniusModL_pow_isIntegral25 p K n)
    hpow

/-- A chosen finite-field embedding identifies Frobenius-fixed places with degree-one places. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra k K]
    (n : ℕ) (hn : 0 < n) (hk : Nat.card k = p ^ n) :
    Nat.card (Function.fixedPoints ((ModularCurve.qExpFrobeniusPlaceModL K Γ25 p)^[n])) =
      Nat.card {P : AlgebraicCurve.Place k (FBase k) // P.deg = 1} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := frobenius_restrictAlong_card_eq_finiteField25 p k K (m + 1) hk
  rw [restrictAlong_qExpFrobeniusModL_pow25] at h
  exact h

end N25.Endgame

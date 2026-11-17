-- Prove2me | solution 1 for N25.Endgame.ternaryLPolynomial25_zeta_of_place_sums
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:07.6041+00:00
-- url     : https://prove2.me/submissions/83ed0e63-726e-432e-8543-b167c57e1df5

import Mathlib
import Theorems.Thm_N25_Endgame_ternaryLPolynomial25_of_divisor_recurrence
import Theorems.Thm_N25_Endgame_ternary_zeta_initial_coefficients25
import Definitions.Def_N25_GenusFourNumerator
import Theorems.Thm_N25_Endgame_genusFF_goodPrime25
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_N25_Endgame_xH25C_isCurveOver
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_N25_Endgame_xH25C_constantsAreBase
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_N25_Endgame_xH25C_essFiniteType
import Theorems.Thm_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum
import Theorems.Thm_AlgebraicCurve_exists_LPolynomial_of_finite

/-! The full ternary zeta identity from the first four weighted place counts. -/
namespace N25.Endgame

/-- Recurrence and reciprocity turn the four weighted place counts into the full series identity. -/
theorem _root_.solution
    (hN : ∀ n : Fin 4,
      (∑ d ∈ Nat.divisors (n.val + 1), d *
        Nat.card {v : AlgebraicCurve.Place (ZMod 3) (FBase (ZMod 3)) | v.deg = d}) =
          (![5, 5, 20, 89] : Fin 4 → ℕ) n) :
    (1 - PowerSeries.X) * (1 - PowerSeries.C (3 : ℤ) * PowerSeries.X) *
      PowerSeries.mk (fun n : ℕ =>
        (Nat.card {D : AlgebraicCurve.Divisor (ZMod 3) (FBase (ZMod 3)) //
          0 ≤ D ∧ AlgebraicCurve.Divisor.degree D = (n : ℤ)} : ℤ)) =
        (ternaryLPolynomial25 : PowerSeries ℤ) := by
  let : AlgebraicCurve.IsCurveOver (ZMod 3) (FBase (ZMod 3)) :=
    xH25C_isCurveOver (ZMod 3)
  let : Algebra.EssFiniteType (ZMod 3) (FBase (ZMod 3)) :=
    xH25C_essFiniteType (ZMod 3)
  obtain ⟨L, hdeg, hzero, hrec, hzeta⟩ :=
    AlgebraicCurve.exists_LPolynomial_of_finite (ZMod 3) (FBase (ZMod 3))
      (xH25C_constantsAreBase (ZMod 3))
  have hg := genusFF_goodPrime25 3 (by norm_num)
  rw [hg] at hdeg hrec
  norm_num only [Nat.card_eq_fintype_card, ZMod.card, Nat.cast_ofNat,
    Nat.reduceMul] at hdeg hrec hzeta
  let A (n : ℕ) : ℕ := Nat.card
    {D : AlgebraicCurve.Divisor (ZMod 3) (FBase (ZMod 3)) //
      0 ≤ D ∧ AlgebraicCurve.Divisor.degree D = (n : ℤ)}
  let N (n : ℕ) : ℕ := ∑ d ∈ Nat.divisors n, d *
    Nat.card {v : AlgebraicCurve.Place (ZMod 3) (FBase (ZMod 3)) | v.deg = d}
  have h₁ := hN 0
  have h₂ := hN 1
  have h₃ := hN 2
  have h₄ := hN 3
  norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk,
    Nat.reduceAdd, Matrix.cons_val_zero, Matrix.cons_val_succ] at h₁ h₂ h₃ h₄
  change N 1 = 5 at h₁
  change N 2 = 5 at h₂
  change N 3 = 20 at h₃
  change N 4 = 89 at h₄
  have hA (n : ℕ) := AlgebraicCurve.card_effectiveDivisors_mul_eq_sum
    (ZMod 3) (FBase (ZMod 3)) n
  change ∀ n, n * A n = ∑ r ∈ Finset.Icc 1 n, N r * A (n-r) at hA
  have hA₁ := hA 1
  have hA₂ := hA 2
  have hA₃ := hA 3
  have hA₄ := hA 4
  norm_num [Finset.sum_Icc_succ_top, h₁, h₂, h₃, h₄] at hA₁ hA₂ hA₃ hA₄
  obtain ⟨hA₀, hc₁, hc₂, hc₃, hc₄⟩ := ternary_zeta_initial_coefficients25 L (fun n => (A n : ℤ)) hzero hzeta
  have hL : L = ternaryLPolynomial25 :=
    ternaryLPolynomial25_of_divisor_recurrence L (fun n => (A n : ℤ)) 5 5 20 89
      rfl rfl rfl rfl hdeg hzero hrec hA₀
      (by exact_mod_cast hA₁) (by exact_mod_cast hA₂)
      (by exact_mod_cast hA₃) (by exact_mod_cast hA₄) hc₁ hc₂ hc₃ hc₄
  rwa [hL] at hzeta

end N25.Endgame

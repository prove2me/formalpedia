-- Prove2me | solution 1 for Kyprianou.Ch01.branchingRenewalSolutionUnique
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T14:12:23.445994+00:00
-- url     : https://prove2.me/submissions/62888593-eea6-4b3f-98d3-dab594231264
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingRenewalHomogeneousVanish

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem solution
    (rate : ℝ) (hrate : 0 < rate)
    (offspring : PMF ℕ)
    (K L : PopulationLaws)
    (hKZero : ∀ t : ℝ≥0, ∀ k : ℕ, K 0 t k = (PMF.pure 0) k)
    (hLZero : ∀ t : ℝ≥0, ∀ k : ℕ, L 0 t k = (PMF.pure 0) k)
    (hKRenew : ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
      IntervalIntegrable
        (fun s : ℝ =>
          (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
        volume 0 (t : ℝ) ∧
      (K y t k).toReal =
        (if k = y then Real.exp (-(rate * (y : ℝ) * (t : ℝ))) else 0) +
          ∫ s in (0 : ℝ)..(t : ℝ),
            (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
              ∑' j : ℕ, (offspring j).toReal *
                (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
    (hLRenew : ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
      IntervalIntegrable
        (fun s : ℝ =>
          (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (L ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
        volume 0 (t : ℝ) ∧
      (L y t k).toReal =
        (if k = y then Real.exp (-(rate * (y : ℝ) * (t : ℝ))) else 0) +
          ∫ s in (0 : ℝ)..(t : ℝ),
            (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
              ∑' j : ℕ, (offspring j).toReal *
                (L ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal) :
    ∀ y : ℕ, ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ, K y t k = L y t k := by
  let h : ℕ → ℝ≥0 → ℕ → ℝ :=
    fun y s j => (K y s j).toReal - (L y s j).toReal
  have hToRealLe : ∀ (F : PopulationLaws) (y : ℕ) (s : ℝ≥0) (j : ℕ),
      (F y s j).toReal ≤ 1 := by
    intro F y s j
    have hle : F y s j ≤ 1 := (F y s).coe_le_one j
    have hmono := ENNReal.toReal_mono ENNReal.one_ne_top hle
    simpa [ENNReal.toReal_one] using hmono
  have hBound : ∀ y : ℕ, ∀ s : ℝ≥0, ∀ j : ℕ, |h y s j| ≤ 1 := by
    intro y s j
    have hK0 : 0 ≤ (K y s j).toReal := ENNReal.toReal_nonneg
    have hL0 : 0 ≤ (L y s j).toReal := ENNReal.toReal_nonneg
    have hK1 : (K y s j).toReal ≤ 1 := hToRealLe K y s j
    have hL1 : (L y s j).toReal ≤ 1 := hToRealLe L y s j
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith
  have hAtZero : ∀ s : ℝ≥0, ∀ j : ℕ, h 0 s j = 0 := by
    intro s j
    simp [h, hKZero, hLZero]
  have hsum (F : PopulationLaws) (y : ℕ) (t : ℝ≥0) (k : ℕ) (s : ℝ) :
      Summable (fun j : ℕ =>
        (offspring j).toReal *
          (F ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal) := by
    have hsumP : Summable (fun j : ℕ => (offspring j).toReal) :=
      ENNReal.summable_toReal offspring.tsum_coe_ne_top
    refine hsumP.of_norm_bounded fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg
      (hToRealLe F ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k)
  have hHom : ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
      IntervalIntegrable
        (fun s : ℝ =>
          (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              h ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k)
        volume 0 (t : ℝ) ∧
      h y t k =
        ∫ s in (0 : ℝ)..(t : ℝ),
          (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              h ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k := by
    intro y hy t ht k
    obtain ⟨hKint, hKeq⟩ := hKRenew y hy t ht k
    obtain ⟨hLint, hLeq⟩ := hLRenew y hy t ht k
    let fK : ℝ → ℝ := fun s =>
      (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
        ∑' j : ℕ, (offspring j).toReal *
          (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal
    let fL : ℝ → ℝ := fun s =>
      (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
        ∑' j : ℕ, (offspring j).toReal *
          (L ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal
    let fH : ℝ → ℝ := fun s =>
      (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
        ∑' j : ℕ, (offspring j).toReal *
          h ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k
    have hKL : ∀ s : ℝ, fK s - fL s = fH s := by
      intro s
      have hsub :=
        (hsum K y t k s).tsum_sub (hsum L y t k s)
      rw [show fK s - fL s =
          (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
              (∑' j : ℕ, (offspring j).toReal *
                (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal) -
            (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
              (∑' j : ℕ, (offspring j).toReal *
                (L ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal) by rfl]
      rw [← mul_sub, ← hsub]
      refine congrArg
        (fun z => (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) * z) ?_
      refine tsum_congr fun j => ?_
      rw [mul_sub]
    have heqfun : (fun s => fK s - fL s) = fH := funext hKL
    have hint : IntervalIntegrable fH volume 0 (t : ℝ) := by
      rw [← heqfun]
      exact hKint.sub hLint
    refine ⟨hint, ?_⟩
    have hdiff : h y t k =
        (∫ s in (0 : ℝ)..(t : ℝ), fK s) - ∫ s in (0 : ℝ)..(t : ℝ), fL s := by
      rw [show h y t k = (K y t k).toReal - (L y t k).toReal by rfl, hKeq, hLeq]
      ring
    rw [hdiff, ← intervalIntegral.integral_sub hKint hLint, heqfun]
  have hVanish :=
    branchingRenewalHomogeneousVanish rate hrate offspring h hBound hAtZero hHom
  intro y t ht k
  have hzero : (K y t k).toReal - (L y t k).toReal = 0 := hVanish y t ht k
  have hto : (K y t k).toReal = (L y t k).toReal := sub_eq_zero.mp hzero
  exact (ENNReal.toReal_eq_toReal_iff'
    ((K y t).apply_ne_top k) ((L y t).apply_ne_top k)).mp hto

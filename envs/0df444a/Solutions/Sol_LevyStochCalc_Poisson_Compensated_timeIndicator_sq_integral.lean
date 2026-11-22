-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.timeIndicator_sq_integral
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:53:14.009795+00:00
-- url     : https://prove2.me/submissions/f8eb5aac-3083-495e-9a6c-ecd632a85dea

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-sum process and its `L²` isometry

The process `∑ᵢ ∑ₖ ξᵢₖ Ñ((tᵢ, tᵢ₊₁] × Bₖ)` attached to adapted bounded coefficients, its second
moment as the `L²(P ⊗ ds ⊗ ν)` energy of the associated integrand, and the isometry for the
difference of two such processes. The energy is computed from the product form of the reference
intensity on time-mark boxes; completeness of `L²(P)` then turns a Cauchy sequence of such
processes into a limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]



theorem _root_.solution
    {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T) (f : Fin N₀ → ℝ) :
    ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * f i) ^ 2 ∂volume
      = ∑ i : Fin N₀, (p i.succ - p i.castSucc) * (f i) ^ 2 := by
  classical
  let J (i : Fin N₀) := Set.Ioc (p i.castSucc) (p i.succ)
  have hdis : Pairwise (fun i j : Fin N₀ => Disjoint (J i) (J j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro s hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · have hij' : i.succ ≤ j.castSucc := by exact Nat.succ_le_of_lt h
      exact (not_lt_of_ge (hi.2.trans (hpmono.monotone hij'))) hj.1
    · have hji' : j.succ ≤ i.castSucc := by exact Nat.succ_le_of_lt h
      exact (not_lt_of_ge (hj.2.trans (hpmono.monotone hji'))) hi.1
  have he (s : ℝ) : (∑ i : Fin N₀, (J i).indicator (fun _ => (1 : ℝ)) s * f i)^2 =
      ∑ i : Fin N₀, (J i).indicator (fun _ => (f i)^2) s := by
    by_cases hex : ∃ i : Fin N₀, s ∈ J i
    · obtain ⟨i, hi⟩ := hex
      have hn (j : Fin N₀) (hji : j ≠ i) : s ∉ J j :=
        fun hj => (Set.disjoint_left.mp (hdis hji)) hj hi
      rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
      · simp [Set.indicator_of_mem hi]
      · intro j _ hj
        exact Set.indicator_of_notMem (hn j hj) _
      · simp
      · intro j _ hj
        simp [Set.indicator_of_notMem (hn j hj)]
      · simp
    · have hn (i : Fin N₀) : s ∉ J i := fun hi => hex ⟨i, hi⟩
      simp [Set.indicator_of_notMem, hn]
  change (∫ s in Set.Icc (0 : ℝ) T, (∑ i, (J i).indicator (fun _ => (1 : ℝ)) s * f i)^2) = _
  simp_rw [he]
  have hJ (i : Fin N₀) : MeasurableSet (J i) := measurableSet_Ioc
  have hsub (i : Fin N₀) : J i ⊆ Set.Icc (0 : ℝ) T := by
    intro r hr
    have hlo := hpmono.monotone (Fin.zero_le i.castSucc)
    have hhi := hpmono.monotone (Fin.le_last i.succ)
    rw [hp0] at hlo
    exact ⟨hlo.trans hr.1.le, hr.2.trans (hhi.trans hpleT)⟩
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (hJ i), Measure.restrict_restrict (hJ i),
      Set.inter_eq_left.mpr (hsub i), integral_const, smul_eq_mul]
    have h := hpmono (Fin.castSucc_lt_succ (i := i))
    simp [J, Real.volume_real_Ioc_of_le h.le]
  · intro i _
    exact (integrable_const _).indicator (hJ i)

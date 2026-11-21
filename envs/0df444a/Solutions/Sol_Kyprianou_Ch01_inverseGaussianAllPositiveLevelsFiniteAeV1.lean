-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianAllPositiveLevelsFiniteAeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:15:33.109236+00:00
-- url     : https://prove2.me/submissions/52713b47-7b66-4d6c-9099-dd26c35871b5

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstUpperPassageAlmostSureFinitePublic
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageBarrierMonotone
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s →
      Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω ≠ ⊤ := by
  have hEach (n : ℕ) :
      ∀ᵐ ω ∂P,
        firstUpperPassage X (((n + 1 : ℕ) : ℝ)) ω ≠ ⊤ :=
    inverseGaussianFirstUpperPassageAlmostSureFinitePublic P X b
      (((n + 1 : ℕ) : ℝ)) hb (by positivity) hB hMeas
  have hAll :
      ∀ᵐ ω ∂P, ∀ n : ℕ,
        firstUpperPassage X (((n + 1 : ℕ) : ℝ)) ω ≠ ⊤ :=
    (ae_all_iff).2 hEach
  filter_upwards [hAll] with ω hω
  intro s hs
  obtain ⟨n, hsn⟩ := exists_nat_gt (s : ℝ)
  have hsn' : (s : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ n
    exact (le_of_lt hsn).trans hn
  have hmono :=
    firstUpperPassageBarrierMonotone X (s : ℝ)
      (((n + 1 : ℕ) : ℝ)) hsn' ω
  intro htop
  rw [htop] at hmono
  have htop' : firstUpperPassage X (((n + 1 : ℕ) : ℝ)) ω = ⊤ :=
    top_unique hmono
  exact hω n htop'

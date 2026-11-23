-- Prove2me | solution 1 for Kyprianou.Ch02.markIntegralIncrementFromIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:20:11.787608+00:00
-- url     : https://prove2.me/submissions/f331d07b-345d-408e-b06e-062fb6e26e8f

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ × ℝ)) (B : Set ℝ) (hB : MeasurableSet B)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hint : IntegrableOn (fun z : ℝ × ℝ => z.2)
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) μ) :
    (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ) -
    (∫ z in (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B), z.2 ∂μ) =
      ∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ := by
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := (s.property)
  have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  let A : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B
  let C : Set (ℝ × ℝ) := Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B
  have hUnion : A ∪ C = Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B := by
    dsimp [A, C]
    rw [← Set.Ioc_union_Ioc_eq_Ioc hs0 hst', Set.union_prod]
  have hDisj : Disjoint A C := by
    exact Set.Disjoint.set_prod_left
      (Set.Ioc_disjoint_Ioc_of_le (le_refl (s : ℝ))) _ _
  have hCmeas : MeasurableSet C := measurableSet_Ioc.prod hB
  have hAint : IntegrableOn (fun z : ℝ × ℝ => z.2) A μ :=
    hint.mono_set (by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2.trans hst'⟩, hz.2⟩)
  have hCint : IntegrableOn (fun z : ℝ × ℝ => z.2) C μ :=
    hint.mono_set (by
      intro z hz
      exact ⟨⟨lt_of_le_of_lt hs0 hz.1.1, hz.1.2⟩, hz.2⟩)
  have hAdd := setIntegral_union hDisj hCmeas hAint hCint
  rw [hUnion] at hAdd
  dsimp [A, C] at hAdd
  linarith

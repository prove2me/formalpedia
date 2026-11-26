-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_positive_exponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:31:14.702516+00:00
-- url     : https://prove2.me/submissions/399556ff-2f28-4b66-bc8d-c10f25787831

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_cor412_secant_deriv
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hm : 0 < derivWithin L.ψ (Ici 0) 0) :
    let m := derivWithin L.ψ (Ici 0) 0
    (∀ b : ℝ, 0 < b → m ≤ L.ψ b / b) ∧
    (∀ b : ℝ, 0 < b → 0 < L.ψ b) := by
  intro m
  letI : IsProbabilityMeasure P := L.isProbability
  obtain ⟨h0, _, hc, _, _⟩ :=
    Kyprianou.Ch03.exercise35LaplaceExponentRegularity P F L
  have hs := Kyprianou.Ch04.cor412_secant_deriv L.ψ h0 hc hm
  let S := (fun b : ℝ => L.ψ b / b) '' Ioi 0
  change max 0 (sInf S) = m at hs
  have hb : BddBelow S := by
    by_contra h
    rw [Real.sInf_of_not_bddBelow h, max_self] at hs
    linarith
  have hi : sInf S = m := by
    by_cases h : sInf S ≤ 0
    · rw [max_eq_left h] at hs
      linarith
    · rwa [max_eq_right (le_of_not_ge h)] at hs
  have hlo (b : ℝ) (hpos : 0 < b) : m ≤ L.ψ b / b := by
    rw [← hi]
    exact csInf_le hb ⟨b, hpos, rfl⟩
  refine ⟨hlo, fun b hpos => ?_⟩
  exact (mul_pos hm hpos).trans_le ((le_div_iff₀ hpos).mp (hlo b hpos))

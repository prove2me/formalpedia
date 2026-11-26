-- Prove2me | solution 1 for ManyServerQED.Scheduling.finite_coordinate_modulus_controls_vector_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:00:32.26616+00:00
-- url     : https://prove2.me/submissions/66628e14-67ef-4aab-8eef-4b437bf12b31

import Mathlib

open Filter Topology Set MeasureTheory
open scoped ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ) (T : ℝ)
    (h : ∀ i : Fin k, ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
        ε ≤ |X n ω s i-X n ω t i|} ≤ ENNReal.ofReal η) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η := by
  classical
  intro ε η hε hη
  let v := η/((k:ℝ)+1)
  have hv : 0 < v := by dsimp [v]; positivity
  choose d hd hdN using fun i => h i ε v hε hv
  have minPos (S : Finset (Fin k)) : ∃ δ > (0:ℝ), ∀ i ∈ S, δ ≤ d i := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert i S hi hS =>
        obtain ⟨r,hr,hrS⟩ := hS
        refine ⟨min (d i) r,lt_min (hd i) hr,fun j hj => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hrS j hj)
  obtain ⟨δ,hδ,hL⟩ := minPos Finset.univ
  refine ⟨δ,hδ,?_⟩
  have hAll : ∀ᶠ n in atTop, ∀ i, P {ω | ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T,
      |s-t| ≤ d i ∧ ε ≤ |X n ω s i-X n ω t i|} ≤ ENNReal.ofReal v :=
    Filter.eventually_all.2 hdN
  filter_upwards [hAll] with n hn
  let D (i : Fin k) := {ω | ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T,
    |s-t| ≤ d i ∧ ε ≤ |X n ω s i-X n ω t i|}
  calc
    _ ≤ P (⋃ i, D i) := by
      apply measure_mono
      rintro ω ⟨s,hs,t,ht,hd,hh⟩
      have hi : ∃ i, ε ≤ |X n ω s i-X n ω t i| := by
        by_contra! hlt
        apply not_lt_of_ge hh
        apply (pi_norm_lt_iff hε).2
        intro i
        simpa only [Pi.sub_apply,Real.norm_eq_abs] using hlt i
      obtain ⟨i,hi⟩ := hi
      exact Set.mem_iUnion.2 ⟨i,s,hs,t,ht,hd.trans (hL i (Finset.mem_univ _)),hi⟩
    _ ≤ ∑ i, P (D i) := by simpa only [tsum_fintype] using measure_iUnion_le D
    _ ≤ ∑ _i : Fin k, ENNReal.ofReal v := Finset.sum_le_sum (fun i _ => hn i)
    _ ≤ ENNReal.ofReal η := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      dsimp [v]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < (k:ℝ)+1)).2
      nlinarith

-- Prove2me | solution 1 for Kyprianou.Ch02.prmBadTimeSliceMeasureGridBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:09:21.530812+00:00
-- url     : https://prove2.me/submissions/7dc745a7-433d-4178-bfd5-53462955b856

import Theorems.Thm_Kyprianou_Ch02_equalGridPositiveTimeCoverV1
import Theorems.Thm_Kyprianou_Ch02_prmEqualGridCellTwoPointBoundV1
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (A : Set ℝ) (hA : MeasurableSet A) (hfin : ν A < ⊤) (T : ℝ≥0)
    (n : ℕ) :
    P.real {ω | ¬ ∀ t : ℝ≥0, 0 < t → t ≤ T →
      N.N ω ({(t : ℝ)} ×ˢ A) ≤ 1} ≤
      ((T : ℝ) * (ν A).toReal)^2 / ((n+1 : ℕ) : ℝ) := by
  classical
  let d : ℝ := (T : ℝ) / ((n+1 : ℕ) : ℝ)
  let C (k : ℕ) : Set Ω := {ω | 1 < N.N ω
    (Set.Ioc ((k : ℝ) * d) (((k+1 : ℕ) : ℝ) * d) ×ˢ A)}
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hsub : {ω | ¬ ∀ t : ℝ≥0, 0 < t → t ≤ T →
      N.N ω ({(t : ℝ)} ×ˢ A) ≤ 1} ⊆ ⋃ k ∈ Finset.range (n+1), C k := by
    intro ω hω
    push_neg at hω
    obtain ⟨t, ht, htT, hbad⟩ := hω
    obtain ⟨k, hk, hcover⟩ := Kyprianou.Ch02.equalGridPositiveTimeCoverV1 T t ht htT n
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hk, ?_⟩⟩
    exact hbad.trans_le (measure_mono (fun z hz => ⟨hz.1.symm ▸ hcover, hz.2⟩))
  have hcell (k : ℕ) : (P (C k)).toReal ≤ (d * (ν A).toReal)^2 := by
    have h := Kyprianou.Ch02.prmEqualGridCellTwoPointBoundV1 P ν N A hA hfin
      ((k : ℝ) * d) d (by positivity) hd
    have hEq : ((k+1 : ℕ) : ℝ) * d = (k : ℝ) * d + d := by push_cast; ring
    change (P {ω | 1 < N.N ω (Set.Ioc ((k : ℝ) * d) (((k+1 : ℕ) : ℝ) * d) ×ˢ A)}).toReal ≤ _
    rw [hEq]
    exact h
  change (P _).toReal ≤ _
  calc
    (P _).toReal ≤ (P (⋃ k ∈ Finset.range (n+1), C k)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    _ ≤ (∑ k ∈ Finset.range (n+1), P (C k)).toReal :=
      ENNReal.toReal_mono (ENNReal.sum_ne_top.2 (fun k hk => measure_ne_top _ _))
        (measure_biUnion_finset_le _ _)
    _ = ∑ k ∈ Finset.range (n+1), (P (C k)).toReal :=
      ENNReal.toReal_sum (fun k hk => measure_ne_top _ _)
    _ ≤ ∑ _k ∈ Finset.range (n+1), (d * (ν A).toReal)^2 :=
      Finset.sum_le_sum (fun k hk => hcell k)
    _ = ((T : ℝ) * (ν A).toReal)^2 / ((n+1 : ℕ) : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [d]
      field_simp
      <;> ring

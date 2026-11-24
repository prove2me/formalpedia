-- Prove2me | solution 1 for Kyprianou.Ch02.smallJumpCompactMarkSupportCapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:52:55.582839+00:00
-- url     : https://prove2.me/submissions/4afc6316-1c7d-4f06-9ce3-4b72e2adf6db

import Theorems.Thm_Kyprianou_Ch02_prmFiniteWindowDiracLawV1
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

open scoped Topology

open Kyprianou Kyprianou.Ch02
open scoped BigOperators

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (hν : ProbabilityTheory.IsLevyMeasure ν) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | c < |x| ∧ |x| < 1}) = 0  := by
  classical
  let B : Set ℝ := {x | (1/2 : ℝ) ≤ |x| ∧ |x| < 1}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hfin : ν B < ⊤ := by
    have hle : ν B ≤ ν {x : ℝ | (1/2 : ℝ) ≤ |x|} :=
      measure_mono (fun _ hx => hx.1)
    exact lt_of_le_of_lt hle
      (ProbabilityTheory.IsLevyMeasure.measure_setOf_abs_ge_lt_top hν (by norm_num))
  obtain ⟨K, hK⟩ := exists_nat_gt T
  have hKT : (T : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK.le
  filter_upwards [Kyprianou.Ch02.prmFiniteWindowDiracLawV1
    P ν N B hB hfin] with ω hω
  obtain ⟨s, hs⟩ := hω K
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (K : ℝ) ×ˢ B
  have hdiff : MeasurableSet (R \ (s : Set (ℝ × ℝ))) :=
    (measurableSet_Ioc.prod hB).diff s.finite_toSet.measurableSet
  have hsupport : N.N ω (R \ (s : Set (ℝ × ℝ))) = 0 := by
    have hEq : (N.N ω).restrict R (R \ (s : Set (ℝ × ℝ))) =
        N.N ω (R \ (s : Set (ℝ × ℝ))) := by
      rw [Measure.restrict_apply hdiff, Set.inter_eq_left.mpr Set.diff_subset]
    rw [← hEq]
    change ((N.N ω).restrict R) (R \ (s : Set (ℝ × ℝ))) = 0
    rw [show (N.N ω).restrict R =
      ∑ p ∈ s, ((N.N ω).restrict R) {p} • Measure.dirac p from hs]
    rw [Measure.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Measure.smul_apply, Measure.dirac_apply' p hdiff]
    simp [Set.indicator_of_notMem (show p ∉ R \ (s : Set (ℝ × ℝ)) from fun h => h.2 hp)]
  let Q : Finset ℝ := insert (1/2) ((s.filter (fun p => |p.2| < 1)).image (fun p => |p.2|))
  have hQ : Q.Nonempty := ⟨1/2, by simp [Q]⟩
  let c := Q.max' hQ
  have hcm : c ∈ Q := Finset.max'_mem Q hQ
  have hc0 : (1/2 : ℝ) ≤ c := Finset.le_max' Q _ (by simp [Q])
  have hc1 : c < 1 := by
    rcases Finset.mem_insert.mp hcm with h | h
    · rw [h]
      norm_num
    · obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp h
      rw [← hp']
      exact (Finset.mem_filter.mp hp).2
  refine ⟨c, by linarith, hc1, measure_mono_null ?_ hsupport⟩
  intro p hp
  refine ⟨⟨⟨hp.1.1, hp.1.2.trans hKT⟩, ⟨hc0.trans hp.2.1.le, hp.2.2⟩⟩, ?_⟩
  intro hpS
  have hpQ : |p.2| ∈ Q :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨p, Finset.mem_filter.mpr ⟨hpS, hp.2.2⟩, rfl⟩)
  exact (not_lt_of_ge (Finset.le_max' Q _ hpQ)) hp.2.1

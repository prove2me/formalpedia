-- Prove2me | solution 1 for Kyprianou.Ch02.prmNearOneWindowStrictMarkCapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:53:38.412314+00:00
-- url     : https://prove2.me/submissions/96c9b38c-51da-4679-b336-437f770af46f

import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionAllMeasurableCountNatV1
import Theorems.Thm_Kyprianou_Ch02_integerValuedFiniteSupportV1
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

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (hν : ProbabilityTheory.IsLevyMeasure ν) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | c < |x| ∧ |x| < 1}) = 0 := by
  classical
  let A : Set ℝ := {x : ℝ | (1 / 2 : ℝ) ≤ |x| ∧ |x| < 1}
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hfin : ν A < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun _ hx => hx.1))
      (ProbabilityTheory.IsLevyMeasure.measure_setOf_abs_ge_lt_top hν (by norm_num : (0 : ℝ) < 1/2))
  let R := Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ A
  have hR : MeasurableSet R := measurableSet_Ioc.prod hA
  have hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ := by
    have hvalue : LevyStochCalc.Poisson.referenceIntensity ν R =
        ENNReal.ofReal (T : ℝ) * ν A := by
      rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod,
        Measure.restrict_apply measurableSet_Ioc]
      congr 1
      have heq : Set.Ioc (0 : ℝ) (T : ℝ) ∩ Set.Ici (0 : ℝ) =
          Set.Ioc (0 : ℝ) (T : ℝ) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, and_iff_left_iff_imp]
        exact fun h => h.1.le
      rw [heq, Real.volume_Ioc, sub_zero]
    rw [hvalue]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  filter_upwards [Kyprianou.Ch02.prmFiniteRegionAllMeasurableCountNatV1
    P ν N R hR hRfin] with ω hω
  have hInt : LevyStochCalc.Probability.IsIntegerValued ((N.N ω).restrict R) := by
    intro E hE
    rw [Measure.restrict_apply hE]
    exact hω E hE
  obtain ⟨s, hs⟩ := Kyprianou.Ch02.integerValuedFiniteSupportV1 ((N.N ω).restrict R) hInt
  let V : Finset ℝ := insert (1 / 2 : ℝ) ((s.filter fun z => |z.2| < 1).image fun z => |z.2|)
  have hV : V.Nonempty := Finset.insert_nonempty _ _
  let c := V.max' hV
  have hc : (1 / 2 : ℝ) ≤ c := Finset.le_max' V _ (Finset.mem_insert_self _ _)
  have hc1 : c < 1 := by
    have hm := Finset.max'_mem V hV
    simp only [V, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hm
    rcases hm with h | ⟨z, hz, heq⟩
    · change c = 1 / 2 at h
      linarith
    · change |z.2| = c at heq
      linarith [hz.2]
  refine ⟨c, by linarith, hc1, ?_⟩
  have hnull : N.N ω (R \ (s : Set (ℝ × ℝ))) = 0 := by
    rw [MeasureTheory.ae_iff, Measure.restrict_apply] at hs
    · rw [← hs]
      congr 1
      ext z
      simp [and_comm]
    · exact s.measurableSet.compl
  apply measure_mono_null _ hnull
  intro z hz
  refine ⟨⟨hz.1, le_trans hc (le_of_lt hz.2.1), hz.2.2⟩, ?_⟩
  intro hzs
  have hmem : |z.2| ∈ V :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z,
      Finset.mem_filter.mpr ⟨hzs, hz.2.2⟩, rfl⟩)
  exact (not_le_of_gt hz.2.1) (Finset.le_max' V _ hmem)

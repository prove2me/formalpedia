-- Prove2me | solution 1 for Kyprianou.Ch05.passageBoundaryBorelVersionsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:29:59.61441+00:00
-- url     : https://prove2.me/submissions/89cbbb41-f854-4c86-996f-19bb64d9ad0c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_shrinking_right_grid_samples_recover_original_path
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_measurable_left_grid_sample_family
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_source_grid_has_strict_left_mark_sample
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_local_left_grid_samples_recover_left_limit
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    (t : (NNReal → ℝ) → NNReal) (ht : Measurable t) :
    ∃ R L : (NNReal → ℝ) → ℝ, Measurable R ∧ Measurable L ∧
      (∀ f : NNReal → ℝ, ContinuousWithinAt f (Ici (t f)) (t f) → R f = f (t f)) ∧
      ∀ f : NNReal → ℝ, 0 < t f → Monotone f → L f = Function.leftLim f (t f) := by
  obtain ⟨grid,hdense⟩ := TopologicalSpace.exists_dense_seq NNReal
  let eps : ℕ → NNReal := fun n => (1/2 : NNReal)^n
  have hp (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  have he : Tendsto eps atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨ri,hrim,hrm,hrb,hr⟩ :=
    AvramDividend.Classical.avram_wave7_01_measurable_shrinking_right_grid_samples_recover_original_path
      grid hdense t ht eps hp he
  obtain ⟨li,hlim,hlm,hlb⟩ :=
    AvramDividend.Classical.avram_wave7_01_countable_measurable_left_grid_sample_family
      grid t ht eps (fun n f hf =>
        AvramDividend.Classical.avram_wave7_01_dense_source_grid_has_strict_left_mark_sample
          grid hdense (t f) (eps n) hf (hp n))
  let R : (NNReal → ℝ) → ℝ := fun f => limUnder atTop (fun n : ℕ => f (grid (ri n f)))
  let L : (NNReal → ℝ) → ℝ := fun f => limUnder atTop (fun n : ℕ => f (grid (li n f)))
  refine ⟨R,L,(StronglyMeasurable.limUnder (fun n => (hrm n).stronglyMeasurable)).measurable,
    (StronglyMeasurable.limUnder (fun n => (hlm n).stronglyMeasurable)).measurable,?_,?_⟩
  · intro f hf
    exact (hr f hf).limUnder_eq
  · intro f hpos hm
    have hb (n : ℕ) : t f - eps n ≤ grid (li n f) ∧ grid (li n f) < t f :=
      ⟨tsub_le_iff_right.mpr (hlb n f hpos).2.le,(hlb n f hpos).1⟩
    have hlow : Tendsto (fun n : ℕ => t f - eps n) atTop (nhds (t f)) := by
      simpa only [tsub_zero] using tendsto_const_nhds.sub he
    exact (AvramDividend.Classical.avram_wave7_01_local_left_grid_samples_recover_left_limit
      grid f (t f) (fun n => t f - eps n) (fun n => li n f) hb hlow
      (hm.tendsto_leftLim (t f))).limUnder_eq

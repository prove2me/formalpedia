-- Prove2me | solution 1 for Kyprianou.Ch05.pointFamilyNonanticipatingFiltrationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:03:57.602882+00:00
-- url     : https://prove2.me/submissions/91513fe3-ddf1-46ec-8559-b01192f095f2

import Mathlib
import Theorems.Thm_ProbabilityTheory_indep_prmEvalSigma
import Theorems.Thm_Kyprianou_Ch05_pointFamilyAllRegionEvalMeasurableV1
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) P)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P Pi)
    (hN : ∀ w, N.N w = (poissonRandomMeasure K Z w).restrict (Ici (0 : ℝ) ×ˢ univ)) :
    ∃ F : Filtration NNReal inferInstance,
      Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P Pi F N ∧
      ∀ t : NNReal, F t = prmEvalSigma K Z ((volume : Measure ℝ).prod Pi) (Iic (t : ℝ) ×ˢ univ) := by
  let m := (volume : Measure ℝ).prod Pi
  let F : Filtration NNReal inferInstance :=
    { seq := fun t => prmEvalSigma K Z m (Iic (t : ℝ) ×ˢ univ)
      mono' := fun u v huv => prmEvalSigma_mono (fun z hz => ⟨mem_Iic.mpr ((mem_Iic.mp hz.1).trans (show (u : ℝ) ≤ (v : ℝ) by exact_mod_cast huv)),hz.2⟩)
      le' := fun t => prmEvalSigma_le hd.measurable_count hd.measurable_point _ }
  refine ⟨F,?_,fun _ => rfl⟩
  intro u t B hut hB
  let T : Set (ℝ × ℝ) := Ioc (u : ℝ) (t : ℝ) ×ˢ B
  let R : Set (ℝ × ℝ) := Iic (u : ℝ) ×ˢ univ
  let S : Set (ℝ × ℝ) := Ici (0 : ℝ) ×ˢ univ
  have hRT : Disjoint T R := disjoint_left.2 fun z hz hr => (not_lt_of_ge hr.1) hz.1.1
  apply indep_of_indep_of_le_left (indep_prmEvalSigma hd hRT)
  have he : (fun w => N.N w T) = fun w => poissonRandomMeasure K Z w (T ∩ S) := by
    funext w
    rw [hN,Measure.restrict_apply (measurableSet_Ioc.prod hB)]
  change MeasurableSpace.comap (fun w => N.N w T) inferInstance ≤ prmEvalSigma K Z m T
  rw [he]
  exact (Kyprianou.Ch05.pointFamilyAllRegionEvalMeasurableV1 m K Z T
    (T ∩ S) ((measurableSet_Ioc.prod hB).inter (measurableSet_Ici.prod MeasurableSet.univ))
    inter_subset_left).comap_le

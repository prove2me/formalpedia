-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_M_adapted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:34:52.006461+00:00
-- url     : https://prove2.me/submissions/11377ae3-a319-4445-adf1-1f88ae6b6ff2

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_J_adapted
import Theorems.Thm_Kyprianou_Ch04_kw48_S_adapted_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_adapted
import Theorems.Thm_Kyprianou_Ch04_kw48_M_norm_bound
import Theorems.Thm_Kyprianou_Ch04_exercise47RunningSupremumIntegrable
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The proposed Kella–Whitt process is strongly adapted and integrable. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) :
    StronglyAdapted F (M L Psi alpha beta) ∧
      ∀ t, Integrable (M L Psi alpha beta t) P := by
  letI : IsProbabilityMeasure P := L.isProbability
  have hAdapt : StronglyAdapted F (M L Psi alpha beta) := by
    intro t
    have hJ := Kyprianou.Ch04.kw48_J_adapted L Psi alpha beta t
    have hZ := (Kyprianou.Ch04.kw48_Z_adapted L Psi alpha beta t).1
    have hS := ((Kyprianou.Ch04.kw48_S_adapted_bound L beta).1 t).measurable
    change StronglyMeasurable[F t] (fun w =>
      -Psi alpha*J L alpha beta t w+1-Z L alpha beta t w-
        Complex.I*((alpha-beta:Real):Complex)*S L beta t w)
    exact ((((measurable_const.mul hJ).add measurable_const).sub hZ).sub
      (measurable_const.mul hS)).stronglyMeasurable
  refine ⟨hAdapt,?_⟩
  intro t
  have hU := Kyprianou.Ch04.exercise47RunningSupremumIntegrable P F L t
  simp_rw [← Kyprianou.Ch04.kw47_runningSup_raw_eq L] at hU
  have hDom : Integrable (fun w => ‖Psi alpha‖*(t:Real)+2+
      |alpha-beta| * runningSup L t w) P :=
    (integrable_const _).add (hU.const_mul _)
  exact hDom.mono' ((hAdapt t).mono (F.le t)).aestronglyMeasurable
    (Eventually.of_forall fun w => Kyprianou.Ch04.kw48_M_norm_bound L Psi alpha beta t w)

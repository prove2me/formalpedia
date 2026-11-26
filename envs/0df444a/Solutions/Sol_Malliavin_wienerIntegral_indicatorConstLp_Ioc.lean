-- Prove2me | solution 1 for Malliavin.wienerIntegral_indicatorConstLp_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:07.671431+00:00
-- url     : https://prove2.me/submissions/43dc88ea-9bde-4fac-bd25-4cc00eee4fba

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_wienerIntegral_intervalIndicator

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) {a b : ℝ≥0}
    (hab : a ≤ b) :
    wienerIntegral hB (indicatorConstLp 2 measurableSet_Ioc
      (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ)) = brownianLp hB b - brownianLp hB a := by
  have hdisj : Disjoint (Set.Ioc 0 a) (Set.Ioc a b) :=
    Set.Ioc_disjoint_Ioc.mpr ((min_le_left a b).trans (le_max_right 0 a))
  have hunion := indicatorConstLp_disjoint_union (p := 2) (μ := nonnegativeLebesgueMeasure)
    measurableSet_Ioc measurableSet_Ioc (nonnegativeLebesgueMeasure_Ioc_ne_top 0 a)
    (nonnegativeLebesgueMeasure_Ioc_ne_top a b) hdisj (1 : ℝ)
  have hIoc : Set.Ioc 0 a ∪ Set.Ioc a b = Set.Ioc 0 b := Set.Ioc_union_Ioc_eq_Ioc zero_le hab
  rw [← wienerIntegral_intervalIndicator, ← wienerIntegral_intervalIndicator, ← map_sub]
  congr 1
  rw [eq_sub_iff_add_eq, add_comm, intervalIndicator, intervalIndicator, ← hunion]
  congr 1
end Malliavin

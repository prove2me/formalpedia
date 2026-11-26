-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52PassageToRationalGapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:29:25.110859+00:00
-- url     : https://prove2.me/submissions/0a0ae8d9-1a91-43e8-87f4-3b2697975d3d

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05

open Topology
/-- Monotone path passage margins imply a rational gap. -/
theorem solution
    (Y L : NNReal → ℝ) (hm : Monotone Y)
    (s : NNReal) (hs0 : 0 < s)
    (hl : Tendsto Y (nhdsWithin s (Iio s)) (nhds (L s)))
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y)
    (ho : u < Y s - x) (hlow : y < x - L s) :
    (∃ a b : ℚ, (a : ℝ) < x-y ∧ x+u < (b : ℝ) ∧
      (∀ q : ℚ, Y (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ Y (Real.toNNReal q)) ∧
      ∃ q : ℚ, (b : ℝ) ≤ Y (Real.toNNReal q)) := by
  letI : (nhdsWithin s (Iio s)).NeBot :=
    nhdsWithin_Iio_neBot' ⟨0, hs0⟩ le_rfl
  have hleft (t : NNReal) (hts : t < s) : Y t ≤ L s := by
    apply ge_of_tendsto hl
    filter_upwards [(eventually_gt_nhds hts).filter_mono nhdsWithin_le_nhds] with v hv
    exact hm hv.le
  obtain ⟨a, ha, ha'⟩ := exists_rat_btwn (show L s < x-y by linarith)
  obtain ⟨b, hb, hb'⟩ := exists_rat_btwn (show x+u < Y s by linarith)
  refine ⟨a,b,ha',hb,?_,?_⟩
  · intro q
    by_cases hq : Real.toNNReal q < s
    · exact Or.inl ((hleft _ hq).trans ha.le)
    · exact Or.inr (hb'.le.trans (hm (le_of_not_gt hq)))
  · obtain ⟨q,hq⟩ := exists_rat_gt (s : ℝ)
    have hq0 : 0 ≤ (q : ℝ) := (NNReal.coe_nonneg s).trans hq.le
    have hsq : s ≤ Real.toNNReal q := by
      exact NNReal.coe_le_coe.mp (by rw [Real.coe_toNNReal _ hq0]; exact hq.le)
    exact ⟨q, hb'.le.trans (hm hsq)⟩

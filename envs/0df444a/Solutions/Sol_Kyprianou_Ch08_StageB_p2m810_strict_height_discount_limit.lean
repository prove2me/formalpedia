-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_strict_height_discount_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:45:41.718651+00:00
-- url     : https://prove2.me/submissions/c030cbd2-9103-4d5c-b17d-06bdd2821806

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_null_indicator_integral
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_antitone_null_set_integral
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_height_family_null_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_record_discount_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_height_intersection_payoff
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict record limit proof. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q a l : ℝ), 0 ≤ q → 0 < a → 0 < l →
      Tendsto (fun k : ℕ =>
        ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X l (a + 1 / ((k : ℝ)+1)) ω},
          Real.exp (Phi ψ q * l) * discountedAt q (tauPlus D.X l ω) ∂P)
        atTop (nhds (Real.exp (Phi ψ q * l) *
          (∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X 0 a ω
            then discountedAt q (tauPlus D.X l ω) else 0 ∂P))) := by
  intro Ω mΩ P hP D ψ W hψ hW q a l hq ha hl
  let A := fun n : ℕ => {ω | NoDrawdownBeforeUpcrossing D.X l (a+1/((n:ℝ)+1)) ω}
  let g := fun ω => discountedAt q (tauPlus D.X l ω)
  have hg : Integrable g P := p2m810_record_discount_integrable Ω P D ψ W hψ hW q l hq
  have hm (n : ℕ) : NullMeasurableSet (A n) P :=
    p2m810_height_family_null_measurable Ω P D ψ W hψ hW l _ hl (by positivity)
  have hA : Antitone A := by
    intro i j hij ω hw t ht
    exact lt_of_lt_of_le (hw t ht) (by
      apply add_le_add_right
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1))
  have h := p2m810_antitone_null_set_integral Ω P g A hg hm hA
  have he := (p2m810_null_indicator_integral Ω P g (⋂ n,A n) hg
    (NullMeasurableSet.iInter hm)).2
  rw [← he, integral_congr_ae (p2m810_height_intersection_payoff Ω P D ψ W hψ hW q a l hq ha hl)] at h
  simpa only [A,g,integral_const_mul] using
    (tendsto_const_nhds (x := Real.exp (Phi ψ q*l))).mul h

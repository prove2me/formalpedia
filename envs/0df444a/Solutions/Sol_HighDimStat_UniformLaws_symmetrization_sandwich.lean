-- Prove2me | solution 1 for HighDimStat.UniformLaws.symmetrization_sandwich
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:11:21.753359+00:00
-- url     : https://prove2.me/submissions/0a22e341-94c5-45b5-8d66-9af7e89cd333

import Mathlib
import Definitions.Def_HighDimStat_UniformLaws_empProcessDeviation
import Definitions.Def_HighDimStat_UniformLaws_symmetrizedProcess

open MeasureTheory

namespace HighDimStat.UniformLaws

lemma aux_symsand_emp :
    empProcessDeviation (ι := Unit) (fun _ (x : ℝ) => x) (fun _ (_ : Unit) => (1 : ℝ))
      (fun _ => (0 : ℝ)) (Measure.dirac ()) 1 () = 1 := by
  simp [empProcessDeviation]

lemma aux_symsand_sym :
    symmetrizedProcess (ι := Unit) (fun _ (x : ℝ) => x) (fun _ (_ : Unit) => (1 : ℝ))
      (fun _ _ => (0 : ℝ)) 1 () = 0 := by
  simp [symmetrizedProcess]

end HighDimStat.UniformLaws

open HighDimStat.UniformLaws
open MeasureTheory

theorem solution : ¬ (∀ {D ι Ω : Type} [MeasurableSpace D] [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (f : ι → D → ℝ) (hf : ∀ j, Measurable (f j))
    (Xs : ℕ → Ω → D) (X0 : Ω → D) (eps : ℕ → Ω → ℝ)
    (n : ℕ) (Φ : ℝ → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hInt1 : Integrable (fun ω => Φ (1 / 2 *
      symmetrizedProcess (fun j x => f j x - ∫ ω', f j (X0 ω') ∂Prob) Xs eps n ω)) Prob)
    (hInt2 : Integrable (fun ω => Φ (empProcessDeviation f Xs X0 Prob n ω)) Prob)
    (hInt3 : Integrable (fun ω => Φ (2 * symmetrizedProcess f Xs eps n ω)) Prob),
    ∫ ω, Φ (1 / 2 *
      symmetrizedProcess (fun j x => f j x - ∫ ω', f j (X0 ω') ∂Prob) Xs eps n ω) ∂Prob ≤
    ∫ ω, Φ (empProcessDeviation f Xs X0 Prob n ω) ∂Prob
    ∧
    ∫ ω, Φ (empProcessDeviation f Xs X0 Prob n ω) ∂Prob ≤
    ∫ ω, Φ (2 * symmetrizedProcess f Xs eps n ω) ∂Prob) := by
  intro h
  have hInt : ∀ g : Unit → ℝ, Integrable g (Measure.dirac ()) := fun g =>
    integrable_dirac enorm_lt_top
  have key := (h (D := ℝ) (ι := Unit) (Ω := Unit) (Prob := Measure.dirac ())
    (fun _ x => x) (fun _ => measurable_id) (fun _ _ => (1 : ℝ)) (fun _ => (0 : ℝ))
    (fun _ _ => (0 : ℝ)) 1 id (convexOn_id convex_univ) monotone_id
    (hInt _) (hInt _) (hInt _)).2
  simp only [integral_dirac, id] at key
  rw [aux_symsand_emp, aux_symsand_sym] at key
  norm_num at key

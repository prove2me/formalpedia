-- Prove2me | solution 1 for MartOT.Opt.reroute_competitor
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:05:18.144301+00:00
-- url     : https://prove2.me/submissions/65e13c5d-8f45-4d70-9587-1e5d5a687eaa

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory

namespace Aux_reroute

theorem int3 (f : ℝ × ℝ → ℝ) (a b c : ℝ × ℝ) (r s : ℝ) :
    Integrable f (ENNReal.ofReal r • Measure.dirac a + ENNReal.ofReal s • Measure.dirac b +
      Measure.dirac c) :=
  (((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)).add_measure
    (integrable_dirac enorm_lt_top)

theorem integral3 (f : ℝ × ℝ → ℝ) (a b c : ℝ × ℝ) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    ∫ p, f p ∂(ENNReal.ofReal r • Measure.dirac a + ENNReal.ofReal s • Measure.dirac b +
      Measure.dirac c) = r * f a + s * f b + f c := by
  rw [integral_add_measure, integral_add_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, integral_dirac, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal hs, smul_eq_mul, smul_eq_mul]
  · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  · exact ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)
  · exact integrable_dirac enorm_lt_top

end Aux_reroute

theorem solution (x x' ym yp y' l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (hcomb : l * yp + (1 - l) * ym = y') :
    MartOT.Var.IsCompetitor
      (ENNReal.ofReal l • Measure.dirac (x, yp) + ENNReal.ofReal (1 - l) • Measure.dirac (x, ym) +
        Measure.dirac (x', y'))
      (ENNReal.ofReal (1 - l) • Measure.dirac (x', ym) + ENNReal.ofReal l • Measure.dirac (x', yp) +
        Measure.dirac (x, y')) := by
  have h1 : (0:ℝ) ≤ 1 - l := by linarith
  have hsum : ENNReal.ofReal l + ENNReal.ofReal (1 - l) = 1 := by
    rw [← ENNReal.ofReal_add hl0.le h1]; simp
  have hsum' : ENNReal.ofReal (1 - l) + ENNReal.ofReal l = 1 := by
    rw [add_comm]; exact hsum
  refine ⟨?_, ?_, Aux_reroute.int3 _ _ _ _ _ _, Aux_reroute.int3 _ _ _ _ _ _, ?_⟩
  · rw [Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst,
      Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst,
      Measure.map_smul, Measure.map_smul, Measure.map_smul, Measure.map_smul,
      Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst,
      Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst,
      Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst]
    simp only
    rw [← add_smul, ← add_smul, hsum, hsum', one_smul, one_smul, add_comm]
  · rw [Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd,
      Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd,
      Measure.map_smul, Measure.map_smul, Measure.map_smul, Measure.map_smul,
      Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd,
      Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd,
      Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd]
    simp only
    abel
  · intro ρ _ _
    rw [Aux_reroute.integral3 _ _ _ _ _ _ hl0.le h1, Aux_reroute.integral3 _ _ _ _ _ _ h1 hl0.le]
    simp only
    rw [← hcomb]
    ring

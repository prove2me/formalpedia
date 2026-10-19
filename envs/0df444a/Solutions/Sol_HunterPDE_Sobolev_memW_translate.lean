-- Prove2me | solution 1 for HunterPDE.Sobolev.memW_translate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T11:05:37.759995+00:00
-- url     : https://prove2.me/submissions/27897418-db9e-45d2-a721-725de83e7878

import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_translate
import Mathlib.MeasureTheory.Group.Measure
open MeasureTheory HunterPDE.Sobolev
set_option autoImplicit false

theorem solution {n k : ℕ} {p : ENNReal}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (a : EuclideanSpace ℝ (Fin n)) :
    MemW k p Set.univ (fun x => f (x - a)) := by
  have hzero := hf.2 (fun _ => 0) (by simp)
  obtain ⟨g₀, hg₀, _⟩ := hzero
  refine ⟨(HasWeakDeriv.translate hg₀ a).1, ?_⟩
  intro α hα
  obtain ⟨g, hg, hgp⟩ := hf.2 α hα
  refine ⟨fun x => g (x-a), hg.translate a, ?_⟩
  simp only [Measure.restrict_univ] at hgp ⊢
  exact hgp.comp_measurePreserving (measurePreserving_sub_right volume a)

-- Prove2me | solution 1 for HunterPDE.Newtonian.integrableOn_secondPartial_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:16:55.506517+00:00
-- url     : https://prove2.me/submissions/3b74ffe7-d025-479f-a3b5-fef49e6077bd

import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Theorems.Thm_HunterPDE_Newtonian_norm_secondPartial_le
import Theorems.Thm_MeasureTheory_integrableOn_singularKernel_mul_sub
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory HunterPDE.Newtonian
open scoped ContDiff
set_option autoImplicit false

theorem solution (n : ℕ) (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R) (i j : Fin n) :
    IntegrableOn (fun y => secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x))
      (Metric.ball x R) := by
  have hΓ := (fundamentalSolution_partial n hn).1
  have hopen : IsOpen ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := isClosed_singleton.isOpen_compl
  have hp : ContDiffOn ℝ ∞ (partialDeriv (fundamentalSolution n) j) {0}ᶜ := by
    exact (hΓ.fderiv_of_isOpen hopen (by simp)).clm_apply contDiffOn_const
  have hmeas : AEStronglyMeasurable (secondPartial (fundamentalSolution n) i j) volume := by
    apply Measurable.aestronglyMeasurable
    apply measurable_of_continuousOn_compl_singleton 0
    exact ((hp.fderiv_of_isOpen (m := 0) hopen (by simp)).clm_apply contDiffOn_const).continuousOn
  obtain ⟨C, hC, hbound⟩ := norm_secondPartial_le n hn i j
  have hg : ContDiff ℝ 1 (fun z => f (x - z)) :=
    hf.comp (contDiff_const.sub contDiff_id)
  have hi := MeasureTheory.integrableOn_singularKernel_mul_sub n (by omega)
    (secondPartial (fundamentalSolution n) i j) (fun z => f (x - z))
    hmeas hg C hC hbound R hR
  have he := (Homeomorph.subLeft x).measurableEmbedding
  have hm := Measure.measurePreserving_sub_left (volume : Measure (EuclideanSpace ℝ (Fin n))) x
  have ht := (hm.integrableOn_comp_preimage he).2 hi
  have hset : (fun y => x - y) ⁻¹' Metric.ball 0 R = Metric.ball x R := by
    ext y
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero]
    rw [norm_sub_rev]
  simpa only [hset, Function.comp_def, sub_sub_cancel, sub_zero] using ht

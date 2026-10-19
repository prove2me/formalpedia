-- Prove2me | solution 1 for HunterPDE.Sobolev.sobolevNorm_translation_small
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T11:05:19.876457+00:00
-- url     : https://prove2.me/submissions/53f5bbd3-d178-41e0-8d07-7b6c89336149

import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_translate
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_ae_eq
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_sub
import Theorems.Thm_BookProof_MollifierL2_tendsto_translate_Lp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

open MeasureTheory HunterPDE.Sobolev Filter Metric
open scoped ENNReal Topology
set_option autoImplicit false

theorem solution {n k : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ < r →
      sobolevNorm k p Set.univ (f - (fun x => f (x - a))) < ε := by
  classical
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  have hd : ∀ α ∈ multiIndices n k,
      Tendsto (fun a : EuclideanSpace ℝ (Fin n) =>
        eLpNorm (weakDeriv Set.univ α (f - (fun x => f (x-a)))) p volume)
        (𝓝 0) (𝓝 0) := by
    intro α hα
    obtain ⟨d, hd, hdp⟩ := hf.2 α (Finset.mem_filter.mp hα).2
    have hdp' : MemLp d p volume := by simpa using hdp
    have heq : ∀ a : EuclideanSpace ℝ (Fin n),
        eLpNorm (weakDeriv Set.univ α (f - (fun x => f (x-a)))) p volume =
          eLpNorm (fun x => d (x-a) - d x) p volume := by
      intro a
      have hsub := hd.sub (hd.translate a)
      have hchosen : HasWeakDeriv Set.univ α (f - (fun x => f (x-a)))
          (weakDeriv Set.univ α (f - (fun x => f (x-a)))) := by
        unfold weakDeriv
        rw [dif_pos (show ∃ g, HasWeakDeriv Set.univ α
          (f - (fun x => f (x-a))) g from ⟨_, hsub⟩)]
        exact Exists.choose_spec _
      have hae := hchosen.ae_eq isOpen_univ hsub
      simp only [Measure.restrict_univ] at hae
      rw [eLpNorm_congr_ae hae]
      exact eLpNorm_sub_comm d (fun x => d (x-a)) p volume
    simp_rw [heq]
    exact BookProof.MollifierL2.tendsto_translate_Lp hp0 hp' hp hdp'
  have hs : Tendsto (fun a : EuclideanSpace ℝ (Fin n) =>
      ∑ α ∈ multiIndices n k,
        eLpNorm (weakDeriv Set.univ α (f - (fun x => f (x-a)))) p volume ^ p.toReal)
      (𝓝 0) (𝓝 0) := by
    have H := tendsto_finsetSum (multiIndices n k)
      (fun α hα => (hd α hα).ennrpow_const p.toReal)
    simpa [ENNReal.zero_rpow_of_pos hpr] using H
  have hn : Tendsto (fun a : EuclideanSpace ℝ (Fin n) =>
      sobolevNorm k p Set.univ (f - (fun x => f (x-a)))) (𝓝 0) (𝓝 0) := by
    simpa [sobolevNorm, hp', Measure.restrict_univ,
      ENNReal.zero_rpow_of_pos (inv_pos.mpr hpr)] using hs.ennrpow_const (1 / p.toReal)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hn.eventually (gt_mem_nhds hε))
  exact ⟨r, hr, fun a ha => hball (by simpa [dist_zero_right] using ha)⟩


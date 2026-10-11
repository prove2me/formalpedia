-- Prove2me | solution 1 for HunterPDE.Sobolev.sobolevNorm_sub_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:44:59.565166+00:00
-- url     : https://prove2.me/submissions/402107ca-ae77-48fc-99b7-532c13d58210

import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_ae_eq
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_sub
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.MeanInequalities

open MeasureTheory HunterPDE.Sobolev

theorem solution {n k : ℕ}
    {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemW k p Ω f) (hg : MemW k p Ω g) (hh : MemW k p Ω h) :
    sobolevNorm k p Ω (f - h) ≤
      sobolevNorm k p Ω (f - g) + sobolevNorm k p Ω (g - h) := by
  classical
  have chosen {u v : EuclideanSpace ℝ (Fin n) → ℝ} {α : Fin n → ℕ}
      (hv : HasWeakDeriv Ω α u v) : HasWeakDeriv Ω α u (weakDeriv Ω α u) := by
    unfold weakDeriv
    rw [dif_pos (show ∃ v, HasWeakDeriv Ω α u v from ⟨v, hv⟩)]
    exact Exists.choose_spec _
  have coord (α : Fin n → ℕ) (hα : α ∈ multiIndices n k) :
      eLpNorm (weakDeriv Ω α (f - h)) p (volume.restrict Ω) ≤
        eLpNorm (weakDeriv Ω α (f - g)) p (volume.restrict Ω) +
        eLpNorm (weakDeriv Ω α (g - h)) p (volume.restrict Ω) := by
    have hdeg : ∑ i, α i ≤ k := (Finset.mem_filter.mp hα).2
    obtain ⟨u, hu, hup⟩ := hf.2 α hdeg
    obtain ⟨v, hv, hvp⟩ := hg.2 α hdeg
    obtain ⟨w, hw, hwp⟩ := hh.2 α hdeg
    have hfh := (chosen (hu.sub hw)).ae_eq hΩ (hu.sub hw)
    have hfg := (chosen (hu.sub hv)).ae_eq hΩ (hu.sub hv)
    have hgh := (chosen (hv.sub hw)).ae_eq hΩ (hv.sub hw)
    rw [eLpNorm_congr_ae hfh, eLpNorm_congr_ae hfg, eLpNorm_congr_ae hgh]
    have heq : u - w = (u - v) + (v - w) := by
      ext x
      simp
    rw [heq]
    exact eLpNorm_add_le (hup.sub hvp).aestronglyMeasurable
      (hvp.sub hwp).aestronglyMeasurable hp
  have hpReal : 1 ≤ p.toReal := by
    exact_mod_cast (ENNReal.toReal_mono hptop hp)
  simp only [sobolevNorm, if_neg hptop]
  calc
    _ ≤ (∑ α ∈ multiIndices n k,
          (eLpNorm (weakDeriv Ω α (f - g)) p (volume.restrict Ω) +
            eLpNorm (weakDeriv Ω α (g - h)) p (volume.restrict Ω)) ^ p.toReal)
          ^ (1 / p.toReal) := by
      apply ENNReal.rpow_le_rpow
      · exact Finset.sum_le_sum fun α hα =>
          ENNReal.rpow_le_rpow (coord α hα) ENNReal.toReal_nonneg
      · positivity
    _ ≤ _ := ENNReal.Lp_add_le (multiIndices n k) _ _ hpReal

-- Prove2me | solution 1 for JHolomorphic.exists_hasWeakPartialsOn_of_diffQuot_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T20:58:15.359755+00:00
-- url     : https://prove2.me/submissions/ac505c01-88d9-4b26-81b2-ecd8a5ef7b8b

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_enorm_integral_fderiv_smul_le_of_diffQuot
import Theorems.Thm_JHolomorphic_exists_memLp_weakDeriv_of_enorm_integral_le



namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

theorem exists_hasWeakPartialsOn_of_diffQuot_bounded_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) {c : ℂ} {r R : ℝ}
    (hrR : r < R) {f : ℂ → E} (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (ball c R)))
    (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hC : ∀ v ∈ ({1, Complex.I} : Set ℂ), ∀ h : ℝ, h ≠ 0 → |h| < δ →
      eLpNorm (fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)) (ENNReal.ofReal p)
        (volume.restrict (ball c r)) ≤ ENNReal.ofReal C) :
    ∃ fs ft : ℂ → E, HasWeakPartialsOn (ball c r) f fs ft ∧
      MemLp fs (ENNReal.ofReal p) (volume.restrict (ball c r)) ∧
      MemLp ft (ENNReal.ofReal p) (volume.restrict (ball c r)) := by
  have hfR : IntegrableOn f (ball c R) := by
    haveI : IsFiniteMeasure (volume.restrict (ball c R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    exact hf.integrable (ENNReal.one_le_ofReal.2 hp.le)
  have hfK : ∀ K ⊆ ball c r, IsCompact K → IntegrableOn f K := fun K hK _ =>
    hfR.mono_set (hK.trans (ball_subset_ball hrR.le))
  obtain ⟨fs, hfs, hfs'⟩ := exists_memLp_weakDeriv_of_enorm_integral_le p hp isOpen_ball hfK 1 C
    (enorm_integral_fderiv_smul_le_of_diffQuot p hp hrR hfR 1 (by simp) δ hδ C (hC 1 (by simp)))
  obtain ⟨ft, hft, hft'⟩ := exists_memLp_weakDeriv_of_enorm_integral_le p hp isOpen_ball hfK
    Complex.I C (enorm_integral_fderiv_smul_le_of_diffQuot p hp hrR hfR Complex.I (by simp) δ hδ C
      (hC Complex.I (by simp)))
  exact ⟨fs, ft, fun φ hφ hφc hφU => ⟨hfs' φ hφ hφc hφU, hft' φ hφ hφc hφU⟩, hfs, hft⟩

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) {c : ℂ} {r R : ℝ}
    (hrR : r < R) {f : ℂ → E} (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (ball c R)))
    (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hC : ∀ v ∈ ({1, Complex.I} : Set ℂ), ∀ h : ℝ, h ≠ 0 → |h| < δ →
      eLpNorm (fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)) (ENNReal.ofReal p)
        (volume.restrict (ball c r)) ≤ ENNReal.ofReal C) :
    ∃ fs ft : ℂ → E, HasWeakPartialsOn (ball c r) f fs ft ∧
      MemLp fs (ENNReal.ofReal p) (volume.restrict (ball c r)) ∧
      MemLp ft (ENNReal.ofReal p) (volume.restrict (ball c r)) :=
  exists_hasWeakPartialsOn_of_diffQuot_bounded_aux p hp hrR hf δ hδ C hC

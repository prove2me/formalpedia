-- Prove2me | solution 1 for LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated_ae
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T18:47:43.230179+00:00
-- url     : https://prove2.me/submissions/49f792e3-a81b-4a76-a1f2-6d72bbe3e64d

import Mathlib
open MeasureTheory Filter Topology
universe v
variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
theorem solution
    {T : ℝ} {A : ℕ → Set E} {fs : ℕ → ℝ → E → ℝ} {f g : ℝ → E → ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hev : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m)
    (hmeas : ∀ m, AEStronglyMeasurable (fun p : ℝ × E => fs m p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hg : Integrable (fun p : ℝ × E => g p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hdom : ∀ m, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ e, |fs m s e| ≤ g s e)
    (hconv : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ e,
      Tendsto (fun m => fs m s e) atTop (𝓝 (f s e))) :
    Tendsto (fun m => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e, f s e ∂ν)) := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) T)
  let cut (m : ℕ) : Set (ℝ × E) := Prod.snd ⁻¹' (A m)ᶜ
  have hcut (m : ℕ) : MeasurableSet (cut m) := measurable_snd (hA m).compl
  let F (m : ℕ) := (cut m).indicator (fun p : ℝ × E => fs m p.1 p.2)
  let G := fun p : ℝ × E => g p.1 p.2
  let L := fun p : ℝ × E => f p.1 p.2
  have hFm (m : ℕ) : AEStronglyMeasurable (F m) (μ.prod ν) :=
    (hmeas m).indicator (hcut m)
  have hbd (m : ℕ) : ∀ᵐ p ∂μ.prod ν, ‖F m p‖ ≤ G p := by
    have hs := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (hdom m)
    filter_upwards [hs] with p hp
    have h := hp p.2
    by_cases hc : p ∈ cut m
    · simpa [F, Set.indicator_of_mem hc, Real.norm_eq_abs, G] using h
    · simpa [F, Set.indicator_of_notMem hc, G] using (abs_nonneg _).trans h
  have hlim : ∀ᵐ p ∂μ.prod ν, Tendsto (fun m => F m p) atTop (𝓝 (L p)) := by
    have hs := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hconv
    have he := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hev
    filter_upwards [hs, he] with p hp hpe
    apply (hp p.2).congr'
    filter_upwards [hpe] with m hm
    exact (Set.indicator_of_mem (show p ∈ cut m from hm) (fun q : ℝ × E => fs m q.1 q.2)).symm
  have hG : Integrable G (μ.prod ν) := hg
  have hi (m : ℕ) : Integrable (F m) (μ.prod ν) := hG.mono' (hFm m) (hbd m)
  have hLi : Integrable L (μ.prod ν) := by
    apply hG.mono' (aestronglyMeasurable_of_tendsto_ae _ hFm hlim)
    filter_upwards [hlim, ae_all_iff.mpr hbd] with p hp hb
    exact le_of_tendsto hp.norm (Eventually.of_forall hb)
  have hd := tendsto_integral_of_dominated_convergence G hFm hG hbd hlim
  rw [integral_prod L hLi] at hd
  have hFn (m : ℕ) : (∫ p, F m p ∂μ.prod ν) =
      ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν := by
    rw [integral_prod (F m) (hi m)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro s
    change (∫ y, F m (s,y) ∂ν) = ∫ e in (A m)ᶜ, fs m s e ∂ν
    rw [← integral_indicator (hA m).compl]
    rfl
  simpa only [hFn] using hd
#print axioms solution

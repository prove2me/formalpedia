-- Prove2me | solution 1 for MaxSpectralRisk.Duality.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:38:30.140963+00:00
-- url     : https://prove2.me/submissions/c0b2eba5-f533-4e4c-8779-74b8d39ac1a2

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

open MeasureTheory Filter Topology MaxSpectralRisk.Duality

namespace MSRLemma1Aux

instance gam_finite (sig : SpectralFunction) : IsFiniteMeasure (gam sig) := by
  refine ⟨?_⟩
  unfold gam
  rw [Measure.restrict_apply_univ]
  exact measure_Ico_lt_top

lemma int_pos (sig : SpectralFunction) {β : ℝ → ℝ} (hβ : Integrable β (gam sig)) (t : ℝ) :
    Integrable (fun u => max (t - β u) 0) (gam sig) := by
  refine Integrable.mono' ((integrable_const |t|).add hβ.norm)
    ((continuous_id.max continuous_const).comp_aestronglyMeasurable
      ((aestronglyMeasurable_const).sub hβ.1)) (ae_of_all _ fun u => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [le_abs_self t, neg_abs_le (β u)]) (by positivity)

/-- `Φ(t) = ∫ (t - β(u))₊ dγσ(u)`, so that `C^β(x, y) = Φ(L(x, y))`. -/
noncomputable def Φ (sig : SpectralFunction) (β : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u, max (t - β u) 0 ∂(gam sig)

lemma Φ_mono (sig : SpectralFunction) {β : ℝ → ℝ} (hβ : Integrable β (gam sig)) :
    Monotone (Φ sig β) := fun s t hst =>
  integral_mono (int_pos sig hβ s) (int_pos sig hβ t) fun u =>
    max_le_max (by linarith) le_rfl

lemma Φ_cont (sig : SpectralFunction) {β : ℝ → ℝ} (hβ : Integrable β (gam sig)) :
    Continuous (Φ sig β) := by
  have hlip : ∀ s t, dist (Φ sig β s) (Φ sig β t) ≤ (gam sig).real Set.univ * dist s t := by
    intro s t
    rw [Real.dist_eq, Real.dist_eq, Φ, Φ, ← integral_sub (int_pos sig hβ s) (int_pos sig hβ t)]
    have := norm_integral_le_of_norm_le_const (μ := gam sig)
      (f := fun u => max (s - β u) 0 - max (t - β u) 0) (C := |s - t|)
      (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs]
        have := abs_max_sub_max_le_abs (s - β u) (t - β u) 0
        rwa [show s - β u - (t - β u) = s - t by ring] at this)
    rw [Real.norm_eq_abs] at this
    linarith
  refine (LipschitzWith.of_dist_le_mul (K := ⟨(gam sig).real Set.univ, measureReal_nonneg⟩)
    fun s t => ?_).continuous
  exact hlip s t

lemma Φ_le (sig : SpectralFunction) {β : ℝ → ℝ} (hβ : Integrable β (gam sig)) (t : ℝ) :
    Φ sig β t ≤ (gam sig).real Set.univ * |t| + ∫ u, |β u| ∂(gam sig) := by
  unfold Φ
  calc ∫ u, max (t - β u) 0 ∂(gam sig) ≤ ∫ u, (|t| + |β u|) ∂(gam sig) :=
        integral_mono (int_pos sig hβ t) ((integrable_const |t|).add hβ.abs) fun u =>
          max_le (by linarith [le_abs_self t, neg_abs_le (β u)]) (by positivity)
    _ = (gam sig).real Set.univ * |t| + ∫ u, |β u| ∂(gam sig) := by
        rw [integral_add (integrable_const _) hβ.abs, integral_const, smul_eq_mul]

end MSRLemma1Aux

open MSRLemma1Aux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) (β : ℝ → ℝ) (hβ : Integrable β (gam sig)) :
    UpperSemicontinuous (fun p : X × Y => Cbeta sig L β p.1 p.2) ∧
    (∀ x y, Integrable (fun u => max (L (x, y) - β u) 0) (gam sig)) ∧
    (∀ x y, 0 ≤ Cbeta sig L β x y) ∧
    ∃ (Aβ : X → ℝ) (Bβ : Y → ℝ), Integrable Aβ μ ∧ Integrable Bβ ν ∧
      AERect μ ν (fun x y => Cbeta sig L β x y ≤ Aβ x + Bβ y) := by
  have hC : ∀ x y, Cbeta sig L β x y = Φ sig β (L (x, y)) := fun _ _ => rfl
  refine ⟨?_, fun x y => int_pos sig hβ _, fun x y => integral_nonneg fun u => le_max_right _ _,
    ?_⟩
  · have : (fun p : X × Y => Cbeta sig L β p.1 p.2) = Φ sig β ∘ L := by
      funext p; simp [hC]
    rw [this]
    exact (Φ_cont sig hβ).comp_upperSemicontinuous hA.usc (Φ_mono sig hβ)
  · obtain ⟨A, B, -, hAi, -, hBi, N, hN, N', hN', hub⟩ := hA.upper_bound
    set m := (gam sig).real Set.univ
    refine ⟨fun x => m * |A x| + ∫ u, |β u| ∂(gam sig), fun y => m * |B y|,
      (hAi.abs.const_mul m).add (integrable_const _), hBi.abs.const_mul m,
      N, hN, N', hN', fun x hx y hy => ?_⟩
    have hm : 0 ≤ m := measureReal_nonneg
    show Cbeta sig L β x y ≤ m * |A x| + ∫ u, |β u| ∂(gam sig) + m * |B y|
    rw [hC]
    calc Φ sig β (L (x, y)) ≤ Φ sig β (A x + B y) := Φ_mono sig hβ (hub x hx y hy)
      _ ≤ m * |A x + B y| + ∫ u, |β u| ∂(gam sig) := Φ_le sig hβ _
      _ ≤ m * |A x| + ∫ u, |β u| ∂(gam sig) + m * |B y| := by
        have := abs_add_le (A x) (B y)
        nlinarith

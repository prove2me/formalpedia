-- Prove2me | solution 1 for HunterPDE.Compactness.smooth_halfSpace_trace_power_le_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T16:25:19.090605+00:00
-- url     : https://prove2.me/submissions/e669aee3-ead6-4cac-b676-8766a040bbf7

import Theorems.Thm_HunterPDE_Compactness_classical_halfSpace_trace_power_le_lintegral
import Theorems.Thm_HunterPDE_Shared_hasWeakDeriv_partial_of_contDiffOn
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_ae_eq
import Definitions.Def_HunterPDE_Compactness_Sobolev
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory HunterPDE.Compactness HunterPDE.Shared
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution {m : ℕ}
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : IsSmoothCompactClosedHalfSpace f) :
    eLpNorm (fun x' => f (boundaryPoint x')) p volume ^ p.toReal ≤
      ENNReal.ofReal p.toReal *
        ∫⁻ x, ‖HunterPDE.Shared.weakDeriv (upperHalfSpace m) 0 f x‖ₑ ^ (p.toReal - 1) *
          ‖HunterPDE.Shared.weakDeriv (upperHalfSpace m)
            (Pi.single (Fin.last m) 1) f x‖ₑ ∂volume.restrict (upperHalfSpace m) := by
  have hΩ : IsOpen (upperHalfSpace m) :=
    isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last m)).continuous
  have hsub : upperHalfSpace m ⊆ closedUpperHalfSpace m := fun x hx => (show 0 ≤ x (Fin.last m) from le_of_lt hx)
  have hc : ContDiffOn ℝ 1 f (upperHalfSpace m) := (hf.1.of_le (by simp)).mono hsub
  have hzero : HasWeakDeriv (upperHalfSpace m) 0 f f := by
    have hloc : LocallyIntegrableOn f (upperHalfSpace m) volume :=
      hc.continuousOn.locallyIntegrableOn hΩ.measurableSet
    refine ⟨hloc, hloc, ?_⟩
    intro φ _
    have hz : multiIndexList (0 : Fin (m + 1) → ℕ) = [] := by
      simp [multiIndexList]
    simp [multiDeriv, hz, iteratedPartial]
  have hnormal := hasWeakDeriv_partial_of_contDiffOn hΩ f hc (Fin.last m)
  have hchosen (α : Fin (m + 1) → ℕ) (g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
      (hg : HasWeakDeriv (upperHalfSpace m) α f g) :
      weakDeriv (upperHalfSpace m) α f =ᵐ[volume.restrict (upperHalfSpace m)] g := by
    have hex : ∃ v, HasWeakDeriv (upperHalfSpace m) α f v := ⟨g, hg⟩
    have hd : HasWeakDeriv (upperHalfSpace m) α f (weakDeriv (upperHalfSpace m) α f) := by
      simpa only [weakDeriv, dif_pos hex] using hex.choose_spec
    exact hd.ae_eq hΩ hg
  have henergy :
      (∫⁻ x, ‖weakDeriv (upperHalfSpace m) 0 f x‖ₑ ^ (p.toReal - 1) *
        ‖weakDeriv (upperHalfSpace m) (Pi.single (Fin.last m) 1) f x‖ₑ
          ∂volume.restrict (upperHalfSpace m)) =
      ∫⁻ x, ‖f x‖ₑ ^ (p.toReal - 1) * ‖partialDeriv f (Fin.last m) x‖ₑ
        ∂volume.restrict (upperHalfSpace m) := by
    apply lintegral_congr_ae
    filter_upwards [hchosen 0 f hzero, hchosen _ _ hnormal] with x hx hy
    rw [hx, hy]
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hr1 : 1 ≤ p.toReal := by exact_mod_cast (ENNReal.toReal_mono hp' hp)
  have hr0 : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hr1
  rw [henergy, eLpNorm_eq_eLpNorm' hp0 hp',
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hr0]
  exact classical_halfSpace_trace_power_le_lintegral p.toReal hr1 f
    (hf.1.of_le (by simp)) hf.2



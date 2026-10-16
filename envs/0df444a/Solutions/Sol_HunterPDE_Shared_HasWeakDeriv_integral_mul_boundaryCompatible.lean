-- Prove2me | solution 1 for HunterPDE.Shared.HasWeakDeriv.integral_mul_boundaryCompatible
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T07:51:15.515368+00:00
-- url     : https://prove2.me/submissions/5108c2a2-b995-4ed3-95f3-a573a9db500a

import Theorems.Thm_HunterPDE_Shared_IsTestFunction_exists_boundaryCompatible_approx
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter HunterPDE.Shared
open scoped Topology ContDiff
set_option autoImplicit false

theorem solution (m : ℕ) (i : Fin (m + 1)) (f g ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : LocallyIntegrable f (volume.restrict (HunterPDE.Compactness.upperHalfSpace m)))
    (hg : LocallyIntegrable g (volume.restrict (HunterPDE.Compactness.upperHalfSpace m)))
    (hd : HunterPDE.Shared.HasWeakDeriv (HunterPDE.Compactness.upperHalfSpace m)
      (Pi.single i 1) f g)
    (hψ : HunterPDE.Shared.IsTestFunction Set.univ ψ)
    (hb : i = Fin.last m → ∀ x, x (Fin.last m) = 0 → ψ x = 0) :
    (∫ x in HunterPDE.Compactness.upperHalfSpace m, g x * ψ x) =
      -(∫ x in HunterPDE.Compactness.upperHalfSpace m,
        f x * HunterPDE.Shared.multiDeriv ψ (Pi.single i 1) x) := by
  classical
  let H := HunterPDE.Compactness.upperHalfSpace m
  let μ := volume.restrict H
  have hH : MeasurableSet H :=
    (isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last m)).continuous).measurableSet
  obtain ⟨K, hK, C, hC, φ, hφ, hbound, hlim⟩ :=
    IsTestFunction.exists_boundaryCompatible_approx m i ψ hψ hb
  have hsmooth (u : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
      (hu : ContDiff ℝ ∞ u) (l : List (Fin (m + 1))) :
      ContDiff ℝ ∞ (iteratedPartial u l) := by
    induction l with
    | nil => exact hu
    | cons j l ih =>
      exact (ih.contDiff_fderiv_apply (m := ∞) (by simp)).comp
        (contDiff_id.prodMk contDiff_const)
  have pass (a : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
      (ha : LocallyIntegrable a μ)
      (u : ℕ → EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
      (v : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
      (hu : ∀ n, Continuous (u n))
      (hbnd : ∀ n x, ‖u n x‖ ≤ K.indicator (fun _ => C) x)
      (hv : ∀ x ∈ H, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
      Tendsto (fun n => ∫ x, a x * u n x ∂μ) atTop (𝓝 (∫ x, a x * v x ∂μ)) := by
    have hdom : Integrable (fun x => K.indicator (fun y => ‖a y‖ * C) x) μ :=
      (integrable_indicator_iff hK.measurableSet).2
        ((ha.integrableOn_isCompact hK).norm.mul_const C)
    apply tendsto_integral_of_dominated_convergence
      (fun x => K.indicator (fun y => ‖a y‖ * C) x)
      (fun n => ha.aestronglyMeasurable.mul (hu n).aestronglyMeasurable) hdom
    · intro n
      apply Filter.Eventually.of_forall
      intro x
      change ‖a x * u n x‖ ≤ K.indicator (fun y => ‖a y‖ * C) x
      rw [norm_mul]
      calc
        ‖a x‖ * ‖u n x‖ ≤ ‖a x‖ * K.indicator (fun _ => C) x :=
          mul_le_mul_of_nonneg_left (hbnd n x) (norm_nonneg _)
        _ = K.indicator (fun y => ‖a y‖ * C) x := by
          by_cases hx : x ∈ K <;> simp [hx]
    · filter_upwards [ae_restrict_mem hH] with x hx
      exact tendsto_const_nhds.mul (hv x hx)
  have hleft := pass g hg φ ψ (fun n => (hφ n).1.continuous)
    (fun n x => (hbound n x).1) (fun x hx => (hlim x hx).1)
  have hright := pass f hf (fun n => multiDeriv (φ n) (Pi.single i 1))
    (multiDeriv ψ (Pi.single i 1))
    (fun n => (hsmooth (φ n) (hφ n).1 (multiIndexList (Pi.single i 1))).continuous)
    (fun n x => (hbound n x).2) (fun x hx => (hlim x hx).2)
  have heq (n : ℕ) : (∫ x, g x * φ n x ∂μ) =
      -(∫ x, f x * multiDeriv (φ n) (Pi.single i 1) x ∂μ) := by
    simpa [μ, H] using hd.2.2 (φ n) (hφ n)
  exact tendsto_nhds_unique hleft (hright.neg.congr (fun n => (heq n).symm))

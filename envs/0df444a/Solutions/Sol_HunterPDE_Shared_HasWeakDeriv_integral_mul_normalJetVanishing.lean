-- Prove2me | solution 1 for HunterPDE.Shared.HasWeakDeriv.integral_mul_normalJetVanishing
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T13:48:52.770989+00:00
-- url     : https://prove2.me/submissions/d69cc54a-a2fe-45f5-bd77-535081b2636c

import Theorems.Thm_HunterPDE_Shared_IsTestFunction_exists_normalJetVanishing_approx
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory Filter HunterPDE.Shared
open scoped Topology ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} (i : Fin n) (α : Fin n → ℕ)
    (f g ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : LocallyIntegrable f (volume.restrict {x | 0 < x i}))
    (hg : LocallyIntegrable g (volume.restrict {x | 0 < x i}))
    (hd : HasWeakDeriv {x | 0 < x i} α f g)
    (hψ : IsTestFunction Set.univ ψ)
    (hb : ∀ r : ℕ, r < α i → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial ψ (List.replicate r i) x = 0) :
    (∫ x in {x : EuclideanSpace ℝ (Fin n) | 0 < x i}, g x * ψ x) =
      (-1 : ℝ) ^ (∑ k, α k) *
        ∫ x in {x : EuclideanSpace ℝ (Fin n) | 0 < x i}, f x * multiDeriv ψ α x := by
  classical
  let H : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 < x i}
  let μ := volume.restrict H
  have hH : MeasurableSet H :=
    (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).measurableSet
  obtain ⟨K, hK, C, hC, φ, hφ, hbound, hlim⟩ :=
    IsTestFunction.exists_normalJetVanishing_approx i α ψ hψ hb
  have hsmooth (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (hu : ContDiff ℝ ∞ u) (l : List (Fin n)) :
      ContDiff ℝ ∞ (iteratedPartial u l) := by
    induction l with
    | nil => exact hu
    | cons j l ih =>
      exact (ih.contDiff_fderiv_apply (m := ∞) (by simp)).comp
        (contDiff_id.prodMk contDiff_const)
  have pass (a : EuclideanSpace ℝ (Fin n) → ℝ)
      (ha : LocallyIntegrable a μ)
      (u : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
      (v : EuclideanSpace ℝ (Fin n) → ℝ)
      (hu : ∀ j, Continuous (u j))
      (hbnd : ∀ j x, ‖u j x‖ ≤ K.indicator (fun _ => C) x)
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
  have hright := pass f hf (fun n => multiDeriv (φ n) α)
    (multiDeriv ψ α)
    (fun n => (hsmooth (φ n) (hφ n).1 (multiIndexList α)).continuous)
    (fun n x => (hbound n x).2) (fun x hx => (hlim x hx).2)
  have heq (n : ℕ) : (∫ x, g x * φ n x ∂μ) =
      (-1 : ℝ) ^ (∑ k, α k) * (∫ x, f x * multiDeriv (φ n) α x ∂μ) := by
    simpa [μ, H] using hd.2.2 (φ n) (hφ n)
  exact tendsto_nhds_unique hleft
    ((tendsto_const_nhds.mul hright).congr (fun j => (heq j).symm))

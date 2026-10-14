-- Prove2me | solution 1 for HunterPDE.Sobolev.eLpNorm_weakDeriv_mul_le_tail
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T21:38:22.671142+00:00
-- url     : https://prove2.me/submissions/7f95f45c-0aaf-4201-8157-53b05159a41a

import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_mul_jet_bound
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_ae_eq
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

open MeasureTheory HunterPDE.Sobolev Filter
open scoped Topology

theorem solution {n k : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (f η : EuclideanSpace ℝ (Fin n) → ℝ)
    (d : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : ∀ β, ∑ i, β i ≤ k → HasWeakDeriv Set.univ β f (d β) ∧ MemLp (d β) p volume)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (R C : ℝ) (hC : 0 ≤ C)
    (hzero : ∀ x, ‖x‖ < R → η x = 0)
    (hbound : ∀ β, ∑ i, β i ≤ k → ∀ x, ‖iteratedPartial β η x‖ ≤ C)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k) :
    eLpNorm (weakDeriv Set.univ α (fun x => η x * f x)) p volume ≤
      (2 : ENNReal) ^ k * ENNReal.ofReal C *
        ∑ β ∈ multiIndices n k, eLpNorm (d β) p (volume.restrict {x | R ≤ ‖x‖}) := by
  classical
  -- Locality of the classical derivatives gives the vanishing of every jet.
  have jets_zero (β : Fin n → ℕ) :
      ∀ x, ‖x‖ < R → iteratedPartial β η x = 0 := by
    have step (i : Fin n) (v : EuclideanSpace ℝ (Fin n) → ℝ)
        (hv : ∀ x, ‖x‖ < R → v x = 0) :
        ∀ x, ‖x‖ < R → partialDeriv i v x = 0 := by
      intro x hx
      have hn : ∀ᶠ y in 𝓝 x, ‖y‖ < R :=
        IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) hx
      have he : v =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := hn.mono (fun y hy => hv y hy)
      simp [partialDeriv, he.fderiv_eq]
    have iter (i : Fin n) (m : ℕ) (v : EuclideanSpace ℝ (Fin n) → ℝ)
        (hv : ∀ x, ‖x‖ < R → v x = 0) :
        ∀ x, ‖x‖ < R → ((partialDeriv i)^[m] v) x = 0 := by
      induction m with
      | zero => simpa using hv
      | succ m ih => simpa only [Function.iterate_succ_apply'] using step i _ ih
    unfold iteratedPartial
    generalize List.finRange n = l
    induction l with
    | nil => simpa using hzero
    | cons i l ih => exact iter i (β i) _ ih
  let S : Set (EuclideanSpace ℝ (Fin n)) := {x | R ≤ ‖x‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_norm.measurable
  let A : EuclideanSpace ℝ (Fin n) → ℝ := S.indicator (fun _ => C)
  have hA : ∀ x, 0 ≤ A x := by
    intro x
    by_cases hx : x ∈ S <;> simp [A, hx, hC]
  have hjet : ∀ β, ∑ i, β i ≤ k → ∀ x, ‖iteratedPartial β η x‖ ≤ A x := by
    intro β hβ x
    by_cases hx : x ∈ S
    · simpa [A, hx] using hbound β hβ x
    · have hxr : ‖x‖ < R := lt_of_not_ge hx
      simp [A, hx, jets_zero β x hxr]
  obtain ⟨g, hg, hgbound⟩ := HasWeakDeriv.mul_jet_bound f η d
    (fun β hβ => (hd β hβ).1) hη A hA hjet α hα
  have hchosen : HasWeakDeriv Set.univ α (fun x => η x * f x)
      (weakDeriv Set.univ α (fun x => η x * f x)) := by
    unfold weakDeriv
    rw [dif_pos (show ∃ g, HasWeakDeriv Set.univ α (fun x => η x * f x) g from ⟨g, hg⟩)]
    exact Exists.choose_spec _
  have heq : weakDeriv Set.univ α (fun x => η x * f x) =ᵐ[volume] g := by
    simpa only [Measure.restrict_univ] using HasWeakDeriv.ae_eq isOpen_univ hchosen hg
  rw [eLpNorm_congr_ae heq]
  let u : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun β => S.indicator (fun x => ‖d β x‖)
  have hunonneg : ∀ β x, 0 ≤ u β x := by
    intro β x
    by_cases hx : x ∈ S <;> simp [u, hx]
  have hdom : ∀ᵐ x ∂volume,
      ‖g x‖ ≤ ((2 : ℝ) ^ k * C) * ‖(∑ β ∈ multiIndices n k, u β) x‖ := by
    apply Eventually.of_forall
    intro x
    have hsum : 0 ≤ ∑ β ∈ multiIndices n k, u β x :=
      Finset.sum_nonneg fun β _ => hunonneg β x
    simp only [Finset.sum_apply, Real.norm_of_nonneg hsum]
    by_cases hx : x ∈ S
    · simpa [A, u, hx] using hgbound x
    · simpa [A, u, hx] using hgbound x
  have hu : ∀ β ∈ multiIndices n k, AEStronglyMeasurable (u β) volume := by
    intro β hβ
    have hdeg : ∑ i, β i ≤ k := (Finset.mem_filter.mp hβ).2
    exact (hd β hdeg).2.aestronglyMeasurable.norm.indicator hS
  calc
    eLpNorm g p volume ≤ ENNReal.ofReal ((2 : ℝ) ^ k * C) *
        eLpNorm (∑ β ∈ multiIndices n k, u β) p volume :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom p
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ k * C) *
        ∑ β ∈ multiIndices n k, eLpNorm (u β) p volume :=
      mul_le_mul le_rfl (eLpNorm_sum_le hu hp) (by positivity) (by positivity)
    _ = _ := by
      simp only [u, eLpNorm_indicator_eq_eLpNorm_restrict hS, eLpNorm_norm]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
      norm_num
      rfl

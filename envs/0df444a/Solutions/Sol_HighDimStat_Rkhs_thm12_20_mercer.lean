-- Prove2me | solution 1 for HighDimStat.Rkhs.thm12_20_mercer
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:19:17.951701+00:00
-- url     : https://prove2.me/submissions/ca971375-8c01-4748-9443-d2ad89240f1b

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace
open MeasureTheory

theorem aux_m1220_psd_one {Y : Type*} : IsPSDKernel (fun (_ : Y) (_ : Y) => (1 : ℝ)) := by
  refine ⟨fun _ _ => rfl, fun n x α => ?_⟩
  have h : ∑ i, ∑ j, α i * α j * (1 : ℝ) = (∑ i, α i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    simp
  rw [h]
  exact sq_nonneg _

end HighDimStat.Rkhs

open HighDimStat.Rkhs
open scoped RealInnerProductSpace
open MeasureTheory

theorem solution : ¬ (∀ {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (hKpsd : IsPSDKernel K)
    (hHS : Integrable (fun p : X × X => (K p.1 p.2) ^ 2) (P.prod P))
    (TK : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 P)
    (hTK : ∀ f : Lp ℝ 2 P, (TK f : X → ℝ) =ᵐ[P] fun x => ∫ z, K x z * (f z) ∂P),
    ∃ (ι : Type) (_ : Countable ι) (φ : HilbertBasis ι ℝ (Lp ℝ 2 P)) (μ : ι → ℝ),
      (∀ j, 0 ≤ μ j) ∧
      (∀ j, TK (φ j) = μ j • (φ j : Lp ℝ 2 P)) ∧
      (∀ x z, HasSum (fun j => μ j * (φ j : X → ℝ) x * (φ j : X → ℝ) z) (K x z)) ∧
      (∀ e : ℕ ≃ ι, TendstoUniformly (fun n : ℕ => fun p : X × X =>
          ∑ k ∈ Finset.range n, μ (e k) * (φ (e k) : X → ℝ) p.1 * (φ (e k) : X → ℝ) p.2)
        (Function.uncurry K) Filter.atTop)) := by
  intro H
  obtain ⟨ι, _, φ, μ, -, -, hsum, -⟩ :=
    H (X := PUnit) (0 : Measure PUnit) (fun _ _ => (1 : ℝ)) continuous_const
      aux_m1220_psd_one (by simp) 0 (fun f => by simp [Filter.EventuallyEq])
  have hempty : IsEmpty ι := by
    refine ⟨fun j => ?_⟩
    have h1 : ‖(φ j : Lp ℝ 2 (0 : Measure PUnit))‖ = 1 := φ.orthonormal.1 j
    rw [Lp.norm_measure_zero] at h1
    exact zero_ne_one h1
  have h := (hsum PUnit.unit PUnit.unit).unique hasSum_empty
  exact one_ne_zero h

-- Prove2me | solution 1 for JHolomorphic.exists_memLp_sum_mul_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T11:38:30.103491+00:00
-- url     : https://prove2.me/submissions/280087db-2d87-4e82-b3e4-cfe1e3aa9c93

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.OfBasis



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- Given `g, w` continuous on `B(0,ρ)` with `‖w‖ ≤ M ‖g‖` there, there is a bounded measurable
operator field `A` with `∑ gᵢ (A r)ᵢ = ∑ wᵢ rᵢ` on `B̄(0,ρ/2)`. -/
theorem exists_coeff_aux (n : ℕ) (ρ M : ℝ) (hρ : 0 < ρ) (g w : ℂ → EuclideanSpace ℂ (Fin n))
    (hg : ContinuousOn g (ball 0 ρ)) (hw : ContinuousOn w (ball 0 ρ))
    (hM : ∀ z ∈ ball (0 : ℂ) ρ, ‖w z‖ ≤ M * ‖g z‖) (p : ℝ≥0∞) :
    ∃ A : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n),
      MemLp A p (volume.restrict (ball 0 1)) ∧
      ∀ z ∈ closedBall (0 : ℂ) (ρ / 2), ∀ r : EuclideanSpace ℂ (Fin n),
        ∑ i, g z i * A z r i = ∑ i, w z i * r i := by
  set S : Set ℂ := closedBall 0 (ρ / 2)
  have hSρ : S ⊆ ball 0 ρ := closedBall_subset_ball (by linarith)
  let t : Fin n → Fin n → ℂ → ℂ := fun i j z =>
    ((‖g z‖ ^ 2)⁻¹ : ℝ) * w z i * (starRingEnd ℂ) (g z j)
  let s : Fin n → Fin n → ℂ → ℂ := fun i j => S.indicator (t i j)
  let E : Fin n → Fin n → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) := fun i j =>
    ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).smulRight
      (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ
  have hE : ∀ i j r, E i j r = r i • EuclideanSpace.single j (1 : ℂ) := fun _ _ _ => rfl
  let A : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) := fun z =>
    ∑ i, ∑ j, s i j z • E i j
  have hAr : ∀ z r k, A z r k = ∑ i, s i k z * r i := by
    intro z r k
    simp [A, hE, WithLp.ofLp_sum, EuclideanSpace.single_apply, Pi.single_apply, mul_comm]
  -- bound on the scalar coefficients
  have hs_bd : ∀ i j z, ‖s i j z‖ ≤ max M 0 := by
    intro i j z
    by_cases hz : z ∈ S
    · simp only [s, indicator_of_mem hz, t, norm_mul, Complex.norm_real, RCLike.norm_conj]
      have h1 : ‖w z i‖ ≤ ‖w z‖ := PiLp.norm_apply_le _ _
      have h2 : ‖g z j‖ ≤ ‖g z‖ := PiLp.norm_apply_le _ _
      have h3 := hM z (hSρ hz)
      rcases eq_or_ne ‖g z‖ 0 with h0 | h0
      · simp [h0]
      · have hpos : 0 < ‖g z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
        rw [Real.norm_of_nonneg (by positivity)]
        calc (‖g z‖ ^ 2)⁻¹ * ‖w z i‖ * ‖g z j‖ ≤ (‖g z‖ ^ 2)⁻¹ * (M * ‖g z‖) * ‖g z‖ := by
              exact mul_le_mul (mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)) h2
                (norm_nonneg _) (mul_nonneg (by positivity) ((norm_nonneg _).trans h3))
          _ = M := by field_simp
          _ ≤ max M 0 := le_max_left _ _
    · simp [s, indicator_of_notMem hz]
  refine ⟨A, ?_, ?_⟩
  · haveI : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 1)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have hsm : ∀ i j, AEStronglyMeasurable (s i j) volume := by
      intro i j
      refine (aestronglyMeasurable_indicator_iff measurableSet_closedBall).2 ?_
      have hgS : ContinuousOn g S := hg.mono hSρ
      have hwS : ContinuousOn w S := hw.mono hSρ
      have hgm : AEStronglyMeasurable g (volume.restrict S) :=
        hgS.aestronglyMeasurable measurableSet_closedBall
      have hwi : AEStronglyMeasurable (fun z => w z i) (volume.restrict S) :=
        ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).continuous.comp_continuousOn
          hwS).aestronglyMeasurable measurableSet_closedBall
      have hgj : AEStronglyMeasurable (fun z => (starRingEnd ℂ) (g z j)) (volume.restrict S) :=
        ((Complex.continuous_conj.comp
          (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).continuous).comp_continuousOn
          hgS).aestronglyMeasurable measurableSet_closedBall
      have hn2 : AEMeasurable (fun z => ‖g z‖ ^ 2) (volume.restrict S) :=
        ((continuous_norm.pow 2).comp_aestronglyMeasurable hgm).aemeasurable
      have hc : AEStronglyMeasurable (fun z => (((‖g z‖ ^ 2)⁻¹ : ℝ) : ℂ)) (volume.restrict S) :=
        (Complex.measurable_ofReal.comp_aemeasurable hn2.inv).aestronglyMeasurable
      exact (hc.mul hwi).mul hgj
    have hAm : AEStronglyMeasurable A volume := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hsm i j).smul_const _
    refine MemLp.of_bound hAm.restrict (∑ i, ∑ j, max M 0 * ‖E i j‖) (ae_of_all _ fun z => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hs_bd i j z) (norm_nonneg _)
  · intro z hz r
    simp only [hAr, s, indicator_of_mem hz, t]
    have hnorm : ∑ k, g z k * (starRingEnd ℂ) (g z k) = ((‖g z‖ ^ 2 : ℝ) : ℂ) := by
      have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (g z)
      rw [PiLp.inner_apply] at this
      push_cast
      refine Eq.trans ?_ this
      exact Finset.sum_congr rfl fun k _ => by
        simp [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hlhs : ∑ k, g z k * ∑ i, (((‖g z‖ ^ 2)⁻¹ : ℝ) : ℂ) * w z i * (starRingEnd ℂ) (g z k) * r i
        = (((‖g z‖ ^ 2)⁻¹ : ℝ) : ℂ) * (∑ k, g z k * (starRingEnd ℂ) (g z k)) *
          ∑ i, w z i * r i := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [hlhs, hnorm]
    rcases eq_or_ne ‖g z‖ 0 with h0 | h0
    · have hw0 : w z = 0 := by
        have := hM z (hSρ hz)
        rw [h0, mul_zero] at this
        exact norm_le_zero_iff.1 this
      simp [hw0]
    · have : (((‖g z‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((‖g z‖ ^ 2 : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity), Complex.ofReal_one]
      rw [this, one_mul]

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

theorem solution (n : ℕ) (ρ M : ℝ) (hρ : 0 < ρ) (g w : ℂ → EuclideanSpace ℂ (Fin n))
    (hg : ContinuousOn g (ball 0 ρ)) (hw : ContinuousOn w (ball 0 ρ))
    (hM : ∀ z ∈ ball (0 : ℂ) ρ, ‖w z‖ ≤ M * ‖g z‖) (p : ℝ≥0∞) :
    ∃ A : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n),
      MemLp A p (volume.restrict (ball 0 1)) ∧
      ∀ z ∈ closedBall (0 : ℂ) (ρ / 2), ∀ r : EuclideanSpace ℂ (Fin n),
        ∑ i, g z i * A z r i = ∑ i, w z i * r i :=
  exists_coeff_aux n ρ M hρ g w hg hw hM p

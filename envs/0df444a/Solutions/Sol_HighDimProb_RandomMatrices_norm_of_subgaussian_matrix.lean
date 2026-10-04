-- Prove2me | solution 1 for HighDimProb.RandomMatrices.norm_of_subgaussian_matrix
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:26:46.052598+00:00
-- url     : https://prove2.me/submissions/1b83f1b4-6ba4-4111-ade1-3efb1353112b

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Cex18e7

/-- The probability measure: Lebesgue measure restricted to `(0, 1]`. -/
noncomputable def P : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

instance : IsProbabilityMeasure P := ⟨by simp [P]⟩

theorem not_int_inv : ¬ Integrable (fun x : ℝ => x⁻¹) P := by
  intro h
  have h1 : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 h
  rw [intervalIntegrable_inv_iff] at h1
  rcases h1 with h1 | h1
  · norm_num at h1
  · exact h1 (by simp)

theorem bound (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ‖x⁻¹‖ ≤ t * Real.exp ((x⁻¹) ^ 2 / t ^ 2) := by
  set s := x⁻¹ / t with hs
  have hx : x⁻¹ = t * s := by rw [hs]; field_simp
  have he : (x⁻¹) ^ 2 / t ^ 2 = s ^ 2 := by rw [hs, div_pow]
  rw [he, Real.norm_eq_abs, hx, abs_mul, abs_of_pos ht]
  have h2 := Real.add_one_le_exp (s ^ 2)
  have h3 : |s| ≤ s ^ 2 + 1 := by
    have := sq_abs s
    nlinarith [abs_nonneg s, sq_nonneg (|s| - 1)]
  exact mul_le_mul_of_nonneg_left (h3.trans h2) ht.le

theorem sgn_zero :
    HighDimProb.Concentration.subgaussianNorm P (fun ω => ω⁻¹) = 0 := by
  unfold HighDimProb.Concentration.subgaussianNorm
  have : {t : ℝ | 0 < t ∧ Integrable (fun ω : ℝ => Real.exp ((ω⁻¹) ^ 2 / t ^ 2)) P ∧
      ∫ ω, Real.exp ((ω⁻¹) ^ 2 / t ^ 2) ∂P ≤ 2} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro ht hint _
    apply not_int_inv
    refine Integrable.mono' (hint.const_mul t) measurable_inv.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => bound t ht x)
  rw [this, Real.sInf_empty]

theorem mean_zero : ∫ ω, ω⁻¹ ∂P = 0 := integral_undef not_int_inv

theorem opnorm_pos (x : ℝ) (hx : x ≠ 0) :
    ¬ HighDimProb.RandomMatrices.matrixOpNorm
      (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => x⁻¹)) ≤ 0 := by
  intro h
  unfold HighDimProb.RandomMatrices.matrixOpNorm at h
  have h0 := norm_le_zero_iff.1 h
  have h1 : Matrix.toEuclideanLin (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => x⁻¹)) = 0 := by
    have := congrArg (fun f : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) =>
      (f : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1))) h0
    simpa using this
  have h2 : (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => x⁻¹)) = 0 :=
    (LinearEquiv.map_eq_zero_iff Matrix.toEuclideanLin).1 h1
  have h3 := congrFun (congrFun h2 0) 0
  simp at h3
  exact hx h3

theorem cex : ¬ (∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Ω → Matrix (Fin m) (Fin n) ℝ)
        (hindep : iIndepFun (fun p : Fin m × Fin n => fun ω => A ω p.1 p.2) Prob)
        (hmean : ∀ i j, ∫ ω, A ω i j ∂Prob = 0)
        (K : ℝ) (hK : ∀ i j, HighDimProb.Concentration.subgaussianNorm Prob (fun ω => A ω i j) ≤ K)
        (t : ℝ) (ht : 0 < t),
        1 - 2 * Real.exp (-(t ^ 2)) ≤
          Prob.real {ω | HighDimProb.RandomMatrices.matrixOpNorm (A ω) ≤ C * K * (Real.sqrt m + Real.sqrt n + t)}) := by
  rintro ⟨C, _, hC⟩
  have key := hC (Ω := ℝ) P (m := 1) (n := 1) one_pos one_pos
    (fun ω => Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => ω⁻¹))
    iIndepFun.of_subsingleton
    (fun _ _ => by simpa using mean_zero)
    0 (fun _ _ => by simp [sgn_zero]) 1 one_pos
  have hsub : {ω : ℝ | HighDimProb.RandomMatrices.matrixOpNorm
      ((fun ω => Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => ω⁻¹)) ω) ≤
        C * 0 * (Real.sqrt ((1 : ℕ) : ℝ) + Real.sqrt ((1 : ℕ) : ℝ) + 1)} ⊆ {0} := by
    intro ω hω
    simp only [mul_zero, zero_mul, Set.mem_setOf_eq] at hω
    by_contra hne
    exact opnorm_pos ω hne hω
  have hzero : P.real {ω : ℝ | HighDimProb.RandomMatrices.matrixOpNorm
      ((fun ω => Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => ω⁻¹)) ω) ≤
        C * 0 * (Real.sqrt ((1 : ℕ) : ℝ) + Real.sqrt ((1 : ℕ) : ℝ) + 1)} = 0 := by
    apply measureReal_mono_null hsub
    simp [P]
  rw [hzero, one_pow] at key
  have he : Real.exp (-1) < 1 / 2 := by
    have h1 := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  linarith

end Cex18e7

theorem solution : ¬ (∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Ω → Matrix (Fin m) (Fin n) ℝ)
        (hindep : iIndepFun (fun p : Fin m × Fin n => fun ω => A ω p.1 p.2) Prob)
        (hmean : ∀ i j, ∫ ω, A ω i j ∂Prob = 0)
        (K : ℝ) (hK : ∀ i j, HighDimProb.Concentration.subgaussianNorm Prob (fun ω => A ω i j) ≤ K)
        (t : ℝ) (ht : 0 < t),
        1 - 2 * Real.exp (-(t ^ 2)) ≤
          Prob.real {ω | HighDimProb.RandomMatrices.matrixOpNorm (A ω) ≤ C * K * (Real.sqrt m + Real.sqrt n + t)}) := by
  exact Cex18e7.cex

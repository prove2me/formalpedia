-- Prove2me | solution 1 for GinibrePermanent977.Anticoncentration.corollary_3_3_two_coordinate_compression
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:34:36.909224+00:00
-- url     : https://prove2.me/submissions/c5a1869a-8f1e-4d16-88c9-dcdc2d20a634

import Theorems.Thm_GinibrePermanent977_Anticoncentration_lemma_3_1_quadratic_scaling
import Theorems.Thm_GinibrePermanent977_Anticoncentration_lemma_3_2_geometric_interpolation
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexOrder
set_option autoImplicit false
namespace GinibrePermanent977.Anticoncentration

lemma continuous_bilin_parameters {d k : ℕ} (a b : Fin k → ℝ) :
    Continuous (fun q : (Fin d → Fin d → ℝ) × (Fin d → Fin k → ℝ) =>
      bilinChar (Matrix.of q.1) (Matrix.of q.2) a b) := by
  unfold bilinChar
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro q
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · intro q
    exact Filter.Eventually.of_forall (fun p => by simp [Complex.norm_exp])
  · exact integrable_const 1
  · apply Filter.Eventually.of_forall
    intro p
    fun_prop

lemma norm_bilinChar_le_one {d k : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k → ℝ) : ‖bilinChar T L a b‖ ≤ 1 := by
  unfold bilinChar
  have h := norm_integral_le_of_norm_le_const (C := (1 : ℝ))
    (μ := (SmoothBerr.stdGaussianVec d).prod (SmoothBerr.stdGaussianVec d))
    (f := fun p : (Fin d → ℝ) × (Fin d → ℝ) => Complex.exp (Complex.I *
      ((p.1 ⬝ᵥ (T *ᵥ p.2) + p.1 ⬝ᵥ (L *ᵥ b) + p.2 ⬝ᵥ (L *ᵥ a) : ℝ) : ℂ)))
    (Filter.Eventually.of_forall (fun p => by simp [Complex.norm_exp]))
  simpa using h

lemma weighted_integral_le {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (∫ x, f x^θ*g x^(1-θ) ∂ρ) ≤ (∫ x, f x ∂ρ)^θ*(∫ x, g x ∂ρ)^(1-θ) := by
  by_cases he0 : θ = 0
  · simp [he0]
  by_cases he1 : θ = 1
  · simp [he1]
  have ht : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm he0)
  have hs : 0 < 1-θ := sub_pos.mpr (lt_of_le_of_ne hθ1 he1)
  have hfg : (1/θ).HolderConjugate (1/(1-θ)) :=
    Real.holderConjugate_one_div ht hs (by ring)
  have hmfp : Measurable (fun x => f x^θ) := by fun_prop
  have hmgp : Measurable (fun x => g x^(1-θ)) := by fun_prop
  have hfp : MemLp (fun x => f x^θ) (ENNReal.ofReal (1/θ)) ρ := by
    apply MemLp.of_bound hmfp.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hf0 x) _)]
    exact Real.rpow_le_one (hf0 x) (hf1 x) hθ0
  have hgp : MemLp (fun x => g x^(1-θ)) (ENNReal.ofReal (1/(1-θ))) ρ := by
    apply MemLp.of_bound hmgp.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hg0 x) _)]
    exact Real.rpow_le_one (hg0 x) (hg1 x) hs.le
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hfg
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hf0 x) θ))
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hg0 x) (1-θ))) hfp hgp
  simp_rw [← Real.rpow_mul (hf0 _), ← Real.rpow_mul (hg0 _)] at h
  simpa [ht.ne', hs.ne'] using h

end GinibrePermanent977.Anticoncentration

open GinibrePermanent977.Anticoncentration

theorem solution {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (ρ : Measure ((Fin d → Fin d → ℝ) × (Fin d → Fin k → ℝ))) [IsProbabilityMeasure ρ]
    (a b : Fin k → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∫ q, ‖bilinChar (Matrix.of q.1) (Matrix.of q.2) (Real.sqrt θ • a)
        (Real.sqrt (1 - θ) • b)‖ ∂ρ ≤
      (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) a 0).re ∂ρ) ^ θ *
        (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) 0 b).re ∂ρ) ^ (1 - θ) ∧
    (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) a 0).re ∂ρ) ^ θ *
        (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) 0 b).re ∂ρ) ^ (1 - θ) ≤
      max (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) a 0).re ∂ρ)
        (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) 0 b).re ∂ρ) := by
  let f := fun q : (Fin d → Fin d → ℝ) × (Fin d → Fin k → ℝ) =>
    (bilinChar (Matrix.of q.1) (Matrix.of q.2) a 0).re
  let g := fun q : (Fin d → Fin d → ℝ) × (Fin d → Fin k → ℝ) =>
    (bilinChar (Matrix.of q.1) (Matrix.of q.2) 0 b).re
  have hf : Measurable f := (Complex.continuous_re.comp (continuous_bilin_parameters a 0)).measurable
  have hg : Measurable g := (Complex.continuous_re.comp (continuous_bilin_parameters 0 b)).measurable
  have hf0 (q) : 0 ≤ f q := (Complex.pos_iff.mp
    (lemma_3_1_quadratic_scaling hd hk (Matrix.of q.1) (Matrix.of q.2) a b).1).1.le
  have hg0 (q) : 0 ≤ g q := (Complex.pos_iff.mp
    (lemma_3_1_quadratic_scaling hd hk (Matrix.of q.1) (Matrix.of q.2) a b).2.1).1.le
  have hf1 (q) : f q ≤ 1 := (Complex.re_le_norm _).trans (norm_bilinChar_le_one _ _ a 0)
  have hg1 (q) : g q ≤ 1 := (Complex.re_le_norm _).trans (norm_bilinChar_le_one _ _ 0 b)
  constructor
  · have heq : (∫ q, ‖bilinChar (Matrix.of q.1) (Matrix.of q.2) (Real.sqrt θ • a)
        (Real.sqrt (1-θ) • b)‖ ∂ρ) = ∫ q, f q^θ*g q^(1-θ) ∂ρ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro q
      exact lemma_3_2_geometric_interpolation hd hk (Matrix.of q.1) (Matrix.of q.2) a b θ hθ0 hθ1
    rw [heq]
    exact weighted_integral_le ρ f g hf hg hf0 hg0 hf1 hg1 θ hθ0 hθ1
  · have hIf : 0 ≤ ∫ q, f q ∂ρ := integral_nonneg hf0
    have hIg : 0 ≤ ∫ q, g q ∂ρ := integral_nonneg hg0
    apply (Real.geom_mean_le_arith_mean2_weighted hθ0 (sub_nonneg.mpr hθ1) hIf hIg (by ring)).trans
    calc
      θ*(∫ q, f q ∂ρ)+(1-θ)*(∫ q, g q ∂ρ) ≤
          θ*max (∫ q, f q ∂ρ) (∫ q, g q ∂ρ)+(1-θ)*max (∫ q, f q ∂ρ) (∫ q, g q ∂ρ) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hθ0)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr hθ1))
      _ = max (∫ q, f q ∂ρ) (∫ q, g q ∂ρ) := by ring

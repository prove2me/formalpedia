-- Prove2me | solution 1 for OAI.IndependentProducts.gaussian_bilinear_excess
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:14:03.456333+00:00
-- url     : https://prove2.me/submissions/ad7e74f3-e632-432f-883d-311834a9acae

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/GaussianMoments.lean:L265-L304
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.gaussian_bilinear_excess. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Theorems.Thm_OAI_IndependentProducts_gaussian_integral_fourth
import Theorems.Thm_OAI_IndependentProducts_map_gaussian_weighted_sum
import Theorems.Thm_OAI_IndependentProducts_weighted_sum_tail

-- ---- from OAI.Analysis.ProductSpaces.ScalarBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

lemma gaussianTail_nonneg (r : ℝ) : 0 ≤ gaussianTail r := ENNReal.toReal_nonneg

lemma gaussian_integral_sq : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id'.aemeasurable] at h
  simpa using h

section SecondMoment
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

variable [IsProbabilityMeasure μ]

end SecondMoment
end IndependentProducts

namespace IndependentProducts

section GaussianSum
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [DecidableEq ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

variable [Fintype ι]

end GaussianSum
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.GaussianMoments ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts
section WeightedMoments
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
variable {P : Measure Ω}

variable [IsProbabilityMeasure P]

end WeightedMoments
section GaussianVector
variable {ι : Type uι} [Fintype ι]

lemma gaussian_eval_hasLaw (i : ι) : HasLaw (fun x : ι → ℝ => x i) (gaussianReal 0 1) gaussianVector :=
  (measurePreserving_eval (fun _ => gaussianReal 0 1) i).hasLaw

lemma gaussian_square_memLp : MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 4).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert h using 1
  funext x
  change (x ^ 2) ^ 2 = |x| ^ 4
  rw [← pow_mul]
  norm_num
  rw [← abs_pow, abs_of_nonneg (by positivity)]

lemma gaussian_quadratic_tail (a : ι → ℝ) (ha : 0 < ∑ i, a i ^ 2) :
    1 / 12 ≤ (gaussianVector (ι := ι)).real
      {x | (∑ i, a i ^ 2) / 2 ≤ ∑ i, a i ^ 2 * x i ^ 2} := by
  have hU : ∀ i : ι, MemLp (fun x : ι → ℝ => x i ^ 2) 2 gaussianVector := fun i =>
    gaussian_square_memLp.comp_measurePreserving
      (measurePreserving_eval (fun _ => gaussianReal 0 1) i)
  have hm : ∀ i : ι, (∫ x : ι → ℝ, x i ^ 2 ∂gaussianVector) = 1 := by
    intro i
    exact (gaussian_eval_hasLaw i).integral_comp (by fun_prop) |>.trans gaussian_integral_sq
  have hm2 : ∀ i : ι, (∫ x : ι → ℝ, (x i ^ 2) ^ 2 ∂gaussianVector) ≤ 3 := by
    intro i
    have he : (∫ x : ι → ℝ, (x i ^ 2) ^ 2 ∂gaussianVector) = 3 := by
      exact ((gaussian_eval_hasLaw i).integral_comp (f := fun x : ℝ => (x ^ 2) ^ 2)
        (by fun_prop)).trans (by simpa only [← pow_mul, Nat.reduceMul] using gaussian_integral_fourth)
    exact he.le
  have hh := weighted_sum_tail a (fun i (x : ι → ℝ) => x i ^ 2) hU
    (fun _ => by fun_prop) (fun _ _ => sq_nonneg _) hm 3 (by norm_num) hm2 ha
  norm_num at hh ⊢
  exact hh

end GaussianVector
end IndependentProducts

namespace IndependentProducts

lemma excess_nonneg (t r z : ℝ) : 0 ≤ excess t r z := le_max_right _ _

lemma integrable_excess {Ω : Type uΩ} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Integrable X P) (t r : ℝ) :
    Integrable (fun ω => excess t r (X ω)) P :=
  ((hX.abs.const_mul t).sub (integrable_const r)).sup (integrable_const 0)

lemma integral_excess_ge_tail {Ω : Type uΩ} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P)
    (hXm : Measurable X) {t : ℝ} (ht : 0 ≤ t) (r k : ℝ) (hk : 0 ≤ k) :
    P.real {ω | k ≤ |X ω|} * excess t r k ≤ ∫ ω, excess t r (X ω) ∂P := by
  let A : Set Ω := {ω | k ≤ |X ω|}
  have hA : MeasurableSet A := measurableSet_le measurable_const hXm.abs
  calc
    _ = ∫ ω, A.indicator (fun _ => excess t r k) ω ∂P := by simp [integral_indicator hA, mul_comm, A]
    _ ≤ ∫ ω, excess t r (X ω) ∂P := by
      apply integral_mono ((integrable_const _).indicator hA) (integrable_excess hX t r)
      intro ω
      by_cases hω : ω ∈ A
      · simp only [Set.indicator_of_mem hω]
        apply max_le_max_right
        have hh : k ≤ |X ω| := hω
        exact sub_le_sub_right (by simpa [abs_of_nonneg hk] using mul_le_mul_of_nonneg_left hh ht) _
      · simp only [Set.indicator_of_notMem hω]
        exact excess_nonneg _ _ _

end IndependentProducts

namespace IndependentProducts

lemma gaussian_sqrt_scale (v : ℝ≥0) :
    HasLaw (fun x : ℝ => Real.sqrt (v : ℝ) * x) (gaussianReal 0 v) (gaussianReal 0 1) := by
  refine ⟨by fun_prop, ?_⟩
  rw [gaussianReal_map_const_mul]
  apply congrArg₂ gaussianReal
  · ring
  · ext
    change (Real.sqrt (v : ℝ)) ^ 2 * 1 = (v : ℝ)
    rw [Real.sq_sqrt v.coe_nonneg, mul_one]

lemma gaussian_tail_variance_lower (v : ℝ≥0) (K s : ℝ) (hK : 0 ≤ K) (hs : 0 ≤ s)
    (hv : s ^ 2 / 2 ≤ (v : ℝ)) :
    gaussianTail (Real.sqrt 2 * K) ≤ (gaussianReal 0 v).real {x | K * s ≤ |x|} := by
  rw [← (gaussian_sqrt_scale v).measureReal_eq (measurableSet_le measurable_const (by fun_prop))]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  change Real.sqrt 2 * K ≤ |x| at hx
  change K * s ≤ |Real.sqrt (v : ℝ) * x|
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsv := Real.sq_sqrt v.coe_nonneg
  have htwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hscale : s ≤ Real.sqrt (v : ℝ) * Real.sqrt 2 := by
    have hp : (Real.sqrt (v : ℝ) * Real.sqrt 2) ^ 2 = (v : ℝ) * 2 := by
      rw [mul_pow, hsv, htwo]
    apply (sq_le_sq₀ hs (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    nlinarith [hp]
  calc
    K * s ≤ K * (Real.sqrt (v : ℝ) * Real.sqrt 2) := mul_le_mul_of_nonneg_left hscale hK
    _ = Real.sqrt (v : ℝ) * (Real.sqrt 2 * K) := by ring
    _ ≤ Real.sqrt (v : ℝ) * |x| := mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _)

section GaussianFinite
variable {ι : Type uι} [Fintype ι]

lemma gaussian_weighted_hasLaw (a : ι → ℝ) :
    HasLaw (fun x : ι → ℝ => ∑ i, a i * x i)
      (gaussianReal 0 (NNReal.mk (∑ i, a i ^ 2) (Finset.sum_nonneg fun _ _ => sq_nonneg _))) gaussianVector := by
  classical
  refine ⟨(by fun_prop : Measurable (fun x : ι → ℝ => ∑ i, a i * x i)).aemeasurable, ?_⟩
  unfold gaussianVector
  rw [map_gaussian_weighted_sum]
  congr 1
  ext
  simp

lemma gaussian_weighted_excess (a : ι → ℝ) (K s t r : ℝ)
    (hK : 0 ≤ K) (hs : 0 ≤ s) (ht : 0 ≤ t) (hv : s ^ 2 / 2 ≤ ∑ i, a i ^ 2) :
    gaussianTail (Real.sqrt 2 * K) * excess t r (K * s) ≤
      ∫ x : ι → ℝ, excess t r (∑ i, a i * x i) ∂gaussianVector := by
  have hm : Measurable (fun x : ι → ℝ => ∑ i, a i * x i) := by fun_prop
  have hint : Integrable (fun x : ι → ℝ => ∑ i, a i * x i) gaussianVector :=
    (gaussian_weighted_hasLaw a).hasGaussianLaw.integrable
  have htail : gaussianTail (Real.sqrt 2 * K) ≤
      gaussianVector.real {x : ι → ℝ | K * s ≤ |∑ i, a i * x i|} := by
    rw [(gaussian_weighted_hasLaw a).measureReal_eq (p := fun z : ℝ => K * s ≤ |z|)
      (measurableSet_le measurable_const (by fun_prop))]
    exact gaussian_tail_variance_lower _ K s hK hs hv
  exact (mul_le_mul_of_nonneg_right htail (excess_nonneg _ _ _)).trans
    (integral_excess_ge_tail _ hint hm ht r (K * s) (mul_nonneg hK hs))

lemma integrable_gaussian_bilinear (a : ι → ℝ) :
    Integrable (fun z : (ι → ℝ) × (ι → ℝ) => ∑ i, a i * z.1 i * z.2 i)
      (gaussianVector.prod gaussianVector) := by
  apply integrable_finsetSum
  intro i _
  have hi := (gaussian_eval_hasLaw i).hasGaussianLaw.integrable
  exact (hi.const_mul _).mul_prod hi

lemma gaussian_bilinear_excess (a : ι → ℝ) (K t r : ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (gaussianTail (Real.sqrt 2 * K) / 12) *
      excess t r (K * Real.sqrt (∑ i, a i ^ 2)) ≤
      ∫ z : (ι → ℝ) × (ι → ℝ), excess t r (∑ i, a i * z.1 i * z.2 i)
        ∂gaussianVector.prod gaussianVector := by
  let S : ℝ := ∑ i, a i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  change (gaussianTail (Real.sqrt 2 * K) / 12) * excess t r (K * Real.sqrt S) ≤ _
  by_cases hS0 : S = 0
  · simp only [hS0, Real.sqrt_zero, mul_zero, excess, abs_zero, zero_sub,
      max_eq_right (neg_nonpos.mpr hr), mul_zero]
    exact integral_nonneg (fun _ => excess_nonneg _ _ _)
  have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
  let A : Set (ι → ℝ) := {x | S / 2 ≤ ∑ i, a i ^ 2 * x i ^ 2}
  have hA : MeasurableSet A := measurableSet_le measurable_const (by fun_prop)
  let c := gaussianTail (Real.sqrt 2 * K) * excess t r (K * Real.sqrt S)
  have hc : 0 ≤ c := mul_nonneg (gaussianTail_nonneg _) (excess_nonneg _ _ _)
  have hint := integrable_excess (integrable_gaussian_bilinear a) t r
  rw [integral_prod _ hint]
  calc
    _ ≤ gaussianVector.real A * c := by
      have hp := gaussian_quadratic_tail a hSp
      have hh := mul_le_mul_of_nonneg_right hp hc
      dsimp [c, A, S] at hh ⊢
      nlinarith
    _ = ∫ x : ι → ℝ, A.indicator (fun _ => c) x ∂gaussianVector := by
      simp [integral_indicator hA, mul_comm]
    _ ≤ ∫ x : ι → ℝ, ∫ y : ι → ℝ, excess t r (∑ i, a i * x i * y i)
        ∂gaussianVector ∂gaussianVector := by
      apply integral_mono ((integrable_const _).indicator hA) hint.integral_prod_left
      intro x
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx]
        apply gaussian_weighted_excess (fun i => a i * x i) K (Real.sqrt S) t r hK
          (Real.sqrt_nonneg S) ht
        rw [Real.sq_sqrt hS]
        simpa only [A, Set.mem_ofPred_eq, mul_pow] using hx
      · simp only [Set.indicator_of_notMem hx]
        exact integral_nonneg (fun _ => excess_nonneg _ _ _)

end GaussianFinite
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι
variable {ι : Type uι} [Fintype ι]

theorem solution (a : ι → ℝ) (K t r : ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (gaussianTail (Real.sqrt 2 * K) / 12) *
      excess t r (K * Real.sqrt (∑ i, a i ^ 2)) ≤
      ∫ z : (ι → ℝ) × (ι → ℝ), excess t r (∑ i, a i * z.1 i * z.2 i)
        ∂gaussianVector.prod gaussianVector := by
  first
    | exact OAI.IndependentProducts.gaussian_bilinear_excess a K t r hK ht hr
    | exact OAI.IndependentProducts.gaussian_bilinear_excess
    | (apply OAI.IndependentProducts.gaussian_bilinear_excess <;> assumption)
    | (intros; apply OAI.IndependentProducts.gaussian_bilinear_excess <;> assumption)

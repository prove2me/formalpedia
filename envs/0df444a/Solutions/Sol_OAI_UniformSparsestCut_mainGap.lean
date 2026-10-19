-- Prove2me | solution 1 for OAI.UniformSparsestCut.mainGap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:49:04.330368+00:00
-- url     : https://prove2.me/submissions/699a551e-6c4f-4f6d-9ff8-be7e6ee98ca3

import Mathlib
import Definitions.Def_UniformSparsestCut
import Definitions.Def_OAIQWUS000
import Theorems.Thm_OAI_UniformSparsestCut_SourceUniform_instance_exists

section
-- module Solutions.OAIQW_UniformSparsestCut.GaussianTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianTools

section Concentration
variable {Ω : Type u1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma subgaussian_abs_tail {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {sample | u < |X sample|} ≤ 2 * Real.exp (-u^2 / (2 * c)) := by
  have hsub : {sample | u < |X sample|} ⊆ {sample | u ≤ X sample} ∪ {sample | u ≤ -X sample} := by
    intro sample hω
    change u < |X sample| at hω
    rcases lt_abs.mp hω with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  calc
    _ ≤ μ.real ({sample | u ≤ X sample} ∪ {sample | u ≤ -X sample}) := measureReal_mono hsub
    _ ≤ μ.real {sample | u ≤ X sample} + μ.real {sample | u ≤ -X sample} := measureReal_union_le _ _
    _ ≤ Real.exp (-u^2 / (2 * c)) + Real.exp (-u^2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hu) (hX.neg.measure_ge_le hu)
    _ = _ := by ring

theorem bounded_concentration {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ)
    {B : ℝ} (hB : 0 < B) (hbound : ∀ i, ∀ᵐ sample ∂μ, |X i sample| ≤ B)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {sample | u < |(∑ i, (X i sample - ∫ z, X i z ∂μ)) / (n : ℝ)|} ≤
      2 * Real.exp (-(n : ℝ) * u^2 / (2 * B^2)) := by
  classical
  let Y : Fin n → Ω → ℝ := fun i sample => X i sample - ∫ z, X i z ∂μ
  have hY (i : Fin n) : HasSubgaussianMGF (Y i) ⟨B^2, sq_nonneg B⟩ μ := by
    have hh := hasSubgaussianMGF_of_mem_Icc (hmeas i)
      (show ∀ᵐ sample ∂μ, X i sample ∈ Icc (-B) B by
        filter_upwards [hbound i] with sample hω using abs_le.mp hω)
    have hc : ((‖B - -B‖₊ / 2) ^ 2) = (⟨B^2, sq_nonneg B⟩ : ℝ≥0) := by
      ext
      change (‖B - -B‖ / 2) ^ 2 = B ^ 2
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith : 0 ≤ B - -B)]
      ring
    exact (congrArg (fun variance : ℝ≥0 => HasSubgaussianMGF (Y i) variance μ) hc).mp hh
  have hYi : iIndepFun Y μ := hind.comp (fun i z => z - ∫ z, X i z ∂μ) (fun i => by fun_prop)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hYi
    (s := Finset.univ) (fun i hi => hY i)
  have havg := hsum.const_mul ((n : ℝ)⁻¹)
  have htail := subgaussian_abs_tail havg hu
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  convert htail using 1
  · congr 1; ext sample
    simp only [Y, div_eq_mul_inv, mul_comm]
  · congr 2
    have hc : ((⟨(n : ℝ)⁻¹ ^ 2, sq_nonneg _⟩ : ℝ≥0) *
        ∑ _ : Fin n, (⟨B^2, sq_nonneg _⟩ : ℝ≥0) : ℝ≥0) =
        (⟨B^2 / n, div_nonneg (sq_nonneg _) (by positivity)⟩ : ℝ≥0) := by
      apply NNReal.eq
      change (n : ℝ)⁻¹ ^ 2 * ↑(∑ _ : Fin n, (⟨B^2, sq_nonneg _⟩ : ℝ≥0)) = B^2 / n
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      change (n : ℝ)⁻¹ ^ 2 * ↑(n • (⟨B^2, sq_nonneg _⟩ : ℝ≥0)) = B^2 / n
      simp only [nsmul_eq_mul]
      change (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * B^2) = B^2 / n
      field_simp

    change -(n : ℝ) * u^2 / (2 * B^2) =
      -u^2 / (2 * (((⟨(n : ℝ)⁻¹ ^ 2, sq_nonneg _⟩ : ℝ≥0) *
        ∑ _ : Fin n, (⟨B^2, sq_nonneg _⟩ : ℝ≥0) : ℝ≥0) : ℝ))
    rw [hc]
    change -(n : ℝ) * u^2 / (2 * B^2) = -u^2 / (2 * (B^2 / n))
    field_simp

end Concentration

section Fourier
variable {E : Type u2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_cos_integrable (w : E) :
    Integrable (fun g : E => Real.cos (inner ℝ g w)) (stdGaussian E) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (by fun_prop : Continuous (fun g : E => Real.cos (inner ℝ g w))).aestronglyMeasurable
  · exact ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)

lemma gaussian_cos (w : E) :
    (∫ g : E, Real.cos (inner ℝ g w) ∂stdGaussian E) =
      Real.exp (-‖w‖^2 / 2) := by
  have hh := congrArg Complex.re (charFun_stdGaussian w)
  rw [charFun_apply] at hh
  have hf : Integrable (fun g : E => Complex.exp ((inner ℝ g w : ℂ) * Complex.I))
      (stdGaussian E) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact (by fun_prop : Continuous (fun g : E => Complex.exp ((inner ℝ g w : ℂ) * Complex.I))).aestronglyMeasurable
    · exact ae_of_all _ (fun g => by simp)
  have hi := Complex.reCLM.integral_comp_comm hf
  change (∫ g : E, (Complex.exp ((inner ℝ g w : ℂ) * Complex.I)).re ∂stdGaussian E) =
    (∫ g : E, Complex.exp ((inner ℝ g w : ℂ) * Complex.I) ∂stdGaussian E).re at hi
  rw [← hi] at hh
  simpa [Complex.exp_re, pow_two, Complex.mul_re, Complex.mul_im] using hh

lemma gaussian_linear_sin_integrable (w v : E) :
    Integrable (fun g : E => inner ℝ g v * Real.sin (inner ℝ g w)) (stdGaussian E) := by
  apply Integrable.mono' ((IsGaussian.integrable_id (μ := stdGaussian E)).norm.mul_const ‖v‖)
  · exact (by fun_prop : Continuous (fun g : E => inner ℝ g v * Real.sin (inner ℝ g w))).aestronglyMeasurable
  · filter_upwards [] with g
    simp only [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |inner ℝ g v| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ ≤ ‖g‖ * ‖v‖ := by simpa using abs_real_inner_le_norm g v

lemma gaussian_linear_sin (w v : E) :
    (∫ g : E, inner ℝ g v * Real.sin (inner ℝ g w) ∂stdGaussian E) =
      inner ℝ w v * Real.exp (-‖w‖^2 / 2) := by
  let F : ℝ → E → ℝ := fun t g => Real.cos (inner ℝ g (w + t • v))
  let F' : ℝ → E → ℝ := fun t g => -Real.sin (inner ℝ g (w + t • v)) * inner ℝ g v
  have hd (g : E) (t : ℝ) : HasDerivAt (fun t => F t g) (F' t g) t := by
    have h := ((hasDerivAt_const t w).add ((hasDerivAt_id t).smul_const v))
    have hh := ((hasDerivAt_const t g).inner ℝ h).cos
    simpa [F, F'] using hh
  have hbound (g : E) (t : ℝ) : ‖F' t g‖ ≤ ‖g‖ * ‖v‖ := by
    simp only [F', Real.norm_eq_abs, abs_mul, abs_neg]
    calc
      _ ≤ 1 * |inner ℝ g v| := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
      _ ≤ ‖g‖ * ‖v‖ := by simpa using abs_real_inner_le_norm g v
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := stdGaussian E) (F := F) (F' := F') (bound := fun g => ‖g‖ * ‖v‖)
    (s := Set.univ) (x₀ := (0 : ℝ)) (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun t =>
      (show Continuous (F t) by dsimp [F]; fun_prop).aestronglyMeasurable))
    (by simpa [F] using gaussian_cos_integrable w)
    (show AEStronglyMeasurable (F' 0) (stdGaussian E) from
      (show Continuous (F' 0) by dsimp [F']; fun_prop).aestronglyMeasurable)
    (ae_of_all _ (fun g t _ => hbound g t))
    ((IsGaussian.integrable_id (μ := stdGaussian E)).norm.mul_const ‖v‖)
    (ae_of_all _ (fun g t _ => hd g t))
  have ht := (((hasDerivAt_const (0 : ℝ) w).add
    ((hasDerivAt_id (0 : ℝ)).smul_const v)).norm_sq.neg.div_const 2).exp
  have heq : (fun t => ∫ g : E, F t g ∂stdGaussian E) =
      (fun t : ℝ => Real.exp (-‖w + t • v‖^2 / 2)) := by
    funext t
    exact gaussian_cos _
  rw [heq] at hi
  have huniq := hi.2.unique ht
  simp only [F', zero_smul, add_zero, one_smul, zero_add] at huniq
  have hneg : (∫ g : E, -Real.sin (inner ℝ g w) * inner ℝ g v ∂stdGaussian E) =
      -(∫ g : E, inner ℝ g v * Real.sin (inner ℝ g w) ∂stdGaussian E) := by
    rw [← integral_neg]
    congr 1
    funext g
    ring
  rw [hneg] at huniq
  dsimp at huniq
  simp only [zero_smul, add_zero] at huniq
  nlinarith

lemma gaussian_vector_sin_integrable (w : E) :
    Integrable (fun g : E => Real.sin (inner ℝ g w) • g) (stdGaussian E) := by
  exact (IsGaussian.integrable_id (μ := stdGaussian E)).bdd_smul 1
    (by fun_prop) (ae_of_all _ (fun g => by simpa using Real.abs_sin_le_one (inner ℝ g w)))

lemma gaussian_vector_sin (w : E) :
    (∫ g : E, Real.sin (inner ℝ g w) • g ∂stdGaussian E) =
      Real.exp (-‖w‖^2 / 2) • w := by
  apply ext_inner_left ℝ
  intro v
  rw [← integral_inner (gaussian_vector_sin_integrable w), inner_smul_right]
  simp only [inner_smul_right]
  simpa only [real_inner_comm, mul_comm] using gaussian_linear_sin w v

lemma gaussian_inner_law (v : E) :
    (stdGaussian E).map (fun g => inner ℝ v g) =
      gaussianReal 0 (⟨‖v‖^2, sq_nonneg _⟩ : ℝ≥0) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ v)
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm] at h
  have hvariance : (‖v‖^2).toNNReal = (⟨‖v‖^2, sq_nonneg _⟩ : ℝ≥0) :=
    Real.toNNReal_of_nonneg (sq_nonneg _)
  exact h.trans (congrArg (gaussianReal 0) hvariance)

lemma gaussian_inner_sq (v : E) :
    (∫ g : E, (inner ℝ v g)^2 ∂stdGaussian E) = ‖v‖^2 := by
  have h := variance_dual_stdGaussian (innerSL ℝ v)
  rw [variance_eq_integral (by fun_prop), integral_strongDual_stdGaussian] at h
  simpa only [sub_zero, innerSL_apply_norm, innerSL_apply_apply] using h

lemma gaussian_inner_subgaussian (v : E) :
    HasSubgaussianMGF (fun g => inner ℝ v g) (⟨‖v‖^2, sq_nonneg _⟩ : ℝ≥0) (stdGaussian E) where
  integrable_exp_mul t := by
    have h := integrable_exp_mul_gaussianReal (μ := 0)
      (v := (⟨‖v‖^2, sq_nonneg _⟩ : ℝ≥0)) t
    rw [← gaussian_inner_law v] at h
    exact (integrable_map_measure h.aestronglyMeasurable (by fun_prop)).mp h
  mgf_le t := by
    rw [mgf_gaussianReal (gaussian_inner_law v)]
    simp

lemma gaussian_inner_tail (v : E) (hv : ‖v‖ = 1) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {g | u < |inner ℝ v g|} ≤ 2 * Real.exp (-u^2 / 2) := by
  have h := subgaussian_abs_tail (gaussian_inner_subgaussian v) hu
  change _ ≤ 2 * Real.exp (-u^2 / (2 * ‖v‖^2)) at h
  simpa [hv] using h

end Fourier
section NormTails

lemma gaussian_real_exp_sq (t : ℝ) (ht : t < 1/2) :
    (∫ x : ℝ, Real.exp (t * x^2) ∂gaussianReal 0 1) =
      Real.exp (-(1/2 : ℝ) * Real.log (1 - 2*t)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have heq (x : ℝ) : gaussianPDFReal 0 1 x * Real.exp (t * x^2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2-t) * x^2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [smul_eq_mul, heq]
  rw [integral_const_mul, integral_gaussian]
  have hpos : 0 < 1 - 2*t := by linarith
  have hhalf : 0 < 1/2-t := by linarith
  have hpi := Real.pi_pos
  have heq2 : (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1/2-t)) =
      Real.sqrt ((1 - 2*t)⁻¹) := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (inv_nonneg.mpr (by positivity))]
    congr 1
    field_simp

  rw [heq2, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (inv_pos.mpr hpos), Real.log_inv]
  congr 1
  ring

lemma gaussian_exp_norm_sq {n : ℕ} (t : ℝ) (ht : t < 1/2) :
    (∫ g : EuclideanSpace ℝ (Fin n), Real.exp (t * ‖g‖^2)
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      Real.exp (-(n : ℝ)/2 * Real.log (1-2*t)) := by
  rw [← map_pi_eq_stdGaussian]
  rw [integral_map (by fun_prop) (by fun_prop)]
  have heq (g : Fin n → ℝ) : Real.exp (t * ‖WithLp.toLp 2 g‖^2) =
      ∏ i, Real.exp (t * (g i)^2) := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Real.exp_sum]
  simp_rw [heq]
  have hp := integral_fintype_prod_eq_pow (ι := Fin n) (μ := gaussianReal 0 1)
    (fun x : ℝ => Real.exp (t * x^2))
  rw [Fintype.card_fin] at hp
  change (∫ x : Fin n → ℝ, ∏ i, Real.exp (t * x i ^ 2) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    (∫ x : ℝ, Real.exp (t * x^2) ∂gaussianReal 0 1) ^ n at hp
  rw [hp, gaussian_real_exp_sq t ht, ← Real.exp_nat_mul]
  congr 1
  ring

lemma gaussian_exp_norm_sq_integrable {n : ℕ} (t : ℝ) (ht : t < 1/2) :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) => Real.exp (t * ‖g‖^2))
       (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  by_contra h
  have hh := gaussian_exp_norm_sq (n := n) t ht
  rw [integral_undef h] at hh
  exact (Real.exp_ne_zero _).symm hh

lemma gaussian_norm_upper {n : ℕ} :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {g | 4 * (n : ℝ) < ‖g‖^2} ≤ Real.exp (-(n : ℝ)/2) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun g => Real.exp ((1/4 : ℝ) * ‖g‖^2))
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))
    (gaussian_exp_norm_sq_integrable (1/4) (by norm_num)) (Real.exp n)
  rw [gaussian_exp_norm_sq (1/4) (by norm_num)] at hmark
  have hs : {g : EuclideanSpace ℝ (Fin n) | 4 * (n : ℝ) < ‖g‖^2} ⊆
      {g | Real.exp n ≤ Real.exp ((1/4 : ℝ) * ‖g‖^2)} := by
    intro g hg
    apply Real.exp_le_exp.mpr
    change 4 * (n : ℝ) < ‖g‖^2 at hg
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ μ.real {g | Real.exp n ≤ Real.exp ((1/4 : ℝ) * ‖g‖^2)} := measureReal_mono hs
    _ ≤ Real.exp (-(n : ℝ)/2 * Real.log (1-2*(1/4 : ℝ))) / Real.exp n :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using hmark)
    _ ≤ Real.exp (-(n : ℝ)/2) := by
      rw [← Real.exp_sub]
      apply Real.exp_le_exp.mpr
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      have hl : Real.log (1-2*(1/4 : ℝ)) = -Real.log 2 := by
        norm_num
        rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [hl]
      nlinarith

lemma gaussian_norm_lower {n : ℕ} :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {g | ‖g‖^2 < (n : ℝ)/4} ≤ Real.exp (-(n : ℝ)/8) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun g => Real.exp ((-1/2 : ℝ) * ‖g‖^2))
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))
    (gaussian_exp_norm_sq_integrable (-1/2) (by norm_num)) (Real.exp (-(n : ℝ)/8))
  rw [gaussian_exp_norm_sq (-1/2) (by norm_num)] at hmark
  have hs : {g : EuclideanSpace ℝ (Fin n) | ‖g‖^2 < (n : ℝ)/4} ⊆
      {g | Real.exp (-(n : ℝ)/8) ≤ Real.exp ((-1/2 : ℝ) * ‖g‖^2)} := by
    intro g hg
    apply Real.exp_le_exp.mpr
    change ‖g‖^2 < (n : ℝ)/4 at hg
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ μ.real {g | Real.exp (-(n : ℝ)/8) ≤ Real.exp ((-1/2 : ℝ) * ‖g‖^2)} := measureReal_mono hs
    _ ≤ Real.exp (-(n : ℝ)/2 * Real.log (1-2*(-1/2 : ℝ))) / Real.exp (-(n : ℝ)/8) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using hmark)
    _ ≤ Real.exp (-(n : ℝ)/8) := by
      rw [← Real.exp_sub]
      apply Real.exp_le_exp.mpr
      norm_num only at *
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      nlinarith

lemma gaussian_truncated_sq_bound {n : ℕ} :
    (∫ g : EuclideanSpace ℝ (Fin n),
      ({g | 4*(n : ℝ) < ‖g‖^2} : Set (EuclideanSpace ℝ (Fin n))).indicator
        (fun g => ‖g‖^2) g ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      16 * Real.exp (-(n : ℝ)/12) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hm (g : EuclideanSpace ℝ (Fin n)) :
      ({g | 4*(n : ℝ) < ‖g‖^2} : Set (EuclideanSpace ℝ (Fin n))).indicator
        (fun g => ‖g‖^2) g ≤
      (16 * Real.exp (-(n : ℝ)/4)) * Real.exp ((1/8 : ℝ) * ‖g‖^2) := by
    by_cases hg : 4*(n : ℝ) < ‖g‖^2
    · simp only [Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte]
      have he := Real.add_one_le_exp (‖g‖^2/16)
      have hh : Real.exp (‖g‖^2/16) ≤
          Real.exp (-(n : ℝ)/4) * Real.exp ((1/8 : ℝ) * ‖g‖^2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      nlinarith
    · simp only [Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte]
      positivity
  have hi := (gaussian_exp_norm_sq_integrable (n := n) (1/8) (by norm_num)).const_mul
    (16 * Real.exp (-(n : ℝ)/4))
  calc
    _ ≤ ∫ g : EuclideanSpace ℝ (Fin n),
        (16 * Real.exp (-(n : ℝ)/4)) * Real.exp ((1/8 : ℝ) * ‖g‖^2) ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun g => Set.indicator_nonneg (fun g _ => sq_nonneg ‖g‖) g)
      · exact hi
      · exact ae_of_all _ hm
    _ = 16 * Real.exp (-(n : ℝ)/4 - (n : ℝ)/2 * Real.log (1-2*(1/8 : ℝ))) := by
      rw [integral_const_mul, gaussian_exp_norm_sq (1/8) (by norm_num), mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 16 * Real.exp (-(n : ℝ)/12) := by
      gcongr
      have hl : Real.log (1-2*(1/8 : ℝ)) = -Real.log (4/3) := by
        norm_num
        rw [show (3/4 : ℝ) = (4/3 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [hl]
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4/3)
      have hn := Nat.cast_nonneg (α := ℝ) n
      nlinarith

lemma gaussian_norm_sq_integrable {n : ℕ} :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) => ‖g‖^2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  apply Integrable.mono' ((gaussian_exp_norm_sq_integrable (n := n) (1/4) (by norm_num)).const_mul 4)
  · fun_prop
  · filter_upwards [] with g
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := Real.add_one_le_exp ((1/4 : ℝ) * ‖g‖^2)
    linarith

end NormTails

section Truncation
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "μ" => stdGaussian E

lemma measurable_truncation_set : MeasurableSet {g : E | ‖g‖^2 ≤ 4*(n : ℝ)} := by
  measurability

lemma measurable_tail_set : MeasurableSet {g : E | 4*(n : ℝ) < ‖g‖^2} := by
  measurability

lemma integrable_truncate {f : E → ℝ} (hf : Integrable f μ) :
    Integrable (truncate n f) μ := hf.indicator measurable_truncation_set

lemma truncation_bias {f : E → ℝ} (hf : Integrable f μ)
    (hb : ∀ g, 4*(n : ℝ) < ‖g‖^2 → |f g| ≤ ‖g‖^2) :
    |(∫ g, truncate n f g ∂μ) - ∫ g, f g ∂μ| ≤
      16 * Real.exp (-(n : ℝ)/12) := by
  let T : Set E := {g | 4*(n : ℝ) < ‖g‖^2}
  have hT : MeasurableSet T := measurable_tail_set
  have hid (g : E) : truncate n f g - f g = -T.indicator f g := by
    by_cases h : ‖g‖^2 ≤ 4*(n : ℝ)
    · simp [truncate, T, h, not_lt.mpr h]
    · simp [truncate, T, h, lt_of_not_ge h]
  rw [← integral_sub (integrable_truncate hf) hf]
  simp_rw [hid]
  rw [integral_neg, abs_neg]
  calc
    |∫ g, T.indicator f g ∂μ| ≤ ∫ g, |T.indicator f g| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ g, T.indicator (fun g => ‖g‖^2) g ∂μ := by
      apply integral_mono ((hf.indicator hT).abs) (gaussian_norm_sq_integrable.indicator hT)
      intro g
      by_cases hg : g ∈ T
      · simpa [Set.indicator_of_mem hg] using hb g hg
      · simp [Set.indicator_of_notMem hg]
    _ ≤ _ := gaussian_truncated_sq_bound

lemma inner_sq_integrable (v : E) : Integrable (fun g => (inner ℝ v g)^2) μ := by
  apply Integrable.mono' (gaussian_norm_sq_integrable.const_mul (‖v‖^2))
  · fun_prop
  · filter_upwards [] with g
    simp only [Real.norm_eq_abs, abs_sq]
    have h := abs_real_inner_le_norm v g
    simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) h 2

lemma truncation_covariance_bias (v : E) (hv : ‖v‖ = 1) :
    |(∫ g, truncate n (fun g => (inner ℝ v g)^2) g ∂μ) - 1| ≤
      16 * Real.exp (-(n : ℝ)/12) := by
  have h := truncation_bias (inner_sq_integrable v) (fun g hg => by
    have hh := abs_real_inner_le_norm v g
    rw [hv, one_mul] at hh
    simpa only [abs_sq, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2)
  simpa [gaussian_inner_sq, hv] using h

lemma truncation_fourier_bias (hn : 1 ≤ n) (v w : E) (hv : ‖v‖ = 1) :
    |(∫ g, truncate n (fun g => inner ℝ g v * Real.sin (inner ℝ g w)) g ∂μ) -
      inner ℝ w v * Real.exp (-‖w‖^2/2)| ≤
      16 * Real.exp (-(n : ℝ)/12) := by
  have h := truncation_bias (gaussian_linear_sin_integrable w v) (fun g hg => by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hh := abs_real_inner_le_norm g v
    rw [hv, mul_one] at hh
    have hn1 : 1 ≤ ‖g‖ := by nlinarith [norm_nonneg g]
    calc
      |inner ℝ g v * Real.sin (inner ℝ g w)| ≤ |inner ℝ g v| * 1 := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ ≤ ‖g‖^2 := by nlinarith)
  simpa only [gaussian_linear_sin] using h

lemma truncate_fourier_bound (v w : E) (hv : ‖v‖ = 1) (g : E) :
    |truncate n (fun g => inner ℝ g v * Real.sin (inner ℝ g w)) g| ≤ 2*Real.sqrt n := by
  by_cases hg : ‖g‖^2 ≤ 4*(n : ℝ)
  · have hh := abs_real_inner_le_norm g v
    rw [hv, mul_one] at hh
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
    have hb : ‖g‖ ≤ 2*Real.sqrt n := by nlinarith [Real.sqrt_nonneg (n : ℝ), norm_nonneg g]
    simp only [truncate, Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte, abs_mul]
    calc
      _ ≤ |inner ℝ g v| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ ≤ _ := by linarith
  · simp only [truncate, Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte, abs_zero]
    positivity

lemma truncate_covariance_bound (v : E) (hv : ‖v‖ = 1) (g : E) :
    |truncate n (fun g => (inner ℝ v g)^2) g| ≤ 4*(n : ℝ) := by
  by_cases hg : ‖g‖^2 ≤ 4*(n : ℝ)
  · have hh := abs_real_inner_le_norm v g
    rw [hv, one_mul] at hh
    have hb := pow_le_pow_left₀ (abs_nonneg _) hh 2
    rw [sq_abs] at hb
    simp only [truncate, Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte, abs_sq]
    nlinarith
  · simp only [truncate, Set.indicator, Set.mem_ofPred_eq, hg, ↓reduceIte, abs_zero]
    positivity
end Truncation

end UniformSparsestCut.GaussianTools

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.FiniteNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.FiniteNets

lemma euclidean_norm_le_sum_abs {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ ∑ i, |x i| := by
  classical
  have heq : x = ∑ i : Fin n, (PiLp.single 2 i (x i) : EuclideanSpace ℝ (Fin n)) := by
    ext j
    simp
  calc
    _ = ‖∑ i : Fin n, (PiLp.single 2 i (x i) : EuclideanSpace ℝ (Fin n))‖ := congrArg norm heq
    _ ≤ ∑ i : Fin n, ‖(PiLp.single 2 i (x i) : EuclideanSpace ℝ (Fin n))‖ := norm_sum_le _ _
    _ = _ := by simp [PiLp.norm_single, Real.norm_eq_abs]

lemma floor_coordinate_bound {n K : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ (K : ℝ) * δ) (i : Fin n) :
    ⌊x i / δ⌋ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
  have hcoord : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
  have hi : |x i| ≤ (K : ℝ) * δ := hcoord.trans hx
  rw [Finset.mem_Icc]
  constructor
  · apply Int.le_floor.mpr
    push_cast
    apply (le_div_iff₀ hδ).mpr
    linarith [neg_abs_le (x i)]
  · have hh : x i / δ ≤ (K : ℝ) := (div_le_iff₀ hδ).mpr ((le_abs_self _).trans hi)
    have h := Int.floor_mono hh
    simpa using h

lemma same_floor_distance {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {x y : EuclideanSpace ℝ (Fin n)} (hxy : ∀ i, ⌊x i / δ⌋ = ⌊y i / δ⌋) :
    ‖x - y‖ ≤ (n : ℝ) * δ := by
  have hc (i : Fin n) : |x i - y i| ≤ δ := by
    have hx1 := Int.floor_le (x i / δ)
    have hx2 := Int.lt_floor_add_one (x i / δ)
    have hy1 := Int.floor_le (y i / δ)
    have hy2 := Int.lt_floor_add_one (y i / δ)
    rw [hxy i] at hx1 hx2
    apply abs_le.mpr
    constructor
    · have hh : -1 ≤ (x i - y i) / δ := by rw [sub_div]; linarith
      have := (le_div_iff₀ hδ).mp hh
      linarith
    · have hh : (x i - y i) / δ ≤ 1 := by rw [sub_div]; linarith
      have := (div_le_iff₀ hδ).mp hh
      linarith
  calc
    ‖x-y‖ ≤ ∑ i, |(x-y) i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _ : Fin n, δ := Finset.sum_le_sum (fun i _ => hc i)
    _ = _ := by simp

theorem exists_coordinate_net {n K : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : ∀ x ∈ A, ‖x‖ ≤ (K : ℝ) * δ) :
    ∃ V : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ v ∈ V, v ∈ A) ∧ V.card ≤ (2*K+1)^n ∧
      ∀ x ∈ A, ∃ v ∈ V, ‖x-v‖ ≤ (n : ℝ)*δ := by
  classical
  let G := Fin n → ↥(Finset.Icc (-(K : ℤ)) (K : ℤ))
  let represented : G → Prop := fun g => ∃ x ∈ A, ∀ i, ⌊x i / δ⌋ = (g i).val
  let point : G → EuclideanSpace ℝ (Fin n) := fun g =>
    if h : represented g then h.choose else 0
  have hpoint (g : G) (hg : represented g) :
      point g ∈ A ∧ ∀ i, ⌊point g i / δ⌋ = (g i).val := by
    simpa [point, hg] using hg.choose_spec
  let V := (Finset.univ.filter represented).image point
  refine ⟨V, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv
    exact (hpoint g (Finset.mem_filter.mp hg).2).1
  · calc
      V.card ≤ (Finset.univ.filter represented).card := Finset.card_image_le
      _ ≤ Fintype.card G := (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)
      _ = (2*K+1)^n := by
        simp only [G, Fintype.card_fun, Fintype.card_coe, Int.card_Icc, Fintype.card_fin]
        congr 1
        omega
  · intro x hx
    let g : G := fun i => ⟨⌊x i / δ⌋, floor_coordinate_bound hδ (hA x hx) i⟩
    have hg : represented g := ⟨x, hx, fun _ => rfl⟩
    refine ⟨point g, Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩, rfl⟩, ?_⟩
    exact same_floor_distance hδ (fun i => ((hpoint g hg).2 i).symm)

lemma sphere_net_norm_bound {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {V : Finset E} {ρ B : ℝ}
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ V, ‖x-v‖ ≤ ρ)
    {z : E} (hz : ∀ v ∈ V, |inner ℝ z v| ≤ B) (hB : 0 ≤ B) :
    (1-ρ)*‖z‖ ≤ B := by
  by_cases hzero : z = 0
  · simpa [hzero] using hB
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hzero
  let x := ‖z‖⁻¹ • z
  have hx : ‖x‖ = 1 := by simp [x, norm_smul, hn.ne']
  obtain ⟨v, hv, hdist⟩ := hnet x hx
  have hinner : inner ℝ z x = ‖z‖ := by
    simp [x, inner_smul_right, sq, hn.ne']
  have heq : inner ℝ z x = inner ℝ z v + inner ℝ z (x-v) := by
    rw [inner_sub_right]
    ring
  have hbound : ‖z‖ ≤ B + ‖z‖ * ρ := by
    calc
      ‖z‖ = |inner ℝ z x| := by rw [hinner, abs_of_nonneg (norm_nonneg _)]
      _ ≤ |inner ℝ z v| + |inner ℝ z (x-v)| := by rw [heq]; exact abs_add_le _ _
      _ ≤ B + ‖z‖ * ρ := add_le_add (hz v hv)
        ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hdist (norm_nonneg _)))
  nlinarith

end UniformSparsestCut.FiniteNets

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Directions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.Directions
open GaussianTools FiniteNets MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology

section ProductMeasures
variable {E : Type u1} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

lemma integral_eval {n : ℕ} {f : E → ℝ} (hf : Measurable f) (i : Fin n) :
    (∫ x : Fin n → E, f (x i) ∂Measure.pi (fun _ => μ)) = ∫ x, f x ∂μ := by
  have hp := measurePreserving_eval (fun _ : Fin n => μ) i
  have hh := integral_map hp.aemeasurable (hf.aestronglyMeasurable :
    AEStronglyMeasurable f ((Measure.pi (fun _ : Fin n => μ)).map (Function.eval i)))
  rw [hp.map_eq] at hh
  exact hh.symm

lemma real_measure_eval {n : ℕ} {A : Set E} (hA : MeasurableSet A) (i : Fin n) :
    (Measure.pi (fun _ : Fin n => μ)).real {x | x i ∈ A} = μ.real A := by
  have hp := (measurePreserving_eval (fun _ : Fin n => μ) i).measure_preimage hA.nullMeasurableSet
  exact congrArg ENNReal.toReal hp

lemma iid_bounded_concentration {n : ℕ} (hn : 0 < n) {f : E → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : 0 < B) (hfB : ∀ x, |f x| ≤ B)
    {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {x | u < |(∑ i, f (x i)) / (n : ℝ) - ∫ z, f z ∂μ|} ≤
      2 * Real.exp (-(n : ℝ)*u^2/(2*B^2)) := by
  have h := bounded_concentration hn (fun i (x : Fin n → E) => f (x i))
    (fun i => (hf.comp (measurable_pi_apply i)).aemeasurable)
    (iIndepFun_pi (μ := fun _ : Fin n => μ) (fun _ => hf.aemeasurable)) hB
    (fun i => ae_of_all _ (fun x => hfB (x i))) hu
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq (x : Fin n → E) :
      (∑ i, (f (x i) - ∫ z : Fin n → E, f (z i) ∂Measure.pi (fun _ => μ))) / (n : ℝ) =
        (∑ i, f (x i)) / (n : ℝ) - ∫ z, f z ∂μ := by
    simp_rw [integral_eval hf]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simpa only [heq] using h

lemma real_measure_exists_le {n : ℕ} (A : Fin n → Set E) (hA : ∀ i, MeasurableSet (A i))
    {p : ℝ} (hp : ∀ i, μ.real (A i) ≤ p) :
    (Measure.pi (fun _ : Fin n => μ)).real {x | ∃ i, x i ∈ A i} ≤ (n : ℝ)*p := by
  calc
    _ = (Measure.pi (fun _ : Fin n => μ)).real (⋃ i : Fin n, {x | x i ∈ A i}) := by
      congr 1; ext x; simp
    _ ≤ ∑ i : Fin n, (Measure.pi (fun _ : Fin n => μ)).real {x | x i ∈ A i} :=
      measureReal_iUnion_fintype_le _
    _ = ∑ i : Fin n, μ.real (A i) := by simp_rw [real_measure_eval (hA _)]
    _ ≤ ∑ _ : Fin n, p := Finset.sum_le_sum (fun i _ => hp i)
    _ = _ := by simp

lemma bad_chart_fraction {S : ℕ} (hS : 0 < S) {A : Set E} (hA : MeasurableSet A)
    (hp : μ.real A ≤ 1/4) :
    (Measure.pi (fun _ : Fin S => μ)).real
      {x | (S : ℝ)/2 < (badCount A x : ℝ)} ≤
      2 * Real.exp (-(S : ℝ)/32) := by
  classical
  let f : E → ℝ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hbound (x : E) : |f x| ≤ 1 := by
    by_cases hx : x ∈ A <;> simp [f, hx]
  have hmean : (∫ x, f x ∂μ) = μ.real A := integral_indicator_one hA
  have h := iid_bounded_concentration (μ := μ) hS hf (by norm_num : (0 : ℝ) < 1) hbound
    (u := 1/4) (by norm_num)
  have hcount (x : Fin S → E) : (∑ s : Fin S, f (x s)) =
      (badCount A x : ℝ) := by
    dsimp [badCount]
    simp only [f, Set.indicator]
    rw [← Finset.sum_filter]
    simp
  have hspos : (0 : ℝ) < S := by exact_mod_cast hS
  have hsub : {x : Fin S → E | (S : ℝ)/2 < (badCount A x : ℝ)} ⊆
      {x | (1/4 : ℝ) < |(∑ s, f (x s))/(S : ℝ) - ∫ z, f z ∂μ|} := by
    intro x hx
    change (S : ℝ)/2 < (badCount A x : ℝ) at hx
    change (1/4 : ℝ) < |(∑ s, f (x s))/(S : ℝ) - ∫ z, f z ∂μ|
    rw [hcount, hmean]
    apply (lt_abs.mpr (Or.inl ?_))
    have hh : (1/2 : ℝ) < (badCount A x : ℝ)/(S : ℝ) :=
      (lt_div_iff₀ hspos).mpr (by linarith)
    linarith
  calc
    _ ≤ _ := measureReal_mono hsub
    _ ≤ 2 * Real.exp (-(S : ℝ) * (1/4)^2 / (2*1^2)) := h
    _ = _ := by congr 2; ring

lemma exists_outside_of_real_lt_one {Ω : Type u2} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {A : Set Ω} (hA : (ν).real A < 1) :
    ∃ x, x ∉ A := by
  by_contra h
  push Not at h
  have heq : A = Set.univ := Set.eq_univ_of_forall h
  simp [heq, measureReal_def] at hA

lemma exists_outside_with_ae {Ω : Type u3} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {A : Set Ω} (hA : (ν).real A < 1)
    {P : Ω → Prop} (hP : ∀ᵐ x ∂ν, P x) : ∃ x, x ∉ A ∧ P x := by
  have hnull : (ν).real {x | ¬ P x} = 0 := by
    rw [measureReal_def, ae_iff.mp hP, ENNReal.toReal_zero]
  have hlt : (ν).real (A ∪ {x | ¬ P x}) < 1 :=
    ((measureReal_union_le _ _).trans_eq (by rw [hnull, add_zero])).trans_lt hA
  obtain ⟨x,hx⟩ := exists_outside_of_real_lt_one hlt
  exact ⟨x, fun ha => hx (Or.inl ha), by_contra (fun hn => hx (Or.inr hn))⟩

end ProductMeasures

lemma finite_union_bound {Ω : Type u4} {I : Type u5} [MeasurableSpace Ω] [Fintype I]
    {ν : Measure Ω} [IsProbabilityMeasure ν] (A : I → Set Ω) {p : ℝ}
    (hA : ∀ i, (ν).real (A i) ≤ p) :
    (ν).real {x | ∃ i, x ∈ A i} ≤ (Fintype.card I : ℝ)*p := by
  calc
    _ = (ν).real (⋃ i, A i) := by congr 1; ext; simp
    _ ≤ ∑ i, (ν).real (A i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : I, p := Finset.sum_le_sum (fun i _ => hA i)
    _ = _ := by simp

section GaussianSelection
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => stdGaussian E
local notation "ν" => Measure.pi (fun _ : Fin N => μ)
local notation "π" => Measure.pi (fun _ : Fin S => ν)

lemma fourierSummand_measurable (v w : E) : Measurable (fourierSummand v w) :=
  (by fun_prop : Measurable (fun g : E => inner ℝ g v * Real.sin (inner ℝ g w))).indicator
    measurable_truncation_set
lemma covarianceSummand_measurable (v : E) : Measurable (covarianceSummand v) :=
  (by fun_prop : Measurable (fun g : E => (inner ℝ v g)^2)).indicator measurable_truncation_set
lemma normBad_measurable : MeasurableSet (normBad (m := m) (N := N)) := by
  unfold normBad; measurability
lemma fourierBad_measurable (u : ℝ) (v w : E) : MeasurableSet (fourierBad (N := N) u v w) := by
  unfold fourierBad
  have hf (i : Fin N) : Measurable (fun x : Fin N → E => fourierSummand v w (x i)) :=
    (fourierSummand_measurable v w).comp (measurable_pi_apply i)
  measurability
lemma covarianceBad_measurable (v : E) : MeasurableSet (covarianceBad (N := N) v) := by
  unfold covarianceBad
  have hf (i : Fin N) : Measurable (fun x : Fin N → E => covarianceSummand v (x i)) :=
    (covarianceSummand_measurable v).comp (measurable_pi_apply i)
  measurability
lemma projectionBad_measurable (q : ℝ) (v : E) : MeasurableSet (projectionBad (N := N) q v) := by
  unfold projectionBad; measurability

lemma normBad_bound : (ν).real (normBad (m := m) (N := N)) ≤
    (N : ℝ)* (2*Real.exp (-(m : ℝ)/8)) :=
  real_measure_exists_le (fun _ => {g : E | ‖g‖^2 < (m : ℝ)/4 ∨ 4*(m : ℝ) < ‖g‖^2})
    (fun _ => by measurability) (fun _ => by
      have h := (measureReal_union_le
        {g : E | ‖g‖^2 < (m : ℝ)/4} {g : E | 4*(m : ℝ) < ‖g‖^2}).trans
        (add_le_add (gaussian_norm_lower (n := m)) (gaussian_norm_upper (n := m)))
      have he : Real.exp (-(m : ℝ)/2) ≤ Real.exp (-(m : ℝ)/8) :=
        Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
      exact h.trans (by linarith))

lemma fourierBad_bound (hm : 0 < m) (hN : 0 < N) {u : ℝ} (hu : 0 ≤ u)
    (v w : E) (hv : ‖v‖ = 1) :
    (ν).real (fourierBad (N := N) u v w) ≤
      2*Real.exp (-(N : ℝ)*u^2/(2*(2*Real.sqrt m)^2)) := by
  exact iid_bounded_concentration hN (fourierSummand_measurable v w)
    (by positivity) (truncate_fourier_bound v w hv) hu
lemma covarianceBad_bound (hm : 0 < m) (hN : 0 < N) (v : E) (hv : ‖v‖ = 1) :
    (ν).real (covarianceBad (N := N) v) ≤
      2*Real.exp (-(N : ℝ)*(1/8)^2/(2*(4*(m : ℝ))^2)) := by
  exact iid_bounded_concentration hN (covarianceSummand_measurable v)
    (by positivity) (truncate_covariance_bound v hv) (by norm_num)
lemma projectionBad_bound {q : ℝ} (hq : 0 ≤ q) (v : E) (hv : ‖v‖ = 1) :
    (ν).real (projectionBad (N := N) q v) ≤ (N : ℝ)*(2*Real.exp (-q^2/2)) :=
  real_measure_exists_le (fun _ => {g : E | q < |inner ℝ v g|})
    (fun _ => by measurability) (fun _ => gaussian_inner_tail v hv hq)

lemma chartBad_measurable (V W : Finset E) (u : ℝ) :
    MeasurableSet (chartBad (N := N) V W u) := by
  classical
  have hFm : MeasurableSet {x : Fin N → E | ∃ z : V × W, x ∈ fourierBad u z.1 z.2} := by
    rw [show {x : Fin N → E | ∃ z : V × W, x ∈ fourierBad u z.1 z.2} =
      ⋃ z : V × W, fourierBad (N := N) u z.1 z.2 by ext x; simp]
    exact MeasurableSet.iUnion (fun z : V × W => fourierBad_measurable (m := m) (N := N) u z.1 z.2)
  have hCm : MeasurableSet {x : Fin N → E | ∃ v : V, x ∈ covarianceBad v} := by
    rw [show {x : Fin N → E | ∃ v : V, x ∈ covarianceBad v} =
      ⋃ v : V, covarianceBad (N := N) v by ext x; simp]
    exact MeasurableSet.iUnion (fun v : V => covarianceBad_measurable (m := m) (N := N) v)
  exact (normBad_measurable.union hFm).union hCm

lemma chartBad_bound (hm : 0 < m) (hN : 0 < N) (V W : Finset E)
    (hV : ∀ v ∈ V, ‖v‖ = 1) {u : ℝ} (hu : 0 ≤ u) :
    (ν).real (chartBad (N := N) V W u) ≤ (N : ℝ)*(2*Real.exp (-(m : ℝ)/8)) +
        (V.card : ℝ)*(W.card : ℝ)*(2*Real.exp (-(N : ℝ)*u^2/(2*(2*Real.sqrt m)^2))) +
        (V.card : ℝ)*(2*Real.exp (-(N : ℝ)*(1/8)^2/(2*(4*(m : ℝ))^2))) := by
  classical
  have h1 := finite_union_bound («ν» := ν) (fun z : V × W => fourierBad u z.1 z.2)
    (fun z => fourierBad_bound hm hN hu z.1 z.2 (hV z.1 z.1.property))
  have h2 := finite_union_bound («ν» := ν) (fun v : V => covarianceBad v)
    (fun v => covarianceBad_bound hm hN v (hV v v.property))
  simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul] at h1 h2
  exact (measureReal_union_le _ _).trans
    (add_le_add ((measureReal_union_le _ _).trans (add_le_add normBad_bound h1)) h2)

lemma projection_chart_fraction (hS : 0 < S) (v : E) (hv : ‖v‖ = 1)
    {q : ℝ} (hq : 0 ≤ q) (hqprob : (N : ℝ)*(2*Real.exp (-q^2/2)) ≤ 1/4) :
    (π).real {g | (S : ℝ)/2 < (badCount (projectionBad q v) g : ℝ)} ≤
      2*Real.exp (-(S : ℝ)/32) := by
  have hmeas : MeasurableSet (projectionBad (N := N) q v) := projectionBad_measurable q v
  have hbound : (ν).real (projectionBad (N := N) q v) ≤ 1/4 :=
    (projectionBad_bound hq v hv).trans hqprob
  exact bad_chart_fraction hS hmeas hbound

lemma goodBad_bound (hS : 0 < S) (V : Finset E) (hV : ∀ v ∈ V, ‖v‖ = 1)
    {q : ℝ} (hq : 0 ≤ q) (hqprob : (N : ℝ)*(2*Real.exp (-q^2/2)) ≤ 1/4) :
    (π).real {g | ∃ v : V, (S : ℝ)/2 < (badCount (projectionBad q v) g : ℝ)} ≤
      (V.card : ℝ)*(2*Real.exp (-(S : ℝ)/32)) := by
  classical
  have h := finite_union_bound («ν» := π)
    (fun v : V => {g | (S : ℝ)/2 < (badCount (projectionBad q v) g : ℝ)})
    (fun v => projection_chart_fraction hS (v : E) (hV v v.property) hq hqprob)
  simpa only [Fintype.card_coe, Set.mem_ofPred_eq] using h

end GaussianSelection

end UniformSparsestCut.Directions

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.GaussianNonparallel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianNonparallel

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => stdGaussian E

lemma gaussian_inner_zero_measure (v : E) (hv : v ≠ 0) :
    (stdGaussian E) {x | inner ℝ v x = 0} = 0 := by
  let c : ℝ≥0 := ⟨‖v‖^2, sq_nonneg _⟩
  have hc : c ≠ 0 := by
    intro h
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    change ‖v‖^2 = 0 at this
    exact hv (norm_eq_zero.mp (sq_eq_zero_iff.mp this))
  let := nullSingletonClass_gaussianReal («μ» := 0) hc
  have hmap : (stdGaussian E).map (fun x => inner ℝ v x) = gaussianReal 0 c := by
    have h := IsGaussian.map_eq_gaussianReal («μ» := stdGaussian E) (innerSL ℝ v)
    simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
      innerSL_apply_norm] at h
    convert h using 2
    · rfl
    · apply NNReal.eq
      change ‖v‖^2 = ((‖v‖^2).toNNReal : ℝ)
      simp
  have h := congrArg (fun ν : Measure ℝ => ν {0}) hmap
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _), measure_singleton] at h
  exact h

lemma gaussian_coordinate_ne (i : Fin m) : ∀ᵐ x : E ∂μ, x i ≠ 0 := by
  have hv : (EuclideanSpace.single i 1 : E) ≠ 0 := by
    intro h
    have hh := congrArg (fun x : E => x i) h
    simp at hh
  have h := gaussian_inner_zero_measure (EuclideanSpace.single i 1) hv
  apply ae_iff.mpr
  simpa [EuclideanSpace.inner_single_left] using h

lemma gaussian_cross_zero_measure (i j : Fin m) (hij : i ≠ j) :
    ((μ).prod μ) {z : E × E | cross i j z.1 z.2 = 0} = 0 := by
  rw [Measure.prod_apply (by unfold cross; measurability)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [gaussian_coordinate_ne i] with x hx
  let v : E := EuclideanSpace.single j (x i) - EuclideanSpace.single i (x j)
  have hv : v ≠ 0 := by
    intro h
    have hh := congrArg (fun x : E => x j) h
    have hh' : x i = 0 := by simpa [v, PiLp.single_apply, hij, Ne.symm hij] using hh
    exact hx hh'
  have hid (y : E) : inner ℝ v y = cross i j x y := by
    simp [v, cross, inner_sub_left, EuclideanSpace.inner_single_left]
  simpa only [preimage_ofPred_eq, hid, Pi.zero_apply] using gaussian_inner_zero_measure v hv

lemma iid_cross_ne {N : ℕ} (i j : Fin m) (hij : i ≠ j) (a b : Fin N) (hab : a ≠ b) :
    ∀ᵐ g : Fin N → E ∂Measure.pi (fun _ => μ), cross i j (g a) (g b) ≠ 0 := by
  let ν := Measure.pi (fun _ : Fin N => μ)
  have hind : iIndepFun (fun k (g : Fin N → E) => g k) ν :=
    iIndepFun_pi («μ» := fun _ : Fin N => μ) (fun _ => aemeasurable_id)
  have hmap := (hind.indepFun hab).map_prod_eq_prod_map_map
    (measurable_pi_apply a).aemeasurable (measurable_pi_apply b).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin N => μ) a).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) b).map_eq] at hmap
  have hh := congrArg (fun ν : Measure (E × E) => ν {z | cross i j z.1 z.2 = 0}) hmap
  rw [Measure.map_apply (by fun_prop) (by unfold cross; measurability),
    gaussian_cross_zero_measure i j hij] at hh
  apply ae_iff.mpr
  simpa only [ν, preimage_ofPred_eq, not_not] using hh

lemma iid_pairwise_nonparallel {N : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ g : Fin N → E ∂Measure.pi (fun _ => μ),
      ∀ a b, a ≠ b → ∀ t : ℝ, g a ≠ t • g b := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i,j] at this
  have hh : ∀ a b : Fin N, ∀ᵐ g : Fin N → E ∂Measure.pi (fun _ => μ),
      a ≠ b → cross i j (g a) (g b) ≠ 0 := by
    intro a b
    by_cases hab : a = b
    · exact ae_of_all _ (fun _ hn => (hn hab).elim)
    · filter_upwards [iid_cross_ne i j hij a b hab] with g hg using fun _ => hg
  have hall := (ae_all_iff.mpr (fun a => ae_all_iff.mpr (hh a)))
  filter_upwards [hall] with g hg
  intro a b hab t h
  apply hg a b hab
  rw [h]
  simp [cross]
  ring

lemma charts_pairwise_nonparallel {N S : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ g : Fin S → Fin N → E ∂Measure.pi (fun _ => Measure.pi (fun _ => μ)),
      ∀ s a b, a ≠ b → ∀ t : ℝ, g s a ≠ t • g s b := by
  apply ae_all_iff.mpr
  intro s
  exact (measurePreserving_eval (fun _ : Fin S => Measure.pi (fun _ : Fin N => μ)) s).quasiMeasurePreserving.ae
    (iid_pairwise_nonparallel hm)

end UniformSparsestCut.GaussianNonparallel

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.DirectionInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.DirectionInterpolation
open GaussianTools FiniteNets MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

variable {m N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma sin_vector_lipschitz (g w w' : E) :
    ‖Real.sin (inner ℝ g w) • g - Real.sin (inner ℝ g w') • g‖ ≤
      ‖g‖^2 * ‖w-w'‖ := by
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  have hs : |Real.sin (inner ℝ g w) - Real.sin (inner ℝ g w')| ≤
      |inner ℝ g (w-w')| := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, inner_sub_right, NNReal.coe_one, one_mul] using
      Real.lipschitzWith_sin.dist_le_mul (inner ℝ g w) (inner ℝ g w')
  calc
    _ ≤ |inner ℝ g (w-w')| * ‖g‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ ≤ (‖g‖*‖w-w'‖)*‖g‖ := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
    _ = _ := by ring

lemma empiricalSin_lipschitz (hN : 0 < N) (g : Fin N → E) {B : ℝ}
    (hB : ∀ i, ‖g i‖^2 ≤ B) (w w' : E) :
    ‖empiricalSin g w - empiricalSin g w'‖ ≤ B*‖w-w'‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [empiricalSin, empiricalSin, ← smul_sub, ← Finset.sum_sub_distrib, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ i, ‖Real.sin (inner ℝ (g i) w) • g i -
        Real.sin (inner ℝ (g i) w') • g i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (N : ℝ)⁻¹ * ∑ _ : Fin N, B * ‖w-w'‖ := by
      gcongr with i
      exact (sin_vector_lipschitz _ _ _).trans (mul_le_mul_of_nonneg_right (hB i) (norm_nonneg _))
    _ = _ := by simp [hn.ne']

lemma gaussian_norm_sq_mean : (∫ g : E, ‖g‖^2 ∂stdGaussian E) = m := by
  have hid (g : E) : ‖g‖^2 = ∑ i : Fin m, (inner ℝ (EuclideanSpace.single i 1) g)^2 := by
    simp only [EuclideanSpace.norm_sq_eq, EuclideanSpace.inner_single_left, conj_trivial, one_mul,
      Real.norm_eq_abs, sq_abs]
  simp_rw [hid]
  rw [integral_finsetSum _ (fun i _ => inner_sq_integrable _)]
  simp_rw [gaussian_inner_sq]
  simp

lemma gaussianTransform_lipschitz (w w' : E) :
    ‖Real.exp (-‖w‖^2/2) • w - Real.exp (-‖w'‖^2/2) • w'‖ ≤ (m : ℝ)*‖w-w'‖ := by
  rw [← gaussian_vector_sin w, ← gaussian_vector_sin w',
    ← integral_sub (gaussian_vector_sin_integrable w) (gaussian_vector_sin_integrable w')]
  calc
    _ ≤ ∫ g : E, ‖Real.sin (inner ℝ g w) • g - Real.sin (inner ℝ g w') • g‖ ∂stdGaussian E :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ g : E, ‖g‖^2 * ‖w-w'‖ ∂stdGaussian E := by
      apply integral_mono ((gaussian_vector_sin_integrable w).sub (gaussian_vector_sin_integrable w')).norm
        (gaussian_norm_sq_integrable.mul_const ‖w-w'‖)
      exact fun g => sin_vector_lipschitz g w w'
    _ = _ := by rw [integral_mul_const, gaussian_norm_sq_mean]

lemma covariance_lipschitz (hN : 0 < N) (g : Fin N → E) {B : ℝ}
    (hg : ∀ i, ‖g i‖^2 ≤ B) {v v' : E} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    |empiricalCov g v - empiricalCov g v'| ≤ 2*B*‖v-v'‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm (i : Fin N) : |(inner ℝ v (g i))^2 - (inner ℝ v' (g i))^2| ≤
      2*B*‖v-v'‖ := by
    rw [sq_sub_sq, abs_mul, mul_comm]
    have ha : |inner ℝ v (g i)| ≤ ‖g i‖ := by simpa [hv] using abs_real_inner_le_norm v (g i)
    have hb : |inner ℝ v' (g i)| ≤ ‖g i‖ := by simpa [hv'] using abs_real_inner_le_norm v' (g i)
    have hd : |inner ℝ v (g i) - inner ℝ v' (g i)| ≤ ‖v-v'‖*‖g i‖ := by
      simpa only [inner_sub_left] using abs_real_inner_le_norm (v-v') (g i)
    calc
      _ ≤ (‖v-v'‖*‖g i‖)*(2*‖g i‖) :=
        mul_le_mul hd ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _) (by positivity)
      _ = 2*‖g i‖^2*‖v-v'‖ := by ring
      _ ≤ 2*B*‖v-v'‖ := by gcongr; exact hg i
  rw [empiricalCov, empiricalCov, ← sub_div, abs_div, abs_of_pos hn, ← Finset.sum_sub_distrib]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i : Fin N, |(inner ℝ v (g i))^2 - (inner ℝ v' (g i))^2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin N, 2*B*‖v-v'‖ := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp [mul_comm]

lemma covariance_net_bound (hN : 0 < N) (g : Fin N → E) {B b ρ : ℝ}
    (hg : ∀ i, ‖g i‖^2 ≤ B) (hB : 0 ≤ B) (V : Finset E)
    (hV : ∀ v ∈ V, ‖v‖ = 1)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ V, ‖x-v‖ ≤ ρ)
    (hdev : ∀ v ∈ V, |empiricalCov g v - 1| ≤ b)
    (x : E) (hx : ‖x‖ = 1) : |empiricalCov g x - 1| ≤ b + 2*B*ρ := by
  obtain ⟨v,hv,hd⟩ := hnet x hx
  calc
    _ ≤ |empiricalCov g x - empiricalCov g v| + |empiricalCov g v - 1| := abs_sub_le _ _ _
    _ ≤ 2*B*‖x-v‖ + b := add_le_add (covariance_lipschitz hN g hg hx (hV v hv)) (hdev v hv)
    _ ≤ b + 2*B*ρ := by nlinarith

lemma fourier_net_bound (hN : 0 < N) (g : Fin N → E) {B b ρ δ R : ℝ}
    (hg : ∀ i, ‖g i‖^2 ≤ B) (hB : 0 ≤ B) (hb : 0 ≤ b) (hρ : ρ < 1)
    (V W : Finset E)
    (hV : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ V, ‖x-v‖ ≤ ρ)
    (hW : ∀ w : E, ‖w‖ ≤ R → ∃ w' ∈ W, ‖w-w'‖ ≤ δ)
    (hdev : ∀ v ∈ V, ∀ w ∈ W,
      |inner ℝ (empiricalSin g w - Real.exp (-‖w‖^2/2) • w) v| ≤ b)
    (w : E) (hw : ‖w‖ ≤ R) :
    ‖empiricalSin g w - Real.exp (-‖w‖^2/2) • w‖ ≤ b/(1-ρ) + (B+(m : ℝ))*δ := by
  obtain ⟨w',hw',hd⟩ := hW w hw
  have hn : ‖empiricalSin g w' - Real.exp (-‖w'‖^2/2) • w'‖ ≤ b/(1-ρ) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-ρ)).mpr
    nlinarith [sphere_net_norm_bound hV (fun v hv => hdev v hv w' hw') hb]
  calc
    _ ≤ ‖empiricalSin g w - empiricalSin g w'‖ +
        ‖empiricalSin g w' - Real.exp (-‖w'‖^2/2) • w'‖ +
        ‖Real.exp (-‖w'‖^2/2) • w' - Real.exp (-‖w‖^2/2) • w‖ :=
      by
        have hid : empiricalSin g w - Real.exp (-‖w‖^2/2) • w =
            (empiricalSin g w - empiricalSin g w') +
            (empiricalSin g w' - Real.exp (-‖w'‖^2/2) • w') +
            (Real.exp (-‖w'‖^2/2) • w' - Real.exp (-‖w‖^2/2) • w) := by abel
        rw [hid]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ B*‖w-w'‖ + b/(1-ρ) + (m : ℝ)*‖w-w'‖ := by
      apply add_le_add (add_le_add (empiricalSin_lipschitz hN g hg w w') hn)
      simpa only [norm_sub_rev] using gaussianTransform_lipschitz w' w
    _ ≤ b/(1-ρ) + (B+(m : ℝ))*δ := by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith

lemma projection_interpolate {g v v' : E} {q K ρ : ℝ}
    (hg : ‖g‖ ≤ K) (_hK : 0 ≤ K) (hd : ‖v-v'‖ ≤ ρ)
    (hp : |inner ℝ v' g| ≤ q) : |inner ℝ v g| ≤ q + K*ρ := by
  have hi : inner ℝ v g = inner ℝ v' g + inner ℝ (v-v') g := by rw [inner_sub_left]; ring
  calc
    _ ≤ |inner ℝ v' g| + |inner ℝ (v-v') g| := by rw [hi]; exact abs_add_le _ _
    _ ≤ q + ‖v-v'‖*‖g‖ := add_le_add hp (abs_real_inner_le_norm _ _)
    _ ≤ q + K*ρ := by
      have hρ : 0 ≤ ρ := (norm_nonneg _).trans hd
      nlinarith [mul_le_mul hd hg (norm_nonneg _) hρ]

end UniformSparsestCut.DirectionInterpolation

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.DirectionAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.DirectionAsymptotics
open Filter
open scoped Topology

lemma grid_card_bound (m k : ℕ) (hm : 2 ≤ m) :
    (((2*m^k+1)^m : ℕ) : ℝ) ≤ Real.exp (((k : ℝ)+2)*(m : ℝ)^2) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (1 : ℝ) ≤ (m : ℝ)^k := one_le_pow₀ (by linarith)
  have he : (m : ℝ) ≤ Real.exp m := by linarith [Real.add_one_le_exp (m : ℝ)]
  have h3 : (3 : ℝ) ≤ Real.exp m := by linarith [Real.add_one_le_exp (m : ℝ)]
  have hb : (2 : ℝ)*(m : ℝ)^k+1 ≤ Real.exp ((k+1 : ℕ)*(m : ℝ)) := by
    calc
      _ ≤ 3*(m : ℝ)^k := by linarith
      _ ≤ Real.exp m * (Real.exp m)^k := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; rw [← Real.exp_add]; congr 1; push_cast; ring
  push_cast
  calc
    _ ≤ (Real.exp ((k+1 : ℕ)*(m : ℝ)))^m := pow_le_pow_left₀ (by positivity) hb _
    _ = Real.exp (((k : ℝ)+1)*(m : ℝ)^2) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg (m : ℝ)]

lemma polynomial_exp_tendsto_zero (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => (m : ℝ)^k * Real.exp (-c*(m : ℝ))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc).comp
    tendsto_natCast_atTop_atTop
  simpa only [Real.rpow_natCast, Function.comp_def] using h

lemma large_fourier_exponent (x : ℝ) (hx : 1000000 ≤ x) :
    54*x^2 - x^4/2048 ≤ -x := by
  have hx0 : 0 ≤ x := by linarith
  have hx2 : 1000000^2 ≤ x^2 := by nlinarith
  have hprod := mul_nonneg (show 1000000^2 - (54*2048+2048 : ℝ) ≥ 0 by norm_num) (sq_nonneg x)
  have hx4 : (1000000 : ℝ)^2*x^2 ≤ x^4 := by nlinarith [mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)]
  have hxx : x ≤ x^2 := by nlinarith
  nlinarith

lemma large_chart_exponent (x : ℝ) (hx : 1000000 ≤ x) :
    6*x^2 - x^3/32 ≤ -x := by
  have hh : 1000000*x^2 ≤ x^3 := by nlinarith [mul_le_mul_of_nonneg_right hx (sq_nonneg x)]
  have hxx : x ≤ x^2 := by nlinarith
  nlinarith

lemma selection_majorant_tendsto :
    Tendsto (fun m : ℕ => 2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ))) atTop (𝓝 0) := by
  have h1 := (polynomial_exp_tendsto_zero 9 (c := 1/8) (by norm_num)).const_mul 2
  have h2 := (polynomial_exp_tendsto_zero 3 (c := 1) (by norm_num)).const_mul 6
  convert h1.add h2 using 1
  · funext m
    simp only [show -(1/8 : ℝ)*(m : ℝ) = -(m : ℝ)/8 by ring,
      show -(1 : ℝ)*(m : ℝ) = -(m : ℝ) by ring]
    ring
  · norm_num

lemma normalized_fourier_exponent {m : ℕ} (hm : 0 < m) :
    -(m : ℝ)^6*(1/(2*Real.sqrt m))^2/(2*(2*Real.sqrt m)^2) = -(m : ℝ)^4/32 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs : (2*Real.sqrt m)^2 = 4*(m : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m)]
  rw [_root_.one_div_pow, hs]
  field_simp
  ring

lemma normalized_covariance_exponent (m : ℕ) (hm : 0 < m) :
    -(m : ℝ)^6*(1/8)^2/(2*(4*(m : ℝ))^2) = -(m : ℝ)^4/2048 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

lemma probability_majorization {m : ℕ} (hm : 1000000 ≤ m) {A B : ℝ}
    (_hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ≤ Real.exp (6*(m : ℝ)^2)) (hB : B ≤ Real.exp (48*(m : ℝ)^2)) :
    (m : ℝ)^3*((m : ℝ)^6*(2*Real.exp (-(m : ℝ)/8)) +
      A*B*(2*Real.exp (-(m : ℝ)^4/32)) + A*(2*Real.exp (-(m : ℝ)^4/2048))) +
      A*(2*Real.exp (-(m : ℝ)^3/32)) ≤
      2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) + 6*(m : ℝ)^3*Real.exp (-(m : ℝ)) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : (1 : ℝ) ≤ (m : ℝ)^3 := one_le_pow₀ (by linarith)
  have hf : A*B*(2*Real.exp (-(m : ℝ)^4/32)) ≤ 2*Real.exp (-(m : ℝ)) := by
    calc
      _ ≤ Real.exp (6*(m : ℝ)^2)*Real.exp (48*(m : ℝ)^2)*
          (2*Real.exp (-(m : ℝ)^4/32)) := by gcongr
      _ = 2*Real.exp (54*(m : ℝ)^2-(m : ℝ)^4/32) := by
        rw [show 54*(m : ℝ)^2-(m : ℝ)^4/32 =
          (6*(m : ℝ)^2+48*(m : ℝ)^2)+(-(m : ℝ)^4/32) by ring, Real.exp_add, Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        have := large_fourier_exponent (m : ℝ) hm'
        nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) m) 4]
  have hc : A*(2*Real.exp (-(m : ℝ)^4/2048)) ≤ 2*Real.exp (-(m : ℝ)) := by
    calc
      _ ≤ Real.exp (6*(m : ℝ)^2)*(2*Real.exp (-(m : ℝ)^4/2048)) := by gcongr
      _ = 2*Real.exp (6*(m : ℝ)^2-(m : ℝ)^4/2048) := by simp only [Real.exp_sub, neg_div, Real.exp_neg]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        have := large_fourier_exponent (m : ℝ) hm'
        nlinarith [sq_nonneg (m : ℝ)]
  have hg : A*(2*Real.exp (-(m : ℝ)^3/32)) ≤ 2*Real.exp (-(m : ℝ)) := by
    calc
      _ ≤ Real.exp (6*(m : ℝ)^2)*(2*Real.exp (-(m : ℝ)^3/32)) := by gcongr
      _ = 2*Real.exp (6*(m : ℝ)^2-(m : ℝ)^3/32) := by simp only [Real.exp_sub, neg_div, Real.exp_neg]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (large_chart_exponent _ hm')) (by norm_num)
  have hs := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (le_refl
    ((m : ℝ)^6*(2*Real.exp (-(m : ℝ)/8)))) hf) hc) (pow_nonneg (Nat.cast_nonneg m) 3)
  have he := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-(m : ℝ))).le
  have hid : (m : ℝ)^3*((m : ℝ)^6*(2*Real.exp (-(m : ℝ)/8))) =
    2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) := by ring
  nlinarith

lemma projection_failure_bound {m : ℕ} (hm : 2 ≤ m) (hlog : 0 ≤ Real.log m) :
    (m : ℝ)^6*(2*Real.exp (-(10*Real.sqrt (Real.log m))^2/2)) ≤ 1/4 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hs : -(10*Real.sqrt (Real.log m))^2/2 = -((50 : ℕ) * Real.log m) := by
    nlinarith [Real.sq_sqrt hlog]
  rw [hs, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hm0]
  have hpow : (8 : ℝ) ≤ (m : ℝ)^44 := by
    have hh : (2 : ℝ)^44 ≤ (m : ℝ)^44 := pow_le_pow_left₀ (by norm_num) hm' _
    norm_num at hh ⊢ ; linarith
  have hid : (m : ℝ)^6*(2*((m : ℝ)^50)⁻¹) = 2/(m : ℝ)^44 := by
    field_simp
  rw [hid]
  apply (div_le_iff₀ (pow_pos hm0 _)).mpr
  linarith

lemma eventual_bias_bound : ∀ᶠ m : ℕ in atTop,
    0 < m ∧ 16*Real.exp (-(m : ℝ)/12) ≤ 1/(8*(m : ℝ)) := by
  have ht := (polynomial_exp_tendsto_zero 1 (c := 1/12) (by norm_num)).const_mul 128
  have hsmall : ∀ᶠ m : ℕ in atTop,
      128*((m : ℝ)*Real.exp (-(m : ℝ)/12)) < 1 := by
    simpa only [pow_one, mul_zero, neg_mul, one_div_mul_eq_div, neg_div] using
      ht.eventually (gt_mem_nhds (by norm_num : (128 : ℝ)*0 < 1))
  filter_upwards [hsmall, eventually_ge_atTop 1] with m hs hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine ⟨by omega, (le_div_iff₀ (by positivity : (0 : ℝ) < 8*(m : ℝ))).mpr ?_⟩
  nlinarith

lemma scalar_net_error {m : ℕ} (hm : 1000 ≤ m)
    (hb : 16*Real.exp (-(m : ℝ)/12) ≤ 1/(8*(m : ℝ))) :
    (1/(2*Real.sqrt m) + 16*Real.exp (-(m : ℝ)/12))/(1-1/(m : ℝ)^3) +
      (5*(m : ℝ))*(1/(m : ℝ)^3) ≤ 2/Real.sqrt m := by
  have hx : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0 : ℝ) < m := by linarith
  have ht : 0 < Real.sqrt m := Real.sqrt_pos.mpr hx0
  have ht2 := Real.sq_sqrt hx0.le
  have htm : Real.sqrt m ≤ (m : ℝ) := by nlinarith
  have hp3 : (8 : ℝ) ≤ (m : ℝ)^3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (show (2 : ℝ) ≤ m by linarith) 3]
  have hr : 1/(m : ℝ)^3 ≤ 1/8 := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith)
  have hd : (7/8 : ℝ) ≤ 1-1/(m : ℝ)^3 := by linarith
  have hsmall : 1/(8*(m : ℝ)) ≤ 1/(8*Real.sqrt m) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hbs : 1/(2*Real.sqrt m) + 16*Real.exp (-(m : ℝ)/12) ≤ (5/8)/Real.sqrt m := by
    have he : 1/(2*Real.sqrt m) + 1/(8*Real.sqrt m) = (5/8)/Real.sqrt m := by ring
    linarith
  have hfirst : (1/(2*Real.sqrt m) + 16*Real.exp (-(m : ℝ)/12))/(1-1/(m : ℝ)^3) ≤
      (5/7)/Real.sqrt m := by
    calc
      _ ≤ ((5/8)/Real.sqrt m)/(7/8) := div_le_div₀ (by positivity) hbs (by norm_num) hd
      _ = _ := by ring
  have hlast : (5*(m : ℝ))*(1/(m : ℝ)^3) ≤ 1/Real.sqrt m := by
    rw [show (5*(m : ℝ))*(1/(m : ℝ)^3) = 5/(m : ℝ)^2 by field_simp ]
    apply (div_le_div_iff₀ (by positivity) ht).mpr
    nlinarith
  have hrest : (5/7)/Real.sqrt m + 1/Real.sqrt m ≤ 2/Real.sqrt m := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) ht.le
  linarith

lemma covariance_net_error {m : ℕ} (hm : 1000 ≤ m)
    (hb : 16*Real.exp (-(m : ℝ)/12) ≤ 1/(8*(m : ℝ))) :
    1/8 + 16*Real.exp (-(m : ℝ)/12) + 8*(m : ℝ)*(1/(m : ℝ)^3) ≤ 1/2 := by
  have hx : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0 : ℝ) < m := by linarith
  have hsm : 1/(8*(m : ℝ)) ≤ 1/8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hh : 8*(m : ℝ)*(1/(m : ℝ)^3) ≤ 1/4 := by
    rw [show 8*(m : ℝ)*(1/(m : ℝ)^3) = 8/(m : ℝ)^2 by field_simp ]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  linarith

lemma projection_net_error {m : ℕ} (hm : 1000 ≤ m) (hl : 1 ≤ Real.log m) :
    10*Real.sqrt (Real.log m) + 2*Real.sqrt m*(1/(m : ℝ)^3) ≤
      11*Real.sqrt (Real.log m) := by
  have hx : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0 : ℝ) < m := by linarith
  have ht := Real.sq_sqrt hx0.le
  have htm : Real.sqrt m ≤ (m : ℝ) := by nlinarith [Real.sqrt_nonneg (m : ℝ)]
  have hs : 1 ≤ Real.sqrt (Real.log m) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ Real.log m by linarith), Real.sqrt_nonneg (Real.log m)]
  have hg : 2*Real.sqrt m*(1/(m : ℝ)^3) ≤ 1 := by
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    have hp : (m : ℝ)^2 ≤ (m : ℝ)^3 := by
      nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ m by linarith) (sq_nonneg (m : ℝ))]
    nlinarith
  linarith

end UniformSparsestCut.DirectionAsymptotics

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.DirectionFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.DirectionFamily
open Directions DirectionInterpolation DirectionAsymptotics GaussianTools FiniteNets
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma normBounds_of_not_bad {g : Fin N → E} (hg : g ∉ normBad) (i : Fin N) :
    (m : ℝ)/4 ≤ ‖g i‖^2 ∧ ‖g i‖^2 ≤ 4*(m : ℝ) := by
  constructor
  · by_contra h; exact hg ⟨i, Or.inl (lt_of_not_ge h)⟩
  · by_contra h; exact hg ⟨i, Or.inr (lt_of_not_ge h)⟩

lemma inner_empiricalSin (g : Fin N → E) (v w : E) :
    inner ℝ (empiricalSin g w - Real.exp (-‖w‖^2/2) • w) v =
      (∑ i, inner ℝ (g i) v * Real.sin (inner ℝ (g i) w))/(N : ℝ) -
      inner ℝ w v * Real.exp (-‖w‖^2/2) := by
  simp only [empiricalSin, inner_sub_left, inner_smul_left, conj_trivial,
    sum_inner, div_eq_mul_inv]
  congr 1
  · rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

lemma net_fourier_scalar (hm : 0 < m) {g : Fin N → E} (hg : g ∉ normBad)
    {u : ℝ} (v w : E) (hv : ‖v‖ = 1) (hf : g ∉ fourierBad u v w) :
    |inner ℝ (empiricalSin g w - Real.exp (-‖w‖^2/2) • w) v| ≤
      u + 16*Real.exp (-(m : ℝ)/12) := by
  have hsample (i : Fin N) : fourierSummand v w (g i) =
      inner ℝ (g i) v * Real.sin (inner ℝ (g i) w) := by
    dsimp only [fourierSummand, covarianceSummand, truncate]
    exact Set.indicator_of_mem (show g i ∈ {z : E | ‖z‖^2 ≤ 4*(m : ℝ)} from
      (normBounds_of_not_bad hg i).2) _
  have hdev : |(∑ i, fourierSummand v w (g i))/(N : ℝ) -
      ∫ z, fourierSummand v w z ∂stdGaussian E| ≤ u := le_of_not_gt hf
  simp_rw [hsample] at hdev
  rw [inner_empiricalSin]
  have hb := truncation_fourier_bias (show 1 ≤ m by omega) v w hv
  exact (abs_sub_le _ (∫ z, fourierSummand v w z ∂stdGaussian E) _).trans (add_le_add hdev hb)

lemma net_covariance_scalar {g : Fin N → E} (hg : g ∉ normBad)
    (v : E) (hv : ‖v‖ = 1) (hf : g ∉ covarianceBad v) :
    |empiricalCov g v - 1| ≤ 1/8 + 16*Real.exp (-(m : ℝ)/12) := by
  have hsample (i : Fin N) : covarianceSummand v (g i) = (inner ℝ v (g i))^2 := by
    dsimp only [fourierSummand, covarianceSummand, truncate]
    exact Set.indicator_of_mem (show g i ∈ {z : E | ‖z‖^2 ≤ 4*(m : ℝ)} from
      (normBounds_of_not_bad hg i).2) _
  have hdev : |(∑ i, covarianceSummand v (g i))/(N : ℝ) -
      ∫ z, covarianceSummand v z ∂stdGaussian E| ≤ 1/8 := le_of_not_gt hf
  simp_rw [hsample] at hdev
  exact (abs_sub_le _ (∫ z, covarianceSummand v z ∂stdGaussian E) _).trans
    (add_le_add hdev (truncation_covariance_bias v hv))

lemma source_nets (hm : 2 ≤ m) : ∃ V W : Finset E,
    (∀ v ∈ V, ‖v‖ = 1) ∧
    (V.card : ℝ) ≤ Real.exp (6*(m : ℝ)^2) ∧
    (W.card : ℝ) ≤ Real.exp (48*(m : ℝ)^2) ∧
    (∀ v : E, ‖v‖ = 1 → ∃ v' ∈ V, ‖v-v'‖ ≤ 1/(m : ℝ)^3) ∧
    (∀ w : E, ‖w‖ ≤ (m : ℝ)^42 → ∃ w' ∈ W, ‖w-w'‖ ≤ 1/(m : ℝ)^3) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hδ : (0 : ℝ) < 1/(m : ℝ)^4 := by positivity
  have hid : (m : ℝ) * (1/(m : ℝ)^4) = 1/(m : ℝ)^3 := by field_simp
  obtain ⟨V,hV,hVc,hVnet⟩ := exists_coordinate_net (K := m^4) hδ {v : E | ‖v‖ = 1} (by
    intro v hv
    change ‖v‖ = 1 at hv
    rw [hv, Nat.cast_pow]
    simp [hm0.ne'])
  obtain ⟨W,hW,hWc,hWnet⟩ := exists_coordinate_net (K := m^46) hδ {w : E | ‖w‖ ≤ (m : ℝ)^42} (by
    intro w hw
    change ‖w‖ ≤ (m : ℝ)^42 at hw
    have he : (((m^46 : ℕ) : ℝ))*(1/(m : ℝ)^4) = (m : ℝ)^42 := by push_cast; field_simp
    rwa [he])
  refine ⟨V,W,hV,?_,?_,?_,?_⟩
  · exact (Nat.cast_le.mpr hVc).trans (by simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, show (4+2 : ℝ) = 6 by norm_num] using grid_card_bound m 4 hm)
  · exact (Nat.cast_le.mpr hWc).trans (by simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, show (46+2 : ℝ) = 48 by norm_num] using grid_card_bound m 46 hm)
  · intro v hv; simpa only [hid] using hVnet v hv
  · intro w hw; simpa only [hid] using hWnet w hw

lemma badCount_le_of_imp {A B : Set (Fin N → E)} (g : Fin S → Fin N → E)
    (h : ∀ s, g s ∈ A → g s ∈ B) : badCount A g ≤ badCount B g := by
  classical
  apply Finset.card_le_card
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact h s hs

lemma good_chart_interpolation {N S : ℕ} (g : Fin S → Fin N → E)
    (hg : ∀ s, g s ∉ normBad) {v v' : E} {ρ q q' : ℝ}
    (hd : ‖v-v'‖ ≤ ρ) (hq : q+2*Real.sqrt m*ρ ≤ q') :
    badCount (projectionBad q' v) g ≤ badCount (projectionBad q v') g := by
  apply badCount_le_of_imp g
  intro s hs
  by_contra hn
  obtain ⟨i,hi⟩ := hs
  have hp : |inner ℝ v' (g s i)| ≤ q := by
    by_contra h; exact hn ⟨i,lt_of_not_ge h⟩
  have hgn : ‖g s i‖ ≤ 2*Real.sqrt m := by
    have := (normBounds_of_not_bad (hg s) i).2
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m), Real.sqrt_nonneg (m : ℝ), norm_nonneg (g s i)]
  have hh := (projection_interpolate hgn (by positivity) hd hp).trans hq
  exact not_lt_of_ge hh hi

end UniformSparsestCut.DirectionFamily

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.PivotFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.PivotFamily
open UniformSparsestCut.GaussianTools UniformSparsestCut.Directions
open UniformSparsestCut.DirectionFamily UniformSparsestCut.DirectionAsymptotics
open UniformSparsestCut.DirectionInterpolation
open scoped NNReal

lemma standard_density_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one,mul_one,sub_zero]
  have hs : 1 ≤ Real.sqrt (2*Real.pi) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.pi_gt_three])
  have hex : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hi : (√(2*Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  simpa using mul_le_mul hi hex (Real.exp_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

lemma standard_small_ball {a : ℝ} (ha : 0 ≤ a) :
    (gaussianReal 0 1).real {x | |x| ≤ a} ≤ 2*a := by
  have hs : {x : ℝ | |x| ≤ a} = Icc (-a) a := by ext (x : ℝ); exact (abs_le : |x| ≤ a ↔ -a ≤ x ∧ x ≤ a)
  rw [hs,measureReal_def,gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  calc
    _ ≤ ∫ x in Icc (-a) a, (1:ℝ) := by
      apply integral_mono (integrable_gaussianPDFReal 0 1).integrableOn (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      exact standard_density_le_one
    _ = 2*a := by
      rw [integral_const,measureReal_def,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith : 0 ≤ a-(-a))]
      simp only [smul_eq_mul,mul_one]; ring

lemma coordinate_small_ball {m : ℕ} (j : Fin m) {a : ℝ} (ha : 0 ≤ a) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).real {x | |x j| ≤ a} ≤ 2*a := by
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin m))).map (fun x => x j) = gaussianReal 0 1 := by
    have h := gaussian_inner_law (EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin m))
    have he : (⟨‖(EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin m))‖^2, sq_nonneg _⟩ : NNReal) = 1 := by
      apply Subtype.ext
      simp
    rw [he] at h
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at h
    exact h
  have h := congrArg (fun μ : Measure ℝ => μ.real {x | |x| ≤ a}) hmap
  simp only [measureReal_def] at h
  rw [Measure.map_apply_of_aemeasurable (by fun_prop) (by measurability)] at h
  exact h.le.trans (standard_small_ball ha)

lemma all_coordinate_small_ball {m N S : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    (Measure.pi (fun _ : Fin S => Measure.pi (fun _ : Fin N => stdGaussian (EuclideanSpace ℝ (Fin m))))).real
      {g | ∃ s i j, |g s i j| ≤ a} ≤ (S:ℝ)*((N:ℝ)*((m:ℝ)*(2*a))) := by
  have hcol : (stdGaussian (EuclideanSpace ℝ (Fin m))).real {x | ∃ j, |x j| ≤ a} ≤ (m:ℝ)*(2*a) := by
    simpa only [Fintype.card_fin,Set.mem_ofPred_eq] using finite_union_bound (fun j : Fin m => {x : EuclideanSpace ℝ (Fin m) | |x j| ≤ a}) (fun j => coordinate_small_ball j ha)
  have hchart := real_measure_exists_le (μ := stdGaussian (EuclideanSpace ℝ (Fin m)))
    (fun _ : Fin N => {x : EuclideanSpace ℝ (Fin m) | ∃ j, |x j| ≤ a}) (fun _ => by measurability) (fun _ => hcol)
  exact real_measure_exists_le
    (fun _ : Fin S => {g : Fin N → EuclideanSpace ℝ (Fin m) | ∃ i j, |g i j| ≤ a})
    (fun _ => by measurability) (fun _ => hchart)

section ExtraSelection
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => stdGaussian E
local notation "ν" => Measure.pi (fun _ : Fin N => μ)
local notation "π" => Measure.pi (fun _ : Fin S => ν)
theorem select_on_nets_extra (hm : 0 < m) (hN : 0 < N) (hS : 0 < S)
    (V W : Finset E) (hV : ∀ v ∈ V, ‖v‖ = 1)
    {u q : ℝ} (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hqprob : (N : ℝ)*(2*Real.exp (-q^2/2)) ≤ 1/4)
    {P : (Fin S → Fin N → E) → Prop} (hP : ∀ᵐ g ∂π, P g)
    (Q : Set (Fin S → Fin N → E)) {p : ℝ} (hQ : (π).real Q ≤ p)
    (hprob : (S : ℝ) * ((N : ℝ)*(2*Real.exp (-(m : ℝ)/8)) +
        (V.card : ℝ)*(W.card : ℝ)*(2*Real.exp (-(N : ℝ)*u^2/(2*(2*Real.sqrt m)^2))) +
        (V.card : ℝ)*(2*Real.exp (-(N : ℝ)*(1/8)^2/(2*(4*(m : ℝ))^2)))) +
        (V.card : ℝ)*(2*Real.exp (-(S : ℝ)/32)) + p < 1) :
    ∃ g : Fin S → Fin N → E, P g ∧ g ∉ Q ∧
      (∀ s, g s ∉ normBad) ∧
      (∀ s, ∀ v ∈ V, ∀ w ∈ W, g s ∉ fourierBad u v w) ∧
      (∀ s, ∀ v ∈ V, g s ∉ covarianceBad v) ∧
      (∀ v ∈ V, (badCount (projectionBad q v) g : ℝ) ≤ (S : ℝ)/2) := by
  classical
  let A := chartBad (N := N) V W u
  let B : Set (Fin S → Fin N → E) := {g | ∃ s, g s ∈ A}
  let C : Set (Fin S → Fin N → E) :=
    {g | ∃ v : V, (S : ℝ)/2 < (badCount (projectionBad q v) g : ℝ)}
  have hBbound := real_measure_exists_le (fun _ : Fin S => A)
    (fun _ => chartBad_measurable V W u) (fun _ => chartBad_bound hm hN V W hV hu)
  have hCbound := goodBad_bound hS V hV hq hqprob
  have hBC : (π).real ((B ∪ C) ∪ Q) < 1 :=
    ((measureReal_union_le (B ∪ C) Q).trans
      (add_le_add ((measureReal_union_le B C).trans (add_le_add hBbound hCbound)) hQ)).trans_lt hprob
  obtain ⟨g, hg0, hgP⟩ := exists_outside_with_ae hBC hP
  have hg : g ∉ B ∪ C := fun h => hg0 (Or.inl h)
  have hgQ : g ∉ Q := fun h => hg0 (Or.inr h)
  have hgB : ∀ s, g s ∉ A := by
    intro s hs; exact hg (Or.inl ⟨s, hs⟩)
  refine ⟨g, hgP, hgQ, ?_, ?_, ?_, ?_⟩
  · intro s hs; exact hgB s (Or.inl (Or.inl hs))
  · intro s v hv w hw hs; exact hgB s (Or.inl (Or.inr ⟨(⟨v,hv⟩,⟨w,hw⟩), hs⟩))
  · intro s v hv hs; exact hgB s (Or.inr ⟨⟨v,hv⟩, hs⟩)
  · intro v hv; by_contra h
    exact hg (Or.inr ⟨⟨v,hv⟩, lt_of_not_ge h⟩)

end ExtraSelection

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma select_source_nets_pivot (hm : 1000000 ≤ m) (hlog : 1 ≤ Real.log m)
    (hmajor : 2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ)) + 2/(m:ℝ)^20 < 1)
    (V W : Finset E) (hV : ∀ v ∈ V, ‖v‖ = 1)
    (hVc : (V.card : ℝ) ≤ Real.exp (6*(m : ℝ)^2))
    (hWc : (W.card : ℝ) ≤ Real.exp (48*(m : ℝ)^2)) :
    ∃ g : Fin (m^3) → Fin (m^6) → E,
      (∀ s a b, a ≠ b → ∀ t : ℝ, g s a ≠ t • g s b) ∧
      (∀ s i j, 1/(m:ℝ)^30 < |g s i j|) ∧
      (∀ s, g s ∉ normBad) ∧
      (∀ s, ∀ v ∈ V, ∀ w ∈ W, g s ∉ fourierBad (1/(2*Real.sqrt m)) v w) ∧
      (∀ s, ∀ v ∈ V, g s ∉ covarianceBad v) ∧
      (∀ v ∈ V, (badCount (projectionBad (10*Real.sqrt (Real.log m)) v) g : ℝ) ≤
        ((m^3 : ℕ) : ℝ)/2) := by
  have hm0 : 0 < m := by omega
  have hsmall := all_coordinate_small_ball (m := m) (N := m^6) (S := m^3) (by positivity : (0:ℝ) ≤ 1/(m:ℝ)^30)
  have hp : ((m^3:ℕ):ℝ)*(((m^6:ℕ):ℝ)*((m:ℝ)*(2*(1/(m:ℝ)^30)))) = 2/(m:ℝ)^20 := by
    push_cast; field_simp
  rw [hp] at hsmall
  obtain ⟨g,hg,hQ,hrest⟩  := select_on_nets_extra (N := m^6) (S := m^3) hm0 (pow_pos hm0 _) (pow_pos hm0 _)
    V W hV (by positivity : (0:ℝ) ≤ 1/(2*Real.sqrt m))
    (by positivity : (0:ℝ) ≤ 10*Real.sqrt (Real.log m))
    (by
      simpa only [Nat.cast_pow] using (projection_failure_bound (show 2 ≤ m by omega)
        (show 0 ≤ Real.log m by linarith)))
    (GaussianNonparallel.charts_pairwise_nonparallel (show 2 ≤ m by omega))
    {g | ∃ s i j, |g s i j| ≤ 1/(m:ℝ)^30} hsmall (by
      simp only [Nat.cast_pow]
      rw [normalized_fourier_exponent hm0, normalized_covariance_exponent m hm0]
      exact (add_le_add_left (probability_majorization hm (Nat.cast_nonneg _) (Nat.cast_nonneg _) hVc hWc) _).trans_lt hmajor)
  refine ⟨g,hg,?_,hrest⟩
  intro s i j
  exact lt_of_not_ge (fun h => hQ ⟨s,i,j,h⟩)

lemma pivot_family_at_large (hm : 1000000 ≤ m) (hlog : 1 ≤ Real.log m)
    (hbias : 16*Real.exp (-(m : ℝ)/12) ≤ 1/(8*(m : ℝ)))
    (hmajor : 2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ)) + 2/(m:ℝ)^20 < 1) : Nonempty (PFamily m) := by
  classical
  obtain ⟨V,W,hV,hVc,hWc,hVnet,hWnet⟩ := source_nets (show 2 ≤ m by omega)
  obtain ⟨g,hpar,hpivot,hg,hfour,hcov,hgood⟩ := select_source_nets_pivot hm hlog hmajor V W hV hVc hWc
  have hm0 : 0 < m := by omega
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hn : 0 < m^6 := pow_pos hm0 _
  have hu (s : Fin (m^3)) (i : Fin (m^6)) : ‖g s i‖^2 ≤ 4*(m : ℝ) :=
    (normBounds_of_not_bad (hg s) i).2
  refine ⟨{ g := g, norms := ?_, nonparallel := hpar, covariance := ?_, fourier := ?_, good := ?_, pivot := hpivot }⟩
  · intro s i
    have h := normBounds_of_not_bad (hg s) i
    have hs := Real.sq_sqrt hm0'.le
    constructor <;> nlinarith [Real.sqrt_nonneg (m : ℝ), norm_nonneg (g s i)]
  · intro s v hv
    have hh := covariance_net_bound hn (g s) (hu s) (by positivity) V hV hVnet
      (fun v hv => net_covariance_scalar (hg s) v (hV v hv) (hcov s v hv)) v hv
    have herr := covariance_net_error (show 1000 ≤ m by omega) hbias
    have heq : 2*(4*(m : ℝ))*(1/(m : ℝ)^3) = 8*(m : ℝ)*(1/(m : ℝ)^3) := by ring
    rw [heq] at hh
    have hab := abs_le.mp (hh.trans herr)
    constructor <;> linarith
  · intro s w hw
    have hρ : 1/(m : ℝ)^3 < 1 := by
      apply (div_lt_one (by positivity)).mpr
      have hx : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 3
      norm_num at hh; linarith
    have hh := fourier_net_bound hn (g s) (hu s) (by positivity) (by positivity) hρ V W
      hVnet hWnet (fun v hv w hw => net_fourier_scalar hm0 (hg s) v w (hV v hv) (hfour s v hv w hw)) w hw
    have herr := scalar_net_error (show 1000 ≤ m by omega) hbias
    have heq : 4*(m : ℝ)+(m : ℝ) = 5*(m : ℝ) := by ring
    rw [heq] at hh
    exact hh.trans herr
  · intro v hv
    obtain ⟨v',hv',hd⟩ := hVnet v hv
    have hh := good_chart_interpolation g hg hd (projection_net_error (show 1000 ≤ m by omega) hlog)
    exact (Nat.cast_le.mpr hh).trans (hgood v' hv')

lemma pivot_majorant_tendsto :
    Tendsto (fun m : ℕ => 2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ)) + 2/(m:ℝ)^20) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => (m:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := (hi.pow 20).const_mul 2
  have h := selection_majorant_tendsto.add hh
  simpa [div_eq_mul_inv,inv_pow] using h

theorem pivot_directions_exist : ∀ᶠ m : ℕ in atTop, Nonempty (PFamily m) := by
  have hlog : ∀ᶠ m : ℕ in atTop, 1 ≤ Real.log m :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hmajor := pivot_majorant_tendsto.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [eventually_ge_atTop 1000000,hlog,eventual_bias_bound,hmajor] with m hm hl hb hp
  exact pivot_family_at_large hm hl hb.2 hp

end UniformSparsestCut.PivotFamily

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.KernelApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.KernelApprox

lemma profile_nonneg (t : ℝ) : 0 ≤ profile t := by
  unfold profile
  have h : -1/(2*t^2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  linarith [Real.exp_le_one_iff.mpr h]

lemma profile_le_one (t : ℝ) : profile t ≤ 1 := by
  unfold profile
  linarith [Real.exp_pos (-1/(2*t^2))]

lemma profile_le_inv_sq (t : ℝ) : profile t ≤ 1/(2*t^2) := by
  have h := Real.add_one_le_exp (-1/(2*t^2))
  unfold profile
  rw [neg_div] at h ⊢
  linarith

lemma profile_pos {t : ℝ} (ht : t ≠ 0) : 0 < profile t := by
  unfold profile
  have h : -1/(2*t^2) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  linarith [Real.exp_lt_one_iff.mpr h]

lemma profile_measurable : Measurable profile := by unfold profile; fun_prop

lemma profile_integrable_lower : IntegrableOn profile (Ioc 0 1) := by
  apply (integrableOn_const (C := (1 : ℝ)) (s := Ioc (0 : ℝ) 1) (by simp)).mono'
    profile_measurable.aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg t)] using profile_le_one t

lemma profile_integrable_upper : IntegrableOn profile (Ioi 1) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)).const_mul (1/2 : ℝ)
  apply hi.mono' profile_measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 1 < t at ht
  have he : (1/2 : ℝ)*t^(-2 : ℝ) = 1/(2*t^2) := by
    rw [Real.rpow_neg (by linarith : 0 ≤ t), Real.rpow_two]
    ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg t), he] using profile_le_inv_sq t

lemma profile_integrable : IntegrableOn profile (Ioi 0) := by
  have h := profile_integrable_lower.union profile_integrable_upper
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] using h

lemma cstar_pos : 0 < cstar := by
  have hp : 0 < ∫ t in Ioi (0 : ℝ), profile t := by
    apply (integral_pos_iff_support_of_nonneg_ae _ profile_integrable).mpr
    · have hs : Ioi (0 : ℝ) ⊆ Function.support profile := by
        intro t ht
        exact ne_of_gt (profile_pos (ne_of_gt ht))
      have hc : (volume.restrict (Ioi (0 : ℝ))) (Ioi (0 : ℝ)) ≠ 0 := by simp
      exact bot_lt_iff_ne_bot.mpr (ne_bot_of_le_ne_bot hc (measure_mono hs))
    · filter_upwards with t using profile_nonneg t
  exact mul_pos (by norm_num) hp

end UniformSparsestCut.KernelApprox

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceMetric
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) [NeZero m]
lemma C₀_pos : 0<C₀ := by unfold C₀; linarith [KernelApprox.cstar_pos]
end
end UniformSparsestCut.SourceMetric

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ContractionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceContraction
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts SourceMetric
open MeasureTheory
noncomputable section
lemma H_nonneg : 0≤H := integral_nonneg (fun _ => abs_nonneg _)
lemma C_pos : 0<C := by
  have hc := KernelApprox.cstar_pos
  have hr := C₀_pos
  have hh := H_nonneg
  unfold C
  positivity
end
end UniformSparsestCut.SourceContraction

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Logarithms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.RateComparison
open Filter
noncomputable section
lemma weight_pos {d : ℕ} (hd : 0<d) (hl : 1≤Real.log d) : 0<weight d := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hl' : 0<Real.log d := by linarith
  unfold weight
  positivity
lemma logarithms {d n : ℕ} (hd : 0<d) (hl : 1≤Real.log d)
    (hnlo : d^d≤n) (hnhi : n≤d^(4030*d)) :
    0<Real.log n ∧ Real.log d≤Real.log (Real.log n) ∧
      Real.log n≤4030*(d:ℝ)*Real.log d := by
  have hx : (0:ℝ)<d := by exact_mod_cast hd
  have hlo : (d:ℝ)*Real.log d≤Real.log n := by
    calc
      _ = Real.log ((d:ℝ)^d) := (Real.log_pow _ _).symm
      _ ≤ _ := Real.log_le_log (by positivity) (by exact_mod_cast hnlo)
  have hdn : (d:ℝ)≤Real.log n := (le_mul_of_one_le_right hx.le hl).trans hlo
  have hn0 : 0<n := (pow_pos hd _).trans_le hnlo
  have hn0' : (0:ℝ)<n := by exact_mod_cast hn0
  refine ⟨hx.trans_le hdn,Real.log_le_log hx hdn,?_⟩
  calc
    _ ≤ Real.log ((d:ℝ)^(4030*d)) := Real.log_le_log hn0' (by exact_mod_cast hnhi)
    _ = _ := by rw [Real.log_pow]; push_cast; ring
lemma bound {d n : ℕ} (hd : 0<d) (hl : 1≤Real.log d)
    (hnlo : d^d≤n) (hnhi : n≤d^(4030*d)) :
    Real.sqrt (Real.log n)/(Real.log (Real.log n))^3≤Real.sqrt 4030*(d:ℝ)/weight d := by
  have hx : (0:ℝ)<d := by exact_mod_cast hd
  have hℓ : 0<Real.log d := by linarith
  obtain ⟨hn0,hll,hln⟩ := logarithms hd hl hnlo hnhi
  have hll0 : 0<Real.log (Real.log n) := hℓ.trans_le hll
  have hs : Real.sqrt (Real.log n)≤Real.sqrt 4030*Real.sqrt d*Real.sqrt (Real.log d) := by
    calc
      _ ≤ Real.sqrt (4030*(d:ℝ)*Real.log d) := Real.sqrt_le_sqrt hln
      _ = _ := by rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by norm_num)]
  apply (div_le_div_iff₀ (pow_pos hll0 _) (weight_pos hd hl)).mpr
  have hlim := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hℓ.le hll 3)
    (mul_nonneg (Real.sqrt_nonneg 4030) hx.le)
  calc
    _ ≤ (Real.sqrt 4030*Real.sqrt d*Real.sqrt (Real.log d))*weight d :=
      mul_le_mul_of_nonneg_right hs (weight_pos hd hl).le
    _ = Real.sqrt 4030*(d:ℝ)*(Real.log d)^3 := by
      unfold weight
      calc
        _ = Real.sqrt 4030*(Real.sqrt d)^2*(Real.sqrt (Real.log d))^2*(Real.log d)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hx.le,Real.sq_sqrt hℓ.le]; ring
    _ ≤ _ := hlim
lemma gap_of_gl {d n : ℕ} (hd : 0<d) (hl : 1≤Real.log d)
    (hnlo : d^d≤n) (hnhi : n≤d^(4030*d))
    {α β opt gl : ℝ} (hα : 0<α) (hβ : 0<β) (hopt : 1≤opt) (hgl : 0<gl)
    (hbound : gl≤β*weight d/(α*(d:ℝ))) :
    (α/(β*Real.sqrt 4030))*Real.sqrt (Real.log n)/(Real.log (Real.log n))^3≤opt/gl := by
  have hx : (0:ℝ)<d := by exact_mod_cast hd
  have hw := weight_pos hd hl
  have hs : (0:ℝ)<Real.sqrt 4030 := by positivity
  have hr := bound hd hl hnlo hnhi
  have hconst : 0<α/(β*Real.sqrt 4030) := by positivity
  have hratio : α*(d:ℝ)/(β*weight d)≤opt/gl := by
    apply (div_le_div_iff₀ (mul_pos hβ hw) hgl).mpr
    have h := (le_div_iff₀ (mul_pos hα hx)).mp hbound
    have h' := mul_le_mul_of_nonneg_right hopt (mul_pos hβ hw).le
    nlinarith only [h,h']
  calc
    _ = (α/(β*Real.sqrt 4030))*(Real.sqrt (Real.log n)/(Real.log (Real.log n))^3) := by ring
    _ ≤ (α/(β*Real.sqrt 4030))*(Real.sqrt 4030*(d:ℝ)/weight d) :=
      mul_le_mul_of_nonneg_left hr hconst.le
    _ = α*(d:ℝ)/(β*weight d) := by field_simp
    _ ≤ _ := hratio
end
end UniformSparsestCut.RateComparison

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut
open Filter
noncomputable section

theorem mainGap_oai :
    ∃ c : ℝ, 0 < c ∧
      ∃ n : ℕ → ℕ, ∃ C : (j : ℕ) → Capacity (n j),
        (∀ j, 2 ≤ n j) ∧
        Tendsto n atTop atTop ∧
        (∀ j, 0 < glValue (C j)) ∧
        ∀ᶠ j in atTop,
          c * Real.sqrt (Real.log (n j : ℝ)) / (Real.log (Real.log (n j : ℝ))) ^ 3 ≤
            OPT (C j) / glValue (C j) := by
  classical
  let α : ℝ := KernelApprox.cstar/6
  let β : ℝ := SourceContraction.C+1
  have hα : 0<α := div_pos KernelApprox.cstar_pos (by norm_num)
  have hβ : 0<β := by have hc := SourceContraction.C_pos; dsimp [β]; linarith
  have hcast : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ d : ℕ in atTop, Nonempty (PivotFamily.PFamily d) ∧
      3000≤d ∧ 1≤Real.log d ∧ SourceContraction.H≤(d:ℝ) ∧
      4*SourceWeighted.D≤(d:ℝ) ∧ SourceMetric.C₀+1≤α*(d:ℝ) := by
    filter_upwards [PivotFamily.pivot_directions_exist,eventually_ge_atTop 3000,
      (Real.tendsto_log_atTop.comp hcast).eventually (eventually_ge_atTop 1),
      hcast.eventually (eventually_ge_atTop SourceContraction.H),
      hcast.eventually (eventually_ge_atTop (4*SourceWeighted.D)),
      hcast.eventually (eventually_ge_atTop ((SourceMetric.C₀+1)/α))] with d hf hd hl hH hD ha
    exact ⟨hf,hd,hl,hH,hD,by simpa only [mul_comm] using (div_le_iff₀ hα).mp ha⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  have hex : ∀ j : ℕ, ∃ (n : ℕ) (C : Capacity n),
      (j+N+1)^(j+N+1)≤n ∧ n≤(j+N+1)^(4030*(j+N+1)) ∧
      2≤n ∧ 1≤OPT C ∧ 0<glValue C ∧ glValue C≤β*RateComparison.weight (j+N+1:ℕ)/(α*(j+N+1:ℕ)) := by
    intro j
    obtain ⟨⟨f⟩,hd,hl,hH,hD,ha⟩ := hN (j+N+1) (by omega)
    exact SourceUniform.instance_exists f hd hl hH hD ha
  choose n C hlo hhi hn hopt hgl hbound using hex
  refine ⟨α/(β*Real.sqrt 4030),by positivity,n,C,hn,?_,hgl,?_⟩
  · apply tendsto_atTop_mono (fun j => ?_) tendsto_id
    have hd1 : 1≤j+N+1 := by omega
    have hp : j+N+1≤(j+N+1)^(j+N+1) := by
      simpa using (Nat.pow_le_pow_right hd1 hd1 : (j+N+1)^1≤(j+N+1)^(j+N+1))
    exact (show j≤j+N+1 by omega).trans (hp.trans (hlo j))
  · exact Filter.Eventually.of_forall (fun j => RateComparison.gap_of_gl
      (by omega : 0<j+N+1) (hN (j+N+1) (by omega)).2.2.1
      (hlo j) (hhi j) hα hβ (hopt j) (hgl j) (hbound j))
end
end UniformSparsestCut

end

end OAI
end

theorem solution : type_of% @OAI.UniformSparsestCut.mainGap_oai := @OAI.UniformSparsestCut.mainGap_oai

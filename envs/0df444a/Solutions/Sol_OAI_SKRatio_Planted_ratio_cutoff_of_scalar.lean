-- Prove2me | solution 1 for OAI.SKRatio.Planted.ratio_cutoff_of_scalar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:20:00.634004+00:00
-- url     : https://prove2.me/submissions/2539b486-b1f5-4a2f-9e62-49829183fca5

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S016
import Theorems.Thm_OAI_SKRatio_Bins_random_binForm_tail
import Theorems.Thm_OAI_SKRatio_Planted_ratio_cutoff_of_planted_form
import Theorems.Thm_OAI_SKRatio_Planted_reduced_error_rare
import Theorems.Thm_OAI_SKRatio_Planted_residual_norm_rare

section
-- module Solutions.OAIQ024_SK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_PlusSpin
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus

open Real Set

lemma hasDerivAt_tanh (y : ℝ) : HasDerivAt tanh (1 - tanh y ^ 2) y := by
  convert! (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (cosh_pos y).ne' using 1
  · ext x
    exact tanh_eq_sinh_div_cosh x
  · rw [tanh_eq_sinh_div_cosh]
    field_simp

lemma tanh_lipschitz_abs (x y : ℝ) : |tanh x-tanh y| ≤ |x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (univ : Set ℝ)) => (hasDerivAt_tanh z).hasDerivWithinAt)
    (C := 1) (fun z _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (tanh_sq_lt_one z).le)]
      linarith [sq_nonneg (tanh z)]) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs,one_mul] using hh

lemma gradientWeight_pos {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    0 < gradientWeight J x i := by
  cases hi : x i
  · have h := Real.neg_one_lt_tanh (field J x i)
    simp only [gradientWeight, spin, hi, Bool.false_eq_true, ↓reduceIte, neg_mul,
      one_mul, sub_neg_eq_add, mean]
    linarith
  · simpa only [gradientWeight, spin, hi, ↓reduceIte, one_mul, mean] using
      sub_pos.mpr (Real.tanh_lt_one (field J x i))

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GOERegression
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise

namespace SKRatioClock.Regression

lemma coordinate_hasLaw {ι : Type*} [Fintype ι] (i : ι) :
    HasLaw (fun g : ι → ℝ => g i) (gaussianReal 0 1) (standardArrayLaw ι) :=
  (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw

lemma coordinates_independent {ι : Type*} [Fintype ι] :
    iIndepFun (fun i (g : ι → ℝ) => g i) (standardArrayLaw ι) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

lemma coordinates_gaussian {ι : Type*} [Fintype ι] :
    HasGaussianLaw (fun g : ι → ℝ => g) (standardArrayLaw ι) :=
  coordinates_independent.hasGaussianLaw (fun i => (coordinate_hasLaw i).hasGaussianLaw)

lemma coordinate_covariance {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    cov[fun g : ι → ℝ => g i, fun g => g j; standardArrayLaw ι] = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    rw [covariance_self (coordinate_hasLaw i).aemeasurable,
      (coordinate_hasLaw i).variance_eq, variance_id_gaussianReal]
    simp
  · rw [ite_eq_right h]
    exact (coordinates_independent.indepFun h).covariance_eq_zero
      ((coordinate_hasLaw i).hasGaussianLaw.memLp_two)
      ((coordinate_hasLaw j).hasGaussianLaw.memLp_two)

lemma goe_symmetric {n : ℕ} (g : (Fin n × Fin n) → ℝ) : (goe g)ᵀ = goe g := by
  ext i j
  simp [goe, add_comm]

attribute [local instance] OAI.SKRatioClock.Regression.matrixMeasurable
local instance matrixBorel_rcb6305_1 {n m : ℕ} : BorelSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin m → ℝ))
lemma goe_gaussian (n : ℕ) :
    HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ => goe g)
      (standardArrayLaw (Fin n × Fin n)) := by
  have h := coordinates_gaussian.map_fun
    (show ((Fin n × Fin n) → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) from goeCLM n)
  exact h.congr (Filter.Eventually.of_forall (goeCLM_apply n))

lemma goe_entry_memLp {n : ℕ} (i j : Fin n) :
    MemLp (fun g : (Fin n × Fin n) → ℝ => goe g i j) 2 (standardArrayLaw (Fin n × Fin n)) :=
  ((goe_gaussian n).eval i |>.eval j).memLp_two

lemma goe_entry_covariance {n : ℕ} (hn : 0 < n) (i j k l : Fin n) :
    cov[fun g : (Fin n × Fin n) → ℝ => goe g i j, fun g => goe g k l;
        standardArrayLaw (Fin n × Fin n)] =
      ((if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) / n := by
  have hLp (a : Fin n × Fin n) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  simp only [goe, covariance_fun_div_left, covariance_fun_div_right]
  change cov[(fun g => g (i,j)) + (fun g => g (j,i)),
    (fun g => g (k,l)) + (fun g => g (l,k)); standardArrayLaw (Fin n × Fin n)] /
      Real.sqrt (2*n) / Real.sqrt (2*n) = _
  rw [covariance_add_left (hLp _) (hLp _) ((hLp _).add (hLp _)),
    covariance_add_right (hLp _) (hLp _) (hLp _),
    covariance_add_right (hLp _) (hLp _) (hLp _)]
  simp only [coordinate_covariance, Prod.mk.injEq]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (2*n) ^ 2 = 2*n := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2*(n : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  rw [div_div, ← pow_two]
  rw [hs]
  have ha : (j = k ∧ i = l) ↔ (i = l ∧ j = k) := and_comm
  have hb : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
  simp only [ha, hb]
  ring

lemma regression_decomposition {n r : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin r) ℝ) (hG : Gᵀ = G) :
    G = (G*U)*Uᵀ + U*(G*U)ᵀ - U*(Uᵀ*(G*U))*Uᵀ +
      residualProjection U * G * residualProjection U := by
  simp only [Matrix.transpose_mul, hG, residualProjection]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.mul_assoc]
  abel

lemma coordinate_mean {ι : Type*} [Fintype ι] (i : ι) :
    (∫ g : ι → ℝ, g i ∂standardArrayLaw ι) = 0 := by
  rw [(coordinate_hasLaw i).integral_eq, integral_id_gaussianReal]

lemma goe_entry_mean {n : ℕ} (i j : Fin n) :
    (∫ g : (Fin n × Fin n) → ℝ, goe g i j ∂standardArrayLaw (Fin n × Fin n)) = 0 := by
  simp only [goe, integral_div]
  rw [integral_add (coordinate_hasLaw (i,j)).hasGaussianLaw.integrable
    (coordinate_hasLaw (j,i)).hasGaussianLaw.integrable]
  simp only [coordinate_mean, add_zero, zero_div]

lemma gaussian_add_constant {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ) (c : ι → ℝ) :
    HasGaussianLaw (fun ω => X ω + c) μ := by
  have := hX.isGaussian_map
  refine ⟨?_⟩
  change IsGaussian (μ.map ((fun x : ι → ℝ => x+c) ∘ X))
  rw [← AEMeasurable.map_map_of_aemeasurable
    (by fun_prop : AEMeasurable (fun x : ι → ℝ => x+c) (μ.map X)) hX.aemeasurable]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma sharedGaussianField_gaussian (n : ℕ) (m a b : ℝ) :
    HasGaussianLaw (sharedGaussianField (n := n) m a b) (standardArrayLaw (Option (Fin n))) := by
  have hh := gaussian_add_constant (coordinates_gaussian.map_fun (sharedGaussianFieldCLM n a b))
    (fun _ : Fin n => m)
  apply hh.congr
  exact Eventually.of_forall fun g => by
    ext i
    simp [sharedGaussianFieldCLM, sharedGaussianField]
    ring

lemma sharedGaussianField_mean {n : ℕ} (m a b : ℝ) (i : Fin n) :
    (∫ g, sharedGaussianField m a b g i ∂standardArrayLaw (Option (Fin n))) = m := by
  have ha := (coordinate_hasLaw (some i)).hasGaussianLaw.integrable.const_mul a
  have hb := (coordinate_hasLaw (none : Option (Fin n))).hasGaussianLaw.integrable.const_mul b
  simp only [sharedGaussianField]
  have hai : Integrable (fun g : Option (Fin n) → ℝ => m+a*g (some i))
      (standardArrayLaw (Option (Fin n))) := (integrable_const m).add ha
  rw [integral_add hai hb,
    integral_add (integrable_const m) ha, integral_const_mul, integral_const_mul,
    coordinate_mean, coordinate_mean]
  simp

lemma sharedGaussianField_covariance {n : ℕ} (m a b : ℝ) (i k : Fin n) :
    cov[fun g => sharedGaussianField m a b g i, fun g => sharedGaussianField m a b g k;
      standardArrayLaw (Option (Fin n))] = (if i=k then a^2 else 0)+b^2 := by
  have hm (i : Fin n) : MemLp (fun g : Option (Fin n) → ℝ => a*g (some i)) 2
      (standardArrayLaw (Option (Fin n))) := (coordinate_hasLaw (some i)).hasGaussianLaw.memLp_two.const_mul a
  have hb : MemLp (fun g : Option (Fin n) → ℝ => b*g none) 2
      (standardArrayLaw (Option (Fin n))) := (coordinate_hasLaw none).hasGaussianLaw.memLp_two.const_mul b
  have he (g : Option (Fin n) → ℝ) (i : Fin n) : sharedGaussianField m a b g i =
      (a*g (some i)+b*g none)+m := by unfold sharedGaussianField; ring
  have hs (j : Fin n) : Integrable (fun g : Option (Fin n) → ℝ => a*g (some j)+b*g none)
      (standardArrayLaw (Option (Fin n))) := ((hm j).add hb).integrable (by norm_num)
  simp_rw [he]
  rw [covariance_add_const_left (hs i),
    covariance_add_const_right (hs k)]
  change cov[(fun g => a*g (some i))+(fun g => b*g none),
    (fun g => a*g (some k))+(fun g => b*g none); standardArrayLaw (Option (Fin n))] = _
  rw [covariance_add_left (hm i) hb ((hm k).add hb),
    covariance_add_right (hm i) (hm k) hb,
    covariance_add_right hb (hm k) hb]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, coordinate_covariance]
  by_cases h : i=k <;> simp [h] <;> ring

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_GaussianEmpirical
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
namespace SKRatioClock.Regression

lemma subgaussian_abs_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ {ω | ε ≤ |X ω|} ≤ 2 * ENNReal.ofReal (Real.exp (-ε^2/(2*(c:ℝ)))) := by
  have hu := ENNReal.ofReal_le_ofReal (hX.measure_ge_le hε)
  have hl := ENNReal.ofReal_le_ofReal (hX.neg.measure_ge_le hε)
  simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hu hl
  have hs : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    intro ω h
    simpa only [Set.mem_union, Set.mem_ofPred_eq, le_abs] using h
  calc
    _ ≤ _ := measure_mono hs
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add hu hl
    _ = _ := (two_mul _).symm

lemma iid_bounded_average_tail_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hXi : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) μ) (f : ℝ → ℝ)
    (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, |f z| ≤ B)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ {g |
      ε ≤ |(∑ i : Fin n, f (X i g))/(n:ℝ) - ∫ z, f z ∂gaussianReal 0 1|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(2*B^2))) := by
  let m := ∫ z, f z ∂gaussianReal 0 1
  have hi : iIndepFun (fun i (g : Ω) => f (X i g) - m) μ :=
    hXi.comp (fun _ z => f z-m) (fun _ => hf.sub_const m)
  have hm (i : Fin n) :
      (∫ g : Ω, f (X i g) ∂μ) = m := by
    exact (hX i).integral_comp hf.aestronglyMeasurable
  have hsub (i : Fin n) : HasSubgaussianMGF (fun g : Ω => f (X i g)-m)
      ((‖B-(-B)‖₊/2)^2) μ := by
    have hb : ∀ᵐ g : Ω ∂μ, f (X i g) ∈ Set.Icc (-B) B :=
      Eventually.of_forall (fun g => abs_le.mp (hbound (X i g)))
    simpa only [hm] using hasSubgaussianMGF_of_mem_Icc
      (show AEMeasurable (fun g : Ω => f (X i g)) μ from
        hf.comp_aemeasurable (hX i).aemeasurable) hb
  have hh := subgaussian_abs_tail
    (HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (fun i _ => hsub i))
    (ε*n) (by positivity)
  have he (g : Ω) :
      (ε*(n:ℝ) ≤ |∑ i : Fin n, (f (X i g)-m)|) ↔
      ε ≤ |(∑ i : Fin n, f (X i g))/(n:ℝ)-m| := by
    have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have heq : (∑ i : Fin n, f (X i g))-(n:ℝ)*m =
        (n:ℝ)*((∑ i : Fin n, f (X i g))/(n:ℝ)-m) := by field_simp
    rw [heq, abs_mul, abs_of_pos hnR]
    rw [mul_comm ε (n:ℝ), mul_le_mul_iff_right₀ hnR]
  simp only [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
    coe_nnnorm, Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith : 0 ≤ B-(-B))]
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  by_cases hB0 : B=0
  · simp [hB0]
  · field_simp
    ring

lemma gaussian_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ where
  integrable_exp_mul t := by
    rw [← mgf_pos_iff, mgf_gaussianReal hX.map_eq]
    exact Real.exp_pos _
  mgf_le t := by
    rw [mgf_gaussianReal hX.map_eq]
    simp

lemma average_common_shift_bound {n : ℕ} (hn : 0 < n) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (v : Fin n → ℝ) (r : ℝ) :
    |(∑ i, f (v i+r))/(n:ℝ) - (∑ i, f (v i))/(n:ℝ)| ≤ (K:ℝ)*|r| := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, (K:ℝ)*|r| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.dist_eq, add_sub_cancel_left] using hf.dist_le_mul (v i+r) (v i)
    _ = _ := by simp [mul_comm]

lemma iid_common_shift_average_tail {n : ℕ} (hn : 0 < n) (m a b : ℝ)
    (f : ℝ → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, |f z| ≤ B)
    (ε : ℝ) (hε : 0 ≤ ε) :
    standardArrayLaw (Option (Fin n)) {g |
      ε ≤ |(∑ i : Fin n, f (m+a*g (some i)+b*g none))/(n:ℝ) -
        ∫ z, f (m+a*z) ∂gaussianReal 0 1|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(8*B^2))) +
      2 * ENNReal.ofReal (Real.exp (-ε^2/(8*(K:ℝ)^2*b^2))) := by
  let M := ∫ z, f (m+a*z) ∂gaussianReal 0 1
  let A (g : Option (Fin n) → ℝ) := (∑ i : Fin n, f (m+a*g (some i)))/(n:ℝ)
  have hi : iIndepFun (fun i : Fin n => fun g : Option (Fin n) → ℝ => g (some i))
      (standardArrayLaw (Option (Fin n))) := coordinates_independent.precomp (Option.some_injective (Fin n))
  have ht := iid_bounded_average_tail_of_hasLaw (μ := standardArrayLaw (Option (Fin n))) hn
    (fun (i : Fin n) (g : Option (Fin n) → ℝ) => g (some i)) hi
    (fun i => coordinate_hasLaw (some i)) (fun z => f (m+a*z))
    (hf.continuous.measurable.comp (measurable_const.add (measurable_const.mul measurable_id)))
    B hB (fun z => hbound _) (ε/2) (by positivity)
  have hz := subgaussian_abs_tail
    ((gaussian_hasSubgaussianMGF (coordinate_hasLaw (none : Option (Fin n)))).const_mul ((K:ℝ)*b))
    (ε/2) (by positivity)
  have hsub : {g | ε ≤ |(∑ i : Fin n, f (m+a*g (some i)+b*g none))/(n:ℝ)-M|} ⊆
      {g | ε/2 ≤ |A g-M|} ∪ {g | ε/2 ≤ |(K:ℝ)*b*g none|} := by
    intro g hg
    by_cases ha : ε/2 ≤ |A g-M|
    · exact Or.inl ha
    apply Or.inr
    have hd := average_common_shift_bound hn hf (fun i => m+a*g (some i)) (b*g none)
    have htri := abs_add_le
      ((∑ i : Fin n, f (m+a*g (some i)+b*g none))/(n:ℝ) - A g) (A g-M)
    have hrad : (K:ℝ)*|b*g none| = |(K:ℝ)*b*g none| := by
      simp [abs_mul, abs_of_nonneg K.coe_nonneg, mul_assoc]
    rw [hrad] at hd
    simp only [sub_add_sub_cancel] at htri
    change ε ≤ _ at hg
    change |(∑ i : Fin n, f (m+a*g (some i)+b*g none))/(n:ℝ) - A g| ≤ _ at hd
    have : |A g-M| < ε/2 := lt_of_not_ge ha
    change ε/2 ≤ |(K:ℝ)*b*g none|
    linarith
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  have h1 : standardArrayLaw (Option (Fin n)) {g | ε/2 ≤ |A g-M|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(8*B^2))) := by
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    congr 3
    ring
  have h2 : standardArrayLaw (Option (Fin n)) {g | ε/2 ≤ |(K:ℝ)*b*g none|} ≤
      2 * ENNReal.ofReal (Real.exp (-ε^2/(8*(K:ℝ)^2*b^2))) := by
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    congr 3
    change -ε^2 / (8 * (K:ℝ)^2 * b^2) = -(ε / 2)^2 / (2 * ((((K:ℝ)*b)^2) * 1))
    ring
  exact add_le_add h1 h2

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_ExponentialEvents
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKRatioClock.Regression

lemma ExponentiallyRare.mono {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {A B : ∀ n, Set (H n)}
    (hB : ExponentiallyRare ρ B) (hAB : ∀ᶠ n in atTop, A n ⊆ B n) :
    ExponentiallyRare ρ A := by
  obtain ⟨C,c,hC,hc,he⟩ := hB
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [he,hAB] with n hn hABn
  exact (measure_mono hABn).trans hn

lemma ExponentiallyRare.union {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {A B : ∀ n, Set (H n)}
    (hA : ExponentiallyRare ρ A) (hB : ExponentiallyRare ρ B) :
    ExponentiallyRare ρ (fun n => A n ∪ B n) := by
  obtain ⟨C,c,hC,hc,he⟩ := hA
  obtain ⟨D,d,hD,hd,hf⟩ := hB
  refine ⟨C+D,min c d,add_pos hC hD,lt_min hc hd,?_⟩
  filter_upwards [he,hf] with n hn hm
  refine (measure_union_le _ _).trans ((add_le_add hn hm).trans ?_)
  have hc' : Real.exp (-c*(n:ℝ)) ≤ Real.exp (-min c d*(n:ℝ)) :=
    Real.exp_le_exp.mpr (by
      have := min_le_left c d
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hd' : Real.exp (-d*(n:ℝ)) ≤ Real.exp (-min c d*(n:ℝ)) :=
    Real.exp_le_exp.mpr (by
      have := min_le_right c d
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
  rw [add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc' hC.le))
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hd' hD.le))

lemma exponentiallyRare_empty {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) : ExponentiallyRare ρ (fun _ => ∅) := by
  refine ⟨1,1,by norm_num,by norm_num,Filter.Eventually.of_forall ?_⟩
  intro n
  simp only [measure_empty, zero_le]

lemma ExponentiallyRare.iUnion_finite {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {ι : Type*} [Finite ι]
    {A : ι → ∀ n, Set (H n)} (hA : ∀ i, ExponentiallyRare ρ (A i)) :
    ExponentiallyRare ρ (fun n => ⋃ i, A i n) := by
  classical
  cases nonempty_fintype ι
  have hs (s : Finset ι) : ExponentiallyRare ρ (fun n => ⋃ i ∈ s, A i n) := by
    induction s using Finset.induction_on with
    | empty => simpa using exponentiallyRare_empty ρ
    | @insert i s hi ih =>
      have heq : (fun n => ⋃ j ∈ insert i s, A j n) =
          (fun n => A i n ∪ ⋃ j ∈ s, A j n) := by
        funext n
        ext h
        simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
        aesop
      rw [heq]
      exact (hA i).union ih
  simpa using hs Finset.univ

lemma ExponentialConvergence.continuous_map
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {X : ∀ n, H n → E} {x : E} (hX : ExponentialConvergence ρ X x)
    {f : E → F} (hf : ContinuousAt f x) :
    ExponentialConvergence ρ (fun n h => f (X n h)) (f x) := by
  intro ε hε
  obtain ⟨δ,hδ,hδe⟩ := Metric.continuousAt_iff.mp hf ε hε
  apply (hX δ hδ).mono
  refine Filter.Eventually.of_forall ?_
  intro n h hh
  by_contra hnot
  have hnear : dist (X n h) x < δ := lt_of_not_ge hnot
  exact (not_lt_of_ge hh) (hδe hnear)

lemma ExponentialConvergence.prod
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {X : ∀ n, H n → E} {Y : ∀ n, H n → F} {x : E} {y : F}
    (hX : ExponentialConvergence ρ X x) (hY : ExponentialConvergence ρ Y y) :
    ExponentialConvergence ρ (fun n h => (X n h,Y n h)) (x,y) := by
  intro ε hε
  apply ((hX ε hε).union (hY ε hε)).mono
  exact Filter.Eventually.of_forall (fun n h hh => by
    simpa only [Prod.dist_eq, le_max_iff, Set.mem_union, Set.mem_ofPred_eq] using hh)

lemma ExponentialConvergence.pi_finite
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, PseudoMetricSpace (E i)]
    {X : ∀ n, H n → ∀ i, E i} {x : ∀ i, E i}
    (hX : ∀ i, ExponentialConvergence ρ (fun n h => X n h i) (x i)) :
    ExponentialConvergence ρ X x := by
  intro ε hε
  apply (ExponentiallyRare.iUnion_finite (fun i => hX i ε hε)).mono
  refine Filter.Eventually.of_forall ?_
  intro n h hh
  by_contra hn
  have hall : ∀ i, dist (X n h i) (x i) < ε := by
    intro i
    apply lt_of_not_ge
    intro hi
    exact hn (Set.mem_iUnion.mpr ⟨i,hi⟩)
  exact (not_lt_of_ge hh) ((dist_pi_lt_iff hε).mpr hall)

lemma ExponentialEmpiricalConcentration.average
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    ExponentialConvergence ρ (fun n h => (∑ i, f (X n h i))/(n:ℝ)) (∫ x, f x ∂ν) := by
  intro ε hε
  simpa only [ExponentiallyRare, Real.dist_eq] using hX f K hf B hB ε hε

lemma ExponentiallyRare.without_prefactor {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {A : ∀ n, Set (H n)} (hA : ExponentiallyRare ρ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ρ n (A n) ≤ ENNReal.ofReal (Real.exp (-c*n)) := by
  obtain ⟨C,c,hC,hc,he⟩ := hA
  refine ⟨c/2,by positivity,?_⟩
  have hnc := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  filter_upwards [he,hnc.eventually (eventually_ge_atTop (2*Real.log C/c))] with n hn hsize
  apply hn.trans
  apply ENNReal.ofReal_le_ofReal
  rw [show C*Real.exp (-c*n)=Real.exp (Real.log C-c*n) by
    rw [Real.exp_sub,Real.exp_log hC,neg_mul,Real.exp_neg,div_eq_mul_inv] ]
  apply Real.exp_le_exp.mpr
  have hh := (div_le_iff₀ hc).mp hsize
  nlinarith

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianSquareTails
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKRatioClock.Regression

lemma bounded_product_lipschitz {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {K L B D : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hb : ∀ x, |f x| ≤ B) (hd : ∀ x, |g x| ≤ D) :
    LipschitzWith (K*D+L*B) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hid : f x*g x-f y*g y = (f x-f y)*g x + f y*(g x-g y) := by ring
  rw [hid]
  calc
    |(f x-f y)*g x+f y*(g x-g y)| ≤ |(f x-f y)*g x|+|f y*(g x-g y)| := abs_add_le _ _
    _ = |f x-f y| * |g x|+|f y| * |g x-g y| := by rw [abs_mul, abs_mul]
    _ ≤ ((K:ℝ)*dist x y)*(D:ℝ)+(B:ℝ)*((L:ℝ)*dist x y) := by
      gcongr
      · exact hf.dist_le_mul x y
      · exact hd x
      · exact hb y
      · exact hg.dist_le_mul x y
    _ = ((K*D+L*B:ℝ≥0):ℝ)*dist x y := by push_cast; ring
lemma gaussian_integrable_exp_quarter_sq :
    Integrable (fun x : ℝ => Real.exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1:ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  have h := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/4)).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  apply h.congr
  filter_upwards [] with x
  symm
  simp only [toReal_gaussianPDF,
    smul_eq_mul, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, one_div]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma iid_upper_deviation_of_log_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hXi : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (ν : Measure ℝ)
    (hLaw : ∀ i, HasLaw (X i) ν μ) {t : ℝ} (ht : 0 < t)
    (hi : Integrable (fun x : ℝ => Real.exp (t*x)) ν) (a : ℝ) :
    μ {ω | a ≤ (∑ i, X i ω)/(n:ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((t*a-cgf id ν t)*(n:ℝ)))) := by
  have he (i : Fin n) : Integrable (fun ω => Real.exp (t*X i ω)) μ :=
    by
      rw [← (hLaw i).map_eq] at hi
      exact (integrable_map_measure (by fun_prop) (hLaw i).aemeasurable).mp hi
  have hsum := hXi.integrable_exp_mul_sum hXm (s := Finset.univ) (fun i _ => he i)
  have hc := measure_ge_le_exp_cgf (μ := μ) (X := ∑ i, X i) (a*n) ht.le hsum
  have hcgf (i : Fin n) : cgf (X i) μ t = cgf id ν t := by
    unfold cgf mgf
    congr 1
    exact (hLaw i).integral_comp (f := fun x : ℝ => Real.exp (t*x)) (by fun_prop)
  rw [hXi.cgf_sum hXm (fun i _ => he i)] at hc
  simp only [hcgf, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hc
  have hset : {ω | a*(n:ℝ) ≤ (∑ i, X i) ω} =
      {ω | a ≤ (∑ i, X i ω)/(n:ℝ)} := by
    ext ω
    simp only [Finset.sum_apply, Set.mem_ofPred_eq,
      le_div_iff₀ ((show (0:ℝ)<n from Nat.cast_pos.mpr hn))]
  rw [hset] at hc
  have h := ENNReal.ofReal_le_ofReal hc
  simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma squareTail_nonneg (R x : ℝ) : 0 ≤ squareTail R x := by
  unfold squareTail
  split_ifs <;> positivity

lemma squareTail_le (R x : ℝ) : squareTail R x ≤ x^2 := by
  unfold squareTail
  split_ifs <;> simp [sq_nonneg]

lemma measurable_squareTail (R : ℝ) : Measurable (squareTail R) := by
  unfold squareTail
  exact Measurable.ite (measurableSet_lt measurable_const measurable_abs)
    (by fun_prop) measurable_const

lemma integrable_exp_squareTail {ν : Measure ℝ}
    (hi : Integrable (fun x : ℝ => Real.exp (x^2/4)) ν) (R : ℝ) :
    Integrable (fun x => Real.exp (squareTail R x/4)) ν := by
  apply hi.mono' (((measurable_squareTail R).div_const 4).exp.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (squareTail_le R x) (by norm_num))

lemma tendsto_squareTail_mgf {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hi : Integrable (fun x : ℝ => Real.exp (x^2/4)) ν) :
    Tendsto (fun R : ℕ => ∫ x, Real.exp (squareTail R x/4) ∂ν) atTop (𝓝 1) := by
  have ht : Tendsto (fun R : ℕ => ∫ x, Real.exp (squareTail R x/4) ∂ν)
      atTop (𝓝 (∫ _x : ℝ, (1:ℝ) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun x : ℝ => Real.exp (x^2/4))
    · intro R
      exact (((measurable_squareTail R).div_const 4).exp.aestronglyMeasurable)
    · exact hi
    · intro R
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (squareTail_le R x) (by norm_num))
    · filter_upwards [] with x
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with R hR
      have hx : |x| ≤ (R:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hR)
      simp [squareTail, not_lt.mpr hx]
  simpa using ht

theorem iid_exponential_squareTails {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (X : ∀ n, H n → Fin n → ℝ)
    (hXm : ∀ n i, Measurable (fun h => X n h i))
    (hXi : ∀ n, iIndepFun (fun i h => X n h i) (ρ n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hLaw : ∀ n i, HasLaw (fun h => X n h i) ν (ρ n))
    (hi : Integrable (fun x : ℝ => Real.exp (x^2/4)) ν) :
    ExponentialSquareTails ρ X := by
  intro ε hε
  have ht : Tendsto (fun R : ℕ => Real.log (∫ x, Real.exp (squareTail R x/4) ∂ν))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp
      (tendsto_squareTail_mgf hi)
  have he : ∀ᶠ R : ℕ in atTop,
      Real.log (∫ x, Real.exp (squareTail R x/4) ∂ν) < ε/4 :=
    ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨R,hR,hm⟩ := (eventually_ge_atTop 1 |>.and he).exists
  let m := Real.log (∫ x, Real.exp (squareTail R x/4) ∂ν)
  have htm : Measurable (squareTail R) := measurable_squareTail R
  have hl : HasLaw (squareTail R) (ν.map (squareTail R)) ν := ⟨htm.aemeasurable,rfl⟩
  have hcg : cgf id (ν.map (squareTail R)) (1/4) = m := by
    unfold cgf mgf m
    rw [integral_map htm.aemeasurable (by fun_prop)]
    congr 2
    ext x
    simp only [id_eq]
    congr 1
    ring
  have hint : Integrable (fun x : ℝ => Real.exp (1/4*x)) (ν.map (squareTail R)) := by
    rw [integrable_map_measure (by fun_prop) htm.aemeasurable]
    simpa only [Function.comp_def, one_div_mul_eq_div] using integrable_exp_squareTail hi R
  refine ⟨R,by exact_mod_cast hR,1,ε/4-m,by norm_num,sub_pos.mpr hm,?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hb := iid_upper_deviation_of_log_mgf hn (fun i h => squareTail R (X n h i))
    ((hXi n).comp (fun _ => squareTail R) (fun _ => htm))
    (fun i => htm.comp (hXm n i)) (ν.map (squareTail R))
    (fun i => hl.fun_comp (hLaw n i)) (by norm_num : (0:ℝ)<1/4) hint ε
  rw [hcg] at hb
  simpa only [one_mul, one_div_mul_eq_div, neg_mul] using hb

lemma squareTail_perturbation (R x y : ℝ) (_hR : 0 ≤ R) :
    squareTail (2*R) y ≤ 4*squareTail R x+4*(x-y)^2 := by
  unfold squareTail
  split_ifs with hy hx
  · nlinarith [sq_nonneg (x+y)]
  · have hx' := le_of_not_gt hx
    have habs := abs_sub_abs_le_abs_sub y x
    have hxy : R < |y-x| := by linarith
    have hyb : |y| ≤ 2*|y-x| := by linarith
    have hs := mul_self_le_mul_self (abs_nonneg y) hyb
    nlinarith [sq_abs y, sq_abs (y-x)]
  · positivity
  · positivity

theorem ExponentialSquareTails.l2_stability
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X Y : ∀ n, H n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X)
    (hXY : ExponentialConvergence ρ
      (fun n h => (∑ i, (X n h i-Y n h i)^2)/(n:ℝ)) 0) :
    ExponentialSquareTails ρ Y := by
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hX (ε/8) (by positivity)
  refine ⟨2*R,by positivity,?_⟩
  apply (ht.union (hXY (ε/8) (by positivity))).mono
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro h hh
  simp only [Set.mem_ofPred_eq] at hh
  by_cases hx : ε/8 ≤ (∑ i, squareTail R (X n h i))/(n:ℝ)
  · exact Or.inl hx
  apply Or.inr
  have hb : (∑ i, squareTail (2*R) (Y n h i))/(n:ℝ) ≤
      4*((∑ i, squareTail R (X n h i))/(n:ℝ))+
      4*((∑ i, (X n h i-Y n h i)^2)/(n:ℝ)) := by
    calc
      _ ≤ (∑ i, (4*squareTail R (X n h i)+4*(X n h i-Y n h i)^2))/(n:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum (fun i _ => squareTail_perturbation R _ _ hR.le)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
  change ε/8 ≤ dist ((∑ i, (X n h i-Y n h i)^2)/(n:ℝ)) 0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hx' := lt_of_not_ge hx
  linarith

lemma squareTail_add (R x y : ℝ) (_hR : 0 ≤ R) :
    squareTail (2*R) (x+y) ≤ 4*(squareTail R x+squareTail R y) := by
  unfold squareTail
  split_ifs with hxy hx hy hy
  · nlinarith [sq_nonneg (x-y)]
  · have hy' := le_of_not_gt hy
    have hxy' : |y| ≤ |x| := hy'.trans (le_of_lt hx)
    have hs := mul_self_le_mul_self (abs_nonneg y) hxy'
    nlinarith [sq_abs x, sq_abs y, sq_nonneg (x-y)]
  · have hx' := le_of_not_gt hx
    have hxy' : |x| ≤ |y| := hx'.trans (le_of_lt hy)
    have hs := mul_self_le_mul_self (abs_nonneg x) hxy'
    nlinarith [sq_abs x, sq_abs y, sq_nonneg (x-y)]
  · have hx' := le_of_not_gt hx
    have hy' := le_of_not_gt hy
    have := abs_add_le x y
    linarith
  all_goals positivity

lemma squareTail_antitone (x : ℝ) : Antitone (fun R => squareTail R x) := by
  intro R S hRS
  dsimp only [squareTail]
  split_ifs <;> first | exact le_rfl | positivity | (exfalso; linarith)

theorem ExponentialSquareTails.add
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X Y : ∀ n, H n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X) (hY : ExponentialSquareTails ρ Y) :
    ExponentialSquareTails ρ (fun n h i => X n h i+Y n h i) := by
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hX (ε/8) (by positivity)
  obtain ⟨S,hS,hs⟩ := hY (ε/8) (by positivity)
  refine ⟨2*max R S,by positivity,?_⟩
  apply (ht.union hs).mono
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro h hh
  simp only [Set.mem_ofPred_eq] at hh
  by_cases hx : ε/8 ≤ (∑ i, squareTail R (X n h i))/(n:ℝ)
  · exact Or.inl hx
  apply Or.inr
  have hb : (∑ i, squareTail (2*max R S) (X n h i+Y n h i))/(n:ℝ) ≤
      4*((∑ i, squareTail R (X n h i))/(n:ℝ))+
      4*((∑ i, squareTail S (Y n h i))/(n:ℝ)) := by
    calc
      _ ≤ (∑ i, 4*(squareTail R (X n h i)+squareTail S (Y n h i)))/(n:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro i _
        exact (squareTail_add _ _ _ (le_max_of_le_left hR.le)).trans
          (mul_le_mul_of_nonneg_left (add_le_add
            (squareTail_antitone _ (le_max_left _ _))
            (squareTail_antitone _ (le_max_right _ _))) (by norm_num))
      _ = _ := by simp_rw [mul_add]; rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum]; ring
  have hx' := lt_of_not_ge hx
  change ε/8 ≤ (∑ i, squareTail S (Y n h i))/(n:ℝ)
  linarith

lemma squareTail_mul (R x a B : ℝ) (_hR : 0 ≤ R) (ha : |a| ≤ B) :
    squareTail (B*R) (a*x) ≤ B^2*squareTail R x := by
  have hB := (abs_nonneg a).trans ha
  unfold squareTail
  split_ifs with hax hx
  · have hs := mul_self_le_mul_self (abs_nonneg a) ha
    have hsq : a^2 ≤ B^2 := by nlinarith [sq_abs a]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg x)]
  · have hx' := le_of_not_gt hx
    have hab : |a*x| ≤ B*R := by rw [abs_mul]; exact mul_le_mul ha hx' (abs_nonneg x) hB
    exact False.elim ((not_lt_of_ge hab) hax)
  all_goals positivity

lemma ExponentialSquareTails.bounded_mul
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X)
    (a : ∀ n, H n → Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n h i, |a n h i| ≤ B) :
    ExponentialSquareTails ρ (fun n h i => a n h i*X n h i) := by
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hX (ε/(B+1)^2) (by positivity)
  refine ⟨(B+1)*R,by positivity,ht.mono ?_⟩
  filter_upwards [] with n
  intro h hh
  change ε/(B+1)^2 ≤ (∑ i, squareTail R (X n h i))/(n:ℝ)
  apply (div_le_iff₀ (by positivity : 0 < (B+1)^2)).mpr
  have hb : (∑ i, squareTail ((B+1)*R) (a n h i*X n h i))/(n:ℝ) ≤
      (B+1)^2*((∑ i, squareTail R (X n h i))/(n:ℝ)) := by
    calc
      _ ≤ (∑ i, (B+1)^2*squareTail R (X n h i))/(n:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum (fun i _ => squareTail_mul R _ _ _ hR.le ((ha n h i).trans (by linarith)))
      _ = _ := by rw [← Finset.mul_sum]; ring
  exact (show ε ≤ _ from hh).trans (by simpa [mul_comm] using hb)

lemma clippedSquare_bounds (R x : ℝ) (hR : 0 ≤ R) :
    0 ≤ clippedSquare R x ∧ clippedSquare R x ≤ x^2 ∧ clippedSquare R x ≤ R^2 := by
  have hm := le_min (abs_nonneg x) hR
  have hx := mul_self_le_mul_self hm (min_le_left |x| R)
  have hr := mul_self_le_mul_self hm (min_le_right |x| R)
  dsimp [clippedSquare]
  exact ⟨sq_nonneg _, by nlinarith [sq_abs x], by nlinarith⟩

lemma clippedSquare_error (R x : ℝ) (hR : 0 ≤ R) :
    |x^2-clippedSquare R x| ≤ squareTail R x := by
  rw [abs_of_nonneg (sub_nonneg.mpr (clippedSquare_bounds R x hR).2.1)]
  by_cases hx : R < |x|
  · simp only [squareTail, ite_eq_left hx]
    linarith [(clippedSquare_bounds R x hR).1]
  · simp [clippedSquare, squareTail, hx, min_eq_left (le_of_not_gt hx)]

lemma clippedSquare_lipschitz (R : ℝ≥0) :
    LipschitzWith (2*R) (clippedSquare R) := by
  have ha : LipschitzWith 1 (fun x : ℝ => |x|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y
  have h : LipschitzWith 1 (fun x : ℝ => min |x| (R:ℝ)) := ha.min_const _
  have hb (x : ℝ) : |min |x| (R:ℝ)| ≤ R := by
    rw [abs_of_nonneg (le_min (abs_nonneg _) R.coe_nonneg)]
    exact min_le_right _ _
  change LipschitzWith (2*R) (fun x : ℝ => (min |x| (R:ℝ))^2)
  simpa only [one_mul, ← two_mul, pow_two] using bounded_product_lipschitz h h hb hb

lemma tendsto_integral_clippedSquare (ν : Measure ℝ)
    (hi : Integrable (fun x : ℝ => x^2) ν) :
    Tendsto (fun R : ℕ => ∫ x, clippedSquare R x ∂ν) atTop (𝓝 (∫ x, x^2 ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun x : ℝ => x^2)
  · intro R
    exact (clippedSquare_lipschitz R).continuous.measurable.aestronglyMeasurable
  · exact hi
  · intro R
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (clippedSquare_bounds R x (Nat.cast_nonneg _)).1]
    exact (clippedSquare_bounds R x (Nat.cast_nonneg _)).2.1
  · filter_upwards [] with x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with R hR
    have hx : |x| ≤ (R:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hR)
    simp [clippedSquare, min_eq_left hx]

theorem ExponentialEmpiricalConcentration.secondMoment
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (hT : ExponentialSquareTails ρ X)
    (hi : Integrable (fun x : ℝ => x^2) ν) :
    ExponentialConvergence ρ (fun n h => (∑ i, X n h i^2)/(n:ℝ))
      (∫ x, x^2 ∂ν) := by
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hT (ε/3) (by positivity)
  have hbias : ∀ᶠ k : ℕ in atTop,
      |(∫ x, clippedSquare k x ∂ν) - ∫ x, x^2 ∂ν| < ε/3 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp
      (tendsto_integral_clippedSquare ν hi)) (ε/3) (by positivity)
  obtain ⟨k,hk,hbias⟩ := ((eventually_ge_atTop ⌈R⌉₊).and hbias).exists
  have hRk : R ≤ (k:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hc : ExponentiallyRare ρ (fun n => {h | ε/3 ≤
      |(∑ i, clippedSquare k (X n h i))/(n:ℝ) - ∫ x, clippedSquare k x ∂ν|}) := by
    apply hX (clippedSquare k) (2*(k:ℝ≥0)) (clippedSquare_lipschitz k)
      ((k:ℝ)^2)
    · intro x
      rw [abs_of_nonneg (clippedSquare_bounds k x (Nat.cast_nonneg _)).1]
      exact (clippedSquare_bounds k x (Nat.cast_nonneg _)).2.2
    · positivity
  apply (ht.union hc).mono
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro h hh
  change ε ≤ |(∑ i, X n h i^2)/(n:ℝ) - ∫ x, x^2 ∂ν| at hh
  by_cases htail : ε/3 ≤ (∑ i, squareTail R (X n h i))/(n:ℝ)
  · exact Or.inl htail
  apply Or.inr
  by_contra hclip
  have herror : |(∑ i, X n h i^2)/(n:ℝ) -
      (∑ i, clippedSquare k (X n h i))/(n:ℝ)| ≤
      (∑ i, squareTail R (X n h i))/(n:ℝ) := by
    rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n), ← Finset.sum_sub_distrib]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    calc
      _ ≤ ∑ i, |X n h i^2-clippedSquare k (X n h i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, squareTail R (X n h i) := by
        apply Finset.sum_le_sum
        intro i _
        exact (clippedSquare_error k _ (Nat.cast_nonneg _)).trans
          (squareTail_antitone _ hRk)
  have htriangle := abs_add_three
    ((∑ i, X n h i^2)/(n:ℝ)-(∑ i, clippedSquare k (X n h i))/(n:ℝ))
    ((∑ i, clippedSquare k (X n h i))/(n:ℝ)-∫ x, clippedSquare k x ∂ν)
    ((∫ x, clippedSquare k x ∂ν)-∫ x, x^2 ∂ν)
  rw [sub_add_sub_cancel, sub_add_sub_cancel] at htriangle
  have ht' := lt_of_not_ge htail
  simp only [Set.mem_ofPred_eq] at hclip
  have hc' := lt_of_not_ge hclip
  linarith

lemma exponentialSquareTails_of_bounded
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (X : ∀ n, H n → Fin n → ℝ) (B : ℝ)
    (hB : ∀ n h i, |X n h i| ≤ B) : ExponentialSquareTails ρ X := by
  intro ε hε
  refine ⟨|B|+1,by positivity, (exponentiallyRare_empty ρ).mono ?_⟩
  filter_upwards [] with n
  intro h hh
  have hz : ∀ i, squareTail (|B|+1) (X n h i) = 0 := by
    intro i
    have hb := (hB n h i).trans (le_abs_self B)
    simp [squareTail, show ¬ |B|+1 < |X n h i| by linarith]
  simp only [Set.mem_ofPred_eq, hz, Finset.sum_const_zero, zero_div] at hh
  exact False.elim ((not_le_of_gt hε) hh)

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianSupport
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKRatioGaussian.GaussianRegression

theorem law_eq_of_mean_covariance {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P')
    (hm : ∀ i, (∫ w, X w i ∂P) = ∫ w, Y w i ∂P')
    (hc : ∀ i k, cov[fun w => X w i, fun w => X w k; P] =
      cov[fun w => Y w i, fun w => Y w k; P']) :
    P.map X = P'.map Y := by
  classical
  have := hX.isProbabilityMeasure
  have := hY.isProbabilityMeasure
  apply Measure.ext_of_charFunDual
  ext L
  rw [hX.charFunDual_map_eq,hY.charFunDual_map_eq]
  let c : ι → ℝ := fun i => L (fun k => if i=k then 1 else 0)
  have hL (x : ι → ℝ) : L x = ∑ i, x i * c i := by
    simpa only [c, smul_eq_mul, ContinuousLinearMap.coe_coe] using L.toLinearMap.pi_apply_eq_sum_univ x
  have hLX : L ∘ X = fun w => ∑ i, X w i*c i := funext (fun w => hL (X w))
  have hLY : L ∘ Y = fun w => ∑ i, Y w i*c i := funext (fun w => hL (Y w))
  have hiX (i : ι) := (hX.eval i).memLp_two
  have hiY (i : ι) := (hY.eval i).memLp_two
  have hem : (∫ w, (L ∘ X) w ∂P) = ∫ w, (L ∘ Y) w ∂P' := by
    rw [hLX,hLY]
    rw [integral_finsetSum _ (fun i _ => ((hX.eval i).integrable.mul_const _)),
      integral_finsetSum _ (fun i _ => ((hY.eval i).integrable.mul_const _))]
    simp only [integral_mul_const,hm]
  have hev : Var[L ∘ X; P] = Var[L ∘ Y; P'] := by
    rw [← covariance_self (hX.map L).aemeasurable,
      ← covariance_self (hY.map L).aemeasurable]
    rw [hLX,hLY]
    rw [covariance_fun_sum_fun_sum (fun i => (hiX i).mul_const _) (fun i => (hiX i).mul_const _),
      covariance_fun_sum_fun_sum (fun i => (hiY i).mul_const _) (fun i => (hiY i).mul_const _)]
    simp only [covariance_mul_const_left,covariance_mul_const_right,hc]
  rw [hev,hem]

end SKRatioGaussian.GaussianRegression
end
end

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_PlantedGOE
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma augmentedDisorder_gaussian (β : ℝ) :
    HasGaussianLaw (augmentedDisorder (n := n) β) (standardArrayLaw (Fin n × Fin n)) := by
  let L : ((Fin n × Fin n) → ℝ) →L[ℝ] Disorder n :=
    β • ContinuousLinearMap.pi (fun e : Edge n => (entryCLM e.1.1 e.1.2).comp (goeCLM n))
  have h := gaussian_add_constant (coordinates_gaussian.map_fun L) (fun _ : Edge n => β^2/(n:ℝ))
  apply h.congr
  exact Eventually.of_forall (fun g => by
    funext e
    simp only [L,smul_apply,
      ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,entryCLM_apply,
      goeCLM_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,augmentedDisorder,augmented])

lemma augmented_mean (β : ℝ) (i j : Fin n) :
    (∫ g, augmented β g i j ∂standardArrayLaw (Fin n × Fin n)) = β^2/(n:ℝ) := by
  unfold augmented
  rw [integral_add (((goe_gaussian n).eval i |>.eval j).integrable.const_mul β)
    (integrable_const _),integral_const_mul,goe_entry_mean]
  simp

lemma augmented_covariance (hn : 0 < n) (β : ℝ) (i j k l : Fin n) :
    cov[fun g => augmented β g i j, fun g => augmented β g k l;
      standardArrayLaw (Fin n × Fin n)] =
      (β^2/(n:ℝ))*((if i=k ∧ j=l then 1 else 0)+(if i=l ∧ j=k then 1 else 0)) := by
  unfold augmented
  rw [covariance_add_const_left (((goe_gaussian n).eval i |>.eval j).integrable.const_mul β),
    covariance_add_const_right (((goe_gaussian n).eval k |>.eval l).integrable.const_mul β),
    covariance_const_mul_left,covariance_const_mul_right,goe_entry_covariance hn]
  ring

lemma augmentedDisorder_covariance (hn : 0 < n) (β : ℝ) (e f : Edge n) :
    cov[fun g => augmentedDisorder β g e,fun g => augmentedDisorder β g f;
      standardArrayLaw (Fin n × Fin n)] = if e=f then β^2/(n:ℝ) else 0 := by
  unfold augmentedDisorder
  rw [augmented_covariance hn]
  have heq : e=f ↔ e.1.1=f.1.1 ∧ e.1.2=f.1.2 := by
    simp only [Subtype.ext_iff,Prod.ext_iff]
  have hcross : ¬(e.1.1=f.1.2 ∧ e.1.2=f.1.1) := by
    rintro ⟨h₁,h₂⟩
    have h := e.2
    rw [h₁,h₂] at h
    exact lt_asymm f.2 h
  simp only [ite_eq_right hcross,add_zero,←heq]
  split_ifs <;> simp

theorem augmentedDisorder_hasLaw (hn : 0 < n) (β : ℝ) :
    HasLaw (augmentedDisorder (n := n) β) (law β n) (standardArrayLaw (Fin n × Fin n)) := by
  have hg := augmentedDisorder_gaussian (n := n) β
  have hl (e : Edge n) : HasLaw (fun g => augmentedDisorder β g e)
      (gaussianReal (β^2/(n:ℝ)) (Real.toNNReal (β^2/(n:ℝ))))
      (standardArrayLaw (Fin n × Fin n)) := by
    refine ⟨(hg.eval e).aemeasurable,?_⟩
    rw [(hg.eval e).map_eq_gaussianReal,show (∫ g, augmentedDisorder β g e
      ∂standardArrayLaw (Fin n × Fin n)) = β^2/(n:ℝ) from augmented_mean β _ _,
      ←covariance_self (hg.eval e).aemeasurable,augmentedDisorder_covariance hn,ite_eq_left rfl]
  exact iIndepFun.hasLaw_pi hl (hg.iIndepFun_of_covariance_eq_zero
    (fun e f h => by rw [augmentedDisorder_covariance hn,ite_eq_right h]))

lemma augmentedField_gaussian (β : ℝ) :
    HasGaussianLaw (augmentedField (n := n) β) (standardArrayLaw (Fin n × Fin n)) := by
  let L : ((Fin n × Fin n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
    β • ContinuousLinearMap.pi (fun i : Fin n => ∑ j : Fin n,
      (entryCLM i j).comp (goeCLM n))
  have h := gaussian_add_constant (coordinates_gaussian.map_fun L)
    (fun _ : Fin n => (n:ℝ)*(β^2/(n:ℝ)))
  apply h.congr
  exact Eventually.of_forall (fun g => by
    ext i
    simp [L,augmentedField,augmented,Finset.sum_add_distrib,Finset.mul_sum])

lemma augmentedField_mean (hn : 0 < n) (β : ℝ) (i : Fin n) :
    (∫ g, augmentedField β g i ∂standardArrayLaw (Fin n × Fin n)) = β^2 := by
  have hi (j : Fin n) : Integrable (fun g => augmented β g i j)
      (standardArrayLaw (Fin n × Fin n)) :=
    (((goe_gaussian n).eval i |>.eval j).integrable.const_mul β).add (integrable_const _)
  change (∫ g, ∑ j : Fin n, augmented β g i j ∂standardArrayLaw (Fin n × Fin n)) = _
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp only [augmented_mean,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')

lemma augmentedField_covariance (hn : 0 < n) (β : ℝ) (i k : Fin n) :
    cov[fun g => augmentedField β g i,fun g => augmentedField β g k;
      standardArrayLaw (Fin n × Fin n)] = (if i=k then β^2 else 0)+β^2/(n:ℝ) := by
  have hLp (i j : Fin n) : MemLp (fun g => augmented β g i j) 2
      (standardArrayLaw (Fin n × Fin n)) :=
    ((goe_entry_memLp i j).const_mul β).add (memLp_const _)
  unfold augmentedField
  rw [covariance_fun_sum_fun_sum (hLp i) (hLp k)]
  simp_rw [augmented_covariance hn,ite_and,mul_add,Finset.sum_add_distrib,mul_ite,
    mul_one,mul_zero,Finset.sum_ite_irrel,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  split_ifs <;> simp [mul_div_cancel₀ _ hn0]

theorem augmentedField_law (hn : 0 < n) (β : ℝ) :
    (standardArrayLaw (Fin n × Fin n)).map (augmentedField β) =
      (standardArrayLaw (Option (Fin n))).map
        (sharedGaussianField (β^2) β (β/sqrt n)) := by
  apply SKRatioGaussian.GaussianRegression.law_eq_of_mean_covariance
    (augmentedField_gaussian β) (sharedGaussianField_gaussian n _ _ _)
  · intro i
    rw [augmentedField_mean hn,sharedGaussianField_mean]
  · intro i k
    rw [augmentedField_covariance hn,sharedGaussianField_covariance,div_pow,
      sq_sqrt (Nat.cast_nonneg n)]

lemma projected_rows_formula (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ = M) (i j : Fin n) :
    M i j = (fieldProjection n*M*fieldProjection n) i j +
      ((∑ k, M i k)+(∑ k, M j k)-(∑ l, ∑ k, M l k)/(n:ℝ))/(n:ℝ) := by
  have hs0 : sqrt (n:ℝ) ≠ 0 := (sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hr := congrFun (congrFun
    (regression_decomposition M (queryColumn (constantDirection n)) hM) i) j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply,
    queryColumn,constantDirection,Fin.sum_univ_one,←Finset.sum_mul,←Finset.mul_sum] at hr
  change M i j = _ + _ - _ + (fieldProjection n*M*fieldProjection n) i j at hr
  have hs : (sqrt (n:ℝ))⁻¹ * (sqrt n)⁻¹ = (n:ℝ)⁻¹ := by
    rw [←mul_inv_rev,←pow_two,sq_sqrt (Nat.cast_nonneg n)]
  calc
    M i j = _ := hr
    _ = _ := by
      calc
        _ = (fieldProjection n*M*fieldProjection n) i j +
            ((∑ k, M i k)+(∑ k, M j k)-(∑ l, ∑ k, M l k)*
              ((sqrt (n:ℝ))⁻¹*(sqrt n)⁻¹))*((sqrt (n:ℝ))⁻¹*(sqrt n)⁻¹) := by ring
        _ = _ := by rw [hs]; simp only [div_eq_mul_inv]

theorem augmented_decomposition (hn : 0 < n) (β : ℝ)
    (g : (Fin n × Fin n) → ℝ) (i j : Fin n) :
    augmented β g i j =
      (fieldProjection n*(β • goe g)*fieldProjection n) i j +
      (augmentedField β g i + augmentedField β g j -
        (∑ k, augmentedField β g k)/(n:ℝ))/(n:ℝ) := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hM : (β • goe g)ᵀ = β • goe g := by
    simp only [Matrix.transpose_smul,goe_symmetric]
  have h := projected_rows_formula hn (β • goe g) hM i j
  have hsum (i : Fin n) : augmentedField β g i = (∑ k, (β • goe g) i k) + β^2 := by
    simp [augmentedField,augmented,Finset.sum_add_distrib,mul_div_cancel₀ _ hn0]
  simp_rw [hsum]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change β*goe g i j+β^2/(n:ℝ) = _
  rw [show β*goe g i j = (β • goe g) i j from rfl,h]
  field_simp
  ring

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarKernel
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Planted.compactWeight_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma v_pos (h : ℝ) : 0 < v h := sub_pos.mpr (tanh_sq_lt_one h)
lemma v_le_one (h : ℝ) : v h ≤ 1 := by dsimp [v]; nlinarith [sq_nonneg (m h)]
lemma v_factor (h : ℝ) : v h = w h * (1+m h) := by unfold v w; ring
lemma kernel_nonneg (h t : ℝ) : 0 ≤ kernel h t :=
  div_nonneg (mul_nonneg (v_pos h).le (v_pos t).le) (add_pos (w_pos h) (w_pos t)).le
lemma kernel_diag (h : ℝ) : kernel h h = (1+m h)*v h/2 := by
  unfold kernel
  nth_rw 1 [v_factor h]
  have hw := (w_pos h).ne'
  field_simp
  ring

lemma kernel_diag_le_one (h : ℝ) : kernel h h ≤ 1 := by
  rw [kernel_diag]
  have hm := (m_bounds h).2.le
  have hv := v_le_one h
  have hv0 := (v_pos h).le
  nlinarith [(mul_le_mul_of_nonneg_right (show 1+m h ≤ 2 by linarith) hv0)]

lemma kernel_square_le (h t : ℝ) : kernel h t^2 ≤ kernel h h * kernel t t := by
  have ha := w_pos h
  have hb := w_pos t
  have hab : 0 < w h+w t := add_pos ha hb
  unfold kernel
  rw [div_pow,div_mul_div_comm]
  apply (div_le_div_iff₀ (sq_pos_of_pos hab) (mul_pos (add_pos ha ha) (add_pos hb hb))).mpr
  have hh := mul_nonneg (sq_nonneg (v h*v t)) (sq_nonneg (w h-w t))
  nlinarith only [hh]

lemma abs_kernel_le_one (h t : ℝ) : |kernel h t| ≤ 1 := by
  rw [abs_of_nonneg (kernel_nonneg h t)]
  have hs := kernel_square_le h t
  have hd := mul_le_mul (kernel_diag_le_one h) (kernel_diag_le_one t)
    (kernel_nonneg t t) (by norm_num : (0:ℝ) ≤ 1)
  nlinarith [sq_nonneg (kernel h t-1)]

lemma continuous_m : Continuous m := by
  unfold m
  simp_rw [tanh_eq_sinh_div_cosh]
  exact Continuous.div Real.continuous_sinh Real.continuous_cosh (fun h => ne_of_gt (Real.cosh_pos h))
lemma continuous_v : Continuous v := continuous_const.sub (continuous_m.pow 2)
lemma continuous_w : Continuous w := continuous_const.sub continuous_m
lemma continuous_kernel : Continuous (Function.uncurry kernel) := by
  apply ((continuous_v.comp continuous_fst).mul (continuous_v.comp continuous_snd)).div
    ((continuous_w.comp continuous_fst).add (continuous_w.comp continuous_snd))
  intro x
  exact (add_pos (w_pos x.1) (w_pos x.2)).ne'
end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarMoments
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma memLp_field (β : ℝ) : MemLp (fun h : ℝ => h) 2 (fieldLaw β) :=
  memLp_id_gaussianReal 2

end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_PlantedEmpirical
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression

lemma modelField_measurable (β : ℝ) (n : ℕ) : Measurable (modelField β n) := by
  unfold modelField sharedGaussianField
  fun_prop

lemma fieldLaw_eq_affine_map (β : ℝ) : Scalar.fieldLaw β =
    (gaussianReal 0 1).map (fun z : ℝ => β^2+β*z) := by
  have hid : (fun z : ℝ => β^2+β*z) = (fun z : ℝ => β^2+z) ∘ (fun z : ℝ => β*z) := rfl
  rw [hid,←Measure.map_map (by fun_prop) (by fun_prop),gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  simp only [mul_zero,zero_add,mul_one,Scalar.fieldLaw]
  congr 1
  apply NNReal.eq
  simp only [Scalar.variance_coe,NNReal.coe_mk]

lemma fieldLaw_secondMoment (β : ℝ) :
    (∫ h, h^2 ∂Scalar.fieldLaw β) = β^2+β^4 := by
  have hv := variance_eq_sub (Scalar.memLp_field β)
  change _ = (∫ h, h^2 ∂Scalar.fieldLaw β)-(∫ h, h ∂Scalar.fieldLaw β)^2 at hv
  have hm : (∫ h, h ∂Scalar.fieldLaw β) = β^2 := integral_id_gaussianReal
  have hvar : Var[(fun h : ℝ => h); Scalar.fieldLaw β] = β^2 := by
    change Var[id; gaussianReal (β^2) (Scalar.variance β)] = β^2
    rw [variance_id_gaussianReal,Scalar.variance_coe]
  rw [hm,hvar] at hv
  nlinarith only [hv]

lemma common_field_convergence (β : ℝ) (hβ : 0 < β) :
    ExponentialConvergence (fun n => standardArrayLaw (Option (Fin n)))
      (fun n g => (β/sqrt (n:ℝ))*g none) 0 := by
  intro ε hε
  refine ⟨2,ε^2/(2*β^2),by norm_num,by positivity,?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have ht := subgaussian_abs_tail
    (gaussian_hasSubgaussianMGF (coordinate_hasLaw (none : Option (Fin n))))
      (ε*sqrt (n:ℝ)/β) (by positivity)
  simp only [Real.dist_eq,sub_zero]
  apply (measure_mono (show {g : Option (Fin n) → ℝ | ε ≤ |β/sqrt (n:ℝ)*g none|} ⊆
    {g | ε*sqrt (n:ℝ)/β ≤ |g none|} from ?_)).trans
  · apply ht.trans_eq
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
    norm_num only [ENNReal.ofReal_ofNat,NNReal.coe_one,mul_one]
    congr 2
    rw [div_pow,mul_pow,sq_sqrt hnR.le]
    ring_nf
  · intro g hg
    change ε ≤ |β/sqrt (n:ℝ)*g none| at hg
    rw [abs_mul,abs_of_pos (by positivity : 0<β/sqrt (n:ℝ))] at hg
    apply (div_le_iff₀ hβ).mpr
    have hh := (le_div_iff₀ (sqrt_pos.mpr hnR)).mp
      (show ε ≤ β*|g none|/sqrt (n:ℝ) by simpa only [div_mul_eq_mul_div] using hg)
    nlinarith

lemma modelField_squareTails (β : ℝ) (hβ : 0 < β) :
    ExponentialSquareTails (fun n => standardArrayLaw (Option (Fin n))) (modelField β) := by
  let ρ := fun n => standardArrayLaw (Option (Fin n))
  have hi : ExponentialSquareTails ρ (fun _ g i => g (some i)) := by
    exact iid_exponential_squareTails ρ _ (fun _ _ => measurable_pi_apply _)
      (fun _ => coordinates_independent.precomp (Option.some_injective _))
      (gaussianReal 0 1) (fun _ _ => coordinate_hasLaw _) gaussian_integrable_exp_quarter_sq
  have ha := hi.bounded_mul (fun _ _ _ => β) |β| (abs_nonneg β) (fun _ _ _ => le_rfl)
  have hm := exponentialSquareTails_of_bounded ρ (fun _ _ _ => β^2) (β^2)
    (fun _ _ _ => by rw [abs_of_nonneg (sq_nonneg β)])
  apply (hm.add ha).l2_stability
  have hz := (common_field_convergence β hβ).continuous_map
    (f := fun x : ℝ => x^2) (by fun_prop)
  simp only [zero_pow (by norm_num : (2:ℕ)≠0)] at hz
  intro ε hε
  apply (hz ε hε).mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro g hg
  have he : (∑ i : Fin n, (β^2+β*g (some i)-modelField β n g i)^2)/(n:ℝ) =
      ((β/sqrt (n:ℝ))*g none)^2 := by
    simp only [modelField,sharedGaussianField,sub_add_cancel_left,neg_sq,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  change ε ≤ dist _ 0 at hg ⊢
  rwa [he] at hg

lemma modelField_empirical (β : ℝ) (hβ : 0 < β) :
    ExponentialEmpiricalConcentration (fun n => standardArrayLaw (Option (Fin n)))
      (modelField β) (Scalar.fieldLaw β) := by
  intro f K hf B hB ε hε
  let L : ℝ≥0 := K+1
  let D : ℝ := |B|+1
  have hL : (0:ℝ) < L := by dsimp [L]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hf' : LipschitzWith L f := hf.weaken (by simp [L])
  have hB' (z : ℝ) : |f z| ≤ D := (hB z).trans (by dsimp [D]; linarith [le_abs_self B])
  let c := min (ε^2/(8*D^2)) (ε^2/(8*(L:ℝ)^2*β^2))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨4,c,by norm_num,hc,?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have ht := iid_common_shift_average_tail hn (β^2) β (β/sqrt n)
    f hf' D hD.le hB' ε hε.le
  have hm : (∫ z, f z ∂Scalar.fieldLaw β) = ∫ z, f (β^2+β*z) ∂gaussianReal 0 1 := by
    rw [fieldLaw_eq_affine_map]
    exact integral_map (by fun_prop) hf.continuous.aestronglyMeasurable
  rw [hm]
  change standardArrayLaw (Option (Fin n)) {g | ε ≤
    |(∑ i : Fin n, f (β^2+β*g (some i)+(β/sqrt n)*g none))/(n:ℝ) -
      ∫ z, f (β^2+β*z) ∂gaussianReal 0 1|} ≤ _
  have he1 : -(ε^2*(n:ℝ))/(8*D^2) ≤ -c*n := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left (ε^2/(8*D^2)) (ε^2/(8*(L:ℝ)^2*β^2))) hnR.le
    have he : -(ε^2*(n:ℝ))/(8*D^2) = -(ε^2/(8*D^2))*n := by ring
    rw [he]
    dsimp [c]
    linarith only [hh]
  have he2 : -ε^2/(8*(L:ℝ)^2*(β/sqrt (n:ℝ))^2) ≤ -c*n := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (ε^2/(8*D^2)) (ε^2/(8*(L:ℝ)^2*β^2))) hnR.le
    have he : -ε^2/(8*(L:ℝ)^2*(β/sqrt (n:ℝ))^2) = -(ε^2/(8*(L:ℝ)^2*β^2))*n := by
      rw [div_pow,sq_sqrt hnR.le]
      field_simp
    rw [he]
    dsimp [c]
    linarith only [hh]
  apply ht.trans
  calc
    _ ≤ 2*ENNReal.ofReal (exp (-c*n))+2*ENNReal.ofReal (exp (-c*n)) := by
      gcongr
    _ = ENNReal.ofReal (4*exp (-c*n)) := by
      rw [←add_mul]
      norm_num only [show (2:ENNReal)+2=4 by norm_num]
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num

lemma augmentedField_event_eq {n : ℕ} (hn : 0 < n) (β : ℝ)
    (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    standardArrayLaw (Fin n × Fin n) ((augmentedField β) ⁻¹' E) =
      standardArrayLaw (Option (Fin n)) ((modelField β n) ⁻¹' E) := by
  have he := congrArg (fun μ : Measure (Fin n → ℝ) => μ E) (augmentedField_law hn β)
  change ((standardArrayLaw (Fin n × Fin n)).map (augmentedField β)) E =
    ((standardArrayLaw (Option (Fin n))).map (modelField β n)) E at he
  rw [Measure.map_apply_of_aemeasurable (augmentedField_gaussian β).aemeasurable hE,
    Measure.map_apply (modelField_measurable β n) hE] at he
  exact he

theorem augmentedField_empirical (β : ℝ) (hβ : 0 < β) :
    ExponentialEmpiricalConcentration (fun n => standardArrayLaw (Fin n × Fin n))
      (fun _ => augmentedField β) (Scalar.fieldLaw β) := by
  intro f K hf B hB ε hε
  obtain ⟨C,c,hC,hc,he⟩ := modelField_empirical β hβ f K hf B hB ε hε
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [he,eventually_gt_atTop 0] with n hn hn0
  have hE : MeasurableSet {v : Fin n → ℝ | ε ≤
    |(∑ i, f (v i))/(n:ℝ) - ∫ z, f z ∂Scalar.fieldLaw β|} := by
    apply measurableSet_le measurable_const
    exact (((Finset.measurable_sum _ (fun i _ => hf.continuous.measurable.comp
      (measurable_pi_apply i))).div_const _).sub_const _).abs
  exact (augmentedField_event_eq hn0 β _ hE).le.trans hn

theorem augmentedField_squareTails (β : ℝ) (hβ : 0 < β) :
    ExponentialSquareTails (fun n => standardArrayLaw (Fin n × Fin n))
      (fun _ => augmentedField β) := by
  intro ε hε
  obtain ⟨R,hR,C,c,hC,hc,he⟩ := modelField_squareTails β hβ ε hε
  refine ⟨R,hR,C,c,hC,hc,?_⟩
  filter_upwards [he,eventually_gt_atTop 0] with n hn hn0
  have hE : MeasurableSet {v : Fin n → ℝ | ε ≤ (∑ i, squareTail R (v i))/(n:ℝ)} := by
    exact measurableSet_le measurable_const ((Finset.measurable_sum _
      (fun i _ => (measurable_squareTail R).comp (measurable_pi_apply i))).div_const _)
  exact (augmentedField_event_eq hn0 β _ hE).le.trans hn

theorem augmentedField_secondMoment (β : ℝ) (hβ : 0 < β) :
    ExponentialConvergence (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n g => (∑ i, augmentedField β g i^2)/(n:ℝ)) (β^2+β^4) := by
  have he := (augmentedField_empirical β hβ).secondMoment
    (augmentedField_squareTails β hβ) (Scalar.memLp_field β).integrable_sq
  rwa [fieldLaw_secondMoment] at he

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinParameters
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [DecidableEq α]
attribute [local instance] Classical.propDecidable

variable [Fintype α]

omit [DecidableEq α] in
lemma parameterSet_compact : IsCompact (ParameterSet α) := by
  have hc : IsClosed {z : ParameterSpace α | ∀ a, 0≤z (.inr a)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    exact isClosed_le continuous_const (EuclideanSpace.proj (Sum.inr a : α ⊕ α)).continuous
  simpa only [ParameterSet,Metric.sphere,dist_zero_right,Set.ofPred_and] using
    (isCompact_sphere (0 : ParameterSpace α) 1).inter_right hc

instance instCompactSpaceParameters : CompactSpace (Parameters α) := isCompact_iff_compactSpace.mp parameterSet_compact

omit [DecidableEq α] in
lemma param_sum_sq (z : Parameters α) : (∑ a, ((paramB z a)^2+(paramR z a)^2))=1 := by
  have hh := EuclideanSpace.real_norm_sq_eq z.val
  rw [z.property.1] at hh
  simpa only [one_pow,Fintype.sum_sum_type,Finset.sum_add_distrib,paramB,paramR] using hh.symm

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_RandomMatrixNet
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
namespace SKRatio.MatrixNet

lemma matrix_opNorm_le_schur {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ i, ∑ j, |A i j| ≤ R) (hc : ∀ j, ∑ i, |A i j| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hR
  intro x y hx hy
  change inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A x) y ≤ R
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  change (∑ i, y i * ∑ j, A i j*x j) ≤ R
  simp only [Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, |A i j| * ((y i)^2 + (x j)^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hab : 2*|y i| *|x j| ≤ (y i)^2+(x j)^2 := by
        nlinarith [sq_nonneg (|y i|-|x j|), sq_abs (y i), sq_abs (x j)]
      have hp := mul_le_mul_of_nonneg_left hab (abs_nonneg (A i j))
      have hh : y i*(A i j*x j) ≤ |y i| *|A i j| *|x j| := by
        simpa only [abs_mul, mul_assoc] using le_abs_self (y i*(A i j*x j))
      nlinarith
    _ = ((∑ i, (y i)^2 * ∑ j, |A i j|) + ∑ j, (x j)^2 * ∑ i, |A i j|)/2 := by
      simp only [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
      rw [Finset.sum_comm (f := fun i j => |A i j| * (x j)^2)]
      simp only [← Finset.sum_mul]
      congr 2 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ ≤ ((∑ i, (y i)^2 * R) + ∑ j, (x j)^2*R)/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hr i) (sq_nonneg _)))
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hc i) (sq_nonneg _)))
    _ = R := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq,
        ← EuclideanSpace.real_norm_sq_eq, hx, hy]
      ring

lemma matrix_diagonal_opNorm_le {n : ℕ} (d : Fin n → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hd : ∀ i, |d i| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal d)‖ ≤ R := by
  apply matrix_opNorm_le_schur _ R hR
  · intro i
    simpa [Matrix.diagonal, apply_ite, abs_zero] using hd i
  · intro i
    simpa [Matrix.diagonal, apply_ite, abs_zero] using hd i

end SKRatio.MatrixNet

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_CompactMatrixMasks
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Set Metric
namespace SKRatio.MatrixNet
attribute [local instance] Classical.propDecidable

lemma kernel_error_norm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (G G' : Fin n → Fin n → ℝ) {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
    (hr : ∀ i, ∑ j, |A i j| ≤ C) (hc : ∀ j, ∑ i, |A i j| ≤ C)
    (he : ∀ i j, |G i j-G' i j| ≤ a) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (fun i j => A i j*(G i j-G' i j))‖ ≤ a*C := by
  apply matrix_opNorm_le_schur _ (a*C) (mul_nonneg ha hC)
  · intro i
    calc
      _ ≤ ∑ j, a*|A i j| := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _))
      _ = a*(∑ j, |A i j|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr i) ha
  · intro j
    calc
      _ ≤ ∑ i, a*|A i j| := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _))
      _ = a*(∑ i, |A i j|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc j) ha

end SKRatio.MatrixNet

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_CompactField
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus

lemma compactV_nonneg (a : FieldWeight) : 0 ≤ compactV a :=
  mul_nonneg a.2.1 (sub_nonneg.mpr a.2.2)
lemma compactV_le (a : FieldWeight) : compactV a≤2*a := by
  dsimp [compactV]
  nlinarith [sq_nonneg (a:ℝ)]
lemma compactF_nonneg (p : FieldWeight × FieldWeight) : 0 ≤ compactF p := by
  unfold compactF
  exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (add_nonneg p.1.2.1 p.2.2.1)
lemma compactK_nonneg (p : FieldWeight × FieldWeight) : 0 ≤ compactK p := by
  unfold compactK
  exact div_nonneg (mul_nonneg (compactV_nonneg _) (compactV_nonneg _)) (add_nonneg p.1.2.1 p.2.2.1)

lemma compactF_bound (p : FieldWeight × FieldWeight) : compactF p ≤ 4*(p.2:ℝ) := by
  by_cases hz : (p.1:ℝ)+(p.2:ℝ)=0
  · simp only [compactF,hz,div_zero]
    exact mul_nonneg (by norm_num) p.2.2.1
  have hd : 0<(p.1:ℝ)+(p.2:ℝ) := lt_of_le_of_ne (add_nonneg p.1.2.1 p.2.2.1) (Ne.symm hz)
  apply (div_le_iff₀ hd).mpr
  have hs : (2-(p.2:ℝ))^2≤4 := by nlinarith [p.2.2.1,p.2.2.2]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (p.2:ℝ))
  nlinarith only [hm,mul_nonneg p.1.2.1 p.2.2.1]

lemma compactK_bound (p : FieldWeight × FieldWeight) : compactK p ≤ 4*(p.2:ℝ) := by
  by_cases hz : (p.1:ℝ)+(p.2:ℝ)=0
  · simp only [compactK,hz,div_zero]
    exact mul_nonneg (by norm_num) p.2.2.1
  have hd : 0<(p.1:ℝ)+(p.2:ℝ) := lt_of_le_of_ne (add_nonneg p.1.2.1 p.2.2.1) (Ne.symm hz)
  apply (div_le_iff₀ hd).mpr
  have hm := mul_le_mul (compactV_le p.1) (compactV_le p.2)
    (compactV_nonneg p.2) (mul_nonneg (by norm_num : (0:ℝ)≤2) p.1.2.1)
  nlinarith only [hm,sq_nonneg (p.2:ℝ)]

lemma continuous_compactV : Continuous compactV := by unfold compactV; fun_prop

lemma continuous_compact_div {f : FieldWeight × FieldWeight → ℝ}
    (hnonneg : ∀ p, 0≤f p) (hbound : ∀ p, f p≤4*(p.2:ℝ))
    (hoff : ∀ p, (p.1:ℝ)+(p.2:ℝ)≠0 → ContinuousAt f p) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hz : (p.1:ℝ)+(p.2:ℝ)=0
  · have h2 : (p.2:ℝ)=0 := by linarith [p.1.2.1,p.2.2.1]
    have hp : f p=0 := le_antisymm (by simpa [h2] using hbound p) (hnonneg p)
    rw [ContinuousAt,hp]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun q : FieldWeight × FieldWeight => 4*(q.2:ℝ))
      (by simpa only [ContinuousAt,h2,mul_zero] using
        (show Continuous (fun q : FieldWeight × FieldWeight => 4*(q.2:ℝ)) by fun_prop).continuousAt (x := p))
      hnonneg hbound
  · exact hoff p hz

lemma continuous_compactF : Continuous compactF := by
  apply continuous_compact_div compactF_nonneg compactF_bound
  intro p hp
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hp

lemma continuous_compactK : Continuous compactK := by
  apply continuous_compact_div compactK_nonneg compactK_bound
  intro p hp
  exact ContinuousAt.div
    ((continuous_compactV.comp continuous_fst).mul (continuous_compactV.comp continuous_snd)).continuousAt
    (by fun_prop) hp

lemma compactV_weight (h : ℝ) : compactV (compactWeight h) = v h := by
  unfold compactV compactWeight w v
  dsimp
  ring

lemma compactF_weight (h t : ℝ) : compactF (compactWeight h,compactWeight t) =
    v t^2/(w h+w t) := by
  unfold compactF
  simp only [compactWeight_coe,←mul_pow]
  rw [show w t*(2-w t)=v t from compactV_weight t]

lemma compactK_weight (h t : ℝ) : compactK (compactWeight h,compactWeight t) =
    kernel h t := by
  unfold compactK kernel
  rw [compactV_weight,compactV_weight]
  rfl

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FormAlgebra
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma quadratic_inner (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    quadratic A p = inner ℝ (WithLp.toLp 2 p)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A (WithLp.toLp 2 p)) := by
  rw [Matrix.inner_toEuclideanCLM]
  simp only [quadratic,dotProduct,Matrix.mulVec,Finset.mul_sum]
  congr 1
  ext i
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadratic_abs_le (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    |quadratic A p| ≤ euclideanOpNorm A*(∑ i, p i^2) := by
  rw [quadratic_inner]
  let P : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 p
  have hb := (abs_real_inner_le_norm P (Matrix.toEuclideanCLM (𝕜 := ℝ) A P)).trans
    (mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) A).le_opNorm P) (norm_nonneg P))
  calc
    _ ≤ ‖P‖*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖*‖P‖) := hb
    _ = euclideanOpNorm A*(∑ i, p i^2) := by
      rw [show ‖P‖*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖*‖P‖) =
        euclideanOpNorm A*‖P‖^2 by unfold euclideanOpNorm; ring]
      rw [EuclideanSpace.real_norm_sq_eq]

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FormContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus MatrixNet
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma weightedForm_field_sub (A : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x y : Fin n → FieldWeight) (p : Fin n → ℝ) :
    weightedForm A G x p-weightedForm A G y p =
      quadratic (fun i j => A i j*(G (x i,x j)-G (y i,y j))) p := by
  simp only [weightedForm,quadratic,mul_sub,sub_mul,Finset.sum_sub_distrib]

lemma weightedForm_field_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x y : Fin n → FieldWeight) (p : Fin n → ℝ)
    {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
    (hr : ∀ i, ∑ j, |A i j| ≤ C) (hc : ∀ j, ∑ i, |A i j| ≤ C)
    (he : ∀ i j, |G (x i,x j)-G (y i,y j)| ≤ a) :
    |weightedForm A G x p-weightedForm A G y p| ≤ a*C*∑ i, p i^2 := by
  rw [weightedForm_field_sub]
  exact (quadratic_abs_le _ p).trans (mul_le_mul_of_nonneg_right
    (kernel_error_norm_le A _ _ ha hC hr hc he) (Finset.sum_nonneg (fun i _ => sq_nonneg (p i))))

lemma diagonalForm_field_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x y : Fin n → FieldWeight) (p : Fin n → ℝ)
    {a C : ℝ} (ha : 0≤a)
    (hr : ∀ i, ∑ j, |A i j| ≤ C)
    (he : ∀ i j, |G (x i,x j)-G (y i,y j)| ≤ a) :
    |diagonalForm A G x p-diagonalForm A G y p| ≤ a*C*∑ i, p i^2 := by
  have hid : diagonalForm A G x p-diagonalForm A G y p =
      ∑ i, (∑ j, A i j*(G (x i,x j)-G (y i,y j)))*p i^2 := by
    simp only [diagonalForm,mul_sub,sub_mul,Finset.sum_sub_distrib]
  have hb (i : Fin n) : |∑ j, A i j*(G (x i,x j)-G (y i,y j))| ≤ a*C := by
    calc
      _ ≤ ∑ j, |A i j*(G (x i,x j)-G (y i,y j))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, a*|A i j| := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _))
      _ = a*(∑ j, |A i j|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr i) ha
  rw [hid]
  calc
    _ ≤ ∑ i, |(∑ j, A i j*(G (x i,x j)-G (y i,y j)))*p i^2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (a*C)*p i^2 := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul,abs_of_nonneg (sq_nonneg (p i))]
      exact mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _))
    _ = _ := (Finset.mul_sum ..).symm

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinProjected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression Scalar
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma weightedForm_variance_bilinear (M : Matrix (Fin n) (Fin n) ℝ)
    (H p : Fin n → ℝ) :
    weightedForm M varianceKernel (fun i => compactWeight (H i)) p =
      p ⬝ᵥ (M*ᵥ (fun i => v (H i)*p i)) := by
  simp only [weightedForm,quadratic,varianceKernel,compactV_weight,dotProduct,
    Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma rank_form_expansion (H v p : Fin n → ℝ) :
    (∑ i, ∑ j, ((H i+H j-(∑ k, H k)/(n:ℝ))/(n:ℝ))*v j*p i*p j) =
      rankForm H v p := by
  simp only [rankForm,add_div,sub_div,add_mul,sub_mul,Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have h1 (i : Fin n) : (∑ j, H i/(n:ℝ)*v j*p i*p j) =
      p i*H i*(∑ j, p j*v j)/(n:ℝ) := by
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 (i : Fin n) : (∑ j, H j/(n:ℝ)*v j*p i*p j) =
      p i*(∑ j, p j*H j*v j)/(n:ℝ) := by
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h3 (i : Fin n) : (∑ j, ((∑ k, H k)/(n:ℝ))/(n:ℝ)*v j*p i*p j) =
      ((∑ k, H k)/(n:ℝ))*p i*(∑ j, p j*v j)/(n:ℝ) := by
    conv_rhs => rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [h1,h2,h3]
  simp only [←Finset.sum_div,←Finset.sum_mul,←Finset.mul_sum]

theorem reducedForm_decomposition (hn : 0<n) (β : ℝ)
    (g : (Fin n × Fin n) → ℝ) (p : Fin n → ℝ) :
    reducedForm β g p =
      p ⬝ᵥ ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ
        (fun i => v (augmentedField β g i)*p i)) +
      deterministicForm β (augmentedField β g) p := by
  have h1 : weightedForm (augmented β g) varianceKernel
      (fun i => compactWeight (augmentedField β g i)) p =
      weightedForm (fieldProjection n*(β • goe g)*fieldProjection n) varianceKernel
        (fun i => compactWeight (augmentedField β g i)) p +
      rankForm (augmentedField β g) (fun i => v (augmentedField β g i)) p := by
    simp only [weightedForm,quadratic,varianceKernel,compactV_weight]
    simp_rw [augmented_decomposition hn,add_mul,Finset.sum_add_distrib]
    rw [rank_form_expansion]
  have h2 : 2*weightedForm (fun _ _ => β^2/(n:ℝ)) meanVarianceKernel
      (fun i => compactWeight (augmentedField β g i)) p =
      2*β^2/(n:ℝ)*(∑ i, p i)*(∑ i, p i*m (augmentedField β g i)*v (augmentedField β g i)) := by
    simp only [weightedForm,quadratic,meanVarianceKernel,compactV_weight,compactWeight_coe,
      w,sub_sub_cancel]
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  dsimp only [reducedForm]
  rw [h1,h2,weightedForm_variance_bilinear]
  unfold deterministicForm
  ring

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinFunctional
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

omit [DecidableEq α]

lemma continuous_paramB (a : α) : Continuous (fun z : Parameters α => paramB z a) :=
  (EuclideanSpace.proj (Sum.inl a : α ⊕ α)).continuous.comp continuous_subtype_val
lemma continuous_paramR (a : α) : Continuous (fun z : Parameters α => paramR z a) :=
  (EuclideanSpace.proj (Sum.inr a : α ⊕ α)).continuous.comp continuous_subtype_val

lemma continuous_finiteRadicalSq (v : α → ℝ) (a : α) :
    Continuous (fun q : (α → ℝ) × Parameters α => finiteRadicalSq q.1 v q.2 a) := by
  unfold finiteRadicalSq moment
  have hb (d : α) := (continuous_paramB d).comp (continuous_snd (X := α → ℝ))
  have hr (d : α) := (continuous_paramR d).comp (continuous_snd (X := α → ℝ))
  fun_prop

lemma continuous_finiteGaussian (β : ℝ) (v : α → ℝ) :
    Continuous (fun q : (α → ℝ) × Parameters α => finiteGaussian β q.1 v q.2) := by
  unfold finiteGaussian
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro a _
  exact (((continuous_apply a).comp continuous_fst).mul
    ((continuous_paramR a).comp continuous_snd)).mul
    (continuous_sqrt.comp (continuous_finiteRadicalSq v a))

lemma continuous_finiteA (β : ℝ) (h : α → ℝ) :
    Continuous (fun q : (α → ℝ) × Parameters α => finiteA β q.1 h q.2) := by
  unfold finiteA moment
  have hb (a : α) := (continuous_paramB a).comp (continuous_snd (X := α → ℝ))
  have hr (a : α) := (continuous_paramR a).comp (continuous_snd (X := α → ℝ))
  fun_prop

lemma continuous_finiteV (β : ℝ) (h : α → ℝ) :
    Continuous (fun q : (α → ℝ) × Parameters α => finiteV β q.1 h q.2) :=
  (continuous_finiteA β h).add (continuous_finiteGaussian β (fun a => v (h a)))

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma momentProduct (p f q k : Fin n → ℝ) :
    siteMoment p f*siteMoment q k=(∑ i, p i*f i)*(∑ i, q i*k i)/(n:ℝ) := by
  unfold siteMoment
  rw [div_mul_div_comm,←pow_two,sq_sqrt (Nat.cast_nonneg n)]

lemma deterministic_corrected (β : ℝ) (H p : Fin n → ℝ) :
    deterministicForm β H p = correctedForm β H p+
      (β^2-(∑ i, H i)/(n:ℝ))*siteMoment p (fun _ => 1)*siteMoment p (fun i => v (H i)) := by
  unfold deterministicForm correctedForm rankForm
  simp only [mul_assoc]
  simp only [←mul_assoc,momentProduct,mul_one,Finset.sum_mul]
  ring

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinNet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma norm_of_sum_sq_one {p : Fin n → ℝ} (hp : ∑ i, p i^2=1) :
    ‖WithLp.toLp 2 p‖=1 := by
  have he := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 p)
  simp only [hp] at he
  nlinarith only [he,norm_nonneg (WithLp.toLp 2 p)]

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma siteNorm_nonneg (f : Fin n → ℝ) : 0≤ siteNorm f := by unfold siteNorm; positivity

lemma siteNorm_sq (f : Fin n → ℝ) : siteNorm f^2=(∑ i, f i^2)/(n:ℝ) := by
  rw [siteNorm,div_pow,EuclideanSpace.real_norm_sq_eq,sq_sqrt (Nat.cast_nonneg n)]

lemma siteNorm_add (f g : Fin n → ℝ) :
    siteNorm (fun i => f i+g i)≤ siteNorm f+siteNorm g := by
  unfold siteNorm
  rw [←add_div]
  exact div_le_div_of_nonneg_right
    (norm_add_le (WithLp.toLp 2 f) (WithLp.toLp 2 g)) (sqrt_nonneg _)

lemma siteNorm_le_of_abs_le {f : Fin n → ℝ} {D : ℝ} (hD : 0≤D)
    (hf : ∀ i, |f i|≤D) : siteNorm f≤D := by
  have hs : (∑ i, f i^2)≤(n:ℝ)*D^2 := by
    calc
      _ ≤ ∑ _i : Fin n, D^2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).mpr (hf i))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  by_cases hn : n=0
  · simp only [siteNorm,hn,Nat.cast_zero,sqrt_zero,div_zero]
    exact hD
  · have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hh : siteNorm f^2≤D^2 := by
      rw [siteNorm_sq]
      exact (div_le_iff₀ hnR).mpr (by nlinarith only [hs])
    nlinarith only [hh,siteNorm_nonneg f,hD]

lemma siteNorm_mul_le {f g : Fin n → ℝ} {D : ℝ} (hD : 0≤D)
    (hg : ∀ i, |g i|≤D) : siteNorm (fun i => f i*g i)≤D*siteNorm f := by
  have hs : (∑ i, (f i*g i)^2)≤D^2*(∑ i, f i^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh : g i^2≤D^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).mpr (hg i)
    rw [mul_pow,mul_comm (D^2)]
    exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)
  have hh : siteNorm (fun i => f i*g i)^2≤(D*siteNorm f)^2 := by
    rw [mul_pow,siteNorm_sq,siteNorm_sq,←mul_div_assoc]
    exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
  have hz : 0≤D*siteNorm f := mul_nonneg hD (siteNorm_nonneg f)
  nlinarith only [hh,siteNorm_nonneg (fun i => f i*g i),hz]

lemma siteMoment_abs_le {p : Fin n → ℝ} (hp : ∑ i, p i^2=1) (f : Fin n → ℝ) :
    |siteMoment p f|≤ siteNorm f := by
  have hh := abs_real_inner_le_norm (WithLp.toLp 2 p) (WithLp.toLp 2 f)
  rw [norm_of_sum_sq_one hp,one_mul] at hh
  have he : inner ℝ (WithLp.toLp 2 p) (WithLp.toLp 2 f) = ∑ i, p i*f i := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [he] at hh
  unfold siteMoment siteNorm
  rw [abs_div,abs_of_nonneg (sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right hh (sqrt_nonneg _)

lemma siteMoment_sub (p f g : Fin n → ℝ) :
    siteMoment p (fun i => f i-g i)=siteMoment p f-siteMoment p g := by
  simp only [siteMoment,mul_sub,Finset.sum_sub_distrib,sub_div]

lemma siteMoment_one {p : Fin n → ℝ} (hp : ∑ i, p i^2=1) :
    |siteMoment p (fun _ => 1)|≤1 :=
  (siteMoment_abs_le hp _).trans (siteNorm_le_of_abs_le (by norm_num) (fun _ => by norm_num))

lemma v_abs_le_one (x : ℝ) : |v x|≤1 := by rw [abs_of_nonneg (v_pos x).le]; exact v_le_one x

lemma siteMoment_v {p : Fin n → ℝ} (hp : ∑ i, p i^2=1) (H : Fin n → ℝ) :
    |siteMoment p (fun i => v (H i))|≤1 :=
  (siteMoment_abs_le hp _).trans (siteNorm_le_of_abs_le (by norm_num) (fun _ => v_abs_le_one _))

lemma product_error {x y x' y' S T d e : ℝ} (hS : 0≤S) (hT : 0≤T)
    (hy : |y|≤S) (hx : |x'|≤T) (hd : |x-x'|≤d) (he : |y-y'|≤e) :
    |x*y-x'*y'|≤d*S+T*e := by
  rw [show x*y-x'*y'=(x-x')*y+x'*(y-y') by ring]
  calc
    _ ≤ |(x-x')*y|+|x'*(y-y')| := abs_add_le _ _
    _ ≤ d*S+T*e := by
      simp only [abs_mul]
      exact add_le_add ((mul_le_mul_of_nonneg_left hy (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hd hS))
        (mul_le_mul hx he (abs_nonneg _) hT)

lemma mean_constant_rows (hn : 0<n) (β : ℝ) (_ : Fin n) :
    (∑ _j : Fin n, |β^2/(n:ℝ)|)=β^2 := by
  simp only [abs_of_nonneg (by positivity : 0≤β^2/(n:ℝ)),Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')

theorem correctedForm_field_error (hn : 0<n) (β : ℝ) (H H' p : Fin n → ℝ)
    (hp : ∑ i, p i^2=1) {a d T : ℝ} (ha : 0≤a) (hd : 0≤d) (hT : 0≤T)
    (he : siteNorm (fun i => H i-H' i)≤d) (hsize : siteNorm H'≤T)
    (hv : ∀ i, |v (H i)-v (H' i)|≤a)
    (hmv : ∀ i, |m (H i)*v (H i)-m (H' i)*v (H' i)|≤a)
    (hf : ∀ i j, |compactF (compactWeight (H i),compactWeight (H j))-
      compactF (compactWeight (H' i),compactWeight (H' j))|≤a)
    (hk : ∀ i j, |compactK (compactWeight (H i),compactWeight (H j))-
      compactK (compactWeight (H' i),compactWeight (H' j))|≤a) :
    |correctedForm β H p-correctedForm β H' p|≤2*d+2*T*a+5*β^2*a := by
  have hH : |siteMoment p H-siteMoment p H'|≤d := by
    rw [←siteMoment_sub]
    exact (siteMoment_abs_le hp _).trans he
  have hV : |siteMoment p (fun i => v (H i))-siteMoment p (fun i => v (H' i))|≤a := by
    rw [←siteMoment_sub]
    exact (siteMoment_abs_le hp _).trans (siteNorm_le_of_abs_le ha hv)
  have hMV : |siteMoment p (fun i => m (H i)*v (H i))-
      siteMoment p (fun i => m (H' i)*v (H' i))|≤a := by
    rw [←siteMoment_sub]
    exact (siteMoment_abs_le hp _).trans (siteNorm_le_of_abs_le ha hmv)
  have hHv : |siteMoment p (fun i => H i*v (H i))-
      siteMoment p (fun i => H' i*v (H' i))|≤d+T*a := by
    rw [←siteMoment_sub]
    apply (siteMoment_abs_le hp _).trans
    have heq : (fun i => H i*v (H i)-H' i*v (H' i))=
        (fun i => (H i-H' i)*v (H i)+H' i*(v (H i)-v (H' i))) := by funext i; ring
    rw [heq]
    apply (siteNorm_add _ _).trans
    have h1 := siteNorm_mul_le (f := fun i => H i-H' i) (by norm_num : (0:ℝ)≤1)
      (fun i => v_abs_le_one (H i))
    have h2 := siteNorm_mul_le (f := H') ha hv
    have h3 := mul_le_mul_of_nonneg_left hsize ha
    nlinarith only [h1,h2,h3,he]
  have h1 := product_error (by norm_num : (0:ℝ)≤1) hT (siteMoment_v hp H)
    ((siteMoment_abs_le hp H').trans hsize) hH hV
  have h₂ : |siteMoment p (fun _ => 1)*siteMoment p (fun i => H i*v (H i))-
      siteMoment p (fun _ => 1)*siteMoment p (fun i => H' i*v (H' i))|≤d+T*a := by
    rw [←mul_sub,abs_mul,mul_comm]
    exact (mul_le_mul hHv (siteMoment_one hp) (abs_nonneg _)
      (add_nonneg hd (mul_nonneg hT ha))).trans_eq (mul_one _)
  have h₃ : |β^2*siteMoment p (fun _ => 1)*
      (siteMoment p (fun i => v (H i))-siteMoment p (fun i => v (H' i)))|≤β^2*a := by
    rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg β)]
    exact mul_le_mul ((mul_le_mul_of_nonneg_left (siteMoment_one hp) (sq_nonneg β)).trans_eq (mul_one _))
      hV (abs_nonneg _) (sq_nonneg β)
  have h₄ : |2*β^2*siteMoment p (fun _ => 1)*
      (siteMoment p (fun i => m (H i)*v (H i))-siteMoment p (fun i => m (H' i)*v (H' i)))|≤2*β^2*a := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤2*β^2)]
    exact mul_le_mul ((mul_le_mul_of_nonneg_left (siteMoment_one hp) (by positivity : 0≤2*β^2)).trans_eq (mul_one _))
      hMV (abs_nonneg _) (by positivity)
  have h₅ := diagonalForm_field_bound (fun _ _ => β^2/(n:ℝ)) compactF
    (fun i => compactWeight (H i)) (fun i => compactWeight (H' i)) p ha
    (fun i => (mean_constant_rows hn β i).le) hf
  have h₆ := weightedForm_field_bound (fun _ _ => β^2/(n:ℝ)) compactK
    (fun i => compactWeight (H i)) (fun i => compactWeight (H' i)) p ha (sq_nonneg β)
    (fun i => (mean_constant_rows hn β i).le) (fun i => (mean_constant_rows hn β i).le) hk
  rw [hp,mul_one] at h₅ h₆
  let A := siteMoment p H*siteMoment p (fun i => v (H i))-
    siteMoment p H'*siteMoment p (fun i => v (H' i))
  let B := siteMoment p (fun _ => 1)*siteMoment p (fun i => H i*v (H i))-
    siteMoment p (fun _ => 1)*siteMoment p (fun i => H' i*v (H' i))
  let C := β^2*siteMoment p (fun _ => 1)*(siteMoment p (fun i => v (H i))-siteMoment p (fun i => v (H' i)))
  let D := 2*β^2*siteMoment p (fun _ => 1)*(siteMoment p (fun i => m (H i)*v (H i))-
    siteMoment p (fun i => m (H' i)*v (H' i)))
  let E := diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF (fun i => compactWeight (H i)) p-
    diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF (fun i => compactWeight (H' i)) p
  let F := weightedForm (fun _ _ => β^2/(n:ℝ)) compactK (fun i => compactWeight (H i)) p-
    weightedForm (fun _ _ => β^2/(n:ℝ)) compactK (fun i => compactWeight (H' i)) p
  have heq : correctedForm β H p-correctedForm β H' p=A+B-C+D+E+F := by
    dsimp [correctedForm,A,B,C,D,E,F]; ring
  rw [heq]
  have ht : |A+B-C+D+E+F|≤|A|+|B|+|C|+|D|+|E|+|F| := by
    calc
      _ ≤ |A+B-C+D+E|+|F| := abs_add_le _ _
      _ ≤ (|A+B-C+D|+|E|)+|F| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|A+B-C|+|D|)+|E|)+|F| := by gcongr; exact abs_add_le _ _
      _ ≤ (((|A+B|+|C|)+|D|)+|E|)+|F| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  change |A|≤_ at h1
  change |B|≤_ at h₂
  change |C|≤_ at h₃
  change |D|≤_ at h₄
  change |E|≤_ at h₅
  change |F|≤_ at h₆
  nlinarith only [ht,h1,h₂,h₃,h₄,h₅,h₆]

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_FieldSize
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression Bins
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma augmentedAverage_gaussian (β : ℝ) :
    HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ =>
      (∑ i, augmentedField β g i)/(n:ℝ)) (standardArrayLaw (Fin n × Fin n)) := by
  simpa only [smul_apply,ContinuousLinearMap.id_apply,
    smul_eq_mul,inv_mul_eq_div] using
    (augmentedField_gaussian (n := n) β).fun_sum.map_fun
      ((n:ℝ)⁻¹ • ContinuousLinearMap.id ℝ ℝ)

lemma augmentedAverage_hasLaw (hn : 0<n) (β : ℝ) :
    HasLaw (fun g : (Fin n × Fin n) → ℝ => (∑ i, augmentedField β g i)/(n:ℝ))
      (gaussianReal (β^2) (Real.toNNReal (2*β^2/(n:ℝ))))
      (standardArrayLaw (Fin n × Fin n)) := by
  have hg := augmentedAverage_gaussian (n := n) β
  have hLp (i : Fin n) := ((augmentedField_gaussian β).eval i).memLp_two
  have hmean : (∫ g, (∑ i, augmentedField β g i)/(n:ℝ)
      ∂standardArrayLaw (Fin n × Fin n))=β^2 := by
    rw [integral_div,integral_finsetSum _ (fun i _ => ((augmentedField_gaussian β).eval i).integrable)]
    simp only [augmentedField_mean hn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hvar : Var[(fun g => (∑ i, augmentedField β g i)/(n:ℝ));
      standardArrayLaw (Fin n × Fin n)] = 2*β^2/(n:ℝ) := by
    rw [←covariance_self hg.aemeasurable,covariance_fun_div_left,covariance_fun_div_right,
      covariance_fun_sum_fun_sum hLp hLp]
    simp only [augmentedField_covariance hn,Finset.sum_add_distrib,Finset.sum_ite_eq,
      Finset.mem_univ,ite_true, if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
    ring
  exact ⟨hg.aemeasurable,by rw [hg.map_eq_gaussianReal,hmean,hvar]⟩

theorem augmentedField_firstMoment (β : ℝ) (hβ : 0<β) :
    ExponentialConvergence (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n g => (∑ i, augmentedField β g i)/(n:ℝ)) (β^2) := by
  intro ε hε
  refine ⟨2,ε^2/(4*β^2),by norm_num,by positivity,?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hc : HasLaw (fun g : (Fin n × Fin n) → ℝ =>
      (∑ i, augmentedField β g i)/(n:ℝ)-β^2)
      (gaussianReal 0 (Real.toNNReal (2*β^2/(n:ℝ))))
      (standardArrayLaw (Fin n × Fin n)) := by
    have h := gaussianReal_add_const (augmentedAverage_hasLaw hn β) (-(β^2 : ℝ))
    rw [add_neg_cancel] at h
    simpa only [sub_eq_add_neg] using h
  have ht := subgaussian_abs_tail (gaussian_hasSubgaussianMGF hc) ε hε.le
  rw [Real.coe_toNNReal _ (by positivity : 0≤2*β^2/(n:ℝ))] at ht
  have he : -ε^2/(2*(2*β^2/(n:ℝ)))=-(ε^2/(4*β^2))*(n:ℝ) := by field_simp; ring
  rw [he,←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by norm_num)] at ht
  exact ht

lemma siteNorm_eq_sqrt (H : Fin n → ℝ) :
    siteNorm H = sqrt ((∑ i, H i^2)/(n:ℝ)) := by
  rw [←siteNorm_sq,sqrt_sq (siteNorm_nonneg H)]

lemma augmentedField_siteNorm (β : ℝ) (hβ : 0<β) :
    ExponentialConvergence (fun n => standardArrayLaw (Fin n × Fin n))
      (fun _ g => siteNorm (augmentedField β g)) (sqrt (β^2+β^4)) := by
  simpa only [siteNorm_eq_sqrt] using
    (augmentedField_secondMoment β hβ).continuous_map continuous_sqrt.continuousAt

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_EmpiricalIntervals
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real Set
namespace SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma cdfRamp_bounds (a b x : ℝ) : 0 ≤ cdfRamp a b x ∧ cdfRamp a b x≤1 := by
  unfold cdfRamp
  exact ⟨le_max_left ..,max_le (by norm_num) (min_le_left ..)⟩

lemma cdfRamp_lipschitz {a b : ℝ} (hab : a<b) :
    LipschitzWith ⟨(b-a)⁻¹,by positivity⟩ (cdfRamp a b) := by
  let K : ℝ≥0 := ⟨(b-a)⁻¹,by positivity⟩
  change LipschitzWith K (cdfRamp a b)
  have hlin : LipschitzWith K (fun x : ℝ => (b-x)/(b-a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((b-x)/(b-a)) ((b-y)/(b-a)) ≤ (b-a)⁻¹*dist x y
    simp only [Real.dist_eq]
    rw [←sub_div,show b-x-(b-y)=-(x-y) by ring,abs_div,abs_neg,
      abs_of_pos (sub_pos.mpr hab)]
    exact le_of_eq (by ring)
  unfold cdfRamp
  simpa only [max_self] using
    (LipschitzWith.const' 0 (K:=K)).max
      ((LipschitzWith.const' 1 (K:=K)).min hlin)

lemma cdfRamp_sandwich {a b : ℝ} (hab : a<b) (x : ℝ) :
    (Set.Iic a).indicator (fun _ : ℝ => (1:ℝ)) x ≤ cdfRamp a b x ∧
    cdfRamp a b x≤(Set.Iic b).indicator (fun _ : ℝ => (1:ℝ)) x := by
  constructor
  · by_cases hx : x≤a
    · rw [indicator_of_mem (show x∈Set.Iic a from hx)]
      unfold cdfRamp
      have hh : 1≤(b-x)/(b-a) := (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
      rw [min_eq_left hh,max_eq_right (by norm_num : (0:ℝ)≤1)]
    · rw [indicator_of_notMem (show x∉Set.Iic a from hx)]
      exact (cdfRamp_bounds ..).1
  · by_cases hx : x≤b
    · rw [indicator_of_mem (show x∈Set.Iic b from hx)]
      exact (cdfRamp_bounds ..).2
    · rw [indicator_of_notMem (show x∉Set.Iic b from hx)]
      have hh : (b-x)/(b-a)≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      unfold cdfRamp
      rw [min_eq_right (hh.trans (by norm_num)),max_eq_left hh]

lemma integrable_cdfRamp {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a<b) :
    Integrable (cdfRamp a b) μ :=
  (integrable_const (1:ℝ)).mono' (cdfRamp_lipschitz hab).continuous.aestronglyMeasurable
    (ae_of_all μ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (cdfRamp_bounds ..).1]; exact (cdfRamp_bounds ..).2))

lemma integral_cdfRamp_bounds {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a<b) :
    μ.real (Set.Iic a)≤∫ x, cdfRamp a b x ∂μ ∧ (∫ x, cdfRamp a b x ∂μ)≤μ.real (Set.Iic b) := by
  have h1 := integral_mono ((integrable_const (1:ℝ)).indicator measurableSet_Iic)
    (integrable_cdfRamp (μ:=μ) hab) (fun x => (cdfRamp_sandwich hab x).1)
  have h2 := integral_mono (integrable_cdfRamp (μ:=μ) hab)
    ((integrable_const (1:ℝ)).indicator measurableSet_Iic) (fun x => (cdfRamp_sandwich hab x).2)
  simpa only [integral_indicator measurableSet_Iic,integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using And.intro h1 h2

lemma continuous_measureReal_Iic (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Continuous (fun t : ℝ => μ.real (Set.Iic t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := ((integrable_const (1:ℝ) : Integrable (fun _ : ℝ => (1:ℝ)) μ).integrableOn).continuousOn_Iic_primitive_Iic (a₀:=t+1)
  have ht := h.continuousAt (Iic_mem_nhds (by linarith : t<t+1))
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using ht

theorem ExponentialEmpiricalConcentration.Iic
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    {μ : Measure ℝ} [IsFiniteMeasure μ] [NullSingletonClass μ]
    (hX : ExponentialEmpiricalConcentration ρ X μ) (t : ℝ) :
    ExponentialConvergence ρ
      (fun n ω => (∑ i, (Set.Iic t).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ))
      (μ.real (Set.Iic t)) := by
  intro ε hε
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousAt_iff.mp ((continuous_measureReal_Iic μ).continuousAt (x:=t)) (ε/4) (by positivity)
  let d := δ/2
  have hd : 0<d := by dsimp [d]; positivity
  have hlo := hnear (x:=t-d) (by simpa only [Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos hd] using (show d<δ by dsimp [d]; linarith))
  have hhi := hnear (x:=t+d) (by simpa only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hd] using (show d<δ by dsimp [d]; linarith))
  have hL := hX.average (cdfRamp (t-d) t) (cdfRamp_lipschitz (by linarith : t-d<t)) 1
    (fun x => by rw [abs_of_nonneg (cdfRamp_bounds ..).1]; exact (cdfRamp_bounds ..).2)
  have hU := hX.average (cdfRamp t (t+d)) (cdfRamp_lipschitz (by linarith : t<t+d)) 1
    (fun x => by rw [abs_of_nonneg (cdfRamp_bounds ..).1]; exact (cdfRamp_bounds ..).2)
  apply ((hL (ε/2) (by positivity)).union (hU (ε/2) (by positivity))).mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro ω hbad
  by_contra hh
  have heL : |(∑ i, cdfRamp (t-d) t (X n ω i))/(n:ℝ)-∫ x, cdfRamp (t-d) t x ∂μ|<ε/2 := by
    apply lt_of_not_ge
    intro he
    exact hh (Or.inl he)
  have heU : |(∑ i, cdfRamp t (t+d) (X n ω i))/(n:ℝ)-∫ x, cdfRamp t (t+d) x ∂μ|<ε/2 := by
    apply lt_of_not_ge
    intro he
    exact hh (Or.inr he)
  have hsumL : (∑ i, cdfRamp (t-d) t (X n ω i))/(n:ℝ)≤
      (∑ i, (Set.Iic t).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ) :=
    div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => (cdfRamp_sandwich (by linarith : t-d<t) _).2)) (Nat.cast_nonneg n)
  have hsumU : (∑ i, (Set.Iic t).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ)≤
      (∑ i, cdfRamp t (t+d) (X n ω i))/(n:ℝ) :=
    div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => (cdfRamp_sandwich (by linarith : t<t+d) _).1)) (Nat.cast_nonneg n)
  have hibL := (integral_cdfRamp_bounds (μ:=μ) (by linarith : t-d<t)).1
  have hibU := (integral_cdfRamp_bounds (μ:=μ) (by linarith : t<t+d)).2
  change ε≤|(∑ i, (Set.Iic t).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ) - μ.real (Set.Iic t)| at hbad
  rw [Real.dist_eq] at hlo hhi
  rcases abs_cases ((∑ i, (Set.Iic t).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ) - μ.real (Set.Iic t)) with ⟨he,_⟩ | ⟨he,_⟩
  · rw [he] at hbad
    linarith only [hε,hbad,hsumU,hibU,(abs_lt.mp heU).2,(abs_lt.mp hhi).2]
  · rw [he] at hbad
    linarith only [hε,hbad,hsumL,hibL,(abs_lt.mp heL).1,(abs_lt.mp hlo).1]

lemma ExponentialConvergence.congr_eventually
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {ρ : ∀ n, Measure (Ω n)}
    {E : Type*} [PseudoMetricSpace E] {X Y : ∀ n, Ω n → E} {x : E}
    (hX : ExponentialConvergence ρ X x) (he : ∀ᶠ n in atTop, X n=Y n) :
    ExponentialConvergence ρ Y x := by
  intro ε hε
  apply (hX ε hε).mono
  filter_upwards [he] with n hn
  rw [hn]

lemma indicator_Ioc_sub {a b : ℝ} (hab : a≤b) (x : ℝ) :
    (Set.Ioc a b).indicator (fun _ : ℝ => (1:ℝ)) x=
      (Set.Iic b).indicator (fun _ : ℝ => (1:ℝ)) x-
        (Set.Iic a).indicator (fun _ : ℝ => (1:ℝ)) x := by
  by_cases hxa : x≤a
  · have hxb := hxa.trans hab
    simp [Set.indicator,Set.mem_Ioc,Set.mem_Iic,hxa,hxb,not_lt_of_ge hxa]
  · by_cases hxb : x≤b <;>
      simp [Set.indicator,Set.mem_Ioc,Set.mem_Iic,hxa,hxb,lt_of_not_ge hxa]

lemma ExponentialEmpiricalConcentration.Ioc
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    {μ : Measure ℝ} [IsFiniteMeasure μ] [NullSingletonClass μ]
    (hX : ExponentialEmpiricalConcentration ρ X μ) {a b : ℝ} (hab : a≤b) :
    ExponentialConvergence ρ
      (fun n ω => (∑ i, (Set.Ioc a b).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ))
      (μ.real (Set.Ioc a b)) := by
  have hm : μ.real (Set.Ioc a b)=μ.real (Set.Iic b)-μ.real (Set.Iic a) := by
    rw [←integral_indicator_one measurableSet_Ioc]
    change (∫ x, (Set.Ioc a b).indicator (fun _ : ℝ => (1:ℝ)) x ∂μ)=_
    simp_rw [indicator_Ioc_sub hab]
    rw [integral_sub ((integrable_const (1:ℝ)).indicator measurableSet_Iic)
      ((integrable_const (1:ℝ)).indicator measurableSet_Iic)]
    simp only [integral_indicator measurableSet_Iic,integral_const,
      smul_eq_mul,mul_one,measureReal_restrict_apply_univ]
  rw [hm]
  convert! ((hX.Iic b).prod (hX.Iic a)).continuous_map (f:=fun q : ℝ×ℝ => q.1-q.2) (by fun_prop) using 1
  all_goals try with_reducible_and_instances rfl
  funext n ω
  simp only [indicator_Ioc_sub hab,Finset.sum_sub_distrib,sub_div]

lemma ExponentialEmpiricalConcentration.Ioi
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hX : ExponentialEmpiricalConcentration ρ X μ) (a : ℝ) :
    ExponentialConvergence ρ
      (fun n ω => (∑ i, (Set.Ioi a).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ))
      (μ.real (Set.Ioi a)) := by
  have hm : μ.real (Set.Ioi a)=1-μ.real (Set.Iic a) := by
    rw [←Set.compl_Iic,measureReal_compl measurableSet_Iic,probReal_univ]
  rw [hm]
  apply ((hX.Iic a).continuous_map (f:=fun x : ℝ => 1-x) (by fun_prop)).congr_eventually
  filter_upwards [eventually_gt_atTop 0] with n hn
  funext ω
  have hi (x : ℝ) : (Set.Ioi a).indicator (fun _ : ℝ => (1:ℝ)) x=
      1-(Set.Iic a).indicator (fun _ : ℝ => (1:ℝ)) x := by
    by_cases hx : x≤a
    · simp [Set.indicator,hx,not_lt_of_ge hx]
    · simp [Set.indicator,hx,lt_of_not_ge hx]
  simp only [hi,Finset.sum_sub_distrib,sub_div,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one,div_self (show (n:ℝ)≠0 from Nat.cast_ne_zero.mpr hn.ne')]

end SKRatioClock.Regression

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_PlantedCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma continuous_field (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => field (coupling g) x i) := by
  unfold field
  exact continuous_finsetSum _ (fun j _ => (continuous_coupling i j).mul_const _)

lemma continuous_mean (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => mean (coupling g) x i) :=
  (continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_tanh y).continuousAt)).comp
    (continuous_field x i)

lemma continuous_conditionalVariance (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => conditionalVariance (coupling g) x i) := by
  unfold conditionalVariance
  exact continuous_const.sub ((continuous_mean x i).pow 2)

lemma continuous_gradientWeight (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => gradientWeight (coupling g) x i) := by
  unfold gradientWeight
  exact continuous_const.sub ((continuous_mean x i).const_mul _)

lemma continuous_gradientForm (p : Fin n → ℝ) :
    Continuous (fun g : Disorder n => gradientForm (coupling g) p) := by
  unfold gradientForm pairSum
  apply Continuous.add
  · apply Continuous.add
    · exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        (((continuous_coupling i j).mul_const _).mul
          (continuous_conditionalVariance _ j)).mul_const _))
    · apply Continuous.const_mul
      exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        (((((continuous_coupling i j).pow 2).mul_const _).mul
          (continuous_mean _ j)).mul (continuous_conditionalVariance _ j)).mul_const _))
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    apply Continuous.div
    · exact ((continuous_coupling i j).pow 2).mul
        ((((continuous_conditionalVariance _ j).mul_const _).add
          ((continuous_conditionalVariance _ i).mul_const _)).pow 2)
    · exact (continuous_gradientWeight _ i).add (continuous_gradientWeight _ j)
    · intro g
      exact (add_pos (gradientWeight_pos _ _ _) (gradientWeight_pos _ _ _)).ne'

lemma formBad_measurable (ρ : ℝ) (n : ℕ) : MeasurableSet (formBad ρ n) := by
  have he : formBad ρ n = ⋃ p : Fin n → ℝ,
      {g | (1-ρ)*(∑ i, p i^2) < gradientForm (coupling g) p} := by
    ext g
    simp [formBad]
  rw [he]
  exact (isOpen_iUnion (fun p => isOpen_lt continuous_const (continuous_gradientForm p))).measurableSet

lemma gradientForm_smul (J : Interaction n) (p : Fin n → ℝ) (a : ℝ) :
    gradientForm J (fun i => a*p i) = a^2*gradientForm J p := by
  unfold gradientForm pairSum
  simp only [mul_add,Finset.mul_sum,mul_div_assoc]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma gradientForm_zero (J : Interaction n) : gradientForm J 0 = 0 := by
  simp [gradientForm,pairSum]

lemma formBad_iff_unit (ρ : ℝ) (g : Disorder n) :
    g ∈ formBad ρ n ↔ ∃ p : Fin n → ℝ, (∑ i, p i^2) = 1 ∧
      1-ρ < gradientForm (coupling g) p := by
  constructor
  · rintro ⟨p,hp⟩
    have hnorm0 : 0 ≤ ∑ i, p i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hnorm : 0 < ∑ i, p i^2 := by
      by_contra h
      have hz : ∑ i, p i^2 = 0 := le_antisymm (not_lt.mp h) hnorm0
      have hp0 : p = 0 := by
        funext i
        have hi : p i^2 ≤ 0 := by
          rw [←hz]
          exact Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
        have : p i = 0 := by nlinarith [sq_nonneg (p i)]
        exact this
      rw [hp0,gradientForm_zero] at hp
      simp at hp
    let a := (sqrt (∑ i, p i^2))⁻¹
    have ha : 0 < a := inv_pos.mpr (sqrt_pos.mpr hnorm)
    have ha2 : a^2*(∑ i, p i^2) = 1 := by
      dsimp [a]
      rw [inv_pow,sq_sqrt hnorm0,inv_mul_cancel₀ hnorm.ne']
    refine ⟨fun i => a*p i,?_,?_⟩
    · simp only [mul_pow,←Finset.mul_sum]
      exact ha2
    · rw [gradientForm_smul]
      have ht := mul_lt_mul_of_pos_left hp (sq_pos_of_pos ha)
      have he : a^2*((1-ρ)*(∑ i, p i^2)) = (1-ρ)*(a^2*(∑ i, p i^2)) := by ring
      rw [he,ha2,mul_one] at ht
      exact ht
  · rintro ⟨p,hp,h⟩
    exact ⟨p,by simpa only [hp,mul_one] using h⟩

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinPartition
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar
variable {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma measurable_finite_comp {σ : Ω → α} (hσ : Measurable σ) (f : α → ℝ) :
    Measurable (fun x => f (σ x)) := (measurable_of_countable f).comp hσ

lemma memLp_finite_comp {σ : Ω → α} (hσ : Measurable σ) (f : α → ℝ) :
    MemLp (fun x => f (σ x)) 2 μ := by
  apply MemLp.of_bound (measurable_finite_comp hσ f).aestronglyMeasurable (∑ a, |f a|)
  exact ae_of_all _ (fun x => by
    rw [norm_eq_abs]
    exact Finset.single_le_sum (fun a _ => abs_nonneg (f a)) (Finset.mem_univ (σ x)))

omit [IsProbabilityMeasure μ] in
lemma measurable_pullback {σ : Ω → α} (hσ : Measurable σ) (B : α → ℝ) :
    Measurable (pullback μ σ B) := measurable_finite_comp hσ (fun a => B a / massRoot μ σ a)

lemma memLp_pullback {σ : Ω → α} (hσ : Measurable σ) (B : α → ℝ) :
    MemLp (pullback μ σ B) 2 μ := memLp_finite_comp hσ (fun a => B a / massRoot μ σ a)

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
lemma massRoot_pos {σ : Ω → α} (hm : ∀ a, 0<binMass μ σ a) (a : α) : 0 < massRoot μ σ a :=
  sqrt_pos.mpr (hm a)

lemma integral_pullback {σ : Ω → α} (hσ : Measurable σ) (hm : ∀ a, 0<binMass μ σ a)
    (B f : α → ℝ) : (∫ x, pullback μ σ B x*f (σ x) ∂μ)=moment (massRoot μ σ) B f := by
  rw [show (fun x => pullback μ σ B x*f (σ x))=
    (fun x => (fun a => B a/massRoot μ σ a*f a) (σ x)) from rfl,
    integral_finite_partition (μ := μ) hσ (fun a => B a / massRoot μ σ a * f a)]
  unfold moment
  apply Finset.sum_congr rfl
  intro a _
  have hs := massRoot_sq (μ := μ) σ a
  have hn := (massRoot_pos hm a).ne'
  rw [←hs]
  field_simp

lemma integral_pullback_energy {σ : Ω → α} (hσ : Measurable σ)
    (hm : ∀ a, 0<binMass μ σ a) (B R f : α → ℝ) :
    (∫ x, f (σ x)*(pullback μ σ B x^2+pullback μ σ R x^2) ∂μ)=
      ∑ a, f a*(B a^2+R a^2) := by
  rw [show (fun x => f (σ x)*(pullback μ σ B x^2+pullback μ σ R x^2))=
    (fun x => (fun a => f a*((B a/massRoot μ σ a)^2+(R a/massRoot μ σ a)^2)) (σ x)) from rfl,
    integral_finite_partition (μ := μ) hσ (fun a => f a*((B a/massRoot μ σ a)^2+(R a/massRoot μ σ a)^2))]
  apply Finset.sum_congr rfl
  intro a _
  rw [div_pow,div_pow,massRoot_sq]
  field_simp [(hm a).ne']

lemma pullback_normalized [DecidableEq α] {σ : Ω → α} (hσ : Measurable σ)
    (hm : ∀ a, 0<binMass μ σ a) (z : Parameters α) :
    (∫ x, pullback μ σ (paramB z) x^2+pullback μ σ (paramR z) x^2 ∂μ)=1 := by
  simpa only [one_mul] using (integral_pullback_energy hσ hm (paramB z) (paramR z) (fun _ => 1)).trans
    (by simpa only [one_mul] using param_sum_sq z)

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_IntervalBins
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real Set
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma intervalBin_le_cut {N : ℕ} {e : Fin N → ℝ} (he : StrictMono e)
    (x : ℝ) (j : Fin N) : (intervalBin e x).val≤j.val ↔ x≤e j := by
  constructor
  · intro hj
    by_contra hh
    have hx : e j<x := lt_of_not_ge hh
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun i => e i<x) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(he.monotone (Finset.mem_Iic.mp hi)).trans_lt hx⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    change (Finset.univ.filter (fun i => e i<x)).card≤j.val at hj
    omega
  · intro hx
    have hsub : Finset.univ.filter (fun i => e i<x) ⊆ Finset.Iio j := by
      intro i hi
      exact Finset.mem_Iio.mpr (he.lt_iff_lt.mp ((Finset.mem_filter.mp hi).2.trans_le hx))
    have hc := Finset.card_le_card hsub
    rwa [Fin.card_Iio] at hc

lemma intervalBin_eq_zero {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e) (x : ℝ) :
    intervalBin e x=0 ↔ x≤e ⟨0,hN⟩ := by
  rw [←intervalBin_le_cut he x ⟨0,hN⟩]
  simp only [Fin.ext_iff,Fin.val_zero,Nat.le_zero_eq]

lemma intervalBin_eq_last {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e) (x : ℝ) :
    intervalBin e x=Fin.last N ↔ e ⟨N-1,by omega⟩<x := by
  have hh := intervalBin_le_cut he x ⟨N-1,by omega⟩
  simp only [Fin.ext_iff,Fin.val_last]
  have hbound := (intervalBin e x).isLt
  constructor
  · intro h
    exact lt_of_not_ge (fun hx => by have := hh.mpr hx; omega)
  · intro h
    have hh' : ¬ (intervalBin e x).val≤N-1 := fun hu => not_le.mpr h (hh.mp hu)
    omega

lemma intervalBin_eq_middle {N : ℕ} {e : Fin N → ℝ} (he : StrictMono e)
    (x : ℝ) (j : Fin (N+1)) (hj0 : 0<j.val) (hjN : j.val<N) :
    intervalBin e x=j ↔ e ⟨j.val-1,by omega⟩<x ∧ x≤e ⟨j.val,hjN⟩ := by
  have hlo := intervalBin_le_cut he x ⟨j.val-1,by omega⟩
  have hhi := intervalBin_le_cut he x ⟨j.val,hjN⟩
  dsimp only [Fin.val_mk] at hlo hhi
  rw [Fin.ext_iff]
  constructor
  · intro hh
    constructor
    · exact lt_of_not_ge (fun hx => by have := hlo.mpr hx; omega)
    · exact hhi.mp (by omega)
  · rintro ⟨hl,hu⟩
    have h1 := hhi.mpr hu
    have h2 : ¬ (intervalBin e x).val≤j.val-1 := fun h => not_le.mpr hl (hlo.mp h)
    omega

lemma measurableSet_intervalBin {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e)
    (j : Fin (N+1)) : MeasurableSet {x | intervalBin e x=j} := by
  by_cases hj0 : j.val=0
  · have hj : j=0 := Fin.ext hj0
    simp only [hj,intervalBin_eq_zero hN he]
    exact measurableSet_Iic
  · by_cases hjN : j.val=N
    · have hj : j=Fin.last N := Fin.ext hjN
      simp only [hj,intervalBin_eq_last hN he]
      exact measurableSet_Ioi
    · have h1 : 0<j.val := Nat.pos_of_ne_zero hj0
      have h2 : j.val<N := by have := j.isLt; omega
      simp only [intervalBin_eq_middle he _ j h1 h2]
      exact measurableSet_Ioc

lemma measurable_intervalBin {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e) :
    Measurable (intervalBin e) := by
  apply measurable_to_countable'
  intro j
  exact measurableSet_intervalBin hN he j

lemma intervalBin_empirical {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hX : ExponentialEmpiricalConcentration ρ X μ) (j : Fin (N+1)) :
    ExponentialConvergence ρ
      (fun n ω => (count (fun i => intervalBin e (X n ω i)) j:ℝ)/(n:ℝ))
      (μ.real {x | intervalBin e x=j}) := by
  have heq (n : ℕ) (ω : Ω n) : (count (fun i => intervalBin e (X n ω i)) j:ℝ) =
      ∑ i, {x | intervalBin e x=j}.indicator (fun _ : ℝ => (1:ℝ)) (X n ω i) := by
    simp only [count,Finset.cast_card,Set.indicator,Set.mem_ofPred_eq]
    exact Finset.sum_filter _ _
  simp_rw [heq]
  by_cases hj0 : j.val=0
  · have hj : j=0 := Fin.ext hj0
    simpa only [hj,intervalBin_eq_zero hN he,Set.Iic_def] using hX.Iic (e ⟨0,hN⟩)
  · by_cases hjN : j.val=N
    · have hj : j=Fin.last N := Fin.ext hjN
      simpa only [hj,intervalBin_eq_last hN he,Set.Ioi_def] using hX.Ioi (e ⟨N-1,by omega⟩)
    · have h1 : 0<j.val := Nat.pos_of_ne_zero hj0
      have h2 : j.val<N := by have := j.isLt; omega
      simpa only [intervalBin_eq_middle he _ j h1 h2,Set.Ioc_def] using
        hX.Ioc (he.monotone (show (⟨j.val-1,by omega⟩ : Fin N)≤⟨j.val,h2⟩ from by simp))

lemma gaussianReal_real_pos_of_volume_pos (μ : ℝ) {s : ℝ≥0} (hs : s≠0)
    {E : Set ℝ} (hE : 0<volume E) : 0<(gaussianReal μ s).real E := by
  apply ENNReal.toReal_pos _ (measure_ne_top _ _)
  exact fun h => hE.ne' (gaussianReal_absolutelyContinuous' μ hs h)

lemma intervalBin_mass_pos {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e)
    (β : ℝ) (hβ : β≠0) (j : Fin (N+1)) :
    0<(fieldLaw β).real {x | intervalBin e x=j} := by
  have hv : variance β≠0 := by
    intro hh
    have hh' := congrArg (fun x : ℝ≥0 => (x:ℝ)) hh
    rw [variance_coe,NNReal.coe_zero] at hh'
    exact hβ (sq_eq_zero_iff.mp hh')
  apply gaussianReal_real_pos_of_volume_pos (β^2) hv
  by_cases hj0 : j.val=0
  · have hj : j=0 := Fin.ext hj0
    simp only [hj,intervalBin_eq_zero hN he,Set.Iic_def,Real.volume_Iic]
    exact ENNReal.zero_lt_top
  · by_cases hjN : j.val=N
    · have hj : j=Fin.last N := Fin.ext hjN
      simp only [hj,intervalBin_eq_last hN he,Set.Ioi_def,Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    · have h1 : 0<j.val := Nat.pos_of_ne_zero hj0
      have h2 : j.val<N := by have := j.isLt; omega
      simp only [intervalBin_eq_middle he _ j h1 h2]
      change 0<volume (Ioc _ _)
      rw [Real.volume_Ioc,ENNReal.ofReal_pos]
      exact sub_pos.mpr (he (show (⟨j.val-1,by omega⟩ : Fin N)<⟨j.val,h2⟩ from by change j.val-1<j.val; omega))

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinEmpirical
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
  {μ : Measure ℝ} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  {N : ℕ} {e : Fin N → ℝ}

lemma binT_eq_sqrt {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (σ : Fin n → α) (d : α) : binT σ d=sqrt ((count σ d:ℝ)/(n:ℝ)) := by
  rw [binT,Fintype.card_fin,sqrt_div (Nat.cast_nonneg _)]

lemma intervalBin_roots_empirical (hN : 0<N) (he : StrictMono e)
    (hX : ExponentialEmpiricalConcentration ρ X μ) :
    ExponentialConvergence ρ (fun n ω => binT (fun i => intervalBin e (X n ω i)))
      (massRoot μ (intervalBin e)) := by
  apply ExponentialConvergence.pi_finite
  intro d
  have hh := (intervalBin_empirical hN he hX d).continuous_map continuous_sqrt.continuousAt
  simpa only [binT_eq_sqrt,massRoot,binMass] using hh

lemma intervalBin_binSize_rare (hN : 0<N) (he : StrictMono e)
    (hX : ExponentialEmpiricalConcentration ρ X μ)
    (hm : ∀ d, 0<binMass μ (intervalBin e) d) :
    ExponentiallyRare ρ (fun n => {ω | ∃ d, count (fun i => intervalBin e (X n ω i)) d<2}) := by
  have hd (d : Fin (N+1)) : ExponentiallyRare ρ
      (fun n => {ω | count (fun i => intervalBin e (X n ω i)) d<2}) := by
    let p := binMass μ (intervalBin e) d
    have hp : 0<p := hm d
    apply ((intervalBin_empirical hN he hX d) (p/2) (by positivity)).mono
    have hlarge := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (4/p))
    filter_upwards [hlarge,eventually_gt_atTop 0] with n hn hn0
    intro ω hω
    have hc : (count (fun i => intervalBin e (X n ω i)) d:ℝ)≤1 := by
      exact_mod_cast (show count (fun i => intervalBin e (X n ω i)) d≤1 from by simpa using hω)
    have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn0
    change p/2≤|(count (fun i => intervalBin e (X n ω i)) d:ℝ)/(n:ℝ)-p|
    have hpn := (div_le_iff₀ hp).mp hn
    have hu : (count (fun i => intervalBin e (X n ω i)) d:ℝ)/(n:ℝ)≤p/2 := by
      apply (div_le_iff₀ hnR).mpr
      nlinarith only [hc,hpn]
    have hh := neg_le_abs ((count (fun i => intervalBin e (X n ω i)) d:ℝ)/(n:ℝ)-p)
    linarith only [hu,hh]
  apply (ExponentiallyRare.iUnion_finite hd).mono
  exact .of_forall (fun _ _ ⟨d,hd⟩ => Set.mem_iUnion.mpr ⟨d,hd⟩)

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarReduction
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma abs_v_sum_le (h t : ℝ) : |v h+v t| ≤ 2 := by
  rw [abs_of_nonneg (add_nonneg (v_pos h).le (v_pos t).le)]
  linarith [v_le_one h,v_le_one t]

lemma v_sum_sq_le (h t : ℝ) : (v h+v t)^2 ≤ 4 := by
  nlinarith [abs_v_sum_le h t,neg_le_abs (v h+v t),le_abs_self (v h+v t)]

lemma abs_diagonal_kernel_le (h t : ℝ) : |v t^2/(w h+w t)| ≤ 2 := by
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (add_pos (w_pos h) (w_pos t)).le)]
  apply (div_le_iff₀ (add_pos (w_pos h) (w_pos t))).mpr
  have ht : v t ≤ 2*w t := by rw [v_factor]; nlinarith [w_pos t,(m_bounds t).2]
  have hv : v t^2 ≤ v t := by nlinarith [v_pos t,v_le_one t]
  linarith [w_pos h]

lemma continuous_diagonal_kernel :
    Continuous (fun z : ℝ×ℝ => v z.2^2/(w z.1+w z.2)) := by
  apply ((continuous_v.comp continuous_snd).pow 2).div
    ((continuous_w.comp continuous_fst).add (continuous_w.comp continuous_snd))
  intro z
  exact (add_pos (w_pos z.1) (w_pos z.2)).ne'

section Probability
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

variable {μ}

lemma integral_centered_sq {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ∫ h, (f h-(∫ t, f t ∂μ))^2 ∂μ =
      (∫ h, f h^2 ∂μ)-(∫ h, f h ∂μ)^2 := by
  have hI := hf.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hid (h : ℝ) : (f h-(∫ t, f t ∂μ))^2 =
      f h^2-(2*(∫ t, f t ∂μ))*f h+(∫ t, f t ∂μ)^2 := by ring
  simp_rw [hid]
  have hsub : Integrable (fun h => f h^2-(2*(∫ t, f t ∂μ))*f h) μ :=
    hf.integrable_sq.sub (hI.const_mul _)
  rw [integral_add hsub (integrable_const _),
    integral_sub hf.integrable_sq (hI.const_mul _),integral_const_mul,integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  ring

end Probability

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarHilbert
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Real
namespace SKRatio.Scalar

section Measure
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma l2Norm_nonneg (f : α → ℝ) : 0 ≤ l2Norm μ f := sqrt_nonneg _
lemma l2Norm_sq (f : α → ℝ) : l2Norm μ f^2 = ∫ x, f x^2 ∂μ :=
  sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x)))

lemma abs_integral_mul_le {f u : α → ℝ} (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) :
    |∫ x, f x*u x ∂μ| ≤ l2Norm μ f*l2Norm μ u := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using hu)
  simp only [norm_eq_abs,Real.rpow_two,sq_abs,←sqrt_eq_rpow] at h
  have h' : |∫ x, f x*u x ∂μ| ≤ ∫ x, |f x| * |u x| ∂μ := by
    simpa only [abs_mul] using (abs_integral_le_integral_abs (f := fun x => f x*u x) (μ := μ))
  exact h'.trans h

lemma integral_square_add {u z : α → ℝ}
    (hu : MemLp u 2 μ) (hz : MemLp z 2 μ) (s t : ℝ) :
    ∫ x, (s*u x+t*z x)^2 ∂μ =
      s^2*(∫ x, u x^2 ∂μ)+(2*s*t)*(∫ x, u x*z x ∂μ)+t^2*(∫ x, z x^2 ∂μ) := by
  have hpair : Integrable (fun x => u x*z x) μ := hu.integrable_mul hz
  have hsum : Integrable (fun x => s^2*u x^2+(2*s*t)*(u x*z x)) μ :=
    (hu.integrable_sq.const_mul _).add (hpair.const_mul _)
  have he (x : α) : (s*u x+t*z x)^2 = s^2*u x^2+(2*s*t)*(u x*z x)+t^2*z x^2 := by ring
  simp_rw [he]
  rw [integral_add hsum (hz.integrable_sq.const_mul _),
    integral_add (hu.integrable_sq.const_mul _) (hpair.const_mul _),
    integral_const_mul,integral_const_mul,integral_const_mul]

end Measure

end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FieldL2
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma memLp_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ (fun x => by
    simpa only [norm_eq_abs] using hC x))

lemma l2Norm_le_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hfC : ∀ x, |f x| ≤ C) : l2Norm μ f ≤ C := by
  have hi := integral_mono (memLp_bounded hf hfC (μ := μ)).integrable_sq
    (integrable_const (C^2)) (fun x => show f x^2 ≤ C^2 by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hfC x))
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hi
  have hs := l2Norm_sq (μ := μ) f
  nlinarith only [hi,hs,l2Norm_nonneg (μ := μ) f,hC]

omit [IsProbabilityMeasure μ] in
lemma memLp_field_mul {f u : ℝ → ℝ} (hf : MemLp f 2 μ)
    (hu : Measurable u) {C : ℝ} (hC : ∀ x, |u x| ≤ C) :
    MemLp (fun x => f x*u x) 2 μ := by
  apply hf.of_le_mul (hf.aestronglyMeasurable.mul hu.aestronglyMeasurable) (c := C)
  exact ae_of_all _ (fun x => by
    change |f x*u x| ≤ C*|f x|
    rw [abs_mul]
    nlinarith only [mul_le_mul_of_nonneg_left (hC x) (abs_nonneg (f x))])

omit [IsProbabilityMeasure μ] in
lemma l2Norm_field_mul {f u : ℝ → ℝ} (hf : MemLp f 2 μ)
    (hu : Measurable u) {C : ℝ} (hC : 0 ≤ C) (huC : ∀ x, |u x| ≤ C) :
    l2Norm μ (fun x => f x*u x) ≤ C*l2Norm μ f := by
  have hi := integral_mono (memLp_field_mul hf hu huC).integrable_sq
    (hf.integrable_sq.const_mul (C^2)) (fun x => show (f x*u x)^2 ≤ C^2*f x^2 by
      have hh : u x^2 ≤ C^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (huC x)
      simpa only [mul_pow,mul_comm] using mul_le_mul_of_nonneg_left hh (sq_nonneg (f x)))
  rw [integral_const_mul,←l2Norm_sq,←l2Norm_sq] at hi
  have hn := l2Norm_nonneg (μ := μ) (fun x => f x*u x)
  have hn' : 0 ≤ C*l2Norm μ f := mul_nonneg hC (l2Norm_nonneg f)
  nlinarith only [hi,hn,hn']

omit [IsProbabilityMeasure μ] in
lemma norm_components {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (he : (∫ x, b x^2+r x^2 ∂μ)=1) : l2Norm μ b ≤ 1 ∧ l2Norm μ r ≤ 1 := by
  rw [integral_add hb.integrable_sq hr.integrable_sq,←l2Norm_sq,←l2Norm_sq] at he
  constructor <;> nlinarith only [he,sq_nonneg (l2Norm μ b),sq_nonneg (l2Norm μ r)]

lemma integral_abs_le_l2 {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ l2Norm μ f := by
  have hh : |∫ x, |f x| * (1:ℝ) ∂μ| ≤ l2Norm μ (fun x => |f x|)*l2Norm μ (fun _ => (1:ℝ)) :=
    abs_integral_mul_le hf.abs (memLp_const (1:ℝ) (μ := μ) (p := 2))
  have he : l2Norm μ (fun x => |f x|)=l2Norm μ f := by simp only [l2Norm,sq_abs]
  have ho : l2Norm μ (fun _ : ℝ => (1:ℝ))=1 := by
    simp only [l2Norm,one_pow,integral_const,probReal_univ,smul_eq_mul,one_mul,sqrt_one]
  simp only [mul_one,he,ho] at hh
  rw [abs_of_nonneg (integral_nonneg (fun x : ℝ => abs_nonneg (f x)))] at hh
  exact hh

omit [IsProbabilityMeasure μ] in
lemma field_pair_abs_le {b f : ℝ → ℝ} (hb : MemLp b 2 μ) (hf : MemLp f 2 μ)
    (hb1 : l2Norm μ b ≤ 1) : |∫ x, b x*f x ∂μ| ≤ l2Norm μ f :=
  (abs_integral_mul_le hb hf).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb1 (l2Norm_nonneg f))

lemma integral_abs_bound {f : ℝ → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : |∫ x, f x ∂μ| ≤ C := by
  apply abs_integral_le_integral_abs.trans
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
    integral_mono hf.abs (integrable_const C) hC

lemma bounded_pair_error {b f g : ℝ → ℝ} (hb : MemLp b 2 μ)
    (hb1 : l2Norm μ b ≤ 1) (hf : Measurable f) (hg : Measurable g)
    {C D a : ℝ} (hfC : ∀ x, |f x| ≤ C) (hgD : ∀ x, |g x| ≤ D)
    (ha : 0 ≤ a) (he : ∀ x, |f x-g x| ≤ a) :
    |(∫ x, b x*f x ∂μ)-(∫ x, b x*g x ∂μ)| ≤ a := by
  have hfi : Integrable (fun x => b x*f x) μ := hb.integrable_mul (memLp_bounded hf hfC)
  have hgi : Integrable (fun x => b x*g x) μ := hb.integrable_mul (memLp_bounded hg hgD)
  rw [←integral_sub hfi hgi]
  simp_rw [←mul_sub]
  exact (field_pair_abs_le hb ((memLp_bounded hf hfC).sub (memLp_bounded hg hgD)) hb1).trans
    (l2Norm_le_bounded (hf.sub hg) ha he)

omit [IsProbabilityMeasure μ] in
lemma energy_error {b r f g : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (he : (∫ x, b x^2+r x^2 ∂μ)=1)
    (hf : Measurable f) (hg : Measurable g) {C D a : ℝ}
    (hfC : ∀ x, |f x| ≤ C) (hgD : ∀ x, |g x| ≤ D) (hfg : ∀ x, |f x-g x| ≤ a) :
    |(∫ x, f x*(b x^2+r x^2) ∂μ)-(∫ x, g x*(b x^2+r x^2) ∂μ)| ≤ a := by
  have ih : Integrable (fun x => b x^2+r x^2) μ := hb.integrable_sq.add hr.integrable_sq
  have ihf := ih.bdd_mul hf.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [norm_eq_abs] using hfC x))
  have ihg := ih.bdd_mul hg.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [norm_eq_abs] using hgD x))
  rw [←integral_sub ihf ihg]
  apply abs_integral_le_integral_abs.trans
  have hi := integral_mono (ihf.sub ihg).abs (ih.const_mul a) (fun x => by
    simp only [Pi.sub_apply,←sub_mul,abs_mul,abs_of_nonneg (add_nonneg (sq_nonneg (b x)) (sq_nonneg (r x)))]
    exact mul_le_mul_of_nonneg_right (hfg x) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  simpa only [integral_const_mul,Pi.add_apply,Pi.sub_apply,he,mul_one] using hi

lemma sqrt_difference {s t e : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (he : |s-t| ≤ e) : |sqrt s-sqrt t| ≤ sqrt e := by
  have he0 := (abs_nonneg (s-t)).trans he
  have hs2 := sq_sqrt hs
  have ht2 := sq_sqrt ht
  have he2 := sq_sqrt he0
  have habs : (sqrt s-sqrt t)^2 ≤ e := by
    rcases le_total s t with hst|hts
    · rw [abs_of_nonpos (sub_nonpos.mpr hst)] at he
      have hh := sqrt_le_sqrt hst
      nlinarith only [he,hh,hs2,ht2,mul_nonneg (sqrt_nonneg s) (sub_nonneg.mpr hh)]
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)] at he
      have hh := sqrt_le_sqrt hts
      nlinarith only [he,hh,hs2,ht2,mul_nonneg (sqrt_nonneg t) (sub_nonneg.mpr hh)]
  exact (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg e)).mp (by simpa only [sq_abs,he2] using habs)

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FieldRadical
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma fieldRadicand_nonneg (H b r : ℝ → ℝ) (x : ℝ) :
    0 ≤ fieldRadicand μ H b r x :=
  add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))

omit [IsProbabilityMeasure μ] in
lemma memLp_sum_v_field {b H : ℝ → ℝ} (hb : MemLp b 2 μ) (hH : Measurable H)
    (x : ℝ) : MemLp (fun y => (v (H x)+v (H y))*b y) 2 μ := by
  have hh := memLp_field_mul hb (u := fun y => v (H x)+v (H y))
    (measurable_const.add (continuous_v.measurable.comp hH)) (fun y => abs_v_sum_le (H x) (H y))
  simpa only [mul_comm] using hh

omit [IsProbabilityMeasure μ] in
lemma field_energy_integrable {b r H : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hH : Measurable H) (x : ℝ) :
    Integrable (fun y => (v (H x)+v (H y))^2*(b y^2+r y^2)) μ := by
  have he (y : ℝ) : (v (H x)+v (H y))^2*(b y^2+r y^2)=
      ((v (H x)+v (H y))*b y)^2+((v (H x)+v (H y))*r y)^2 := by ring
  simp_rw [he]
  exact (memLp_sum_v_field hb hH x).integrable_sq.add (memLp_sum_v_field hr hH x).integrable_sq

lemma fieldRadicand_expansion {b r H : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hH : Measurable H) (x : ℝ) : fieldRadicand μ H b r x =
      (∫ y, (v (H x)+v (H y))^2*(b y^2+r y^2) ∂μ)-
        (∫ y, (v (H x)+v (H y))*b y ∂μ)^2 := by
  rw [fieldRadicand,integral_centered_sq (memLp_sum_v_field hb hH x)]
  have he (y : ℝ) : (v (H x)+v (H y))^2*(b y^2+r y^2)=
      ((v (H x)+v (H y))*b y)^2+((v (H x)+v (H y))*r y)^2 := by ring
  simp_rw [he]
  rw [integral_add (memLp_sum_v_field hb hH x).integrable_sq
    (memLp_sum_v_field hr hH x).integrable_sq]
  ring

lemma fieldRadicand_le {b r H : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hH : Measurable H) (he : (∫ x, b x^2+r x^2 ∂μ)=1) (x : ℝ) :
    fieldRadicand μ H b r x ≤ 4 := by
  rw [fieldRadicand_expansion hb hr hH]
  have ih : Integrable (fun y => b y^2+r y^2) μ := hb.integrable_sq.add hr.integrable_sq
  have hi := integral_mono (field_energy_integrable hb hr hH x) (ih.const_mul (4:ℝ))
    (fun y => mul_le_mul_of_nonneg_right (v_sum_sq_le (H x) (H y))
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  rw [integral_const_mul,he,mul_one] at hi
  nlinarith only [hi,sq_nonneg (∫ y, (v (H x)+v (H y))*b y ∂μ)]

lemma measurable_fieldRadicand {b r H : ℝ → ℝ} (hb : Measurable b) (hr : Measurable r)
    (hH : Measurable H) : Measurable (fieldRadicand μ H b r) := by
  have hv := continuous_v.measurable.comp hH
  have hm : Measurable (fun x => ∫ t, (v (H x)+v (H t))*b t ∂μ) :=
    (((hv.comp measurable_fst).add (hv.comp measurable_snd)).mul
      (hb.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable
  have h1 : Measurable (fun x => ∫ y, ((v (H x)+v (H y))*r y)^2 ∂μ) :=
    ((((hv.comp measurable_fst).add (hv.comp measurable_snd)).mul
      (hr.comp measurable_snd)).pow_const 2).stronglyMeasurable.integral_prod_right.measurable
  have h2 : Measurable (fun x => ∫ y,
      ((v (H x)+v (H y))*b y-(∫ t, (v (H x)+v (H t))*b t ∂μ))^2 ∂μ) :=
    (((((hv.comp measurable_fst).add (hv.comp measurable_snd)).mul
      (hb.comp measurable_snd)).sub (hm.comp measurable_fst)).pow_const 2).stronglyMeasurable.integral_prod_right.measurable
  exact h1.add h2

lemma abs_square_sub_le {x y C e : ℝ} (hC : 0 ≤ C) (hx : |x| ≤ C) (hy : |y| ≤ C)
    (he : |x-y| ≤ e) : |x^2-y^2| ≤ 2*C*e := by
  rw [show x^2-y^2=(x-y)*(x+y) by ring,abs_mul]
  have hsum : |x+y| ≤ 2*C := (abs_add_le _ _).trans (by linarith)
  nlinarith only [mul_le_mul hsum he (abs_nonneg _) (mul_nonneg (by norm_num) hC)]

lemma fieldRadicand_error {b r H H' : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hH : Measurable H) (hH' : Measurable H')
    (he : (∫ x, b x^2+r x^2 ∂μ)=1) {a : ℝ} (ha : 0 ≤ a)
    (hv : ∀ x, |v (H x)-v (H' x)| ≤ a) (x : ℝ) :
    |fieldRadicand μ H b r x-fieldRadicand μ H' b r x| ≤ 16*a := by
  let f := fun y => v (H x)+v (H y)
  let g := fun y => v (H' x)+v (H' y)
  have hf : Measurable f := measurable_const.add (continuous_v.measurable.comp hH)
  have hg : Measurable g := measurable_const.add (continuous_v.measurable.comp hH')
  have hf2 (y : ℝ) : |f y| ≤ 2 := abs_v_sum_le _ _
  have hg2 (y : ℝ) : |g y| ≤ 2 := abs_v_sum_le _ _
  have hfg (y : ℝ) : |f y-g y| ≤ 2*a := by
    have heq : f y-g y=(v (H x)-v (H' x))+(v (H y)-v (H' y)) := by dsimp [f,g]; ring
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith [hv x,hv y])
  have hf_sq (y : ℝ) : |f y^2| ≤ 4 := by rw [abs_of_nonneg (sq_nonneg _)]; exact v_sum_sq_le _ _
  have hg_sq (y : ℝ) : |g y^2| ≤ 4 := by rw [abs_of_nonneg (sq_nonneg _)]; exact v_sum_sq_le _ _
  have he_sq (y : ℝ) : |f y^2-g y^2| ≤ 8*a := by
    have hh := abs_square_sub_le (by norm_num : (0:ℝ) ≤ 2) (hf2 y) (hg2 y) (hfg y)
    nlinarith only [hh]
  have he' := energy_error hb hr he (hf.pow_const 2) (hg.pow_const 2) hf_sq hg_sq he_sq
  have hb1 := (norm_components hb hr he).1
  have hp := bounded_pair_error hb hb1 hf hg hf2 hg2 (show 0 ≤ 2*a by positivity) hfg
  have hpf : |∫ y, b y*f y ∂μ| ≤ 2 := (field_pair_abs_le hb (memLp_bounded hf hf2) hb1).trans
    (l2Norm_le_bounded hf (by norm_num) hf2)
  have hpg : |∫ y, b y*g y ∂μ| ≤ 2 := (field_pair_abs_le hb (memLp_bounded hg hg2) hb1).trans
    (l2Norm_le_bounded hg (by norm_num) hg2)
  have hps := abs_square_sub_le (by norm_num : (0:ℝ) ≤ 2) hpf hpg hp
  rw [fieldRadicand_expansion hb hr hH,fieldRadicand_expansion hb hr hH']
  change |(∫ y, f y^2*(b y^2+r y^2) ∂μ)-(∫ y, f y*b y ∂μ)^2-
    ((∫ y, g y^2*(b y^2+r y^2) ∂μ)-(∫ y, g y*b y ∂μ)^2)| ≤ _
  simp_rw [mul_comm (f _) (b _),mul_comm (g _) (b _)]
  have heq : (∫ y, f y^2*(b y^2+r y^2) ∂μ)-(∫ y, b y*f y ∂μ)^2-
      ((∫ y, g y^2*(b y^2+r y^2) ∂μ)-(∫ y, b y*g y ∂μ)^2)=
      ((∫ y, f y^2*(b y^2+r y^2) ∂μ)-(∫ y, g y^2*(b y^2+r y^2) ∂μ))-
      ((∫ y, b y*f y ∂μ)^2-(∫ y, b y*g y ∂μ)^2) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith only [he',hps])

lemma sqrt_fieldRadicand_error {b r H H' : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hH : Measurable H) (hH' : Measurable H')
    (he : (∫ x, b x^2+r x^2 ∂μ)=1) {a : ℝ} (ha : 0 ≤ a)
    (hv : ∀ x, |v (H x)-v (H' x)| ≤ a) (x : ℝ) :
    |sqrt (fieldRadicand μ H b r x)-sqrt (fieldRadicand μ H' b r x)| ≤ 4*sqrt a := by
  have hh := sqrt_difference (fieldRadicand_nonneg H b r x) (fieldRadicand_nonneg H' b r x)
    (fieldRadicand_error hb hr hH hH' he ha hv x)
  simpa only [sqrt_mul (by norm_num : (0:ℝ) ≤ 16),show sqrt (16:ℝ)=4 by norm_num] using hh

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarTemperature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real Set
namespace SKRatio.Scalar

lemma variance_ne_zero {β : ℝ} (hβ : 0 < β) : variance β ≠ 0 := by
  intro hz
  have he := congrArg (fun t : ℝ≥0 => (t:ℝ)) hz
  simp only [variance_coe,NNReal.coe_zero] at he
  nlinarith

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarVariance
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

section Norm
variable {μ : Measure ℝ}

lemma l2Norm_add {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    l2Norm μ (fun x => f x+g x) ≤ l2Norm μ f+l2Norm μ g := by
  have he := integral_square_add hf hg 1 1
  simp only [one_mul,one_pow,mul_one] at he
  have hcs := (le_abs_self _).trans (abs_integral_mul_le hf hg)
  apply (sq_le_sq₀ (l2Norm_nonneg _) (add_nonneg (l2Norm_nonneg _) (l2Norm_nonneg _))).mp
  rw [l2Norm_sq,he]
  nlinarith only [hcs,l2Norm_sq (μ := μ) f,l2Norm_sq (μ := μ) g]

end Norm

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FieldFunctional
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma fieldForm_id (β : ℝ) (b r : ℝ → ℝ) :
    fieldForm (fieldLaw β) β id b r=variational β b r := rfl

lemma measurable_fieldDiagonal {H : ℝ → ℝ} (hH : Measurable H) :
    Measurable (fieldDiagonal μ H) := by
  have hm : StronglyMeasurable (fun z : ℝ×ℝ => v (H z.2)^2/(w (H z.1)+w (H z.2))) :=
    (continuous_diagonal_kernel.measurable.comp
      ((hH.comp measurable_fst).prodMk (hH.comp measurable_snd))).stronglyMeasurable
  exact hm.integral_prod_right.measurable

lemma fieldDiagonal_integrable {H : ℝ → ℝ} (hH : Measurable H) (x : ℝ) :
    Integrable (fun y => v (H y)^2/(w (H x)+w (H y))) μ := by
  apply (integrable_const (2:ℝ)).mono'
    (continuous_diagonal_kernel.measurable.comp (measurable_const.prodMk hH)).aestronglyMeasurable
  exact ae_of_all _ (fun y => by simpa only [norm_eq_abs,Function.comp_apply] using abs_diagonal_kernel_le (H x) (H y))

lemma abs_fieldDiagonal_le {H : ℝ → ℝ} (hH : Measurable H) (x : ℝ) :
    |fieldDiagonal μ H x| ≤ 2 :=
  integral_abs_bound (fieldDiagonal_integrable hH x)
    (fun point => abs_diagonal_kernel_le (H x) (H point))

lemma fieldDiagonal_error {H H' : ℝ → ℝ} (hH : Measurable H) (hH' : Measurable H')
    {a : ℝ} (hf : ∀ x y, |v (H y)^2/(w (H x)+w (H y))-
      v (H' y)^2/(w (H' x)+w (H' y))| ≤ a) (x : ℝ) :
    |fieldDiagonal μ H x-fieldDiagonal μ H' x| ≤ a := by
  unfold fieldDiagonal
  rw [←integral_sub (fieldDiagonal_integrable hH x) (fieldDiagonal_integrable hH' x)]
  exact integral_abs_bound ((fieldDiagonal_integrable hH x).sub (fieldDiagonal_integrable hH' x)) (hf x)

lemma fieldKernel_integrable {H b : ℝ → ℝ} (hH : Measurable H) (hb : MemLp b 2 μ) :
    Integrable (fun z : ℝ×ℝ => b z.1*kernel (H z.1) (H z.2)*b z.2) (μ.prod μ) := by
  have hI := hb.integrable (by norm_num : (1:ENNReal) ≤ 2)
  apply (hI.norm.mul_prod hI.norm).mono'
    ((hb.aestronglyMeasurable.comp_fst.mul
      (continuous_kernel.measurable.comp ((hH.comp measurable_fst).prodMk
        (hH.comp measurable_snd))).aestronglyMeasurable).mul hb.aestronglyMeasurable.comp_snd)
  exact ae_of_all _ (fun z => by
    change |b z.1*kernel (H z.1) (H z.2)*b z.2| ≤ |b z.1| * |b z.2|
    simp only [abs_mul]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (abs_kernel_le_one (H z.1) (H z.2)) (abs_nonneg (b z.1))) (abs_nonneg (b z.2))
    simpa only [mul_one] using hh)

lemma fieldKernel_error {H H' b : ℝ → ℝ} (hH : Measurable H) (hH' : Measurable H')
    (hb : MemLp b 2 μ) (hb1 : l2Norm μ b ≤ 1) {a : ℝ} (ha : 0 ≤ a)
    (hk : ∀ x y, |kernel (H x) (H y)-kernel (H' x) (H' y)| ≤ a) :
    |(∫ z : ℝ×ℝ, b z.1*kernel (H z.1) (H z.2)*b z.2 ∂μ.prod μ)-
      (∫ z : ℝ×ℝ, b z.1*kernel (H' z.1) (H' z.2)*b z.2 ∂μ.prod μ)| ≤ a := by
  have hI := hb.integrable (by norm_num : (1:ENNReal) ≤ 2)
  rw [←integral_sub (fieldKernel_integrable hH hb) (fieldKernel_integrable hH' hb)]
  apply abs_integral_le_integral_abs.trans
  have hi := integral_mono ((fieldKernel_integrable hH hb).sub (fieldKernel_integrable hH' hb)).abs
    ((hI.abs.mul_prod hI.abs).const_mul a) (fun z : ℝ×ℝ => by
      change |b z.1*kernel (H z.1) (H z.2)*b z.2-b z.1*kernel (H' z.1) (H' z.2)*b z.2| ≤ a*(|b z.1| * |b z.2|)
      rw [show b z.1*kernel (H z.1) (H z.2)*b z.2-b z.1*kernel (H' z.1) (H' z.2)*b z.2=
        (kernel (H z.1) (H z.2)-kernel (H' z.1) (H' z.2))*(b z.1*b z.2) by ring,abs_mul,abs_mul]
      exact mul_le_mul_of_nonneg_right (hk z.1 z.2) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  rw [integral_const_mul,integral_prod_mul (fun x => |b x|) (fun x => |b x|)] at hi
  apply hi.trans
  have hn : 0 ≤ ∫ x, |b x| ∂μ := integral_nonneg (fun x => abs_nonneg (b x))
  have hh := (integral_abs_le_l2 hb).trans hb1
  nlinarith only [mul_nonneg ha (sub_nonneg.mpr hh),
    mul_nonneg (mul_nonneg ha hn) (sub_nonneg.mpr hh)]

omit [IsProbabilityMeasure μ] in
lemma field_pair_difference {b f g : ℝ → ℝ} (hb : MemLp b 2 μ)
    (hb1 : l2Norm μ b ≤ 1) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |(∫ x, b x*f x ∂μ)-(∫ x, b x*g x ∂μ)| ≤ l2Norm μ (fun x => f x-g x) := by
  have hfi : Integrable (fun x => b x*f x) μ := hb.integrable_mul hf
  have hgi : Integrable (fun x => b x*g x) μ := hb.integrable_mul hg
  rw [←integral_sub hfi hgi]
  simp_rw [←mul_sub]
  exact field_pair_abs_le hb (hf.sub hg) hb1

lemma field_pair_v_abs {b H : ℝ → ℝ} (hb : MemLp b 2 μ) (hb1 : l2Norm μ b ≤ 1)
    (hH : Measurable H) : |∫ x, b x*v (H x) ∂μ| ≤ 1 :=
  (field_pair_abs_le hb (memLp_bounded (continuous_v.measurable.comp hH)
    (fun x => v_abs_le_one (H x))) hb1).trans
    (l2Norm_le_bounded (continuous_v.measurable.comp hH) (by norm_num) (fun x => v_abs_le_one (H x)))

lemma mean_abs_le_one {b : ℝ → ℝ} (hb : MemLp b 2 μ) (hb1 : l2Norm μ b ≤ 1) :
    |∫ x, b x ∂μ| ≤ 1 := (abs_integral_le_integral_abs.trans (integral_abs_le_l2 hb)).trans hb1

omit [IsProbabilityMeasure μ] in
lemma memLp_Hv {H : ℝ → ℝ} (hH : Measurable H) (hH2 : MemLp H 2 μ) :
    MemLp (fun x => H x*v (H x)) 2 μ :=
  memLp_field_mul hH2 (continuous_v.measurable.comp hH) (fun point => v_abs_le_one (H point))

omit [IsProbabilityMeasure μ] in
lemma Hv_error {H H' : ℝ → ℝ} (hH : Measurable H) (hH' : Measurable H')
    (hH2 : MemLp H 2 μ) (hH2' : MemLp H' 2 μ)
    {a d T : ℝ} (ha : 0 ≤ a) (he : l2Norm μ (fun x => H x-H' x) ≤ d)
    (hsize : l2Norm μ H' ≤ T) (hv : ∀ x, |v (H x)-v (H' x)| ≤ a) :
    l2Norm μ (fun x => H x*v (H x)-H' x*v (H' x)) ≤ d+T*a := by
  have heq : (fun x => H x*v (H x)-H' x*v (H' x))=
      (fun x => (H x-H' x)*v (H x)+H' x*(v (H x)-v (H' x))) := by funext x; ring
  rw [heq]
  have h1 := l2Norm_field_mul (hH2.sub hH2') (continuous_v.measurable.comp hH)
    (by norm_num : (0:ℝ) ≤ 1) (fun x => v_abs_le_one _)
  have h2 := l2Norm_field_mul hH2'
    ((continuous_v.measurable.comp hH).sub (continuous_v.measurable.comp hH')) ha hv
  have ht := l2Norm_add (memLp_field_mul (hH2.sub hH2')
    (continuous_v.measurable.comp hH) (fun x => v_abs_le_one _))
    (memLp_field_mul hH2' ((continuous_v.measurable.comp hH).sub (continuous_v.measurable.comp hH')) hv)
  have h3 := mul_le_mul_of_nonneg_left hsize ha
  simp only [Pi.sub_apply,Pi.sub_def,Function.comp_apply] at h1 h2 ht
  nlinarith only [h1,h2,ht,h3,he]

lemma field_radical_pair_error {b r H H' : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hbm : Measurable b) (hrm : Measurable r) (hH : Measurable H) (hH' : Measurable H')
    (he : (∫ x, b x^2+r x^2 ∂μ)=1) {a : ℝ} (ha : 0 ≤ a)
    (hv : ∀ x, |v (H x)-v (H' x)| ≤ a) :
    |(∫ x, r x*sqrt (fieldRadicand μ H b r x) ∂μ)-
      (∫ x, r x*sqrt (fieldRadicand μ H' b r x) ∂μ)| ≤ 4*sqrt a := by
  apply bounded_pair_error hr (norm_components hb hr he).2
    ((measurable_fieldRadicand hbm hrm hH).sqrt) ((measurable_fieldRadicand hbm hrm hH').sqrt)
    (C := 2) (D := 2) _ _ (by positivity) (sqrt_fieldRadicand_error hb hr hH hH' he ha hv)
  · intro x
    rw [abs_of_nonneg (sqrt_nonneg _)]
    exact (sqrt_le_iff).mpr ⟨by norm_num,by norm_num only [show (2:ℝ)^2=4 by norm_num]; exact fieldRadicand_le hb hr hH he x⟩
  · intro x
    rw [abs_of_nonneg (sqrt_nonneg _)]
    exact (sqrt_le_iff).mpr ⟨by norm_num,by norm_num only [show (2:ℝ)^2=4 by norm_num]; exact fieldRadicand_le hb hr hH' he x⟩

theorem fieldForm_error {b r H H' : ℝ → ℝ} (β : ℝ) (hβ : 0 ≤ β)
    (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) (hbm : Measurable b) (hrm : Measurable r)
    (hH : Measurable H) (hH' : Measurable H') (hH2 : MemLp H 2 μ) (hH2' : MemLp H' 2 μ)
    (he : (∫ x, b x^2+r x^2 ∂μ)=1) {a d T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (herr : l2Norm μ (fun x => H x-H' x) ≤ d) (hsize : l2Norm μ H' ≤ T)
    (hv : ∀ x, |v (H x)-v (H' x)| ≤ a)
    (hmv : ∀ x, |m (H x)*v (H x)-m (H' x)*v (H' x)| ≤ a)
    (hf : ∀ x y, |v (H y)^2/(w (H x)+w (H y))-
      v (H' y)^2/(w (H' x)+w (H' y))| ≤ a)
    (hk : ∀ x y, |kernel (H x) (H y)-kernel (H' x) (H' y)| ≤ a) :
    |fieldForm μ β H b r-fieldForm μ β H' b r| ≤
      2*d+2*T*a+5*β^2*a+4*β*sqrt a := by
  have hb1 := (norm_components hb hr he).1
  have hV := bounded_pair_error hb hb1 (continuous_v.measurable.comp hH)
    (continuous_v.measurable.comp hH') (fun x => v_abs_le_one _) (fun x => v_abs_le_one _) ha hv
  have hmabs (x : ℝ) : |m x*v x| ≤ 1 := by
    have hm : |m x| ≤ 1 := abs_le.mpr ⟨(m_bounds x).1.le,(m_bounds x).2.le⟩
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul hm (v_abs_le_one x) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hMV := bounded_pair_error hb hb1
    ((continuous_m.mul continuous_v).measurable.comp hH)
    ((continuous_m.mul continuous_v).measurable.comp hH')
    (fun x => hmabs _) (fun x => hmabs _) ha hmv
  have hHv := (field_pair_difference hb hb1 (memLp_Hv hH hH2)
    (memLp_Hv hH' hH2')).trans (Hv_error hH hH' hH2 hH2' ha herr hsize hv)
  have h₁ := product_error (by norm_num : (0:ℝ) ≤ 1) hT (field_pair_v_abs hb hb1 hH)
    ((field_pair_abs_le hb hH2' hb1).trans hsize)
    ((field_pair_difference hb hb1 hH2 hH2').trans herr) hV
  have h₂ : |(∫ x, b x ∂μ)*(∫ x, b x*(H x*v (H x)) ∂μ)-
      (∫ x, b x ∂μ)*(∫ x, b x*(H' x*v (H' x)) ∂μ)| ≤ d+T*a := by
    rw [←mul_sub,abs_mul]
    exact (mul_le_mul (mean_abs_le_one hb hb1) hHv (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)
  have h₃ : |β^2*(∫ x, b x ∂μ)*((∫ x, b x*v (H x) ∂μ)-
      (∫ x, b x*v (H' x) ∂μ))| ≤ β^2*a := by
    rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg β)]
    exact mul_le_mul ((mul_le_mul_of_nonneg_left (mean_abs_le_one hb hb1) (sq_nonneg β)).trans_eq (mul_one _))
      hV (abs_nonneg _) (sq_nonneg β)
  have h₄ : |2*β^2*(∫ x, b x ∂μ)*((∫ x, b x*(m (H x)*v (H x)) ∂μ)-
      (∫ x, b x*(m (H' x)*v (H' x)) ∂μ))| ≤ 2*β^2*a := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*β^2)]
    exact mul_le_mul ((mul_le_mul_of_nonneg_left (mean_abs_le_one hb hb1) (by positivity : 0 ≤ 2*β^2)).trans_eq (mul_one _))
      hMV (abs_nonneg _) (by positivity)
  have hd := energy_error hb hr he (measurable_fieldDiagonal (μ := μ) hH) (measurable_fieldDiagonal (μ := μ) hH')
    (abs_fieldDiagonal_le hH) (abs_fieldDiagonal_le hH') (fieldDiagonal_error hH hH' hf)
  have h₅ : |(∫ x, (β^2*fieldDiagonal μ H x)*(b x^2+r x^2) ∂μ)-
      (∫ x, (β^2*fieldDiagonal μ H' x)*(b x^2+r x^2) ∂μ)| ≤ β^2*a := by
    simp_rw [mul_assoc,integral_const_mul]
    rw [←mul_sub,abs_mul,abs_of_nonneg (sq_nonneg β)]
    exact mul_le_mul_of_nonneg_left hd (sq_nonneg β)
  have h₆ : |β^2*((∫ z : ℝ×ℝ, b z.1*kernel (H z.1) (H z.2)*b z.2 ∂μ.prod μ)-
      (∫ z : ℝ×ℝ, b z.1*kernel (H' z.1) (H' z.2)*b z.2 ∂μ.prod μ))| ≤ β^2*a := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg β)]
    exact mul_le_mul_of_nonneg_left (fieldKernel_error hH hH' hb hb1 ha hk) (sq_nonneg β)
  have h₇ : |β*((∫ x, r x*sqrt (fieldRadicand μ H b r x) ∂μ)-
      (∫ x, r x*sqrt (fieldRadicand μ H' b r x) ∂μ))| ≤ 4*β*sqrt a := by
    rw [abs_mul,abs_of_nonneg hβ]
    have hh := mul_le_mul_of_nonneg_left (field_radical_pair_error hb hr hbm hrm hH hH' he ha hv) hβ
    nlinarith only [hh]
  unfold fieldForm
  simp only [Function.comp_apply] at h₁
  have bounds₁ := abs_le.mp h₁
  have bounds₂ := abs_le.mp h₂
  have bounds₃ := abs_le.mp h₃
  have bounds₄ := abs_le.mp h₄
  have bounds₅ := abs_le.mp h₅
  have bounds₆ := abs_le.mp h₆
  have bounds₇ := abs_le.mp h₇
  exact abs_le.mpr ⟨by nlinarith only [bounds₁.1,bounds₂.1,bounds₃.2,bounds₄.1,bounds₅.1,bounds₆.1,bounds₇.1],
    by nlinarith only [bounds₁.2,bounds₂.2,bounds₃.1,bounds₄.2,bounds₅.2,bounds₆.2,bounds₇.2]⟩

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinPullback
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar
variable {α : Type*} [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma integral_finite_partition_prod {σ : ℝ → α} (hσ : Measurable σ) (F : α → α → ℝ) :
    (∫ z : ℝ×ℝ, F (σ z.1) (σ z.2) ∂μ.prod μ)=
      ∑ a, ∑ d, binMass μ σ a*binMass μ σ d*F a d := by
  have hi : Integrable (fun z : ℝ×ℝ => F (σ z.1) (σ z.2)) (μ.prod μ) :=
    (memLp_finite_comp ((hσ.comp measurable_fst).prodMk (hσ.comp measurable_snd))
      (fun ad : α×α => F ad.1 ad.2)).integrable (by norm_num : (1:ENNReal) ≤ 2)
  rw [integral_prod _ hi]
  simp_rw [integral_finite_partition (μ := μ) hσ (F (σ _))]
  rw [integral_finite_partition (μ := μ) hσ (fun a => ∑ d, binMass μ σ d*F a d)]
  simp only [Finset.mul_sum,mul_assoc]

lemma fieldRadicand_pullback {σ : ℝ → α} (hσ : Measurable σ)
    (hm : ∀ a, 0 < binMass μ σ a) (h : α → ℝ) (z : Parameters α) (x : ℝ) :
    fieldRadicand μ (fun x => h (σ x)) (pullback μ σ (paramB z))
      (pullback μ σ (paramR z)) x=
      finiteRadicalSq (massRoot μ σ) (fun a => v (h a)) z (σ x) := by
  rw [fieldRadicand_expansion (memLp_pullback hσ _) (memLp_pullback hσ _)
    (measurable_finite_comp hσ h)]
  rw [integral_pullback_energy hσ hm (paramB z) (paramR z)
    (fun a => (v (h (σ x))+v (h a))^2)]
  simp_rw [mul_comm (v (h (σ x))+v (h (σ _))) (pullback μ σ (paramB z) _)]
  rw [integral_pullback hσ hm (paramB z) (fun a => v (h (σ x))+v (h a))]
  rfl

lemma fieldDiagonal_partition {σ : ℝ → α} (hσ : Measurable σ) (h : α → ℝ) (x : ℝ) :
    fieldDiagonal μ (fun x => h (σ x)) x=
      ∑ d, massRoot μ σ d^2*(v (h d)^2/(w (h (σ x))+w (h d))) := by
  simp_rw [massRoot_sq]
  exact integral_finite_partition hσ (fun d => v (h d)^2/(w (h (σ x))+w (h d)))

lemma field_diagonal_pullback {σ : ℝ → α} (hσ : Measurable σ)
    (hm : ∀ a, 0 < binMass μ σ a) (β : ℝ) (h : α → ℝ) (z : Parameters α) :
    (∫ x, (β^2*fieldDiagonal μ (fun x => h (σ x)) x)*
      (pullback μ σ (paramB z) x^2+pullback μ σ (paramR z) x^2) ∂μ)=
      β^2*(∑ a, ∑ d, massRoot μ σ d^2*(v (h d)^2/(w (h a)+w (h d)))*
        ((paramB z a)^2+(paramR z a)^2)) := by
  simp_rw [fieldDiagonal_partition hσ h,mul_assoc,integral_const_mul]
  rw [integral_pullback_energy hσ hm (paramB z) (paramR z)
    (fun a => ∑ d, massRoot μ σ d^2*(v (h d)^2/(w (h a)+w (h d))))]
  simp only [Finset.sum_mul, mul_assoc]

lemma field_kernel_pullback {σ : ℝ → α} (hσ : Measurable σ)
    (hm : ∀ a, 0 < binMass μ σ a) (h : α → ℝ) (B : α → ℝ) :
    (∫ z : ℝ×ℝ, pullback μ σ B z.1*kernel (h (σ z.1)) (h (σ z.2))*
      pullback μ σ B z.2 ∂μ.prod μ)=
      ∑ a, ∑ d, massRoot μ σ a*B a*kernel (h a) (h d)*(massRoot μ σ d*B d) := by
  change (∫ z : ℝ×ℝ, (fun a d => (B a/massRoot μ σ a)*kernel (h a) (h d)*
    (B d/massRoot μ σ d)) (σ z.1) (σ z.2) ∂μ.prod μ)=_
  rw [integral_finite_partition_prod (μ := μ) hσ (fun a d => (B a/massRoot μ σ a)*kernel (h a) (h d)*(B d/massRoot μ σ d))]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  rw [←massRoot_sq σ a,←massRoot_sq σ d]
  field_simp [(massRoot_pos hm a).ne',(massRoot_pos hm d).ne']

theorem fieldForm_pullback {σ : ℝ → α} (hσ : Measurable σ)
    (hm : ∀ a, 0 < binMass μ σ a) (β : ℝ) (h : α → ℝ) (z : Parameters α) :
    fieldForm μ β (fun x => h (σ x)) (pullback μ σ (paramB z))
      (pullback μ σ (paramR z))=finiteV β (massRoot μ σ) h z := by
  unfold fieldForm
  rw [field_diagonal_pullback hσ hm β h z,field_kernel_pullback hσ hm]
  simp_rw [fieldRadicand_pullback hσ hm h z]
  rw [integral_pullback hσ hm (paramB z) h,
    integral_pullback hσ hm (paramB z) (fun a => v (h a)),
    integral_pullback hσ hm (paramB z) (fun a => h a*v (h a)),
    integral_pullback hσ hm (paramB z) (fun a => m (h a)*v (h a)),
    integral_pullback hσ hm (paramR z) (fun a => sqrt (finiteRadicalSq (massRoot μ σ) (fun a => v (h a)) z a))]
  have hmean : (∫ x, pullback μ σ (paramB z) x ∂μ)=moment (massRoot μ σ) (paramB z) (fun _ => 1) := by
    simpa only [mul_one] using integral_pullback hσ hm (paramB z) (fun _ => 1)
  rw [hmean]
  unfold finiteV finiteA finiteGaussian moment
  ring

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinWeightContinuity
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
lemma finiteV_weight_tolerance (β : ℝ) (h : α → ℝ) {a : ℝ} (ha : 0<a) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (t t' : WeightBox α) (z : Parameters α),
      (∀ d, |(t d:ℝ)-(t' d:ℝ)|<δ) →
      |finiteV β (fun d => t d) h z-finiteV β (fun d => t' d) h z|<a := by
  have hc : Continuous (fun q : WeightBox α × Parameters α =>
      finiteV β (fun d => q.1 d) h q.2) := by
    have ht : Continuous (fun q : WeightBox α × Parameters α =>
        fun d => (q.1 d : ℝ)) := continuous_pi (fun d =>
      continuous_subtype_val.comp ((continuous_apply d).comp continuous_fst))
    have hc' := (continuous_finiteV β h).comp (ht.prodMk
      (continuous_snd : Continuous (fun q : WeightBox α × Parameters α => q.2)))
    convert hc' using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) a ha
  refine ⟨δ,hδ,fun t t' z hh => ?_⟩
  apply hcont (a := (t,z)) (b := (t',z))
  simp only [Prod.dist_eq,dist_self,max_lt_iff]
  refine ⟨(dist_pi_lt_iff hδ).mpr ?_,hδ⟩
  intro d
  simpa only [Subtype.dist_eq,Real.dist_eq] using hh d

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma finiteV_population_tolerance {σ : Ω → α} (hσ : Measurable σ)
    (β : ℝ) (h : α → ℝ) {a : ℝ} (ha : 0<a) :
    ∃ δ : ℝ, 0<δ ∧ ∀ {n : ℕ} (_ : 0<n) (τ : Fin n → α),
      (∀ d, |binT τ d-massRoot μ σ d|<δ) → ∀ z : Parameters α,
      finiteV β (binT τ) h z < finiteV β (massRoot μ σ) h z+a := by
  obtain ⟨δ,hδ,ht⟩ := finiteV_weight_tolerance β h ha
  refine ⟨δ,hδ,?_⟩
  intro n hn τ hh z
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have he := ht (binBox τ) (populationBox (μ := μ) hσ) z hh
  have hle := (le_abs_self _).trans_lt he
  change finiteV β (binT τ) h z-finiteV β (massRoot μ σ) h z<a at hle
  linarith only [hle]

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_CompactTolerance
attribute [-instance] _root_.OAI.SKRatio.Bins.instCompactSpaceParameters _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar

lemma compact_coefficients_tolerance {a : ℝ} (ha : 0<a) :
    ∃ δ : ℝ, 0<δ ∧ ∀ H : ℝ → ℝ,
      (∀ x, dist (compactWeight x) (compactWeight (H x))<δ) →
      (∀ x, |v x-v (H x)|≤a) ∧
      (∀ x, |m x*v x-m (H x)*v (H x)|≤a) ∧
      (∀ x y, |v y^2/(w x+w y)-v (H y)^2/(w (H x)+w (H y))|≤a) ∧
      (∀ x y, |kernel x y-kernel (H x) (H y)|≤a) := by
  have cm : Continuous (fun u : FieldWeight => (1-(u:ℝ))*compactV u) :=
    (continuous_const.sub continuous_subtype_val).mul continuous_compactV
  obtain ⟨δv,hδv,hv⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuous_compactV) a ha
  obtain ⟨δm,hδm,hm⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous cm) a ha
  obtain ⟨δf,hδf,hf⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuous_compactF) a ha
  obtain ⟨δk,hδk,hk⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuous_compactK) a ha
  let δ := min (min δv δm) (min δf δk)
  have hδ : 0<δ := lt_min (lt_min hδv hδm) (lt_min hδf hδk)
  have hδv' : δ≤δv := (min_le_left _ _).trans (min_le_left _ _)
  have hδm' : δ≤δm := (min_le_left _ _).trans (min_le_right _ _)
  have hδf' : δ≤δf := (min_le_right _ _).trans (min_le_left _ _)
  have hδk' : δ≤δk := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,fun H hH => ⟨?_,?_,?_,?_⟩⟩
  · intro x
    have he := hv ((hH x).trans_le hδv')
    simpa only [Real.dist_eq,compactV_weight] using he.le
  · intro x
    have he := hm ((hH x).trans_le hδm')
    have heq (x : ℝ) : 1-(compactWeight x:ℝ)=m x := by dsimp [compactWeight,w]; ring
    simpa only [Real.dist_eq,compactV_weight,heq] using he.le
  · intro x y
    have hd : dist (compactWeight x,compactWeight y) (compactWeight (H x),compactWeight (H y))<δf := by
      rw [Prod.dist_eq,max_lt_iff]
      exact ⟨(hH x).trans_le hδf',(hH y).trans_le hδf'⟩
    have he := hf hd
    simpa only [Real.dist_eq,compactF_weight] using he.le
  · intro x y
    have hd : dist (compactWeight x,compactWeight y) (compactWeight (H x),compactWeight (H y))<δk := by
      rw [Prod.dist_eq,max_lt_iff]
      exact ⟨(hH x).trans_le hδk',(hH y).trans_le hδk'⟩
    have he := hk hd
    simpa only [Real.dist_eq,compactK_weight] using he.le

lemma field_error_tolerance (β T : ℝ) {e : ℝ} (he : 0<e) :
    ∃ a : ℝ, 0<a ∧ a<1 ∧ 2*a+2*T*a+5*β^2*a+4*β*sqrt a<e := by
  have hc : ContinuousAt (fun a : ℝ => 2*a+2*T*a+5*β^2*a+4*β*sqrt a) 0 := by fun_prop
  simp only [ContinuousAt,mul_zero,add_zero,sqrt_zero] at hc
  have hh := hc.eventually (gt_mem_nhds he)
  have hu : ∀ᶠ a : ℝ in 𝓝 0, a<1 := gt_mem_nhds (by norm_num)
  have hp : ∀ᶠ a : ℝ in 𝓝[>] 0, 0<a := self_mem_nhdsWithin
  obtain ⟨a,ha,hua,hga⟩ := (hp.and ((hu.and hh).filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨a,ha,hua,hga⟩

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_Quantizer
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real Set
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma gridCut_strictMono {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) :
    StrictMono (gridCut R N) := by
  intro i j hij
  have hc : (i.val:ℝ)<(j.val:ℝ) := by exact_mod_cast hij
  exact add_lt_add_right (mul_lt_mul_of_pos_left hc (by positivity : 0<2*R/(N:ℝ))) _

lemma gridRep_zero (R : ℝ) (N : ℕ) : gridRep R N 0= -R := by simp [gridRep]
lemma gridRep_last (R : ℝ) {N : ℕ} (hN : 0<N) : gridRep R N (Fin.last (N+1))=R := by
  simp only [gridRep,Fin.val_last,min_eq_right (show N≤N+1 from by omega),div_mul_cancel₀ _ ((Nat.cast_ne_zero.mpr hN.ne' : (N:ℝ)≠0))]
  ring
lemma gridRep_middle (R : ℝ) {N : ℕ} (j : Fin (N+2)) (hj : j.val<N+1) :
    gridRep R N j=gridCut R N ⟨j.val,hj⟩ := by
  simp only [gridRep,gridCut,min_eq_left (show j.val≤N from by omega)]

lemma gridQuant_left {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) {x : ℝ} (hx : x≤-R) :
    gridQuant R N x= -R := by
  unfold gridQuant
  have he : intervalBin (gridCut R N) x=0 := (intervalBin_eq_zero (by omega)
    (gridCut_strictMono hR hN) x).mpr (by simpa [gridCut] using hx)
  rw [he,gridRep_zero]

lemma gridQuant_right {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) {x : ℝ} (hx : R<x) :
    gridQuant R N x=R := by
  unfold gridQuant
  have he : intervalBin (gridCut R N) x=Fin.last (N+1) := (intervalBin_eq_last (by omega)
    (gridCut_strictMono hR hN) x).mpr (by simpa only [Nat.add_sub_cancel,gridCut,div_mul_cancel₀ _ ((Nat.cast_ne_zero.mpr hN.ne' : (N:ℝ)≠0)),show -R+2*R=R by ring] using hx)
  rw [he,gridRep_last R hN]

lemma gridQuant_middle {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) {x : ℝ}
    (hxL : -R<x) (hxU : x≤R) : |x-gridQuant R N x|≤2*R/N := by
  let j := intervalBin (gridCut R N) x
  have hj0 : j≠0 := fun hh => not_le.mpr hxL (by
    simpa only [gridCut,Fin.val_mk,Nat.cast_zero,mul_zero,add_zero] using
      (intervalBin_eq_zero (by omega) (gridCut_strictMono hR hN) x).mp hh)
  have hjLast : j≠Fin.last (N+1) := fun hh => not_lt.mpr hxU (by
    simpa only [Nat.add_sub_cancel,gridCut,Fin.val_mk,div_mul_cancel₀ _ ((Nat.cast_ne_zero.mpr hN.ne' : (N:ℝ)≠0)),
      show -R+2*R=R by ring] using
      (intervalBin_eq_last (by omega) (gridCut_strictMono hR hN) x).mp hh)
  have hj0' : 0<j.val := by have hh : j.val≠0 := fun he => hj0 (Fin.ext he); omega
  have hjN : j.val<N+1 := by
    have hb := j.isLt
    have hh : j.val≠N+1 := fun he => hjLast (Fin.ext he)
    omega
  have hbounds := (intervalBin_eq_middle (gridCut_strictMono hR hN) x j hj0' hjN).mp rfl
  change |x-gridRep R N j|≤_
  rw [gridRep_middle R j hjN]
  simp only [gridCut] at hbounds ⊢
  have hcast : ((j.val-1:ℕ):ℝ)=(j.val:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  rw [hcast] at hbounds
  rw [abs_of_nonpos (sub_nonpos.mpr hbounds.2)]
  linarith only [hbounds.1]

lemma gridQuant_square_error {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) (x : ℝ) :
    (x-gridQuant R N x)^2≤(2*R/N)^2 + squareTail R x := by
  by_cases hxL : x≤-R
  · rw [gridQuant_left hR hN hxL]
    by_cases he : x= -R
    · simp only [he,sub_self,zero_pow (by decide : (2:ℕ)≠0)]
      exact add_nonneg (sq_nonneg _) (squareTail_nonneg _ _)
    · have hlt : x < -R := lt_of_le_of_ne hxL he
      have hx : R < |x| := by rw [abs_of_neg (by linarith)]; linarith
      rw [squareTail,ite_eq_left hx]
      nlinarith [sq_nonneg (2*R/(N:ℝ))]
  · by_cases hxU : x≤R
    · have hb := gridQuant_middle hR hN (lt_of_not_ge hxL) hxU
      have hs : (x-gridQuant R N x)^2≤(2*R/N)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2*R/(N:ℝ))).mpr hb
      linarith [squareTail_nonneg R x]
    · have hx := lt_of_not_ge hxU
      rw [gridQuant_right hR hN hx,squareTail,ite_eq_left (by rw [abs_of_pos (hR.trans hx)]; exact hx)]
      nlinarith [sq_nonneg (2*R/(N:ℝ))]

lemma measurable_gridQuant {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) :
    Measurable (gridQuant R N) :=
  (measurable_of_countable (gridRep R N)).comp (measurable_intervalBin (by omega) (gridCut_strictMono hR hN))

lemma gridQuant_compact_error {δ R : ℝ} (_ : 0<δ) (hR : 0<R) {N : ℕ} (hN : 0<N)
    (hmesh : 2*R/(N:ℝ)<δ)
    (htail : ∀ x : ℝ, R≤|x| → |tanh x-tanh (if 0≤x then R else -R)|<δ) (x : ℝ) :
    dist (compactWeight x) (compactWeight (gridQuant R N x))<δ := by
  change |w x-w (gridQuant R N x)|<δ
  rw [w,w,sub_sub_sub_cancel_left,abs_sub_comm]
  change |tanh x-tanh (gridQuant R N x)|<δ
  by_cases hxL : x≤-R
  · rw [gridQuant_left hR hN hxL]
    have hh := htail x (by rw [abs_of_neg (by linarith)]; linarith)
    simpa only [ite_eq_right (show ¬0≤x by linarith)] using hh
  · by_cases hxU : x≤R
    · exact ((Calculus.tanh_lipschitz_abs _ _).trans
        (gridQuant_middle hR hN (lt_of_not_ge hxL) hxU)).trans_lt hmesh
    · have hx := lt_of_not_ge hxU
      rw [gridQuant_right hR hN hx]
      have hh := htail x (by rw [abs_of_pos (hR.trans hx)]; exact hx.le)
      simpa only [ite_eq_left (hR.trans hx).le] using hh

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_TanhEnds
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology
open Filter MeasureTheory Real Set
namespace SKRatio.Bins
open SKRatioClock.Regression

lemma tanh_exp_negative (x : ℝ) : tanh x=(1-exp (-2*x))/(1+exp (-2*x)) := by
  rw [tanh_eq]
  have he : exp (-2*x)=exp (-x)/exp x := by
    rw [←exp_sub]; congr 1; ring
  rw [he]
  field_simp

lemma tendsto_tanh_atTop : Tendsto tanh atTop (𝓝 1) := by
  have hn : Tendsto (fun x : ℝ => -2*x) atTop atBot := by
    convert tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp
  have he := tendsto_exp_atBot.comp hn
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub he).div ((tendsto_const_nhds (x := (1 : ℝ))).add he)
    (by norm_num : (1:ℝ)+0≠0)
  change Tendsto (fun x : ℝ => (1-exp (-2*x))/(1+exp (-2*x))) atTop (𝓝 ((1-0)/(1+0))) at hh
  simpa only [sub_zero,add_zero,div_one,←tanh_exp_negative] using hh

lemma tanh_tail_uniform {δ : ℝ} (hδ : 0<δ) : ∃ R : ℝ, 0<R ∧
    ∀ S : ℝ, R≤S → ∀ x : ℝ, S≤|x| →
      |tanh x-tanh (if 0≤x then S else -S)|<δ := by
  have he := tendsto_tanh_atTop.eventually (Metric.ball_mem_nhds (1:ℝ) (half_pos hδ))
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  refine ⟨max R 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro S hS x hx
  have hSR : R≤S := (le_max_left _ _).trans hS
  have hpos : 0≤S := (le_of_lt (by norm_num : (0:ℝ)<1)).trans ((le_max_right _ _).trans hS)
  by_cases hx0 : 0≤x
  · rw [ite_eq_left hx0]
    rw [abs_of_nonneg hx0] at hx
    have h1 : |tanh x-1|<δ/2 := hR x (hSR.trans hx)
    have h2 : |tanh S-1|<δ/2 := hR S hSR
    have hh := abs_sub_le (tanh x) 1 (tanh S)
    rw [abs_sub_comm 1 (tanh S)] at hh
    linarith
  · rw [ite_eq_right hx0,tanh_neg]
    have hx' : S≤-x := by simpa only [abs_of_neg (lt_of_not_ge hx0)] using hx
    have h1 : |tanh (-x)-1|<δ/2 := hR (-x) (hSR.trans hx')
    have h2 : |tanh S-1|<δ/2 := hR S hSR
    have hh := abs_sub_le (tanh (-x)) 1 (tanh S)
    rw [abs_sub_comm 1 (tanh S)] at hh
    rw [tanh_neg] at hh h1
    have hid : |tanh x- -tanh S|=|-tanh x-tanh S| := by
      rw [←abs_neg (tanh x- -tanh S)]; congr 1; ring
    rw [hid]
    linarith

lemma squareTail_antitone {R S : ℝ} (hRS : R≤S) (x : ℝ) :
    squareTail S x ≤ squareTail R x := by
  unfold squareTail
  split_ifs with hS hR hR
  · rfl
  · exact (hR (hRS.trans_lt hS)).elim
  · exact sq_nonneg _
  · rfl

lemma integrable_squareTail {μ : Measure ℝ} (hi : Integrable (fun x : ℝ => x^2) μ) (R : ℝ) :
    Integrable (squareTail R) μ := by
  apply hi.mono' (measurable_squareTail R).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [norm_eq_abs,abs_of_nonneg (squareTail_nonneg _ _)]
    exact squareTail_le R x)

lemma tendsto_integral_squareTail {μ : Measure ℝ} (hi : Integrable (fun x : ℝ => x^2) μ) :
    Tendsto (fun R : ℕ => ∫ x, squareTail R x ∂μ) atTop (𝓝 0) := by
  have hh : Tendsto (fun R : ℕ => ∫ x, squareTail R x ∂μ) atTop (𝓝 (∫ _x, (0:ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x : ℝ => x^2)
    · intro R
      exact (measurable_squareTail R).aestronglyMeasurable
    · exact hi
    · intro R
      exact ae_of_all _ (fun x => by
        rw [norm_eq_abs,abs_of_nonneg (squareTail_nonneg _ _)]
        exact squareTail_le R x)
    · apply ae_of_all
      intro x
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with R hR
      have hx : |x|≤(R:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hR)
      simp [squareTail,not_lt.mpr hx]
  simpa only [integral_zero] using hh

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_QuantizerExistence
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real Set
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression

lemma quantizer_integrable_square {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hi : Integrable (fun x : ℝ => x^2) μ) :
    Integrable (fun x => (x-gridQuant R N x)^2) μ := by
  apply ((integrable_const ((2*R/N)^2)).add (integrable_squareTail hi R)).mono'
    ((measurable_id.sub (measurable_gridQuant hR hN)).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact gridQuant_square_error hR hN x)

theorem quantizer_exists
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hi : Integrable (fun x : ℝ => x^2) μ)
    {δ d : ℝ} (hδ : 0<δ) (hd : 0<d) :
    ∃ R : ℝ, ∃ N : ℕ, 0<R ∧ 0<N ∧
      (∀ x, dist (compactWeight x) (compactWeight (gridQuant R N x))<δ) ∧
      (∫ x, (x-gridQuant R N x)^2 ∂μ)<d^2 ∧
      ExponentiallyRare ρ (fun n => {ω | d≤ siteNorm (fun i => X n ω i-gridQuant R N (X n ω i))}) := by
  obtain ⟨Rt,hRt,ht⟩ := hX (d^2/2) (by positivity)
  obtain ⟨Rc,hRc,hc⟩ := tanh_tail_uniform hδ
  have he := (tendsto_integral_squareTail hi).eventually (gt_mem_nhds (by positivity : (0:ℝ)<d^2/4))
  obtain ⟨Ng,hNg⟩ := eventually_atTop.mp he
  let R := max (max Rt Rc) (Ng:ℝ)
  have hR : 0<R := hRc.trans_le ((le_max_right Rt Rc).trans (le_max_left _ _))
  have hRtR : Rt≤R := (le_max_left Rt Rc).trans (le_max_left _ _)
  have hRcR : Rc≤R := (le_max_right Rt Rc).trans (le_max_left _ _)
  have hRg : (Ng:ℝ)≤R := le_max_right _ _
  have hg : (∫ x, squareTail R x ∂μ)<d^2/4 := by
    apply lt_of_le_of_lt (integral_mono (integrable_squareTail hi R) (integrable_squareTail hi Ng)
      (squareTail_antitone hRg))
    exact hNg Ng le_rfl
  let a := min δ (d/2)
  have ha : 0<a := lt_min hδ (half_pos hd)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*R/a)
  have hN0 : 0<N := by
    have hnR : (0:ℝ)<N := (by positivity : (0:ℝ)<2*R/a).trans hN
    exact_mod_cast hnR
  have hmesh : 2*R/(N:ℝ)<a := by
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hN0)]
    have hh := (div_lt_iff₀ ha).mp hN
    nlinarith only [hh]
  have hmeshd : (2*R/(N:ℝ))^2<d^2/4 := by
    have hh := hmesh.trans_le (min_le_right δ (d/2))
    have h0 : 0≤2*R/(N:ℝ) := by positivity
    nlinarith only [hh,hd,h0]
  refine ⟨R,N,hR,hN0,?_,?_,?_⟩
  · exact gridQuant_compact_error hδ hR hN0 (hmesh.trans_le (min_le_left _ _)) (hc R hRcR)
  · have hle := integral_mono (quantizer_integrable_square hR hN0 hi)
      ((integrable_const ((2*R/(N:ℝ))^2)).add (integrable_squareTail hi R))
      (gridQuant_square_error hR hN0)
    simp only [Pi.add_apply] at hle
    rw [integral_add (integrable_const _) (integrable_squareTail hi R),integral_const] at hle
    simp only [probReal_univ,one_smul] at hle
    linarith [sq_pos_of_pos hd]
  · apply ht.mono
    filter_upwards [eventually_gt_atTop 0] with n hn
    intro ω hω
    change d≤ siteNorm (fun i => X n ω i-gridQuant R N (X n ω i)) at hω
    have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have h1 : d^2≤(∑ i, (X n ω i-gridQuant R N (X n ω i))^2)/(n:ℝ) := by
      rw [←siteNorm_sq]
      exact (sq_le_sq₀ hd.le (siteNorm_nonneg _)).mpr hω
    have h2 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => gridQuant_square_error hR hN0 (X n ω i))
    have h3 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => squareTail_antitone hRtR (X n ω i))
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h2
    have hh := div_le_div_of_nonneg_right h2 hnR.le
    rw [add_div,mul_div_cancel_left₀ _ (ne_of_gt hnR)] at hh
    have hh' := div_le_div_of_nonneg_right h3 hnR.le
    change d^2/2≤(∑ i, squareTail Rt (X n ω i))/(n:ℝ)
    nlinarith only [h1,hh,hh',hmeshd,sq_nonneg d]

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_QuantizedPopulation
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression

lemma l2Norm_field (β : ℝ) : l2Norm (fieldLaw β) id=sqrt (β^2+β^4) := by
  unfold l2Norm
  exact congrArg sqrt (fieldLaw_secondMoment β)

lemma quantizer_l2Norm_le {β R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N)
    {a : ℝ} (ha : 0≤a) (herr : (∫ x, (x-gridQuant R N x)^2 ∂fieldLaw β)≤a^2) :
    l2Norm (fieldLaw β) (gridQuant R N)≤ sqrt (β^2+β^4)+a := by
  have hs := measurable_intervalBin (Nat.succ_pos N) (gridCut_strictMono hR hN)
  have hH := memLp_finite_comp (μ := fieldLaw β) hs (gridRep R N)
  have he : l2Norm (fieldLaw β) (fun x => gridQuant R N x-x)≤a := by
    unfold l2Norm
    apply (sqrt_le_iff).mpr ⟨ha,?_⟩
    simpa only [sub_sq_comm] using herr
  have ht := l2Norm_add (memLp_field β) (hH.sub (memLp_field β))
  change l2Norm (fieldLaw β) (fun x => x+(gridQuant R N x-x))≤
    l2Norm (fieldLaw β) id+l2Norm (fieldLaw β) (fun x => gridQuant R N x-x) at ht
  have heq : (fun x => x+(gridQuant R N x-x))=gridQuant R N := by ext x; ring
  rw [heq] at ht
  rw [l2Norm_field] at ht
  linarith only [ht,he]

lemma finiteV_le_of_quantizer {β C a : ℝ} (hβ : 0≤β) (ha : 0≤a)
    (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
      (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r≤C)
    {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) (hβne : β≠0)
    (herr : (∫ x, (x-gridQuant R N x)^2 ∂fieldLaw β)≤a^2)
    {T : ℝ} (hT : 0≤T) (hsize : sqrt (β^2+β^4)+a≤T)
    (hv : ∀ x, |v x-v (gridQuant R N x)|≤a)
    (hmv : ∀ x, |m x*v x-m (gridQuant R N x)*v (gridQuant R N x)|≤a)
    (hf : ∀ x y, |v y^2/(w x+w y)-v (gridQuant R N y)^2/
      (w (gridQuant R N x)+w (gridQuant R N y))|≤a)
    (hk : ∀ x y, |kernel x y-kernel (gridQuant R N x) (gridQuant R N y)|≤a)
    (z : Parameters (Fin (N+2))) :
    finiteV β (massRoot (fieldLaw β) (intervalBin (gridCut R N))) (gridRep R N) z ≤
      C+(2*a+2*T*a+5*β^2*a+4*β*sqrt a) := by
  let σ := intervalBin (gridCut R N)
  have hs : Measurable σ := measurable_intervalBin (Nat.succ_pos N) (gridCut_strictMono hR hN)
  have hm : ∀ d, 0<binMass (fieldLaw β) σ d :=
    intervalBin_mass_pos (Nat.succ_pos N) (gridCut_strictMono hR hN) β hβne
  let b := pullback (fieldLaw β) σ (paramB z)
  let r := pullback (fieldLaw β) σ (paramR z)
  have hb : MemLp b 2 (fieldLaw β) := memLp_pullback hs _
  have hr : MemLp r 2 (fieldLaw β) := memLp_pullback hs _
  have he := pullback_normalized (μ := fieldLaw β) hs hm z
  have hH : MemLp (gridQuant R N) 2 (fieldLaw β) := memLp_finite_comp hs (gridRep R N)
  have herr' : l2Norm (fieldLaw β) (fun x => x-gridQuant R N x)≤a :=
    (sqrt_le_iff).mpr ⟨ha,herr⟩
  have hbnd := fieldForm_error (μ := fieldLaw β) β hβ hb hr
    (measurable_pullback hs _) (measurable_pullback hs _) measurable_id
    (measurable_gridQuant hR hN) (memLp_field β) hH he ha hT herr'
    ((quantizer_l2Norm_le hR hN ha herr).trans hsize) hv hmv hf hk
  have hp := fieldForm_pullback (μ := fieldLaw β) hs hm β (gridRep R N) z
  change fieldForm (fieldLaw β) β (gridQuant R N) b r = _ at hp
  rw [fieldForm_id,hp] at hbnd
  have hu := hscalar b r hb hr he
  have hle := neg_le_abs (variational β b r-finiteV β (massRoot (fieldLaw β) σ) (gridRep R N) z)
  change finiteV β (massRoot (fieldLaw β) σ) (gridRep R N) z≤_
  linarith only [hle,hbnd,hu]

theorem scalar_quantizer_exists
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X)
    {β K C e : ℝ} (hβ : 0<β) (hK : 0≤K) (he : 0<e)
    (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
      (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r≤C) :
    ∃ a R : ℝ, ∃ N : ℕ, 0<a ∧ a<1 ∧ 0<R ∧ 0<N ∧
      (2*a+2*(sqrt (β^2+β^4)+2)*a+5*β^2*a+K*a+4*β*sqrt a<e) ∧
      (∀ x, |v x-v (gridQuant R N x)|≤a) ∧
      (∀ x, |m x*v x-m (gridQuant R N x)*v (gridQuant R N x)|≤a) ∧
      (∀ x y, |v y^2/(w x+w y)-v (gridQuant R N y)^2/
        (w (gridQuant R N x)+w (gridQuant R N y))|≤a) ∧
      (∀ x y, |kernel x y-kernel (gridQuant R N x) (gridQuant R N y)|≤a) ∧
      (∀ z, finiteV β (massRoot (fieldLaw β) (intervalBin (gridCut R N))) (gridRep R N) z<C+e) ∧
      ExponentiallyRare ρ (fun n => {ω | a≤ siteNorm (fun i => X n ω i-gridQuant R N (X n ω i))}) := by
  let T := sqrt (β^2+β^4)+2
  have hT : 0≤T := by dsimp [T]; positivity
  obtain ⟨a,ha,ha1,hea⟩ := field_error_tolerance β (T+K/2) he
  have htotal : 2*a+2*T*a+5*β^2*a+K*a+4*β*sqrt a<e := by linarith only [hea]
  obtain ⟨δ,hδ,ht⟩ := compact_coefficients_tolerance ha
  obtain ⟨R,N,hR,hN,hcomp,hl2,hemp⟩ := quantizer_exists hX (μ := fieldLaw β)
    (memLp_field β).integrable_sq hδ ha
  obtain ⟨hv,hmv,hf,hk⟩ := ht (gridQuant R N) hcomp
  refine ⟨a,R,N,ha,ha1,hR,hN,htotal,hv,hmv,hf,hk,?_,hemp⟩
  intro z
  have hp := finiteV_le_of_quantizer hβ.le ha.le hscalar hR hN hβ.ne'
    hl2.le hT (by dsimp [T]; linarith only [ha1]) hv hmv hf hk z
  have hKa := mul_nonneg hK ha.le
  exact hp.trans_lt (by linarith only [htotal,hKa])

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma variance_bilinear_field_error (M : Matrix (Fin n) (Fin n) ℝ)
    (v v' p : Fin n → ℝ) (hp : ∑ i, p i^2=1) {K a : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hM : euclideanOpNorm M ≤ K)
    (hv : ∀ i, |v i-v' i| ≤ a) :
    |p ⬝ᵥ (M*ᵥ (fun i => v i*p i))-p ⬝ᵥ (M*ᵥ (fun i => v' i*p i))| ≤ K*a := by
  have he : p ⬝ᵥ (M*ᵥ (fun i => v i*p i))-p ⬝ᵥ (M*ᵥ (fun i => v' i*p i)) =
      quadratic (M*Matrix.diagonal (fun i => v i-v' i)) p := by
    simp only [quadratic,Matrix.mul_diagonal,dotProduct,Matrix.mulVec,Finset.mul_sum,
      ←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  have hd := matrix_diagonal_opNorm_le (fun i => v i-v' i) a ha hv
  have hnorm : euclideanOpNorm (M*Matrix.diagonal (fun i => v i-v' i)) ≤ K*a := by
    unfold euclideanOpNorm
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul hM hd (norm_nonneg _) hK)
  simpa only [hp,mul_one] using (quadratic_abs_le _ p).trans
    (mul_le_mul_of_nonneg_right hnorm (Finset.sum_nonneg (fun i _ => sq_nonneg (p i))))

lemma deterministic_corrected_error (β : ℝ) (H p : Fin n → ℝ)
    (hp : ∑ i, p i^2=1) :
    |deterministicForm β H p-correctedForm β H p| ≤  |(∑ i, H i)/(n:ℝ)-β^2| := by
  rw [deterministic_corrected,add_sub_cancel_left,abs_mul,abs_mul,abs_sub_comm]
  have h1 := mul_le_mul_of_nonneg_left (siteMoment_one hp) (abs_nonneg ((∑ i, H i)/(n:ℝ)-β^2))
  have h2 := mul_le_mul_of_nonneg_left (siteMoment_v hp H) (abs_nonneg ((∑ i, H i)/(n:ℝ)-β^2))
  calc
    _  ≤  |(∑ i, H i)/(n:ℝ)-β^2| *|siteMoment p (fun i => v (H i))| := by
      gcongr
      simpa only [mul_one] using h1
    _  ≤  _ := by simpa only [mul_one] using h2

lemma quantized_siteNorm_le (H H' : Fin n → ℝ) {s a : ℝ}
    (hs : siteNorm H ≤ s) (he : siteNorm (fun i => H i-H' i) ≤ a) : siteNorm H' ≤ s+a := by
  have hneg : siteNorm (fun i => H' i-H i)=siteNorm (fun i => H i-H' i) := by
    rw [siteNorm_eq_sqrt,siteNorm_eq_sqrt]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ht := siteNorm_add H (fun i => H' i-H i)
  have hid : (fun i => H i+(H' i-H i))=H' := by ext i; ring
  rw [hid,hneg] at ht
  linarith only [ht,hs,he]

theorem reducedForm_upper_rare {β C e : ℝ} (hβ : 0 < β) (he : 0 < e)
    (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
      (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r ≤ C) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ p : Fin n → ℝ, (∑ i, p i^2)=1 ∧ C+6*e < reducedForm β g p}) := by
  let K := 2*β+2*β^2+2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨a,R,N,ha,ha1,hR,hN,htotal,hv,hmv,hf,hk,hpop,herr⟩ :=
    scalar_quantizer_exists (augmentedField_squareTails β hβ) hβ hK he hscalar
  let q := intervalBin (gridCut R N)
  let h := gridRep R N
  have hq : Measurable q := measurable_intervalBin (Nat.succ_pos N) (gridCut_strictMono hR hN)
  have hnull : NullSingletonClass (fieldLaw β) := by
    unfold fieldLaw
    exact nullSingletonClass_gaussianReal (variance_ne_zero hβ)
  have hemp := augmentedField_empirical β hβ
  have hcount := intervalBin_binSize_rare (Nat.succ_pos N) (gridCut_strictMono hR hN) hemp
    (intervalBin_mass_pos (Nat.succ_pos N) (gridCut_strictMono hR hN) β hβ.ne')
  obtain ⟨δ,hδ,htol⟩ := finiteV_population_tolerance (μ := fieldLaw β) hq β h he
  have hroot := (intervalBin_roots_empirical (Nat.succ_pos N) (gridCut_strictMono hR hN) hemp) δ hδ
  have hmean := (augmentedField_firstMoment β hβ) e he
  have hsize := (augmentedField_siteNorm β hβ) 1 (by norm_num)
  obtain ⟨L,hL⟩ := random_binForm_tail (C := C+2*e) hβ hK he h q hq
  let E := fun n => {g : (Fin n × Fin n) → ℝ |
    (∀ d, 2 ≤ count (fun i => q (augmentedField β g i)) d) ∧
    (∀ z, finiteV β (binT (fun i => q (augmentedField β g i))) h z ≤ C+2*e) ∧
    g ∈ binFormBad β h (fun i => q (augmentedField β g i)) K ((C+2*e)+2*e)}
  have hE : ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n)) E := by
    refine ⟨(L:ℝ)+1,e^2/(π^2*β^2),by positivity,by positivity [pi_pos],?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [←ENNReal.ofReal_toReal (measure_ne_top (standardArrayLaw (Fin n × Fin n)) (E n))]
    apply ENNReal.ofReal_le_ofReal
    have ht := hL hn
    have hexp : -e^2*(n:ℝ)/(π^2*β^2)= -(e^2/(π^2*β^2))*(n:ℝ) := by ring
    rw [hexp] at ht
    exact ht.trans (by nlinarith only [exp_pos (-(e^2/(π^2*β^2))*(n:ℝ))])
  apply ((((((residual_norm_rare hβ).union herr).union hcount).union hroot).union hmean).union hsize).union hE |>.mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  rintro g ⟨p,hp,hbad⟩
  by_contra hb
  have hM : euclideanOpNorm (fieldProjection n*(β • goe g)*fieldProjection n) ≤ K :=
    not_lt.mp (fun hx => hb (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx)))))))
  have herr' : siteNorm (fun i => augmentedField β g i-gridQuant R N (augmentedField β g i)) < a :=
    lt_of_not_ge (fun hx => hb (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))
  have hcount' : ∀ d, 2 ≤ count (fun i => q (augmentedField β g i)) d := by
    intro d
    exact not_lt.mp (fun hx => hb (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨d,hx⟩))))))
  have hroot' : dist (binT (fun i => q (augmentedField β g i))) (massRoot (fieldLaw β) q) < δ :=
    lt_of_not_ge (fun hx => hb (Or.inl (Or.inl (Or.inl (Or.inr hx)))))
  have hmean' : |(∑ i, augmentedField β g i)/(n:ℝ)-β^2| < e :=
    lt_of_not_ge (fun hx => hb (Or.inl (Or.inl (Or.inr hx))))
  have hsize' : siteNorm (augmentedField β g) < sqrt (β^2+β^4)+1 := by
    have hh : |siteNorm (augmentedField β g)-sqrt (β^2+β^4)| < 1 :=
      lt_of_not_ge (fun hx => hb (Or.inl (Or.inr hx)))
    have hh' := (le_abs_self _).trans_lt hh
    linarith only [hh']
  have hfinite : ∀ z, finiteV β (binT (fun i => q (augmentedField β g i))) h z ≤ C+2*e := by
    intro z
    have hne : ∀ d, |binT (fun i => q (augmentedField β g i)) d-massRoot (fieldLaw β) q d| < δ :=
      fun d => by simpa only [Real.dist_eq] using (dist_pi_lt_iff hδ).mp hroot' d
    have h1 := htol hn _ hne z
    have h2 := hpop z
    change finiteV β (massRoot (fieldLaw β) q) h z < C+e at h2
    linarith only [h1,h2]
  have hform : p ⬝ᵥ ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ
      (fun i => v (h (q (augmentedField β g i)))*p i))+
      correctedForm β (fun i => h (q (augmentedField β g i))) p ≤ C+4*e := by
    apply not_lt.mp
    intro hh
    apply hb
    exact Or.inr ⟨hcount',hfinite,hM, p,hp,by linarith only [hh]⟩
  have hsquant : siteNorm (fun i => gridQuant R N (augmentedField β g i)) ≤  sqrt (β^2+β^4)+2 := by
    have ht := quantized_siteNorm_le _ _ hsize'.le herr'.le
    linarith only [ht,ha1]
  have hcf := correctedForm_field_error hn β (augmentedField β g)
    (fun i => gridQuant R N (augmentedField β g i)) p hp ha.le ha.le
    (show 0 ≤  sqrt (β^2+β^4)+2 by positivity) herr'.le hsquant
    (fun i => hv _) (fun i => hmv _)
    (by intro i j; simpa only [compactF_weight] using hf (augmentedField β g i) (augmentedField β g j))
    (by intro i j; simpa only [compactK_weight] using hk (augmentedField β g i) (augmentedField β g j))
  have hbil := variance_bilinear_field_error (fieldProjection n*(β • goe g)*fieldProjection n)
    (fun i => v (augmentedField β g i)) (fun i => v (gridQuant R N (augmentedField β g i))) p
    hp hK ha.le hM (fun i => hv _)
  have hcor := deterministic_corrected_error β (augmentedField β g) p hp
  rw [reducedForm_decomposition hn] at hbad
  have hsum : 0 ≤ 4*β*sqrt a := by positivity
  change p ⬝ᵥ ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ
      (fun i => v (gridQuant R N (augmentedField β g i))*p i))+
      correctedForm β (fun i => gridQuant R N (augmentedField β g i)) p ≤ C+4*e at hform
  have hcf' := (le_abs_self _).trans hcf
  have hbil' := (le_abs_self _).trans hbil
  have hcor' := (le_abs_self _).trans hcor
  linarith only [hbad,hform,hcf',hbil',hcor',htotal,hmean',hsum]

end SKRatio.Bins

namespace SKRatio.Planted
open Bins Scalar SKRatioClock.Regression Calculus
attribute [local instance] Classical.propDecidable

theorem formBad_rare_of_scalar {β C : ℝ} (hβ : 0 < β) (hC : C < 1)
    (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
      (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r ≤ C) :
    ∃ ρ : ℝ, 0 < ρ ∧ ExponentiallyRare (law β) (formBad ρ) := by
  let e := (1-C)/10
  have he : 0 < e := by dsimp [e]; positivity
  have hred := reducedForm_upper_rare hβ he hscalar
  have herr := reduced_error_rare hβ he
  have hbad : ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => (augmentedDisorder β) ⁻¹' formBad e n) := by
    apply (hred.union herr).mono
    exact .of_forall (fun n g hg => by
      obtain ⟨p,hp,hbad⟩ := (formBad_iff_unit e _).mp hg
      by_contra hnot
      have hr : reducedForm β g p ≤ C+6*e := not_lt.mp (fun hx => hnot (Or.inl ⟨p,hp,hx⟩))
      have hu : |gradientForm (coupling (augmentedDisorder β g)) p-reducedForm β g p| ≤ e := by
        have hh : |gradientForm (coupling (augmentedDisorder β g)) p-reducedForm β g p| ≤
            e*(∑ i, p i^2) := not_lt.mp (fun hx => hnot (Or.inr ⟨p,hx⟩))
        simpa only [hp,mul_one] using hh
      have hle := (le_abs_self _).trans hu
      dsimp [e] at hr hu hbad hle
      linarith only [hr,hbad,hle,hC])
  obtain ⟨A,c,hA,hc,hrare⟩ := hbad
  refine ⟨e,he,A,c,hA,hc,?_⟩
  filter_upwards [hrare,eventually_gt_atTop 0] with n hn hn0
  have hl := (augmentedDisorder_hasLaw hn0 β).measure_eq (formBad_measurable e n)
  exact hl.symm.le.trans hn

theorem ratio_cutoff_of_scalar_oai (β ε η C : ℝ)
    (hβ : 0 < β) (hβhalf : β < 1/2) (hε : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η)
    (hC : C < 1)
    (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
      (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r ≤ C) :
    Tendsto (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η  <  (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)}) atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0  <  mixingTime g (1-ε)) := by
  obtain ⟨ρ,hρ,hρrare⟩ := formBad_rare_of_scalar hβ hC hscalar
  obtain ⟨κ,hκ,hplant⟩ := hρrare.without_prefactor
  exact ratio_cutoff_of_planted_form β ε η hβ.le hβhalf hε hεhalf hη hρ hκ hplant

end SKRatio.Planted

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Planted.ratio_cutoff_of_scalar_oai := @OAI.SKRatio.Planted.ratio_cutoff_of_scalar_oai

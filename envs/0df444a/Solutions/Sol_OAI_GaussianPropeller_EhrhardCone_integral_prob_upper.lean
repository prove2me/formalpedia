-- Prove2me | solution 1 for OAI.GaussianPropeller.EhrhardCone.integral_prob_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:21:07.676342+00:00
-- url     : https://prove2.me/submissions/c2b6b418-7f35-4411-9ab0-933e3931ea9e

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/ConeConcavity.lean:L305-L323
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.EhrhardCone.integral_prob_upper. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Theorems.Thm_OAI_GaussianPropeller_EhrhardCone_prob_mem
import Theorems.Thm_OAI_GaussianPropeller_EhrhardSmooth_qheat_concave
import Theorems.Thm_OAI_GaussianPropeller_SoftMin_Z_fderiv
import Theorems.Thm_OAI_GaussianPropeller_SoftMin_hess_bound
import Theorems.Thm_OAI_GaussianPropeller_Translation_translation_derivative

-- ---- from OAI.Probability.GaussianPropeller.Quantile ----
namespace OAI

universe uX

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace GaussianPropeller.Quantile

lemma cdfIso_coe (x : ℝ) : (cdfIso x : ℝ) = Φ x := rfl
lemma q_of_mem {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : q p = cdfIso.symm ⟨p,hp⟩ := by
  simp [q, hp]
lemma Φ_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : Φ (q p) = p := by
  rw [q_of_mem hp, ← cdfIso_coe]
  exact congrArg Subtype.val (cdfIso.apply_symm_apply ⟨p,hp⟩)
lemma continuousOn_q : ContinuousOn q (Ioo (0:ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun p : Ioo (0:ℝ) 1 => q p)
  have heq : (fun p : Ioo (0:ℝ) 1 => q p) = cdfIso.symm := by
    funext p
    exact q_of_mem p.2
  rw [heq]
  exact cdfIso.symm.continuous
lemma continuousAt_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : ContinuousAt q p :=
  continuousOn_q.continuousAt (isOpen_Ioo.mem_nhds hp)
lemma hasDerivAt_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    HasDerivAt q (φ (q p))⁻¹ p := by
  apply HasDerivAt.of_local_left_inverse (continuousAt_q hp) (hasDerivAt_Φ (q p))
    (ne_of_gt (φ_pos _))
  filter_upwards [isOpen_Ioo.mem_nhds hp] with y hy
  exact Φ_q hy
lemma concave_le_tangent {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f)
    {x y d : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x) :
    f y ≤ f x+d*(y-x) := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hh := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · simp
  · have hh := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith only [hh']

section Integration
variable {X : Type uX} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

end Integration
end GaussianPropeller.Quantile

end OAI

-- ---- from OAI.Probability.GaussianPropeller.QuantileCalculus ----
namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

open scoped RealInnerProductSpace
namespace GaussianPropeller.QuantilePDE
open GaussianPropeller.Quantile

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end GaussianPropeller.QuantilePDE

namespace GaussianPropeller.SmoothCDF
open GaussianPropeller.Quantile
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma cdf_bound [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x : E) : ‖Φ (f x)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact (Φ_lt_one _).le

end GaussianPropeller.SmoothCDF

end OAI

-- ---- from OAI.Probability.GaussianPropeller.SoftMinimum ----
namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal

open Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace GaussianPropeller.SoftMin

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

lemma Z_pos (v : ι → E) (x : E) : 0 < Z v x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
lemma weight_pos (v : ι → E) (x : E) (i : ι) : 0 < weight v x i :=
  div_pos (Real.exp_pos _) (Z_pos v x)
lemma sum_weight (v : ι → E) (x : E) : ∑ i, weight v x i = 1 := by
  simp only [weight, ← Finset.sum_div]
  exact div_self (ne_of_gt (Z_pos v x))
omit [Nonempty ι] in
lemma continuous_Z [Nonempty ι] (v : ι → E) : Continuous (Z v) := by unfold Z; fun_prop
lemma continuous_weight (v : ι → E) (i : ι) : Continuous (fun x => weight v x i) := by
  exact (by fun_prop : Continuous (fun x : E => Real.exp (-⟪v i,x⟫))).div
    (continuous_Z v) (fun x => ne_of_gt (Z_pos v x))
lemma continuous_grad (v : ι → E) : Continuous (grad v) := by
  unfold grad
  exact continuous_finsetSum _ (fun i _ => (continuous_weight v i).smul continuous_const)
lemma continuous_hess (v : ι → E) : Continuous (hess v) := by
  unfold hess
  apply continuous_finsetSum
  intro i _
  have h := continuous_grad v
  have hw := continuous_weight v i
  fun_prop
omit [Nonempty ι] in
lemma inner_grad [Nonempty ι] (v : ι → E) (x e : E) :
    ⟪grad v x,e⟫ = ∑ i, weight v x i*⟪v i,e⟫ := by
  simp only [grad, sum_inner, real_inner_smul_left]
lemma value_fderiv (v : ι → E) (x : E) :
    HasFDerivAt (value v) (innerSL ℝ (grad v x)) x := by
  have hh := ((Z_fderiv v x).log (ne_of_gt (Z_pos v x))).neg
  convert hh using 1 <;> (first | rfl | (ext y; simp [ne_of_gt (Z_pos v x)]))
lemma weight_fderiv (v : ι → E) (x : E) (i : ι) :
    HasFDerivAt (fun y => weight v y i)
      (weight v x i • innerSL ℝ (grad v x-v i)) x := by
  have hn := ((innerSL ℝ (v i)).hasFDerivAt (x := x)).neg.exp
  have hi := (hasDerivAt_inv (ne_of_gt (Z_pos v x))).comp_hasFDerivAt x (Z_fderiv v x)
  have hh := hn.mul hi
  convert hh using 1 <;> try rfl
  ext e
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, inner_sub_left,
    Pi.neg_apply, Function.comp_def, add_apply, neg_apply]
  dsimp only [weight]
  field_simp [ne_of_gt (Z_pos v x)]
  ring
lemma grad_fderiv (v : ι → E) (x : E) :
    HasFDerivAt (grad v) (hess v x) x := by
  have hd (i : ι) := (weight_fderiv v x i).smul_const (v i)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)
  convert hs using 1 <;> try rfl
  ext e
  simp [hess, smul_smul]

lemma grad_bound (v : ι → E) {L : ℝ} (hL : ∀ i, ‖v i‖ ≤ L) (x : E) : ‖grad v x‖ ≤ L := by
  calc
    ‖grad v x‖ ≤ ∑ i, ‖weight v x i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, weight v x i*L := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos v x i)]
      exact mul_le_mul_of_nonneg_left (hL i) (weight_pos v x i).le
    _ = L := by rw [← Finset.sum_mul, sum_weight, one_mul]

lemma hess_nonpos (v : ι → E) (x e : E) : ⟪hess v x e,e⟫ ≤ 0 := by
  have hvariance : 0 ≤ ∑ i, weight v x i*(⟪v i,e⟫-⟪grad v x,e⟫)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (weight_pos v x i).le (sq_nonneg _))
  have heq : (∑ i, weight v x i*(⟪v i,e⟫-⟪grad v x,e⟫)^2) =
      -(∑ i, weight v x i*⟪grad v x-v i,e⟫*⟪v i,e⟫) := by
    simp_rw [inner_sub_left]
    have hp (i : ι) : weight v x i*(⟪v i,e⟫-⟪grad v x,e⟫)^2 +
        weight v x i*(⟪grad v x,e⟫-⟪v i,e⟫)*⟪v i,e⟫ =
        weight v x i*⟪grad v x,e⟫^2 - (weight v x i*⟪v i,e⟫)*⟪grad v x,e⟫ := by ring
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hp i)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      sum_weight, one_mul, ← inner_grad] at hh
    nlinarith only [hh]
  rw [heq] at hvariance
  unfold hess
  simp only [sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    sum_inner, real_inner_smul_left, innerSL_apply_apply, ← mul_assoc]
  linarith only [hvariance]

end GaussianPropeller.SoftMin

namespace GaussianPropeller.SoftMin
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma concave_of_hessian {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x)
    (hK : ∀ x e, ⟪K x e,e⟫ ≤ 0) : ConcaveOn ℝ univ f := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  let d := y-x
  have hline (s : ℝ) : HasDerivAt (fun r : ℝ => x+r•d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have hdf (s : ℝ) : HasDerivAt (fun r : ℝ => f (x+r•d)) ⟪g (x+s•d),d⟫ s := by
    simpa only [Function.comp_def, innerSL_apply_apply] using (hf (x+s•d)).comp_hasDerivAt s (hline s)
  have hdg (s : ℝ) : HasDerivAt (fun r : ℝ => ⟪g (x+r•d),d⟫) ⟪K (x+s•d) d,d⟫ s := by
    simpa using ((hg (x+s•d)).comp_hasDerivAt s (hline s)).inner ℝ (hasDerivAt_const s d)
  have hant : Antitone (fun s : ℝ => ⟪g (x+s•d),d⟫) := antitone_of_hasDerivAt_nonpos hdg (fun s => hK _ _)
  have hconc : ConcaveOn ℝ univ (fun s : ℝ => f (x+s•d)) :=
    Antitone.concaveOn_univ_of_deriv (fun s => (hdf s).differentiableAt) (by
      intro s t hst
      rw [(hdf s).deriv, (hdf t).deriv]
      exact hant hst)
  have hh := hconc.2 (mem_univ (0:ℝ)) (mem_univ (1:ℝ)) ha hb hab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul] at hh
  have heq : x+b•d = a•x+b•y := by
    dsimp [d]
    have haeq : a=1-b := by linarith only [hab]
    rw [haeq]
    module
  simpa only [heq, d, add_sub_cancel, smul_eq_mul] using hh

lemma value_concave {ι : Type uι} [Fintype ι] [Nonempty ι] (v : ι → E) :
    ConcaveOn ℝ univ (value v) := concave_of_hessian (value_fderiv v) (grad_fderiv v) (hess_nonpos v)

end GaussianPropeller.SoftMin

namespace GaussianPropeller.SoftMin
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma value_le_score [Nonempty ι] (v : ι → E) (x : E) (i : ι) : value v x ≤ ⟪v i,x⟫ := by
  have hh : Real.exp (-⟪v i,x⟫) ≤ Z v x := by
    apply Finset.single_le_sum (f := fun j => Real.exp (-⟪v j,x⟫))
    · intro j _; exact (Real.exp_pos _).le
    · exact Finset.mem_univ i
  have hl := Real.log_le_log (Real.exp_pos _) hh
  rw [Real.log_exp] at hl
  dsimp only [value]
  linarith only [hl]

lemma value_tendsto_atBot (v : ι → E) (x : E) (i : ι) (hi : ⟪v i,x⟫ < 0) :
    Tendsto (fun n : ℕ => value (fun j => (n:ℝ) • v j) x) atTop atBot := by
  have hh : Tendsto (fun n : ℕ => (n:ℝ)*⟪v i,x⟫) atTop atBot :=
    tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hi
  apply tendsto_atBot_mono (fun n => ?_) hh
  simpa only [real_inner_smul_left] using value_le_score (fun j => (n:ℝ) • v j) x i

lemma value_tendsto_atTop (v : ι → E) (x : E) (hi : ∀ i, 0 < ⟪v i,x⟫) :
    Tendsto (fun n : ℕ => value (fun j => (n:ℝ) • v j) x) atTop atTop := by
  have hz : Tendsto (fun n : ℕ => Z (fun j => (n:ℝ) • v j) x) atTop (𝓝 0) := by
    have hh (i : ι) : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ)*⟪v i,x⟫)) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      simpa only [neg_mul, mul_neg] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const_of_neg (neg_neg_of_pos (hi i))
    have ht := tendsto_finsetSum Finset.univ (fun i _ => hh i)
    simpa only [Z, real_inner_smul_left, neg_mul, Finset.sum_const_zero] using ht
  have hzn : Tendsto (fun n : ℕ => Z (fun j => (n:ℝ) • v j) x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, Filter.Eventually.of_forall (fun n => Z_pos _ _)⟩
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hzn)

end GaussianPropeller.SoftMin

end OAI

-- ---- from OAI.Probability.GaussianPropeller.ConeConcavity ----
namespace OAI

universe uX uι uκ

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

omit [Nonempty κ] in
lemma measurableSet_shifted [Nonempty κ] (v : κ → E) (x : E) : MeasurableSet (shifted v x) := by
  change MeasurableSet {y : E | ∀ i, 0 ≤ ⟪v i,x+y⟫}
  simpa only [ofPred_forall] using MeasurableSet.iInter (fun i =>
    measurableSet_le (measurable_const : Measurable (fun _ : E => (0:ℝ)))
      (show Measurable (fun y : E => ⟪v i,x+y⟫) by fun_prop))

lemma gaussian_hyperplane_null (z : E) (hz : z ≠ 0) (c : ℝ) :
    γ {x | ⟪z,x⟫ = c} = 0 := by
  let L : StrongDual ℝ E := innerSL ℝ z
  have hL : L ≠ 0 := by
    intro heq
    have hx : ⟪z,z⟫ = 0 := by
      have h := DFunLike.congr_fun heq z
      simpa [L] using h
    exact hz (inner_self_eq_zero.mp hx)
  have hv : (variance L γ).toNNReal ≠ 0 := by
    rw [variance_dual_stdGaussian]
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hL)))
  have instN : NullSingletonClass (gaussianReal (∫ x, L x ∂γ) (variance L γ).toNNReal) :=
    nullSingletonClass_gaussianReal hv
  have h := congrArg (fun μ : Measure ℝ => μ {c}) (IsGaussian.map_eq_gaussianReal (μ := γ) L)
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton c), measure_singleton] at h
  exact h

omit [Nonempty κ] in
lemma ae_no_boundary [Nonempty κ] (v : κ → E) (hv : ∀ i, v i ≠ 0) (x : E) :
    ∀ᵐ y ∂γ, ∀ i, ⟪v i,x+y⟫ ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  have hh := gaussian_hyperplane_null (v i) (hv i) (-⟪v i,x⟫)
  have hh' : ∀ᵐ y ∂γ, ⟪v i,y⟫ ≠ -⟪v i,x⟫ := by
    rw [ae_iff]
    simpa only [not_not] using hh
  filter_upwards [hh'] with y hy
  rw [inner_add_right]
  intro hzero
  apply hy
  linarith only [hzero]

lemma cdf_softmin_limit (v : κ → E) (y : E) (hy : ∀ i, ⟪v i,y⟫ ≠ 0) :
    Tendsto (fun n : ℕ => Φ (SoftMin.value (fun i => (n:ℝ) • v i) y)) atTop
      (𝓝 ((cone v).indicator (fun _ => (1:ℝ)) y)) := by
  classical
  by_cases hmem : y ∈ cone v
  · rw [Set.indicator_of_mem hmem]
    exact tendsto_Φ_atTop.comp (SoftMin.value_tendsto_atTop v y
      (fun i => lt_of_le_of_ne (hmem i) (Ne.symm (hy i))))
  · rw [Set.indicator_of_notMem hmem]
    simp only [cone, mem_ofPred_eq, not_forall, not_le] at hmem
    obtain ⟨i,hi⟩ := hmem
    exact tendsto_Φ_atBot.comp (SoftMin.value_tendsto_atBot v y i hi)

lemma prob_limit (v : κ → E) (hv : ∀ i, v i ≠ 0) (x : E) :
    Tendsto (fun n : ℕ => HeatConvolution.heat
      (fun y => Φ (SoftMin.value (fun i => (n:ℝ) • v i) y)) 1 x) atTop (𝓝 (prob v x)) := by
  classical
  have hlim := tendsto_integral_of_dominated_convergence (μ := γ) (bound := fun _ : E => (1:ℝ))
    (F := fun n : ℕ => fun y : E => Φ (SoftMin.value (fun i => (n:ℝ) • v i) (x+y)))
    (f := fun y : E => (cone v).indicator (fun _ => (1:ℝ)) (x+y)) ?_ (integrable_const _) ?_ ?_
  · convert hlim using 1
    · funext n; simp only [HeatConvolution.heat, Real.sqrt_one, one_smul]
    · rw [show (fun y : E => (cone v).indicator (fun _ => (1:ℝ)) (x+y)) =
        (shifted v x).indicator (fun _ => (1:ℝ)) by
          funext y; rfl]
      rw [integral_indicator (measurableSet_shifted v x), setIntegral_const]
      simp only [prob, smul_eq_mul, mul_one]
  · intro n
    have hc : Continuous (SoftMin.value (fun i => (n:ℝ) • v i)) :=
      continuous_iff_continuousAt.mpr (fun y => (SoftMin.value_fderiv _ y).continuousAt)
    exact (continuous_Φ.comp (hc.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · intro n
    exact ae_of_all _ (fun y => SmoothCDF.cdf_bound _ _)
  · filter_upwards [ae_no_boundary v hv x] with y hy
    exact cdf_softmin_limit v (x+y) hy

lemma quantile_prob_concave (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) :
    ConcaveOn ℝ univ (fun x => q (prob v x)) := by
  have hv : ∀ i, v i ≠ 0 := by
    intro i hi; simpa only [hi, inner_zero_left, lt_self_iff_false] using he i
  have hc (n : ℕ) : ConcaveOn ℝ univ (qheat (SoftMin.value (fun i => (n:ℝ) • v i)) 1) := by
    let w : κ → E := fun i => (n:ℝ) • v i
    let L : ℝ≥0 := ∑ i, ‖w i‖₊
    have hL (i : κ) : ‖w i‖ ≤ L := by
      exact_mod_cast (Finset.single_le_sum (f := fun j => ‖w j‖₊) (fun j _ => bot_le) (Finset.mem_univ i))
    exact qheat_concave (SoftMin.value_fderiv w) (SoftMin.grad_fderiv w)
      (SoftMin.continuous_hess w) (SoftMin.grad_bound w hL)
      (SoftMin.hess_bound w L.coe_nonneg hL) (SoftMin.value_concave w) (by norm_num)
  have ht (x : E) : Tendsto (fun n : ℕ => qheat (SoftMin.value (fun i => (n:ℝ) • v i)) 1 x)
      atTop (𝓝 (q (prob v x))) := (continuousAt_q (prob_mem v e he x)).tendsto.comp (prob_limit v hv x)
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  exact le_of_tendsto_of_tendsto ((ht x).const_smul a |>.add ((ht y).const_smul b))
    (ht (a•x+b•y)) (Filter.Eventually.of_forall (fun n => (hc n).2 (mem_univ x) (mem_univ y) ha hb hab))

end GaussianPropeller.EhrhardCone

namespace GaussianPropeller.Quantile

lemma Φ_eq_gaussianReal (a : ℝ) : Φ a = (gaussianReal 0 1).real (Iic a) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal) ≠ 0),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  unfold Φ
  congr 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, φ]

lemma integrable_mul_φ : Integrable (fun x : ℝ => x*φ x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert hi using 1
  funext x
  simp only [φ]
  rw [show -x^2/2 = -(1/2:ℝ)*x^2 by ring]
  ring

lemma tendsto_φ_atBot : Tendsto φ atBot (𝓝 0) := by
  have htop : Tendsto (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-(1/2:ℝ)) < 0))
  have ht : Tendsto (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) atBot (𝓝 0) := by
    simpa only [Function.comp_def, neg_sq] using htop.comp tendsto_neg_atBot_atTop
  convert ht.const_mul ((Real.sqrt (2*Real.pi))⁻¹) using 1
  · funext x; unfold φ; congr 2; ring
  · simp only [mul_zero]

lemma left_first_moment (a : ℝ) : ∫ x in Iic a, x*φ x = -φ a := by
  have hd (x : ℝ) : HasDerivAt (fun x => -φ x) (x*φ x) x := by
    convert (hasDerivAt_φ x).neg using 1 <;> first | rfl | ring
  simpa only [neg_zero, sub_zero, Pi.neg_apply] using integral_Iic_of_hasDerivAt_of_tendsto
    (continuous_φ.neg.continuousWithinAt) (fun x _ => hd x)
    integrable_mul_φ.integrableOn (tendsto_φ_atBot.neg)

lemma integral_positive_cdf (a : ℝ) :
    ∫ x : ℝ, max (a-x) 0 ∂gaussianReal 0 1 = a*Φ a+φ a := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  simp only [show ∀ x : ℝ, gaussianPDFReal 0 1 x = φ x by
    intro x; simp only [gaussianPDFReal, φ, NNReal.coe_one, mul_one, sub_zero], smul_eq_mul]
  have heq : ∫ x : ℝ, φ x * max (a-x) 0 = ∫ x in Iic a, (a-x)*φ x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Iic a)]
    · exact setIntegral_congr_fun measurableSet_Iic (fun x hx => by
        rw [max_eq_left (sub_nonneg.mpr hx)]; ring)
    · intro x hx
      simp only [mem_Iic, not_le] at hx
      rw [max_eq_right (sub_nonpos.mpr hx.le), mul_zero]
  rw [heq]
  simp_rw [sub_mul]
  rw [integral_sub (integrable_φ.const_mul a).integrableOn integrable_mul_φ.integrableOn,
    integral_const_mul, left_first_moment]
  simp only [Φ, sub_neg_eq_add]

lemma tail_integrable {X : Type uX} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hi : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) :
    IntegrableOn (fun t : ℝ => μ.real {x | t ≤ f x}) (Ioi 0) := by
  apply integrable_toReal_of_lintegral_ne_top
  · exact (show Antitone (fun t : ℝ => μ {x | t ≤ f x}) from
      fun _ _ hst => measure_mono (fun _ h => hst.trans h)).measurable.aemeasurable
  · rw [← lintegral_eq_lintegral_meas_le μ hn hi.aemeasurable]
    exact hi.lintegral_lt_top.ne

lemma integral_cdf_tail (a c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Φ (a-c*u)) (Ioi 0) ∧
    (∫ u in Ioi (0:ℝ), Φ (a-c*u)) = (a*Φ a+φ a)/c := by
  let f : ℝ → ℝ := fun x => max (a-x) 0 / c
  have hf : Integrable f (gaussianReal 0 1) := by
    exact (((integrable_const a).sub (IsGaussian.integrable_id (μ := gaussianReal 0 1))).sup
      (integrable_const 0)).div_const c
  have hn : 0 ≤ᵐ[gaussianReal 0 1] f := ae_of_all _ (fun x => div_nonneg (le_max_right _ _) hc.le)
  have heq (u : ℝ) (hu : 0 < u) : (gaussianReal 0 1).real {x | u ≤ f x} = Φ (a-c*u) := by
    rw [Φ_eq_gaussianReal]
    congr 1
    ext x
    simp only [mem_ofPred_eq, mem_Iic, f, le_div_iff₀ hc, le_max_iff]
    have hh : ¬ u*c ≤ 0 := not_le.mpr (mul_pos hu hc)
    simp only [hh, or_false]
    constructor <;> intro h <;> nlinarith only [h]
  have hi : IntegrableOn (fun u : ℝ => Φ (a-c*u)) (Ioi 0) :=
    (tail_integrable hf hn).congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => heq u hu))
  refine ⟨hi,?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq,
    ← hf.integral_eq_integral_meas_le hn]
  rw [show f = fun x => max (a-x) 0 / c from rfl, integral_div, integral_positive_cdf]

end GaussianPropeller.Quantile

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

lemma measurableSet_cone (v : κ → E) : MeasurableSet (cone v) := by
  simpa only [shifted, zero_add, ofPred_mem_eq] using measurableSet_shifted v 0

lemma prob_line_deriv (v : κ → E) (h : E) :
    HasDerivAt (fun u : ℝ => prob v (-u • h))
      (-⟪h, ∫ x in cone v, x ∂γ⟫) 0 := by
  have heq (u : ℝ) : prob v (-u • h) =
      ((γ).map (fun x => x-u•h)).real (cone v) := by
    unfold prob
    rw [measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) (measurableSet_cone v)]
    apply congrArg ENNReal.toReal
    apply congrArg γ
    ext x
    change (-u•h+x ∈ cone v) ↔ (x-u•h ∈ cone v)
    rw [show -u•h+x = x-u•h by simp only [neg_smul, sub_eq_add_neg, add_comm]]
  simp_rw [heq]
  exact Translation.translation_derivative h (cone v) (measurableSet_cone v)

lemma prob_tangent (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) (h : E) (u : ℝ) :
    prob v (-u • h) ≤ Φ (q (prob v 0)-
      (⟪h, ∫ x in cone v, x ∂γ⟫ / φ (q (prob v 0)))*u) := by
  have hc : ConcaveOn ℝ univ (fun t : ℝ => q (prob v (-t•h))) := by
    refine ⟨convex_univ,?_⟩
    intro s _ t _ a b ha hb hab
    have hh := (quantile_prob_concave v e he).2 (mem_univ (-s•h)) (mem_univ (-t•h)) ha hb hab
    change a * q (prob v (-s•h))+b * q (prob v (-t•h)) ≤ q (prob v (-(a*s+b*t)•h))
    rw [show -(a*s+b*t)•h = a•(-s•h)+b•(-t•h) by module]
    exact hh
  have hd := (hasDerivAt_q (prob_mem v e he (-(0:ℝ)•h))).comp (0:ℝ) (prob_line_deriv v h)
  simp only [neg_zero, zero_smul] at hd
  have ht := concave_le_tangent hc (mem_univ 0) (mem_univ u) hd
  simp only [neg_zero, zero_smul, sub_zero] at ht
  have ht' : q (prob v (-u•h)) ≤ q (prob v 0)-
      (⟪h, ∫ x in cone v, x ∂γ⟫ / φ (q (prob v 0)))*u := by
    calc
      _ ≤ q (prob v 0) + (φ (q (prob v 0)))⁻¹ * (-⟪h, ∫ x in cone v, x ∂γ⟫) * u := ht
      _ = _ := by ring
  have hh := strictMono_Φ.monotone ht'
  rwa [Φ_q (prob_mem v e he (-u•h))] at hh

lemma integral_prob_upper (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫)
    (h : E) (hβ : 0 < ⟪h, ∫ x in cone v, x ∂γ⟫) :
    (∫ u in Ioi (0:ℝ), prob v (-u • h)) ≤
      φ (q (prob v 0)) * (q (prob v 0)*prob v 0+φ (q (prob v 0))) /
      ⟪h, ∫ x in cone v, x ∂γ⟫ := by
  let a := q (prob v 0)
  let c := ⟪h, ∫ x in cone v, x ∂γ⟫ / φ a
  have hc : 0 < c := div_pos hβ (φ_pos a)
  calc
    _ ≤ ∫ u in Ioi (0:ℝ), Φ (a-c*u) := integral_mono_of_nonneg
      (ae_of_all (volume.restrict (Ioi (0:ℝ))) (fun u => measureReal_nonneg))
      (integral_cdf_tail a c hc).1
      (ae_of_all _ (prob_tangent v e he h))
    _ = (a*Φ a+φ a)/c := (integral_cdf_tail a c hc).2
    _ = _ := by
      dsimp [a,c]
      rw [Φ_q (prob_mem v e he 0)]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

end GaussianPropeller.EhrhardCone

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.EhrhardCone
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open GaussianPropeller.Quantile


theorem solution.{uι,uκ} : type_of% @_root_.OAI.GaussianPropeller.EhrhardCone.integral_prob_upper.{uι,uκ} := @_root_.OAI.GaussianPropeller.EhrhardCone.integral_prob_upper.{uι,uκ}

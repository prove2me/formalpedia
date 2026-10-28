-- Prove2me | solution 1 for OAI.MomentSlab.variance_from_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T05:25:45.426029+00:00
-- url     : https://prove2.me/submissions/73e3e34a-12bd-4152-96a0-79b83316e99f

import Mathlib
import Definitions.Def_OAIW2LB000
import Theorems.Thm_OAI_MomentKernel_weak_kernel_smooth
import Theorems.Thm_OAI_MomentSlab_range_dual_bound

section
-- module Solutions.OAIW2_LogBM.LogVolume_BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Real

open MeasureTheory
open scoped Topology

open MeasureTheory FourierTransform Convolution
open scoped SchwartzMap

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology

open MeasureTheory TemperedDistribution FourierTransform LineDeriv
open scoped SchwartzMap ContDiff

open Filter Function
open scoped SchwartzMap Topology ContDiff

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology ContDiff
noncomputable section
namespace MatrixOperator
section
open MeasureTheory RealSmoothOperator Matrix
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma operator_actual (τ : Space ι → Matrix ι ι ℝ)
    (hτ : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (f : Space ι → ℝ) :
    operator (principal τ hτ++drift) f = A τ f := by
  ext x
  simp only [operator,principal,drift,List.map_append,List.sum_append,List.map_map,
    Function.comp_def,Finset.sum_map_toList,Finset.sum_apply,Pi.add_apply,
    Fintype.sum_prod_type,derivative,e,A,neg_mul,Finset.sum_neg_distrib]
  ring

end

open MeasureTheory RealSmoothOperator
open scoped ContDiff

end MatrixOperator

namespace WeightedRegularity
open MeasureTheory
open scoped ContDiff
variable {E : Type*} [MeasurableSpace E]

lemma integral_density (μ : Measure E) {ρ : E → ℝ}
    (hm : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x) (f : E → ℝ) :
    (∫ x, f x ∂densityMeasure μ ρ) = ∫ x, ρ x*f x ∂μ := by
  have hh := integral_withDensity_eq_integral_toReal_smul
    (μ:=μ) (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hm)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f
  simpa only [densityMeasure,Function.comp_apply,ENNReal.toReal_ofReal (hp _),smul_eq_mul] using hh

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]

omit [NormedSpace ℝ E] in
lemma integral_reflect (μ : Measure E) [μ.IsNegInvariant] {ρ : E → ℝ}
    (hm : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x) (he : ∀ x, ρ (-x)=ρ x)
    (f : E → ℝ) :
    (∫ x, f (-x) ∂densityMeasure μ ρ) = ∫ x, f x ∂densityMeasure μ ρ := by
  rw [integral_density μ hm hp,integral_density μ hm hp]
  have hh := integral_neg_eq_self (fun x => ρ x*f x) μ
  simpa only [he] using hh

end WeightedRegularity

end

open MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace WeightedCalculus


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma compact_D {f : E → ℝ} (hf : HasCompactSupport f) (v : E) :
    HasCompactSupport (D v f) := hf.fderiv_apply ℝ v

lemma D_add {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v : E) :
    D v (fun x => f x + g x) = fun x => D v f x + D v g x := by
  funext x
  simp only [D, fderiv_fun_add (hf x) (hg x), add_apply]

lemma D_sub {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v : E) :
    D v (fun x => f x - g x) = fun x => D v f x - D v g x := by
  funext x
  simp only [D, fderiv_fun_sub (hf x) (hg x), sub_apply]

lemma D_mul {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v : E) :
    D v (fun x => f x * g x) = fun x => D v f x * g x + f x * D v g x := by
  funext x
  simp only [D, fderiv_fun_mul (hf x) (hg x), add_apply,
    smul_apply, smul_eq_mul]
  ring

lemma D_comm {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v w : E) :
    D v (D w f) = D w (D v f) := by
  have hdf := (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  funext x
  change fderiv ℝ (fun x => fderiv ℝ f x w) x v =
    fderiv ℝ (fun x => fderiv ℝ f x v) x w
  simp only [fderiv_clm_apply (hdf x) (differentiableAt_const _),
    fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  apply hf.contDiffAt.isSymmSndFDerivAt _ v w
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)

lemma smooth_adjoint {V f : E → ℝ} (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (v : E) : ContDiff ℝ ∞ (adjoint V v f) := by
  exact ((smooth_D hV v).mul hf).sub (smooth_D hf v)

lemma compact_adjoint {V f : E → ℝ} (hf : HasCompactSupport f) (v : E) :
    HasCompactSupport (adjoint V v f) := by
  exact hf.mul_left.sub (compact_D hf v)

lemma smooth_weight {V : E → ℝ} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (weight V) := hV.neg.exp

lemma D_weight {V : E → ℝ} (hV : ContDiff ℝ ∞ V) (v : E) :
    D v (weight V) = fun x => -D v V x * weight V x := by
  funext x
  have hx := ((hV.differentiable (by simp) x).hasFDerivAt.neg.exp).fderiv
  change fderiv ℝ (fun x => Real.exp (-V x)) x v =
    -fderiv ℝ V x v * Real.exp (-V x)
  simpa [smul_apply, mul_comm] using congrArg (fun A => A v) hx

lemma commutator {V f : E → ℝ} (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (v w : E) : D w (adjoint V v f) =
      fun x => D w (D v V) x * f x + adjoint V v (D w f) x := by
  have hV' := (smooth_D hV v).differentiable (by simp)
  have hf' := (smooth_D hf v).differentiable (by simp)
  unfold adjoint
  rw [D_sub (f := fun x => D v V x * f x) (g := D v f)
      (fun x => (hV' x).mul (hf.differentiable (by simp) x)) hf',
    D_mul hV' (hf.differentiable (by simp)), D_comm hf w v]
  funext x
  ring

section FiniteDirections

variable {ι : Type*} [Fintype ι]

lemma D_sum (f : ι → E → ℝ) (hf : ∀ i, Differentiable ℝ (f i)) (v : E) :
    D v (fun x => ∑ i, f i x) = fun x => ∑ i, D v (f i) x := by
  funext x
  simp only [D, fderiv_fun_sum (fun i _ => hf i x), sum_apply]

lemma smooth_sum (f : ι → E → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    ContDiff ℝ ∞ (fun x => ∑ i, f i x) := ContDiff.sum (fun i _ => hf i)

omit [NormedSpace ℝ E] in
lemma compact_sum (f : ι → E → ℝ) (hf : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i, f i x) := by
  have heq : (fun x => ∑ i, f i x) = ∑ i, f i := by
    funext x
    exact (Finset.sum_apply x Finset.univ f).symm
  rw [heq]
  exact HasCompactSupport.finset_sum (fun i _ => hf i)

lemma smooth_divergence {V : E → ℝ} {e : ι → E} {W : ι → E → ℝ}
    (hV : ContDiff ℝ ∞ V) (hW : ∀ i, ContDiff ℝ ∞ (W i)) :
    ContDiff ℝ ∞ (divergence V e W) :=
  smooth_sum _ (fun i => smooth_adjoint hV (hW i) (e i))

lemma D_divergence {V : E → ℝ} {e : ι → E} {W : ι → E → ℝ}
    (hV : ContDiff ℝ ∞ V) (hW : ∀ i, ContDiff ℝ ∞ (W i)) (v : E) :
    D v (divergence V e W) = fun x => ∑ i,
      (D v (D (e i) V) x * W i x + adjoint V (e i) (D v (W i)) x) := by
  unfold divergence
  rw [D_sum _ (fun i => (smooth_adjoint hV (hW i) (e i)).differentiable (by simp))]
  simp_rw [commutator hV (hW _) _ v]

end FiniteDirections


variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [Measure.IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] in
lemma integrable_weighted {V f : E → ℝ} (hV : ContDiff ℝ ∞ V)
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x => f x * weight V x) μ :=
  (hf.mul (smooth_weight hV).continuous).integrable_of_hasCompactSupport hfc.mul_right

theorem integration_by_parts {V f g : E → ℝ} (hV : ContDiff ℝ ∞ V)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfc : HasCompactSupport f)
    (v : E) :
    expectation μ V (fun x => D v g x * f x) =
      expectation μ V (fun x => g x * adjoint V v f x) := by
  let fw : E → ℝ := fun x => f x * weight V x
  have hfw : ContDiff ℝ ∞ fw := hf.mul (smooth_weight hV)
  have hfwc : HasCompactSupport fw := hfc.mul_right
  have hi₁ : Integrable (fun x => D v fw x * g x) μ :=
    ((smooth_D hfw v).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (compact_D hfwc v).mul_right
  have hi₂ : Integrable (fun x => fw x * D v g x) μ :=
    (hfw.continuous.mul (smooth_D hg v).continuous).integrable_of_hasCompactSupport
      hfwc.mul_right
  have hi₃ : Integrable (fun x => fw x * g x) μ :=
    (hfw.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfwc.mul_right
  have hp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun x _ => hfw.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)
  calc
    _ = ∫ x, fw x * D v g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [expectation, fw]
      ring
    _ = -∫ x, D v fw x * g x ∂μ := hp
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [fw] at *
      rw [D_mul (hf.differentiable (by simp))
        ((smooth_weight hV).differentiable (by simp)), D_weight hV v]
      dsimp [adjoint]
      ring

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] in
lemma expectation_sum {V : E → ℝ} (hV : ContDiff ℝ ∞ V)
    (f : ι → E → ℝ) (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    expectation μ V (fun x => ∑ i, f i x) = ∑ i, expectation μ V (f i) := by
  simp only [expectation, Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => integrable_weighted μ hV (hf i) (hfc i))

lemma divergence_adjoint {V g : E → ℝ} (e : ι → E) (W : ι → E → ℝ)
    (hV : ContDiff ℝ ∞ V) (hW : ∀ i, ContDiff ℝ ∞ (W i))
    (hg : ContDiff ℝ ∞ g) (hWc : ∀ i, HasCompactSupport (W i)) :
    expectation μ V (fun x => g x * divergence V e W x) =
      ∑ i, expectation μ V (fun x => D (e i) g x * W i x) := by
  have heq : (fun x => g x * divergence V e W x) =
      fun x => ∑ i, g x * adjoint V (e i) (W i) x := by
    funext x
    simp only [divergence, Finset.mul_sum]
  rw [heq, expectation_sum μ hV (fun i x => g x * adjoint V (e i) (W i) x)
    (fun i => hg.continuous.mul (smooth_adjoint hV (hW i) (e i)).continuous)
    (fun i => (compact_adjoint (V := V) (hWc i) (e i)).mul_left)]
  apply Finset.sum_congr rfl
  intro i _
  exact (integration_by_parts μ hV (hW i) hg (hWc i) (e i)).symm


end WeightedCalculus

namespace MomentCoordinates

open WeightedCalculus Matrix
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma basis_sum (v : Space ι) : ∑ i, v i • basis i = v := by
  ext j
  simp [basis, Finset.sum_apply, Pi.single_apply]

lemma linear_coordinates (L : Space ι →L[ℝ] ℝ) (v : Space ι) :
    L v = ∑ i, L (basis i) * v i := by
  conv_lhs => rw [← basis_sum v]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma pd_comp {f : Space ι → ℝ} {F : Space ι → Space ι}
    (hf : Differentiable ℝ f) (hF : Differentiable ℝ F) (j : ι) :
    pd j (f ∘ F) = fun x => ∑ i, pd i f (F x) *
      pd j (fun y => F y i) x := by
  funext x
  simp only [pd, D, fderiv_comp x (hf (F x)) (hF x),
    ContinuousLinearMap.comp_apply]
  rw [linear_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_apply (hF x) i]
  rfl

lemma smooth_grad {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (grad f) := contDiff_pi.mpr (fun i => smooth_pd hf i)

lemma pd_comm {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (i j : ι) :
    pd i (pd j f) = pd j (pd i f) := D_comm hf _ _

lemma hess_symm {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (x : Space ι) (i j : ι) :
    hess f x i j = hess f x j i := congrFun (pd_comm hf j i) x

lemma pd_comp_grad {f φ : Space ι → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ) (a : ι) :
    pd a (f ∘ grad φ) = fun z => ∑ i, hess φ z a i * pd i f (grad φ z) := by
  rw [pd_comp (hf.differentiable (by simp)) ((smooth_grad hφ).differentiable (by simp))]
  funext z
  apply Finset.sum_congr rfl
  intro i _
  change pd i f (grad φ z) * hess φ z i a = _
  rw [hess_symm hφ z i a]
  ring

lemma pd_sum (g : ι → Space ι → ℝ) (hg : ∀ i, ContDiff ℝ ∞ (g i)) (a : ι) :
    pd a (fun z => ∑ i, g i z) = fun z => ∑ i, pd a (g i) z :=
  D_sum g (fun i => (hg i).differentiable (by simp)) (basis a)

lemma pd_sub {g k : Space ι → ℝ} (hg : ContDiff ℝ ∞ g)
    (hk : ContDiff ℝ ∞ k) (a : ι) :
    pd a (fun z => g z - k z) = fun z => pd a g z - pd a k z :=
  D_sub (hg.differentiable (by simp)) (hk.differentiable (by simp)) (basis a)

lemma pullA_divergence {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) :
    pullA φ f = divergence φ basis (fun i => pd i f ∘ grad φ) := by
  funext z
  simp only [pullA, divergence, adjoint, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change grad φ z i * pd i f (grad φ z) - ∑ j, hess φ z i j * hess f (grad φ z) i j =
    pd i φ z * pd i f (grad φ z) - pd i (pd i f ∘ grad φ) z
  rw [pd_comp_grad (smooth_pd hf i) hφ i]
  rfl

lemma smooth_pullA {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (pullA φ f) := by
  rw [pullA_divergence hφ hf]
  exact smooth_divergence hφ (fun i => (smooth_pd hf i).comp (smooth_grad hφ))

lemma P_pd {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (a i : ι) :
    P φ f a i = pd a (pd i f ∘ grad φ) := by
  rw [pd_comp_grad (smooth_pd hf i) hφ a]
  funext z
  apply Finset.sum_congr rfl
  intro j _
  change hess φ z a j * hess f (grad φ z) j i =
    hess φ z a j * hess f (grad φ z) i j
  rw [hess_symm hf _ j i]

lemma smooth_P {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (a i : ι) : ContDiff ℝ ∞ (P φ f a i) := by
  rw [P_pd hφ hf]
  exact smooth_pd ((smooth_pd hf i).comp (smooth_grad hφ)) a

theorem W_gradient {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (a : ι) :
    W φ f a = pd a (fun z => pullA φ f z - f (grad φ z)) := by
  change W φ f a = pd a (fun z => pullA φ f z - (f ∘ grad φ) z)
  rw [pd_sub (smooth_pullA hφ hf) (hf.comp (smooth_grad hφ))]
  have hder := D_divergence (e := basis) hφ
    (fun i => (smooth_pd hf i).comp (smooth_grad hφ)) (basis a)
  have hA : pd a (pullA φ f) = fun z => ∑ i,
      (hess φ z i a * pd i f (grad φ z) +
        adjoint φ (basis i) (pd a (pd i f ∘ grad φ)) z) := by
    rw [pullA_divergence hφ hf]
    exact hder
  rw [hA, pd_comp_grad hf hφ a]
  funext z
  simp only [W, divergence, Finset.sum_add_distrib]
  have hc : (∑ i, hess φ z i a * pd i f (grad φ z)) =
      ∑ i, hess φ z a i * pd i f (grad φ z) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hess_symm hφ z i a]
  rw [hc]
  simp_rw [← P_pd hφ hf]
  ring

lemma compact_pulled_pd {φ f : Space ι → ℝ} (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) (i : ι) :
    HasCompactSupport (pd i f ∘ grad φ) := by
  rw [← hΦ]
  exact (compact_D hfc (basis i)).comp_homeomorph Φ

lemma compact_P {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) (a i : ι) :
    HasCompactSupport (P φ f a i) := by
  rw [P_pd hφ hf]
  exact compact_D (compact_pulled_pd hfc Φ hΦ i) (basis a)

theorem hessian_identity (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]
    {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (Φ : Space ι ≃ₜ Space ι)
    (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    expectation μ φ (fun z => pullA φ f z * (pullA φ f z - f (grad φ z))) =
      ∑ a, ∑ k, expectation μ φ (fun z => P φ f k a z * P φ f a k z) := by
  let g : Space ι → ℝ := fun z => pullA φ f z - f (grad φ z)
  have hg : ContDiff ℝ ∞ g := (smooth_pullA hφ hf).sub (hf.comp (smooth_grad hφ))
  calc
    _ = expectation μ φ (fun z => g z *
        divergence φ basis (fun i => pd i f ∘ grad φ) z) := by
      congr 1
      funext z
      rw [← pullA_divergence hφ hf]
      dsimp [g]
      ring
    _ = ∑ a, expectation μ φ (fun z => pd a g z * pd a f (grad φ z)) :=
      divergence_adjoint μ basis _ hφ
        (fun i => (smooth_pd hf i).comp (smooth_grad hφ)) hg
        (compact_pulled_pd hfc Φ hΦ)
    _ = ∑ a, expectation μ φ (fun z => pd a f (grad φ z) * W φ f a z) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      funext z
      rw [W_gradient hφ hf]
      change pd a g z * pd a f (grad φ z) = pd a f (grad φ z) * pd a g z
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      change expectation μ φ (fun z => (pd a f ∘ grad φ) z *
        divergence φ basis (P φ f a) z) = _
      rw [divergence_adjoint μ basis _ hφ (smooth_P hφ hf a)
        ((smooth_pd hf a).comp (smooth_grad hφ)) (compact_P hφ hf hfc Φ hΦ a)]
      apply Finset.sum_congr rfl
      intro k _
      rw [P_pd hφ hf k a]
      rfl

end MomentCoordinates
end

open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace MomentDifferential
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth_det : ContDiff ℝ ∞ (fun A : Matrix ι ι ℝ => A.det) :=
  (detMultilinear (ι := ι)).contDiff

lemma det_updateRow_eq (A : Matrix ι ι ℝ) (i : ι) (v : ι → ℝ) :
    (A.updateRow i v).det = ∑ j, A.adjugate j i * v j := by
  have h := congrFun (Matrix.cramer_eq_adjugate_mulVec Aᵀ v) i
  simpa only [Matrix.cramer_apply, Matrix.updateCol_transpose,
    Matrix.det_transpose, ← Matrix.adjugate_transpose, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply] using h

lemma det_linearDeriv (A B : Matrix ι ι ℝ) :
    detMultilinear.linearDeriv A B = (A.adjugate * B).trace := by
  change detMultilinear.linearDeriv (fun i j => A i j) (fun i j => B i j) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (A.updateRow i (B i)).det) = _
  simp_rw [det_updateRow_eq]
  rw [Finset.sum_comm]
  rfl

theorem fderiv_det_apply (A B : Matrix ι ι ℝ) :
    fderiv ℝ (fun A : Matrix ι ι ℝ => A.det) A B = (A.adjugate * B).trace := by
  change fderiv ℝ (detMultilinear (ι := ι)) A B = _
  rw [(detMultilinear.hasFDerivAt A).fderiv]
  exact det_linearDeriv A B

lemma smooth_matrix_det {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z => A z i j)) :
    ContDiff ℝ ∞ (fun z => (A z).det) :=
  smooth_det.comp (contDiff_pi.mpr (fun i => contDiff_pi.mpr (hA i)))

omit [DecidableEq ι] in
lemma fderiv_matrix_apply {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z => A z i j)) (v z : E) :
    fderiv ℝ A z v = md v A z := by
  have hd : ∀ i, Differentiable ℝ (fun z j => A z i j) := fun i =>
    (contDiff_pi.mpr (hA i)).differentiable (by simp)
  change fderiv ℝ (fun z i j => A z i j) z v = _
  rw [fderiv_pi (fun i => hd i z)]
  ext i j
  change fderiv ℝ (fun z j => A z i j) z v j = _
  rw [fderiv_pi (fun j => (hA i j).differentiable (by simp) z)]
  rfl

theorem fderiv_logdet {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z => A z i j))
    (hne : ∀ z, (A z).det ≠ 0) (v z : E) :
    fderiv ℝ (fun z => Real.log (A z).det) z v =
      ((A z)⁻¹ * md v A z).trace := by
  have hAd : Differentiable ℝ A :=
    (contDiff_pi.mpr (fun i => contDiff_pi.mpr (hA i))).differentiable (by simp)
  rw [((smooth_matrix_det hA).differentiable (by simp) z).hasFDerivAt.log (hne z) |>.fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]
  have hc := fderiv_comp z (smooth_det.differentiable (by simp) (A z)) (hAd z)
  change (A z).det⁻¹ * fderiv ℝ ((fun A : Matrix ι ι ℝ => A.det) ∘ A) z v = _
  rw [hc, ContinuousLinearMap.comp_apply]
  erw [fderiv_det_apply (A z) (fderiv ℝ A z v)]
  rw [fderiv_matrix_apply hA]
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

end MomentDifferential

namespace MomentEquation
open WeightedCalculus MomentCoordinates MomentDifferential
open scoped ContDiff Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pd_add {f g : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : ι) : pd i (fun z => f z + g z) = fun z => pd i f z + pd i g z :=
  D_add (hf.differentiable (by simp)) (hg.differentiable (by simp)) _

lemma pd_mul {f g : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : ι) : pd i (fun z => f z * g z) = fun z => pd i f z * g z + f z * pd i g z :=
  D_mul (hf.differentiable (by simp)) (hg.differentiable (by simp)) _

lemma C_symm_first {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : ι)
    (z : Space ι) (a b : ι) : C φ i z a b = C φ a z i b := by
  change pd i (pd b (pd a φ)) z = pd a (pd b (pd i φ)) z
  rw [pd_comm (smooth_pd hφ a) i b, pd_comm (smooth_pd hφ i) a b,
    pd_comm hφ i a]

lemma pd_logdet {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hne : ∀ z, (hess φ z).det ≠ 0) (i : ι) :
    pd i (fun z => Real.log (hess φ z).det) =
      fun z => ((hess φ z)⁻¹ * C φ i z).trace := by
  funext z
  exact fderiv_logdet (smooth_hess hφ) hne (basis i) z

theorem first_moment {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {k : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + k - φ z)
    (i : ι) (z : Space ι) :
    (∑ j, hess φ z i j * pd j V (grad φ z)) =
      grad φ z i + ((hess φ z)⁻¹ * C φ i z).trace := by
  have hf : (fun z => Real.log (hess φ z).det) =
      (fun z => (V ∘ grad φ) z + k - φ z) := funext heq
  have hd := congrArg (fun f => pd i f z) hf
  rw [pd_logdet hφ hne, pd_sub ((hV.comp (smooth_grad hφ)).add contDiff_const) hφ,
    pd_add (hV.comp (smooth_grad hφ)) contDiff_const, pd_comp_grad hV hφ i] at hd
  simp only [pd, D, fderiv_const_apply, _root_.zero_apply, add_zero] at hd
  change _ = pd i φ z + _
  dsimp only [pd, D]
  linarith

lemma hess_transpose {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (z : Space ι) :
    (hess φ z)ᵀ = hess φ z := by
  ext i j
  exact hess_symm hφ z j i

end MomentEquation

namespace TargetCoordinates
open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma target_pull {φ : Space ι → ℝ} (Φ : Space ι ≃ₜ Space ι)
    (hΦ : (Φ : Space ι → Space ι) = grad φ) (g : Space ι → ℝ) :
    target Φ g ∘ grad φ = g := by
  rw [← hΦ]
  funext z
  exact congrArg g (Φ.symm_apply_apply z)

lemma target_apply {φ : Space ι → ℝ} (Φ : Space ι ≃ₜ Space ι)
    (hΦ : (Φ : Space ι → Space ι) = grad φ) (g : Space ι → ℝ) (z : Space ι) :
    target Φ g (grad φ z) = g z := congrFun (target_pull Φ hΦ g) z

omit [DecidableEq ι] in
lemma smooth_target {Φ : Space ι ≃ₜ Space ι}
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) {g : Space ι → ℝ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (target Φ g) := hg.comp hInv

lemma target_chain {φ g : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hg : ContDiff ℝ ∞ g) (Φ : Space ι ≃ₜ Space ι)
    (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (i : ι) (z : Space ι) :
    pd i g z = ∑ j, hess φ z i j * pd j (target Φ g) (grad φ z) := by
  have he := congrFun (pd_comp_grad (smooth_target hInv hg) hφ i) z
  rw [target_pull Φ hΦ] at he
  exact he

lemma pd_target {φ g : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hg : ContDiff ℝ ∞ g) (hne : ∀ z, (hess φ z).det ≠ 0)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (i : ι) (z : Space ι) :
    pd i (target Φ g) (grad φ z) = ∑ j, (hess φ z)⁻¹ i j * pd j g z := by
  have he : grad g z = hess φ z *ᵥ grad (target Φ g) (grad φ z) := by
    ext k
    exact target_chain hφ hg Φ hΦ hInv k z
  change grad (target Φ g) (grad φ z) i = ((hess φ z)⁻¹ *ᵥ grad g z) i
  rw [he, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hne z)),
    Matrix.one_mulVec]

lemma stein {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V)
    (hne : ∀ z, (hess φ z).det ≠ 0) {c : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + c - φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (i : ι) (z : Space ι) :
    divergence V basis (fun j => target Φ (fun y => hess φ y i j)) (grad φ z) = grad φ z i := by
  change (∑ j, (pd j V (grad φ z) * target Φ (fun y => hess φ y i j) (grad φ z) -
    pd j (target Φ (fun y => hess φ y i j)) (grad φ z))) = _
  simp_rw [target_apply Φ hΦ, pd_target hφ (smooth_hess hφ _ _) hne Φ hΦ hInv]
  rw [Finset.sum_sub_distrib]
  have ht : (∑ j, ∑ k, (hess φ z)⁻¹ j k * pd k (fun y => hess φ y i j) z) =
      ((hess φ z)⁻¹ * C φ i z).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    change (hess φ z)⁻¹ j k * C φ k z i j = (hess φ z)⁻¹ j k * C φ i z k j
    rw [C_symm_first hφ k z i j]
  rw [ht]
  have hm := first_moment hφ hV hne heq i z
  have hs : (∑ j, pd j V (grad φ z) * hess φ z i j) =
      ∑ j, hess φ z i j * pd j V (grad φ z) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs, hm]
  ring

lemma divergence_product {V : Space ι → ℝ} (P : ι → Space ι → ℝ)
    (T : ι → ι → Space ι → ℝ) (hP : ∀ k, ContDiff ℝ ∞ (P k))
    (hT : ∀ k j, ContDiff ℝ ∞ (T k j)) :
    divergence V basis (fun j z => ∑ k, P k z * T k j z) = fun z =>
      (∑ k, P k z * divergence V basis (T k) z) -
      ∑ k, ∑ j, pd j (P k) z * T k j z := by
  funext z
  change (∑ j, (pd j V z * ∑ k, P k z * T k j z -
    pd j (fun y => ∑ k, P k y * T k j y) z)) = _
  simp_rw [pd_sum _ (fun k => (hP k).mul (hT k _))]
  simp_rw [pd_mul (hP _) (hT _ _)]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    divergence, adjoint]
  rw [Finset.sum_comm (f := fun j k => pd j V z * (P k z * T k j z)),
    Finset.sum_comm (f := fun j k => pd j (P k) z * T k j z),
    Finset.sum_comm (f := fun j k => P k z * pd j (T k j) z)]
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
  have he : (∑ k, ∑ j, pd j V z * P k z * T k j z) =
      ∑ k, ∑ j, P k z * D (basis j) V z * T k j z := by
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    change pd j V z * P k z * T k j z = P k z * pd j V z * T k j z
    ring
  rw [he]
  change _ - (_ + _) = _ - _ - _
  dsimp only [pd]
  ring

lemma row_adjoint {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V)
    (hne : ∀ z, (hess φ z).det ≠ 0) {c : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + c - φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (P : ι → Space ι → ℝ) (hP : ∀ k, ContDiff ℝ ∞ (P k)) (z : Space ι) :
    divergence V basis (fun j => target Φ (fun y => ∑ k, P k y * hess φ y k j))
      (grad φ z) = divergence φ basis P z := by
  have he : (fun j => target Φ (fun y => ∑ k, P k y * hess φ y k j)) =
      fun j x => ∑ k, target Φ (P k) x * target Φ (fun y => hess φ y k j) x := rfl
  rw [he, divergence_product _ _ (fun k => smooth_target hInv (hP k))
    (fun k j => smooth_target hInv (smooth_hess hφ k j))]
  simp_rw [target_apply Φ hΦ, stein hφ hV hne heq Φ hΦ hInv]
  have hc (k : ι) : (∑ j, pd j (target Φ (P k)) (grad φ z) * hess φ z k j) = pd k (P k) z := by
    rw [target_chain hφ (hP k) Φ hΦ hInv k z]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hc]
  change _ = ∑ k, (pd k φ z * P k z - pd k (P k) z)
  rw [Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  change P k z * pd k φ z = pd k φ z * P k z
  ring

variable (μ : Measure (Space ι))

omit [DecidableEq ι] in
lemma source_integral {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (F : Space ι → ℝ) :
    (∫ z, F z ∂sourceMeasure μ φ) = expectation μ φ F := by
  rw [sourceMeasure, integral_withDensity_eq_integral_toReal_smul
    ((smooth_weight hφ).continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul, expectation]
  congr 1
  funext z
  rw [ENNReal.toReal_ofReal (show 0 ≤ weight φ z from le_of_lt (Real.exp_pos _))]
  ring

omit [DecidableEq ι] in
lemma target_integral {V : Space ι → ℝ} (hV : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z)
    (F : Space ι → ℝ) : (∫ x, F x ∂targetMeasure μ V Z) = normalizedE μ V Z F := by
  rw [targetMeasure, integral_withDensity_eq_integral_toReal_smul
    (((smooth_weight hV).continuous.div_const Z).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  change (∫ x, (ENNReal.ofReal (weight V x / Z)).toReal • F x ∂μ) = _
  have hw (x : Space ι) : 0 ≤ weight V x / Z := div_nonneg (le_of_lt (Real.exp_pos _)) hZ.le
  simp only [ENNReal.toReal_ofReal (hw _), smul_eq_mul]
  have he : (fun x => weight V x / Z * F x) = fun x => (F x * weight V x) / Z := by
    funext x
    ring
  rw [he, integral_div]
  rfl

lemma expectation_transport {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hmap : Measure.map (grad φ) (sourceMeasure μ φ) = targetMeasure μ V Z)
    (F : Space ι → ℝ) : expectation μ φ (F ∘ grad φ) = normalizedE μ V Z F := by
  rw [← source_integral μ hφ, ← target_integral μ hV hZ, ← hmap, ← hΦ]
  exact (Φ.measurableEmbedding.integral_map F).symm

end TargetCoordinates

namespace MomentOperator
open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation TargetCoordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma A_pull {φ f : Space ι → ℝ}
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    A Φ φ f ∘ grad φ = pullA φ f := by
  funext z
  have he : Φ.symm (grad φ z) = z := by rw [← hΦ]; exact Φ.symm_apply_apply z
  simp only [Function.comp_apply, A, tau, he, pullA]

lemma A_divergence {φ V f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0) {c : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + c - φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) :
    divergence V basis (flux Φ φ f) = A Φ φ f := by
  have he : flux Φ φ f = fun j => target Φ (fun z => ∑ k, pd k f (grad φ z) * hess φ z k j) := by
    funext j x
    change (∑ k, hess φ (Φ.symm x) j k * pd k f x) =
      ∑ k, pd k f (grad φ (Φ.symm x)) * hess φ (Φ.symm x) k j
    have hcancel : grad φ (Φ.symm x) = x := by rw [← hΦ]; exact Φ.apply_symm_apply x
    rw [hcancel]
    apply Finset.sum_congr rfl
    intro k _
    rw [hess_symm hφ _ j k]
    ring
  rw [he]
  funext x
  obtain ⟨z,rfl⟩ := Φ.surjective x
  rw [hΦ, row_adjoint hφ hV hne heq Φ hΦ hInv
    (fun k z => pd k f (grad φ z)) (fun k => (smooth_pd hf k).comp (smooth_grad hφ)) z]
  change divergence φ basis (fun k => pd k f ∘ grad φ) z = _
  rw [← pullA_divergence hφ hf]
  exact (congrFun (A_pull Φ hΦ) z).symm

variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

lemma hessian_identity_target {φ V f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {Z : ℝ} (hZ : 0 < Z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hmap : Measure.map (grad φ) (sourceMeasure μ φ) = targetMeasure μ V Z) :
    normalizedE μ V Z (fun x => (A Φ φ f x) * (A Φ φ f x - f x)) =
      normalizedE μ V Z (fun x => ∑ a, ∑ k,
        (tau Φ φ x * hess f x) k a * (tau Φ φ x * hess f x) a k) := by
  have ht := MomentCoordinates.hessian_identity μ hφ hf hfc Φ hΦ
  have hleft : (fun z => pullA φ f z * (pullA φ f z - f (grad φ z))) =
      (fun x => A Φ φ f x * (A Φ φ f x - f x)) ∘ grad φ := by
    rw [← A_pull Φ hΦ]
    rfl
  rw [hleft, expectation_transport μ hφ hV hZ Φ hΦ hmap] at ht
  have hs : expectation μ φ (fun z => ∑ a, ∑ k, P φ f k a z * P φ f a k z) =
      ∑ a, ∑ k, expectation μ φ (fun z => P φ f k a z * P φ f a k z) := by
    rw [expectation_sum μ hφ _ (fun a => (smooth_sum _ (fun k =>
      (smooth_P hφ hf k a).mul (smooth_P hφ hf a k))).continuous)
      (fun a => compact_sum _ (fun k => (compact_P hφ hf hfc Φ hΦ k a).mul_right))]
    apply Finset.sum_congr rfl
    intro a _
    exact expectation_sum μ hφ _ (fun k => ((smooth_P hφ hf k a).mul (smooth_P hφ hf a k)).continuous)
      (fun k => (compact_P hφ hf hfc Φ hΦ k a).mul_right)
  rw [← hs] at ht
  have hr : (fun z => ∑ a, ∑ k, P φ f k a z * P φ f a k z) =
      (fun x => ∑ a, ∑ k, (tau Φ φ x * hess f x) k a * (tau Φ φ x * hess f x) a k) ∘ grad φ := by
    funext z
    have hc : Φ.symm (grad φ z) = z := by rw [← hΦ]; exact Φ.symm_apply_apply z
    simp only [Function.comp_apply, tau, hc, Matrix.mul_apply, P]
  rw [hr, expectation_transport μ hφ hV hZ Φ hΦ hmap] at ht
  exact ht

end MomentOperator

namespace MomentMatrix

open Matrix
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_nonneg {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨Q, hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hQ]
  change 0 ≤ (Qᴴ * Q * B).trace
  rw [← Matrix.trace_mul_cycle Q B Qᴴ]
  exact (hB.mul_mul_conjTranspose_same Q).trace_nonneg

lemma trace_conjugate_nonneg {A H : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hH : Hᵀ = H) : 0 ≤ (A * H * A * H).trace := by
  have hc : (H * A * H).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hH] using
      hA.conjTranspose_mul_mul_same H
  simpa only [Matrix.mul_assoc] using trace_mul_nonneg hA hc

lemma quadratic_cs (a b c : ℝ) (h : ∀ t : ℝ, 0 ≤ c - 2 * t * b + t^2 * a) :
    b^2 ≤ a * c := by
  have hd := discrim_le_zero (a := a) (b := -2 * b) (c := c) (fun t => by
    have ht := h t
    nlinarith)
  dsimp [discrim] at hd
  nlinarith

omit [DecidableEq ι] in
lemma form_symm {H : Matrix ι ι ℝ} (hH : Hᵀ = H) (v w : ι → ℝ) :
    v ⬝ᵥ (H *ᵥ w) = w ⬝ᵥ (H *ᵥ v) := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hH, dotProduct_comm]

omit [DecidableEq ι] in
lemma form_nonneg {H : Matrix ι ι ℝ} (hH : H.PosSemidef) (v : ι → ℝ) :
    0 ≤ v ⬝ᵥ (H *ᵥ v) := by
  simpa only [star_trivial] using hH.dotProduct_mulVec_nonneg v

omit [DecidableEq ι] in
lemma form_quadratic {H : Matrix ι ι ℝ} (hH : Hᵀ = H)
    (v w : ι → ℝ) (t : ℝ) :
    (w - t • v) ⬝ᵥ (H *ᵥ (w - t • v)) =
      w ⬝ᵥ (H *ᵥ w) - 2 * t * (v ⬝ᵥ (H *ᵥ w)) + t^2 * (v ⬝ᵥ (H *ᵥ v)) := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [form_symm hH w v]
  ring


open MeasureTheory


end MomentMatrix

namespace DensityEnergy
open MeasureTheory Matrix WeightedCalculus
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma grad_mul {f g : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    grad (fun x => f x*g x) = fun x => g x • grad f x + f x • grad g x := by
  funext x i
  simpa only [grad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm (g x)] using
    congrFun (D_mul (hf.differentiable (by simp)) (hg.differentiable (by simp)) (e i)) x

lemma gamma_symm {τ : Space ι → Matrix ι ι ℝ} (hτ : ∀ x, (τ x)ᵀ = τ x)
    (f g : Space ι → ℝ) (x : Space ι) : gamma τ f g x = gamma τ g f x :=
  MomentMatrix.form_symm (hτ x) _ _

lemma gamma_nonneg {τ : Space ι → Matrix ι ι ℝ} (hτ : ∀ x, (τ x).PosSemidef)
    (f : Space ι → ℝ) (x : Space ι) : 0 ≤ gamma τ f f x :=
  MomentMatrix.form_nonneg (hτ x) _

lemma smooth_gamma {τ : Space ι → Matrix ι ι ℝ}
    (hτ : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j))
    {f g : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (gamma τ f g) := by
  unfold gamma grad dotProduct Matrix.mulVec
  apply ContDiff.sum; intro i _
  apply (smooth_D hf _).mul
  apply ContDiff.sum; intro j _
  exact (hτ i j).mul (smooth_D hg _)

lemma compact_gamma_left {τ : Space ι → Matrix ι ι ℝ} {f g : Space ι → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (gamma τ f g) := by
  unfold gamma grad dotProduct Matrix.mulVec
  exact compact_sum _ (fun i => (compact_D hf (e i)).mul_right)

lemma gamma_mul_left {τ : Space ι → Matrix ι ι ℝ} {f g h : Space ι → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Space ι) :
    gamma τ (fun x => f x*g x) h x =
      g x*gamma τ f h x + f x*gamma τ g h x := by
  unfold gamma
  rw [grad_mul hf hg]
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]

lemma gamma_cutoff_square {τ : Space ι → Matrix ι ι ℝ} {η w : Space ι → ℝ}
    (hη : ContDiff ℝ ∞ η) (hw : ContDiff ℝ ∞ w) (x : Space ι) :
    gamma τ (fun x => η x^2*w x) w x =
      η x^2*gamma τ w w x + 2*η x*w x*gamma τ η w x := by
  simp only [pow_two]
  rw [gamma_mul_left (hη.mul hη) hw, gamma_mul_left hη hη]
  ring

lemma cutoff_young {τ : Space ι → Matrix ι ι ℝ} (hτ : ∀ x, (τ x).PosSemidef)
    (η w : Space ι → ℝ) (x : Space ι) :
    -2*η x*w x*gamma τ η w x ≤
      (1/2)*η x^2*gamma τ w w x + 2*w x^2*gamma τ η η x := by
  have hp := MomentMatrix.form_nonneg (hτ x)
    (η x • grad w x + (2*w x) • grad η x)
  have hs : (τ x)ᵀ = τ x := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (hτ x).isHermitian.eq
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul] at hp
  rw [MomentMatrix.form_symm hs (grad w x) (grad η x)] at hp
  change _ ≤ (1/2)*η x^2*(grad w x ⬝ᵥ (τ x *ᵥ grad w x)) +
    2*w x^2*(grad η x ⬝ᵥ (τ x *ᵥ grad η x))
  unfold gamma
  nlinarith

theorem caccioppoli (μ : Measure (Space ι)) [IsFiniteMeasure μ]
    {τ : Space ι → Matrix ι ι ℝ}
    (hts : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j))
    (htp : ∀ x, (τ x).PosSemidef)
    {η w : Space ι → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hw : ContDiff ℝ ∞ w) (hiw : Integrable (fun x => w x^2) μ)
    (hzero : (∫ x, gamma τ (fun x => η x^2*w x) w x ∂μ) = 0)
    {c : ℝ} (hbound : ∀ x, gamma τ η η x ≤ c) :
    (∫ x, η x^2*gamma τ w w x ∂μ) ≤ 4*c*(∫ x, w x^2 ∂μ) := by
  have hcη : HasCompactSupport (fun x => η x^2) := by
    rw [show (fun x => η x^2) = η*η by ext x; simp only [Pi.mul_apply, pow_two]]
    exact hηc.mul_right
  have hc₂ : HasCompactSupport (fun x => 2*η x) := hηc.mul_left
  have hi₁ : Integrable (fun x => η x^2*gamma τ w w x) μ :=
    ((hη.pow 2).mul (smooth_gamma hts hw hw)).continuous.integrable_of_hasCompactSupport
      hcη.mul_right
  have hi₂ : Integrable (fun x => 2*η x*w x*gamma τ η w x) μ :=
    (((contDiff_const.mul hη).mul hw).mul (smooth_gamma hts hη hw)).continuous.integrable_of_hasCompactSupport
      hc₂.mul_right.mul_right
  have hi₃ : Integrable (fun x => w x^2*gamma τ η η x) μ :=
    ((hw.pow 2).mul (smooth_gamma hts hη hη)).continuous.integrable_of_hasCompactSupport
      (compact_gamma_left hηc).mul_left
  have het : (∫ x, η x^2*gamma τ w w x ∂μ) =
      -(∫ x, 2*η x*w x*gamma τ η w x ∂μ) := by
    simp_rw [gamma_cutoff_square hη hw] at hzero
    rw [integral_add hi₁ hi₂] at hzero
    linarith
  have hh := integral_mono hi₂.neg ((hi₁.const_mul (1/2)).add (hi₃.const_mul 2))
    (fun x => by simpa only [Pi.neg_apply, Pi.add_apply, neg_mul, mul_assoc] using cutoff_young htp η w x)
  simp only [Pi.neg_apply, Pi.add_apply] at hh
  rw [integral_neg, integral_add (hi₁.const_mul (1/2)) (hi₃.const_mul 2),
    integral_const_mul, integral_const_mul, ← het] at hh
  have hb := integral_mono hi₃ (hiw.const_mul c) (fun x => by
    simpa only [mul_comm c] using mul_le_mul_of_nonneg_left (hbound x) (sq_nonneg (w x)))
  rw [integral_const_mul] at hb
  nlinarith

end DensityEnergy
end

open scoped ContDiff Topology
noncomputable section
namespace SmoothCutoff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma base_smooth : ContDiff ℝ ∞ (base (E:=E) : E → ℝ) := (base (E:=E)).contDiff

lemma smooth (r : ℝ) : ContDiff ℝ ∞ (cutoff (E:=E) r) :=
  base_smooth.comp (contDiff_const.smul contDiff_id)

lemma nonneg (r : ℝ) (x : E) : 0 ≤ cutoff r x := (base (E:=E)).nonneg
lemma le_one (r : ℝ) (x : E) : cutoff r x ≤ 1 := (base (E:=E)).le_one

lemma eq_one {r : ℝ} (hr : 0 < r) {x : E} (hx : ‖x‖ ≤ r) : cutoff r x = 1 := by
  apply (base (E:=E)).one_of_mem_closedBall
  change dist (r⁻¹ • x) 0 ≤ (1:ℝ)
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  exact (inv_mul_le_iff₀ hr).mpr (by simpa using hx)

lemma eq_zero {r : ℝ} (hr : 0 < r) {x : E} (hx : 2*r ≤ ‖x‖) : cutoff r x = 0 := by
  apply (base (E:=E)).zero_of_le_dist
  change (2:ℝ) ≤ dist (r⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  exact (le_inv_mul_iff₀ hr).mpr (by nlinarith)

lemma compact {r : ℝ} (hr : 0 < r) : HasCompactSupport (cutoff (E:=E) r) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:E) (2*r))
  intro x hx
  apply eq_zero hr
  have : 2*r < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  exact this.le

lemma first (r : ℝ) (x : E) : fderiv ℝ (cutoff r) x =
    r⁻¹ • fderiv ℝ (base (E:=E) : E → ℝ) (r⁻¹ • x) := by
  have hb := base_smooth.differentiable (by simp) (r⁻¹ • x)
  have hs : HasFDerivAt (fun y : E => r⁻¹ • y) (r⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul r⁻¹
  have hc := hb.hasFDerivAt.comp x hs
  rw [show cutoff r = (base (E:=E) : E → ℝ) ∘ (fun y : E => r⁻¹ • y) from rfl, hc.fderiv]
  ext v
  simp

attribute [local instance] OAI.SmoothCutoff.dualNorm
attribute [local instance] OAI.SmoothCutoff.dualSpace
lemma second (r : ℝ) (x : E) : fderiv ℝ (fderiv ℝ (cutoff r)) x =
    (r⁻¹)^2 • fderiv ℝ (fderiv ℝ (base (E:=E) : E → ℝ)) (r⁻¹ • x) := by
  have he : fderiv ℝ (cutoff (E:=E) r) =
      fun y => r⁻¹ • fderiv ℝ (base (E:=E) : E → ℝ) (r⁻¹ • y) := funext (first r)
  rw [he]
  have hb := (base_smooth.fderiv_right (m:=∞) (by simp)).differentiable (by simp) (r⁻¹ • x)
  have hs : HasFDerivAt (fun y : E => r⁻¹ • y) (r⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul r⁻¹
  have hc := (hb.hasFDerivAt.comp x hs).const_smul r⁻¹
  calc
    _ = r⁻¹ • (fderiv ℝ (fderiv ℝ (base (E:=E) : E → ℝ)) (r⁻¹ • x)).comp
        (r⁻¹ • ContinuousLinearMap.id ℝ E) := hc.fderiv
    _ = _ := by
      ext v w
      simp [pow_two, mul_assoc]

lemma base_first_bound : ∃ C : ℝ, ∀ x : E,
    ‖fderiv ℝ (base (E:=E) : E → ℝ) x‖ ≤ C := by
  have h : Continuous (fderiv ℝ (base (E:=E) : E → ℝ)) :=
    ((base_smooth (E:=E)).fderiv_right (m:=∞) (by simp)).continuous
  exact ((base (E:=E)).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous h

lemma base_second_bound : ∃ C : ℝ, ∀ x : E,
    ‖fderiv ℝ (fderiv ℝ (base (E:=E) : E → ℝ)) x‖ ≤ C := by
  have h₁ : ContDiff ℝ ∞ (fderiv ℝ (base (E:=E) : E → ℝ)) :=
    (base_smooth (E:=E)).fderiv_right (m:=∞) (by simp)
  have h₂ : Continuous (fderiv ℝ (fderiv ℝ (base (E:=E) : E → ℝ))) :=
    h₁.continuous_fderiv (by simp)
  exact (((base (E:=E)).hasCompactSupport.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous h₂

lemma derivative_bounds : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ x : E,
    ‖fderiv ℝ (cutoff r) x‖ ≤ C/r ∧
    ‖fderiv ℝ (fderiv ℝ (cutoff r)) x‖ ≤ C/r^2 := by
  obtain ⟨C₁,hC₁⟩ := base_first_bound (E:=E)
  obtain ⟨C₂,hC₂⟩ := base_second_bound (E:=E)
  let C := max (max C₁ C₂) 1
  have hCC₁ : C₁ ≤ C := (le_max_left C₁ C₂).trans (le_max_left _ 1)
  have hCC₂ : C₂ ≤ C := (le_max_right C₁ C₂).trans (le_max_left _ 1)
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro r hr x
  have h₁ : ‖fderiv ℝ (base (E:=E) : E → ℝ) (r⁻¹ • x)‖ ≤ C := (hC₁ _).trans hCC₁
  have h₂ : ‖fderiv ℝ (fderiv ℝ (base (E:=E) : E → ℝ)) (r⁻¹ • x)‖ ≤ C := (hC₂ _).trans hCC₂
  constructor
  · rw [first, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h₁ (inv_nonneg.mpr hr.le)
  · rw [second]
    apply (ContinuousLinearMap.opNorm_smul_le ((r⁻¹)^2)
      (fderiv ℝ (fderiv ℝ (base (E:=E) : E → ℝ)) (r⁻¹ • x))).trans
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_eq_mul_inv, ← inv_pow]
    simpa only [mul_comm C] using mul_le_mul_of_nonneg_left h₂ (sq_nonneg (r⁻¹))

lemma eventually_one {r : ℝ} (hr : 0 < r) {x : E} (hx : ‖x‖ < r) :
    cutoff r =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hx] with y hy
  exact eq_one hr hy.le

lemma first_zero_inside {r : ℝ} (hr : 0 < r) {x : E} (hx : ‖x‖ < r) :
    fderiv ℝ (cutoff r) x = 0 := by
  rw [(eventually_one hr hx).fderiv_eq]
  exact fderiv_const_apply (1:ℝ)

lemma second_zero_inside {r : ℝ} (hr : 0 < r) {x : E} (hx : ‖x‖ < r) :
    fderiv ℝ (fderiv ℝ (cutoff r)) x = 0 := by
  have he : fderiv ℝ (cutoff r) =ᶠ[𝓝 x] (fun _ => (0:E →L[ℝ] ℝ)) := by
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hx] with y hy
    exact first_zero_inside hr hy
  rw [he.fderiv_eq]
  exact fderiv_const_apply _

end SmoothCutoff

namespace DensityEnergy
open MeasureTheory Matrix WeightedCalculus Filter
open scoped ContDiff Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma D_eventuallyEq {f g : Space ι → ℝ} {x : Space ι}
    (h : f =ᶠ[𝓝 x] g) (v : Space ι) : D v f =ᶠ[𝓝 x] D v g := by
  filter_upwards [h.fderiv (𝕜:=ℝ)] with y hy
  exact congrArg (fun L : Space ι →L[ℝ] ℝ => L v) hy

lemma A_congr {τ : Space ι → Matrix ι ι ℝ} {f g : Space ι → ℝ} {x : Space ι}
    (h : f =ᶠ[𝓝 x] g) : A τ f x = A τ g x := by
  unfold A
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    rw [(D_eventuallyEq h (e i)).eq_of_nhds]
  · apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [(D_eventuallyEq (D_eventuallyEq h (e j)) (e i)).eq_of_nhds]

lemma grad_congr {f g : Space ι → ℝ} {x : Space ι}
    (h : f =ᶠ[𝓝 x] g) : grad f x = grad g x := by
  funext i
  exact (D_eventuallyEq h (e i)).eq_of_nhds

lemma grad_zero_of_not_tsupport {f : Space ι → ℝ} {x : Space ι}
    (hx : x ∉ tsupport f) : grad f x = 0 := by
  have he : f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [grad_congr he]
  funext i
  simp [grad, D]

lemma extend_integration (μ : Measure (Space ι))
    {τ : Space ι → Matrix ι ι ℝ}
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    {f h : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) :
    (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ := by
  obtain ⟨R,hR⟩ := hhc.isBounded.subset_closedBall (0:Space ι)
  let r : ℝ := max R 0 + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let f' : Space ι → ℝ := fun x => SmoothCutoff.cutoff r x*f x
  have hs : ContDiff ℝ ∞ f' := (SmoothCutoff.smooth r).mul hf
  have hc : HasCompactSupport f' := (SmoothCutoff.compact hr).mul_right
  have he (x : Space ι) (hx : x ∈ tsupport h) : f' =ᶠ[𝓝 x] f := by
    have hxR : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hR hx
    have hxr : ‖x‖ < r := by dsimp [r]; have := le_max_left R 0; linarith
    filter_upwards [SmoothCutoff.eventually_one hr hxr] with y hy
    change SmoothCutoff.cutoff r y*f y = f y
    rw [hy, one_mul]
  have hl : (fun x => h x*A τ f' x) = fun x => h x*A τ f x := by
    funext x
    by_cases hx : x ∈ tsupport h
    · rw [A_congr (he x hx)]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hg : gamma τ h f' = gamma τ h f := by
    funext x
    by_cases hx : x ∈ tsupport h
    · unfold gamma; rw [grad_congr (he x hx)]
    · unfold gamma; rw [grad_zero_of_not_tsupport hx]; simp
  have hh' := hibp f' h hs hh hc hhc
  simpa only [hl, hg] using hh'

lemma harmonic_test (μ : Measure (Space ι))
    {τ : Space ι → Matrix ι ι ℝ}
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    {η w : Space ι → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hw : ContDiff ℝ ∞ w) (hAw : A τ w = 0) :
    (∫ x, gamma τ (fun x => η x^2*w x) w x ∂μ) = 0 := by
  have hcη : HasCompactSupport (fun x => η x^2) := by
    rw [show (fun x => η x^2) = η*η by ext x; simp only [Pi.mul_apply, pow_two]]
    exact hηc.mul_right
  rw [← extend_integration μ hibp hw ((hη.pow 2).mul hw) hcη.mul_right]
  simp only [hAw, Pi.zero_apply, mul_zero, integral_zero]


lemma grad_le (f : Space ι → ℝ) (x : Space ι) (i : ι) :
    |grad f x i| ≤ ‖fderiv ℝ f x‖ := by
  have hh := (fderiv ℝ f x).le_opNorm (e i)
  simpa only [e, Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs, grad, D] using hh

lemma gamma_upper {τ : Space ι → Matrix ι ι ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hupper : ∀ x, (Λ • (1 : Matrix ι ι ℝ) - τ x).PosSemidef)
    (f : Space ι → ℝ) (x : Space ι) :
    gamma τ f f x ≤ Λ * (Fintype.card ι : ℝ) * ‖fderiv ℝ f x‖^2 := by
  have hh := MomentMatrix.form_nonneg (hupper x) (grad f x)
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hh
  have hs : grad f x ⬝ᵥ grad f x ≤ (Fintype.card ι : ℝ) * ‖fderiv ℝ f x‖^2 := by
    calc
      _ = ∑ i, (grad f x i)^2 := by simp only [dotProduct, pow_two]
      _ ≤ ∑ _ : ι, ‖fderiv ℝ f x‖^2 := by
        apply Finset.sum_le_sum; intro i _
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr (grad_le f x i)
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_left hs hΛ
  unfold gamma
  nlinarith

lemma cutoff_gamma_bound {τ : Space ι → Matrix ι ι ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hupper : ∀ x, (Λ • (1 : Matrix ι ι ℝ) - τ x).PosSemidef) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (r : ℝ), 0 < r → ∀ x : Space ι,
      gamma τ (SmoothCutoff.cutoff r) (SmoothCutoff.cutoff r) x ≤ D/r^2 := by
  obtain ⟨C,hC,hCb⟩ := SmoothCutoff.derivative_bounds (E:=Space ι)
  refine ⟨Λ*(Fintype.card ι : ℝ)*C^2, by positivity, ?_⟩
  intro r hr x
  calc
    _ ≤ Λ*(Fintype.card ι : ℝ)*‖fderiv ℝ (SmoothCutoff.cutoff r) x‖^2 := gamma_upper hΛ hupper _ _
    _ ≤ Λ*(Fintype.card ι : ℝ)*(C/r)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hCb r hr x).1 2) (by positivity)
    _ = _ := by rw [div_pow, mul_div_assoc]

end DensityEnergy

namespace SmoothCutoff
open Filter MeasureTheory
open scoped ContDiff Topology
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma seq_smooth (k : ℕ) : ContDiff ℝ ∞ (seq (E:=E) k) := smooth _
lemma seq_compact (k : ℕ) : HasCompactSupport (seq (E:=E) k) := compact (by positivity)
lemma seq_nonneg (k : ℕ) (x : E) : 0 ≤ seq k x := nonneg _ _
lemma seq_le_one (k : ℕ) (x : E) : seq k x ≤ 1 := le_one _ _

lemma seq_eventually (x : E) : ∀ᶠ k : ℕ in atTop,
    seq k x = 1 ∧ fderiv ℝ (seq k) x = 0 ∧ fderiv ℝ (fderiv ℝ (seq k)) x = 0 := by
  obtain ⟨N,hN⟩ := exists_nat_gt ‖x‖
  apply eventually_atTop.mpr
  refine ⟨N,fun k hk => ?_⟩
  have hx : ‖x‖ < (k:ℝ)+1 := by
    have hn : (N:ℝ) ≤ k := Nat.cast_le.mpr hk
    linarith
  exact ⟨eq_one (by positivity) hx.le, first_zero_inside (by positivity) hx,
    second_zero_inside (by positivity) hx⟩

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_of_cutoff_bound (μ : Measure E) [IsFiniteMeasure μ]
    {F : E → ℝ} (hF : Continuous F) (hFn : ∀ x, 0 ≤ F x) (p : ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ k : ℕ, (∫ x, (seq k x)^p*F x ∂μ) ≤ C)
    (hi : ∀ k : ℕ, Integrable (fun x => (seq k x)^p*F x) μ) :
    Integrable F μ ∧ (∫ x, F x ∂μ) ≤ C := by
  have hff (k : ℕ) : Continuous (fun x => ENNReal.ofReal ((seq k x)^p*F x)) :=
    ENNReal.continuous_ofReal.comp (((seq_smooth k).continuous.pow p).mul hF)
  have hn (k : ℕ) (x : E) : 0 ≤ (seq k x)^p*F x := mul_nonneg (pow_nonneg (seq_nonneg k x) p) (hFn x)
  have hl (x : E) : liminf (fun k => ENNReal.ofReal ((seq k x)^p*F x)) atTop = ENNReal.ofReal (F x) := by
    apply Tendsto.liminf_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [seq_eventually x] with k hk
    simp only [hk.1, one_pow, one_mul]
  have hb : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, liminf (fun k => ENNReal.ofReal ((seq k x)^p*F x)) atTop ∂μ := by simp only [hl]
      _ ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal ((seq k x)^p*F x) ∂μ) atTop :=
        lintegral_liminf_le (fun k => (hff k).measurable)
      _ ≤ ENNReal.ofReal C := by
        apply liminf_le_of_frequently_le (hu_le := isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
        apply Frequently.of_forall
        intro k
        rw [← ofReal_integral_eq_lintegral_ofReal (hi k) (ae_of_all μ (hn k))]
        exact ENNReal.ofReal_le_ofReal (hbound k)
  have hf : Integrable F μ := ⟨hF.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all μ hFn)).mpr (hb.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hf, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all μ hFn)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hb

end SmoothCutoff

namespace DensityEnergy
open MeasureTheory Matrix WeightedCalculus Filter
open scoped ContDiff Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma energy_estimate (μ : Measure (Space ι)) [IsFiniteMeasure μ]
    {τ : Space ι → Matrix ι ι ℝ}
    (hts : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (htp : ∀ x, (τ x).PosSemidef)
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    {η w : Space ι → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hw : ContDiff ℝ ∞ w) (hiw : Integrable (fun x => w x^2) μ)
    {c : ℝ} (hbound : ∀ x, gamma τ η η x ≤ c) :
    (∫ x, η x^2*gamma τ w w x ∂μ) ≤
      2*(∫ x, η x^2*w x*A τ w x ∂μ) + 4*c*(∫ x, w x^2 ∂μ) := by
  have hcη : HasCompactSupport (fun x => η x^2) := by
    rw [show (fun x => η x^2) = η*η by ext x; simp only [Pi.mul_apply, pow_two]]
    exact hηc.mul_right
  have hc₂ : HasCompactSupport (fun x => 2*η x) := hηc.mul_left
  have hi₁ : Integrable (fun x => η x^2*gamma τ w w x) μ :=
    ((hη.pow 2).mul (smooth_gamma hts hw hw)).continuous.integrable_of_hasCompactSupport hcη.mul_right
  have hi₂ : Integrable (fun x => 2*η x*w x*gamma τ η w x) μ :=
    (((contDiff_const.mul hη).mul hw).mul (smooth_gamma hts hη hw)).continuous.integrable_of_hasCompactSupport
      hc₂.mul_right.mul_right
  have hi₃ : Integrable (fun x => w x^2*gamma τ η η x) μ :=
    ((hw.pow 2).mul (smooth_gamma hts hη hη)).continuous.integrable_of_hasCompactSupport
      (compact_gamma_left hηc).mul_left
  have het := extend_integration μ hibp hw ((hη.pow 2).mul hw) hcη.mul_right
  simp_rw [gamma_cutoff_square hη hw] at het
  rw [integral_add hi₁ hi₂] at het
  have hh := integral_mono hi₂.neg ((hi₁.const_mul (1/2)).add (hi₃.const_mul 2))
    (fun x => by simpa only [Pi.neg_apply, Pi.add_apply, neg_mul, mul_assoc] using cutoff_young htp η w x)
  simp only [Pi.neg_apply, Pi.add_apply] at hh
  rw [integral_neg, integral_add (hi₁.const_mul (1/2)) (hi₃.const_mul 2),
    integral_const_mul, integral_const_mul] at hh
  have hb := integral_mono hi₃ (hiw.const_mul c) (fun x => by
    simpa only [mul_comm c] using mul_le_mul_of_nonneg_left (hbound x) (sq_nonneg (w x)))
  rw [integral_const_mul] at hb
  nlinarith

lemma eigen_energy_integrable (μ : Measure (Space ι)) [IsFiniteMeasure μ]
    {τ : Space ι → Matrix ι ι ℝ}
    (hts : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (htp : ∀ x, (τ x).PosSemidef)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hupper : ∀ x, (Λ • (1 : Matrix ι ι ℝ)-τ x).PosSemidef)
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    {v : Space ι → ℝ} (hv : ContDiff ℝ ∞ v) (hiv : Integrable (fun x => v x^2) μ)
    (hAv : A τ v = v) : Integrable (gamma τ v v) μ := by
  obtain ⟨D,hD,hDb⟩ := cutoff_gamma_bound hΛ hupper
  have hb (k : ℕ) (x : Space ι) : gamma τ (SmoothCutoff.seq k) (SmoothCutoff.seq k) x ≤ D := by
    apply (hDb _ (by positivity) x).trans
    exact div_le_self hD (by have := Nat.cast_nonneg (α:=ℝ) k; nlinarith)
  let C := (2+4*D)*(∫ x, v x^2 ∂μ)
  have hC : 0 ≤ C := mul_nonneg (by positivity) (integral_nonneg fun x => sq_nonneg _)
  have hi (k : ℕ) : Integrable (fun x => (SmoothCutoff.seq k x)^2*gamma τ v v x) μ := by
    have hcη : HasCompactSupport (fun x : Space ι => (SmoothCutoff.seq k x)^2) := by
      rw [show (fun x : Space ι => (SmoothCutoff.seq k x)^2) = SmoothCutoff.seq k*SmoothCutoff.seq k by
        ext x; simp only [Pi.mul_apply,pow_two]]
      exact (SmoothCutoff.seq_compact k).mul_right
    exact (((SmoothCutoff.seq_smooth k).pow 2).mul (smooth_gamma hts hv hv)).continuous.integrable_of_hasCompactSupport
      hcη.mul_right
  apply (SmoothCutoff.integrable_of_cutoff_bound μ (smooth_gamma hts hv hv).continuous
    (gamma_nonneg htp v) 2 hC (fun k => ?_) hi).1
  have hh := energy_estimate μ hts htp hibp (SmoothCutoff.seq_smooth k) (SmoothCutoff.seq_compact k) hv hiv (hb k)
  have he : (fun x => (SmoothCutoff.seq k x)^2*v x*A τ v x) = fun x => (SmoothCutoff.seq k x)^2*v x^2 := by
    rw [hAv]; ext x; ring
  rw [he] at hh
  have hk (x : Space ι) : (SmoothCutoff.seq k x)^2*v x^2 ≤ v x^2 := by
    have hη := pow_le_pow_left₀ (SmoothCutoff.seq_nonneg k x) (SmoothCutoff.seq_le_one k x) 2
    simpa only [one_pow,one_mul] using mul_le_mul_of_nonneg_right hη (sq_nonneg (v x))
  have hir : Integrable (fun x => (SmoothCutoff.seq k x)^2*v x^2) μ := by
    apply hiv.mono' (((SmoothCutoff.seq_smooth k).pow 2).mul (hv.pow 2)).continuous.aestronglyMeasurable
    exact ae_of_all μ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]; exact hk x)
  have hl := integral_mono hir hiv hk
  dsimp [C]
  nlinarith


lemma DD_mul {f g : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i j : ι) : D (e i) (D (e j) (fun x => f x*g x)) = fun x =>
      g x*D (e i) (D (e j) f) x + f x*D (e i) (D (e j) g) x +
      D (e i) f x*D (e j) g x + D (e j) f x*D (e i) g x := by
  rw [D_mul (hf.differentiable (by simp)) (hg.differentiable (by simp)),
    D_add (((smooth_D hf _).mul hg).differentiable (by simp))
      ((hf.mul (smooth_D hg _)).differentiable (by simp)),
    D_mul ((smooth_D hf _).differentiable (by simp)) (hg.differentiable (by simp)),
    D_mul (hf.differentiable (by simp)) ((smooth_D hg _).differentiable (by simp))]
  funext x; ring

lemma gamma_sum (τ : Space ι → Matrix ι ι ℝ) (f g : Space ι → ℝ) (x : Space ι) :
    gamma τ f g x = ∑ i, ∑ j, τ x i j * D (e i) f x * D (e j) g x := by
  simp only [gamma, grad, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma A_mul {τ : Space ι → Matrix ι ι ℝ} (hτ : ∀ x, (τ x)ᵀ = τ x)
    {f g : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Space ι) :
    A τ (fun x => f x*g x) x = f x*A τ g x + g x*A τ f x - 2*gamma τ f g x := by
  have hsym := gamma_symm hτ g f x
  rw [gamma_sum, gamma_sum] at hsym
  conv_lhs =>
    unfold A
    simp only [DD_mul hf hg]
    simp only [D_mul (hf.differentiable (by simp)) (hg.differentiable (by simp))]
  have hd : (∑ i, x i * (D (e i) f x*g x+f x*D (e i) g x)) =
      g x*(∑ i, x i*D (e i) f x) + f x*(∑ i, x i*D (e i) g x) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hd]
  have hh : (∑ i, ∑ j, τ x i j *
      (g x*D (e i) (D (e j) f) x + f x*D (e i) (D (e j) g) x +
        D (e i) f x*D (e j) g x + D (e j) f x*D (e i) g x)) =
      g x*(∑ i, ∑ j, τ x i j*D (e i) (D (e j) f) x) +
      f x*(∑ i, ∑ j, τ x i j*D (e i) (D (e j) g) x) +
      (∑ i, ∑ j, τ x i j*D (e i) f x*D (e j) g x) +
      (∑ i, ∑ j, τ x i j*D (e i) g x*D (e j) f x) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hh, hsym]
  simp only [A, gamma_sum]
  ring

lemma gamma_pow_left {τ : Space ι → Matrix ι ι ℝ} {f g : Space ι → ℝ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : Space ι) :
    gamma τ (fun x => f x^(n+1)) g x = (n+1 : ℝ)*f x^n*gamma τ f g x := by
  induction n with
  | zero => simp only [zero_add, pow_one, Nat.cast_zero, zero_add, pow_zero, mul_one, one_mul]
  | succ n ih =>
    simp only [pow_succ (f _) (n+1)]
    rw [gamma_mul_left (hf.pow _) hf, ih]
    push_cast
    ring

lemma A_pow_succ {τ : Space ι → Matrix ι ι ℝ} (hτ : ∀ x, (τ x)ᵀ = τ x)
    {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : Space ι) :
    A τ (fun x => f x^(n+2)) x =
      (n+2 : ℝ)*f x^(n+1)*A τ f x - (n+2 : ℝ)*(n+1)*f x^n*gamma τ f f x := by
  induction n with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Nat.cast_zero]
    simp only [pow_two]
    rw [A_mul hτ hf hf]
    ring
  | succ n ih =>
    simp only [show n+1+2 = n+2+1 by omega, pow_succ (f _) (n+2)]
    rw [A_mul hτ (hf.pow _) hf, ih, gamma_pow_left hf (n+1)]
    push_cast
    simp only [pow_succ]
    ring

lemma smooth_A {τ : Space ι → Matrix ι ι ℝ}
    (ht : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j))
    {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (A τ f) := by
  apply ContDiff.sub
  · apply ContDiff.sum; intro i _
    exact (contDiff_apply ℝ ℝ i).mul (smooth_D hf _)
  · apply ContDiff.sum; intro i _
    apply ContDiff.sum; intro j _
    exact (ht i j).mul (smooth_D (smooth_D hf _) _)

lemma compact_A {τ : Space ι → Matrix ι ι ℝ} {f : Space ι → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (A τ f) :=
  (compact_sum _ (fun i => (compact_D hf (e i)).mul_left)).sub
    (compact_sum _ (fun i => compact_sum _ (fun j => ((compact_D (compact_D hf (e j)) (e i))).mul_left)))


lemma entries_bound {T : Matrix ι ι ℝ} (hT : T.PosSemidef) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hc : (Λ • (1 : Matrix ι ι ℝ)-T).PosSemidef) (i j : ι) : |T i j| ≤ Λ := by
  have hd (k : ι) : T k k ≤ Λ := by
    have hh := hc.diag_nonneg (i:=k)
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hh
    linarith
  have hs : Tᵀ = T := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hT.isHermitian.eq
  have hsq : (T i j)^2 ≤ T i i*T j j := by
    apply MomentMatrix.quadratic_cs
    intro t
    have hh := MomentMatrix.form_nonneg hT (e j-t • e i)
    rw [MomentMatrix.form_quadratic hs] at hh
    simpa [e, Matrix.mulVec, dotProduct, Pi.single_apply] using hh
  have hle := mul_le_mul (hd i) (hd j) (hT.diag_nonneg (i:=j)) hΛ
  apply (sq_le_sq₀ (abs_nonneg _) hΛ).mp
  rw [sq_abs]
  nlinarith

lemma second_coordinate {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (x : Space ι) (i j : ι) :
    D (e i) (D (e j) f) x = fderiv ℝ (fderiv ℝ f) x (e i) (e j) := by
  have hd := (hf.fderiv_right (m:=∞) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ f y (e j)) x (e i) = _
  simp only [fderiv_clm_apply (hd x) (differentiableAt_const _),
    fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

lemma second_coordinate_bound {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (x : Space ι) (i j : ι) :
    |D (e i) (D (e j) f) x| ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  rw [second_coordinate hf x i j, ← Real.norm_eq_abs]
  have h₁ := (fderiv ℝ (fderiv ℝ f) x (e i)).le_opNorm (e j)
  have h₂ := (fderiv ℝ (fderiv ℝ f) x).le_opNorm (e i)
  simp only [e, Pi.norm_single, norm_one, mul_one] at h₁ h₂
  exact h₁.trans h₂

lemma A_bound {τ : Space ι → Matrix ι ι ℝ} (ht : ∀ x, (τ x).PosSemidef)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hc : ∀ x, (Λ • (1 : Matrix ι ι ℝ)-τ x).PosSemidef)
    {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (x : Space ι) :
    |A τ f x| ≤ (Fintype.card ι : ℝ)*‖x‖*‖fderiv ℝ f x‖ +
      (Fintype.card ι : ℝ)^2*Λ*‖fderiv ℝ (fderiv ℝ f) x‖ := by
  unfold A
  apply (abs_sub _ _).trans
  apply add_le_add
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : ι, ‖x‖*‖fderiv ℝ f x‖ := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul]
        exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i)
          (grad_le f x i) (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp [mul_assoc]
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : ι, ∑ _ : ι, Λ*‖fderiv ℝ (fderiv ℝ f) x‖ := by
        apply Finset.sum_le_sum; intro i _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        exact mul_le_mul (entries_bound (ht x) hΛ (hc x) i j)
          (second_coordinate_bound hf x i j) (abs_nonneg _) hΛ
      _ = _ := by simp [pow_two, mul_assoc]

lemma cutoff_A_bound {τ : Space ι → Matrix ι ι ℝ} (ht : ∀ x, (τ x).PosSemidef)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hc : ∀ x, (Λ • (1 : Matrix ι ι ℝ)-τ x).PosSemidef) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r → ∀ x : Space ι,
      |A τ (SmoothCutoff.cutoff r) x| ≤ K := by
  obtain ⟨C,hC,hCb⟩ := SmoothCutoff.derivative_bounds (E:=Space ι)
  refine ⟨2*(Fintype.card ι : ℝ)*C+(Fintype.card ι : ℝ)^2*Λ*C,by positivity,?_⟩
  intro r hr x
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  by_cases hx : ‖x‖ ≤ 2*r
  · apply (A_bound ht hΛ hc (SmoothCutoff.smooth r) x).trans
    have hh := hCb r hrp x
    have h₁ : ‖x‖*‖fderiv ℝ (SmoothCutoff.cutoff r) x‖ ≤ 2*C := by
      calc
        _ ≤ (2*r)*(C/r) := mul_le_mul hx hh.1 (norm_nonneg _) (by positivity)
        _ = 2*C := by field_simp
    have h₂ : ‖fderiv ℝ (fderiv ℝ (SmoothCutoff.cutoff r)) x‖ ≤ C :=
      hh.2.trans (div_le_self hC.le (by nlinarith))
    nlinarith [mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)),
      mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ (Fintype.card ι : ℝ)^2*Λ)]
  · have he : SmoothCutoff.cutoff r =ᶠ[𝓝 x] (0:Space ι → ℝ) := by
      filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds (not_le.mp hx)] with y hy
      exact SmoothCutoff.eq_zero hrp hy.le
    rw [A_congr he]
    have hz (i : ι) : D (e i) (0:Space ι → ℝ) = 0 := by funext y; simp [D]
    simpa only [A, hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_self, abs_zero] using (show (0:ℝ) ≤ 2*(Fintype.card ι : ℝ)*C+(Fintype.card ι : ℝ)^2*Λ*C from by positivity)


lemma gamma_cs {τ : Space ι → Matrix ι ι ℝ} (ht : ∀ x, (τ x).PosSemidef)
    (f g : Space ι → ℝ) (x : Space ι) :
    (gamma τ f g x)^2 ≤ gamma τ f f x*gamma τ g g x := by
  apply MomentMatrix.quadratic_cs
  intro t
  have hs : (τ x)ᵀ = τ x := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (ht x).isHermitian.eq
  have hh := MomentMatrix.form_nonneg (ht x) (grad g x-t • grad f x)
  rw [MomentMatrix.form_quadratic hs] at hh
  exact hh

lemma eigen_cutoff_square_bound {τ : Space ι → Matrix ι ι ℝ} (ht : ∀ x, (τ x).PosSemidef)
    {η v : Space ι → ℝ} (hη : ContDiff ℝ ∞ η) (hv : ContDiff ℝ ∞ v)
    (hAv : A τ v = v) {D K : ℝ} (_hD : 0 ≤ D) (hK : 0 ≤ K)
    (hηn : ∀ x, 0 ≤ η x) (hηl : ∀ x, η x ≤ 1)
    (hηA : ∀ x, |A τ η x| ≤ K) (hηΓ : ∀ x, gamma τ η η x ≤ D) (x : Space ι) :
    (A τ (fun x => η x*v x) x)^2 ≤
      (4+4*K^2)*v x^2+8*D*gamma τ v v x := by
  have hs (y : Space ι) : (τ y)ᵀ = τ y := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (ht y).isHermitian.eq
  rw [A_mul hs hη hv, hAv]
  have he : (η x)^2 ≤ 1 := by simpa using pow_le_pow_left₀ (hηn x) (hηl x) 2
  have ha : (A τ η x)^2 ≤ K^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (hηA x)
  have hΓ := (gamma_cs ht η v x).trans (mul_le_mul_of_nonneg_right (hηΓ x) (gamma_nonneg ht v x))
  have hy : (η x+A τ η x)^2 ≤ 2+2*K^2 := by nlinarith [sq_nonneg (η x-A τ η x)]
  have hm := mul_le_mul_of_nonneg_right hy (sq_nonneg (v x))
  nlinarith [sq_nonneg ((η x+A τ η x)*v x+2*gamma τ η v x),
    mul_nonneg _hD (gamma_nonneg ht v x)]

omit [DecidableEq ι] in
lemma cutoff_product_eventually (v : Space ι → ℝ) (x : Space ι) :
    ∀ᶠ k : ℕ in atTop, (fun y => SmoothCutoff.seq k y*v y) =ᶠ[𝓝 x] v := by
  obtain ⟨N,hN⟩ := exists_nat_gt ‖x‖
  apply eventually_atTop.mpr
  refine ⟨N,fun k hk => ?_⟩
  have hx : ‖x‖ < (k:ℝ)+1 := by
    have hn : (N:ℝ) ≤ k := Nat.cast_le.mpr hk
    linarith
  filter_upwards [SmoothCutoff.eventually_one (by positivity) hx] with y hy
  change SmoothCutoff.cutoff ((k:ℝ)+1) y*v y = v y
  rw [hy,one_mul]

lemma eigen_graph_integrals (μ : Measure (Space ι)) [IsFiniteMeasure μ]
    {τ : Space ι → Matrix ι ι ℝ}
    (hts : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (htp : ∀ x, (τ x).PosSemidef)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hupper : ∀ x, (Λ • (1 : Matrix ι ι ℝ)-τ x).PosSemidef)
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    {v : Space ι → ℝ} (hv : ContDiff ℝ ∞ v) (hiv : Integrable (fun x => v x^2) μ)
    (hAv : A τ v = v) :
    Tendsto (fun k : ℕ => ∫ x, (A τ (fun y => SmoothCutoff.seq k y*v y) x)^2 ∂μ)
      atTop (𝓝 (∫ x, v x^2 ∂μ)) ∧
    Tendsto (fun k : ℕ => ∫ x, (SmoothCutoff.seq k x*v x)*A τ (fun y => SmoothCutoff.seq k y*v y) x ∂μ)
      atTop (𝓝 (∫ x, v x^2 ∂μ)) := by
  have hiΓ := eigen_energy_integrable μ hts htp hΛ hupper hibp hv hiv hAv
  obtain ⟨D,hD,hDb⟩ := cutoff_gamma_bound hΛ hupper
  obtain ⟨K,hK,hKb⟩ := cutoff_A_bound htp hΛ hupper
  let f (k : ℕ) : Space ι → ℝ := fun x => SmoothCutoff.seq k x*v x
  have hf (k : ℕ) : ContDiff ℝ ∞ (f k) := (SmoothCutoff.seq_smooth k).mul hv
  have hbΓ (k : ℕ) (x : Space ι) : gamma τ (SmoothCutoff.seq k) (SmoothCutoff.seq k) x ≤ D := by
    apply (hDb _ (by positivity) x).trans
    exact div_le_self hD (by have := Nat.cast_nonneg (α:=ℝ) k; nlinarith)
  have hbA (k : ℕ) (x : Space ι) : |A τ (SmoothCutoff.seq k) x| ≤ K :=
    hKb _ (by have := Nat.cast_nonneg (α:=ℝ) k; linarith) x
  let B : Space ι → ℝ := fun x => (4+4*K^2)*v x^2+8*D*gamma τ v v x
  have hiB : Integrable B μ := (hiv.const_mul _).add (hiΓ.const_mul _)
  have hb (k : ℕ) (x : Space ι) : (A τ (f k) x)^2 ≤ B x :=
    eigen_cutoff_square_bound htp (SmoothCutoff.seq_smooth k) hv hAv hD hK
      (SmoothCutoff.seq_nonneg k) (SmoothCutoff.seq_le_one k) (hbA k) (hbΓ k) x
  have hfb (k : ℕ) (x : Space ι) : (f k x)^2 ≤ v x^2 := by
    have hη := pow_le_pow_left₀ (SmoothCutoff.seq_nonneg k x) (SmoothCutoff.seq_le_one k x) 2
    dsimp [f]
    simpa only [mul_pow,one_pow,one_mul] using mul_le_mul_of_nonneg_right hη (sq_nonneg (v x))
  have hev (x : Space ι) : ∀ᶠ k : ℕ in atTop, f k x = v x ∧ A τ (f k) x = v x := by
    filter_upwards [cutoff_product_eventually v x] with k hk
    exact ⟨hk.eq_of_nhds, by rw [A_congr hk,hAv]⟩
  constructor
  · apply tendsto_integral_of_dominated_convergence B
    · intro k; exact ((smooth_A hts (hf k)).pow 2).continuous.aestronglyMeasurable
    · exact hiB
    · intro k; exact ae_of_all μ (fun x => by
        change ‖(A τ (f k) x)^2‖ ≤ B x
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (A τ (f k) x))]
        exact hb k x)
    · apply ae_of_all; intro x
      apply tendsto_const_nhds.congr'
      filter_upwards [hev x] with k hk
      rw [hk.2]
  · apply tendsto_integral_of_dominated_convergence (fun x => v x^2+B x)
    · intro k; exact ((hf k).mul (smooth_A hts (hf k))).continuous.aestronglyMeasurable
    · exact hiv.add hiB
    · intro k; apply ae_of_all; intro x
      rw [Real.norm_eq_abs,abs_mul]
      have hcross := sq_nonneg (|f k x|-|A τ (f k) x|)
      have hnon := sq_nonneg (A τ (f k) x)
      have hb' := hb k x
      have hf' := hfb k x
      nlinarith [sq_abs (f k x),sq_abs (A τ (f k) x)]
    · apply ae_of_all; intro x
      apply tendsto_const_nhds.congr'
      filter_upwards [hev x] with k hk
      change v x^2 = f k x*A τ (f k) x
      rw [hk.1,hk.2,pow_two]


omit [DecidableEq ι] in
lemma cutoff_eventually_dominate (m : ℕ) : ∀ᶠ k : ℕ in atTop,
    ∀ x : Space ι, (SmoothCutoff.seq m x)^2 ≤ (SmoothCutoff.seq k x)^2 := by
  apply eventually_atTop.mpr
  refine ⟨2*m+1, fun k hk x => ?_⟩
  by_cases hx : 2*((m:ℝ)+1) ≤ ‖x‖
  · rw [show SmoothCutoff.seq m x = 0 from SmoothCutoff.eq_zero (by positivity) hx]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using sq_nonneg (SmoothCutoff.seq k x)
  · have hxr : ‖x‖ ≤ (k:ℝ)+1 := by
      have hn : ((2*m+1 : ℕ):ℝ) ≤ k := Nat.cast_le.mpr hk
      push_cast at hn
      linarith [not_le.mp hx]
    rw [show SmoothCutoff.seq k x = 1 from SmoothCutoff.eq_one (by positivity) hxr]
    exact pow_le_pow_left₀ (SmoothCutoff.seq_nonneg m x) (SmoothCutoff.seq_le_one m x) 2

lemma harmonic_energy_zero (μ : Measure (Space ι)) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {τ : Space ι → Matrix ι ι ℝ}
    (hts : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j))
    (htp : ∀ x, (τ x).PosSemidef) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hupper : ∀ x, (Λ • (1 : Matrix ι ι ℝ) - τ x).PosSemidef)
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    {w : Space ι → ℝ} (hw : ContDiff ℝ ∞ w)
    (hiw : Integrable (fun x => w x^2) μ) (hAw : A τ w = 0) :
    ∀ x, gamma τ w w x = 0 := by
  let η := SmoothCutoff.seq (E:=Space ι)
  have hs (k : ℕ) := SmoothCutoff.seq_smooth (E:=Space ι) k
  have hc (k : ℕ) := SmoothCutoff.seq_compact (E:=Space ι) k
  obtain ⟨D,hD,hDb⟩ := cutoff_gamma_bound hΛ hupper
  have hi (k : ℕ) : Integrable (fun x => η k x^2*gamma τ w w x) μ := by
    have hcη : HasCompactSupport (fun x => η k x^2) := by
      rw [show (fun x => η k x^2) = η k*η k by ext x; simp only [Pi.mul_apply, pow_two]]
      exact (hc k).mul_right
    exact (((hs k).pow 2).mul (smooth_gamma hts hw hw)).continuous.integrable_of_hasCompactSupport hcη.mul_right
  have hb (k : ℕ) : (∫ x, η k x^2*gamma τ w w x ∂μ) ≤
      4*(D/((k:ℝ)+1)^2)*(∫ x, w x^2 ∂μ) :=
    caccioppoli μ hts htp (hs k) (hc k) hw hiw
      (harmonic_test μ hibp (hs k) (hc k) hw hAw) (hDb _ (by positivity))
  have ht : Tendsto (fun k : ℕ => 4*(D/((k:ℝ)+1)^2)*(∫ x, w x^2 ∂μ)) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).pow 2
    convert ((hh.const_mul D).const_mul 4).mul_const (∫ x, w x^2 ∂μ) using 1 <;>
      simp [div_eq_mul_inv]
  have hz (m : ℕ) : (∫ x, η m x^2*gamma τ w w x ∂μ) = 0 := by
    apply le_antisymm
    · apply ge_of_tendsto ht
      filter_upwards [cutoff_eventually_dominate (ι:=ι) m] with k hk
      exact (integral_mono (hi m) (hi k) (fun x =>
        mul_le_mul_of_nonneg_right (hk x) (gamma_nonneg htp w x))).trans (hb k)
    · exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (gamma_nonneg htp w x))
  have he (m : ℕ) : (fun x => η m x^2*gamma τ w w x) = 0 := by
    have hae : (fun x => η m x^2*gamma τ w w x) =ᶠ[ae μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (sq_nonneg _) (gamma_nonneg htp w x)) (hi m)).mp (hz m)
    exact ((((hs m).pow 2).mul (smooth_gamma hts hw hw)).continuous.ae_eq_iff_eq μ continuous_const).mp hae
  intro x
  obtain ⟨m,hm⟩ := exists_nat_gt ‖x‖
  have hη : η m x = 1 := SmoothCutoff.eq_one (by positivity) (by linarith)
  have hh := congrFun (he m) x
  simpa only [hη, one_pow, one_mul, Pi.zero_apply] using hh

lemma fderiv_zero_of_grad_zero {w : Space ι → ℝ} {x : Space ι}
    (h : grad w x = 0) : fderiv ℝ w x = 0 := by
  ext v
  have hv : v = ∑ i, v i • e i := by
    funext j
    simp [e, Pi.single_apply]
  rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hh (i : ι) : fderiv ℝ w x (e i) = 0 := congrFun h i
  simp only [hh, mul_zero, Finset.sum_const_zero, _root_.zero_apply]

theorem harmonic_constant (μ : Measure (Space ι)) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {τ : Space ι → Matrix ι ι ℝ}
    (hts : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j))
    (htp : ∀ x, (τ x).PosDef) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hupper : ∀ x, (Λ • (1 : Matrix ι ι ℝ) - τ x).PosSemidef)
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    {w : Space ι → ℝ} (hw : ContDiff ℝ ∞ w)
    (hiw : Integrable (fun x => w x^2) μ) (hAw : A τ w = 0) :
    ∀ x y, w x = w y := by
  have he := harmonic_energy_zero μ hts (fun x => (htp x).posSemidef) hΛ hupper hibp hw hiw hAw
  have hg (x : Space ι) : grad w x = 0 := by
    by_contra hn
    have hp := (htp x).dotProduct_mulVec_pos hn
    have hz := he x
    unfold gamma at hz
    simp only [star_trivial, hz, lt_self_iff_false] at hp
  have hd (x : Space ι) : fderiv ℝ w x = 0 := fderiv_zero_of_grad_zero (hg x)
  exact is_const_of_fderiv_eq_zero (hw.differentiable (by simp)) hd

end DensityEnergy

namespace MomentMatrix
open Matrix
open scoped MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_conjugate_eq_zero {A H : Matrix ι ι ℝ} (hA : A.PosDef)
    (hH : Hᵀ = H) (hz : (A*H*A*H).trace = 0) : H = 0 := by
  obtain ⟨S,hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hu : IsUnit S.det := by
    have hh : IsUnit (Sᴴ.det*S.det) := by
      rw [← Matrix.det_mul]
      change IsUnit (star S*S).det
      rw [← hS]
      exact (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
    exact isUnit_of_mul_isUnit_right hh
  have hstar : Hᴴ = H := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH
  have hc : (S*H*Sᴴ)ᴴ = S*H*Sᴴ := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hstar,Matrix.mul_assoc]
  have he : ((S*H*Sᴴ)ᴴ*(S*H*Sᴴ)).trace = (A*H*A*H).trace := by
    rw [hc,hS]
    change ((S*H*Sᴴ)*(S*H*Sᴴ)).trace = (Sᴴ*S*H*(Sᴴ*S)*H).trace
    calc
      _ = (S*(H*Sᴴ*S*H)*Sᴴ).trace := by simp only [Matrix.mul_assoc]
      _ = (Sᴴ*S*(H*Sᴴ*S*H)).trace := Matrix.trace_mul_cycle _ _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have hz' : S*H*Sᴴ = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (he.trans hz)
  have hv : IsUnit Sᴴ.det := by simpa only [Matrix.det_conjTranspose,star_trivial] using hu
  have hh : H*Sᴴ = 0 := by
    have hh := congrArg (fun M : Matrix ι ι ℝ => S⁻¹*M) hz'
    simpa only [← Matrix.mul_assoc,Matrix.nonsing_inv_mul S hu,Matrix.one_mul,
      Matrix.mul_zero] using hh
  have hh' := congrArg (fun M : Matrix ι ι ℝ => M*(Sᴴ)⁻¹) hh
  simpa only [Matrix.mul_assoc,Matrix.mul_nonsing_inv Sᴴ hv,Matrix.mul_one,
    Matrix.zero_mul] using hh'

end MomentMatrix
end

namespace DensityLimit
open Filter MeasureTheory
open scoped Topology

lemma zero_of_local_limit {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [Measure.IsOpenPosMeasure μ]
    {F : E → ℝ} {f : ℕ → E → ℝ} (hF : Continuous F)
    (hf : ∀ k, Continuous (f k)) (hFn : ∀ x, 0 ≤ F x)
    (hfn : ∀ k x, 0 ≤ f k x) (hi : ∀ k, Integrable (f k) μ)
    (he : ∀ x, ∀ᶠ k in atTop, f k x = F x)
    (ht : Tendsto (fun k => ∫ x, f k x ∂μ) atTop (𝓝 0)) : F = 0 := by
  have hl (x : E) : liminf (fun k => ENNReal.ofReal (f k x)) atTop = ENNReal.ofReal (F x) := by
    apply Tendsto.liminf_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [he x] with k hk
    rw [hk]
  have hl' : Tendsto (fun k => ∫⁻ x, ENNReal.ofReal (f k x) ∂μ) atTop (𝓝 0) := by
    have ht' : Tendsto (fun k => ENNReal.ofReal (∫ x, f k x ∂μ)) atTop
        (𝓝 (ENNReal.ofReal 0)) := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    simpa only [ofReal_integral_eq_lintegral_ofReal (hi _) (ae_of_all μ (hfn _)),
      ENNReal.ofReal_zero] using ht'

  have hb : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) = 0 := by
    apply le_antisymm _ bot_le
    calc
      _ = ∫⁻ x, liminf (fun k => ENNReal.ofReal (f k x)) atTop ∂μ := by simp only [hl]
      _ ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal (f k x) ∂μ) atTop :=
        lintegral_liminf_le (fun k => (ENNReal.continuous_ofReal.comp (hf k)).measurable)
      _ = 0 := hl'.liminf_eq
  have hae := (lintegral_eq_zero_iff' (ENNReal.continuous_ofReal.comp hF).aemeasurable).mp hb
  have hae' : F =ᵐ[μ] 0 := by
    filter_upwards [hae] with x hx
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (hFn x)
  exact (hF.ae_eq_iff_eq μ continuous_const).mp hae'

end DensityLimit

noncomputable section
namespace DensityEnergy
open MeasureTheory Matrix WeightedCalculus Filter
open scoped ContDiff Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma henergy_nonneg {τ : Space ι → Matrix ι ι ℝ} (ht : ∀ x, (τ x).PosSemidef)
    {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (x : Space ι) : 0 ≤ henergy τ f x := by
  apply MomentMatrix.trace_conjugate_nonneg (ht x)
  ext i j
  exact MomentCoordinates.hess_symm hf x j i

lemma smooth_henergy {τ : Space ι → Matrix ι ι ℝ}
    (ht : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j))
    {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (henergy τ f) := by
  unfold henergy Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  apply ContDiff.sum; intro i _
  apply ContDiff.sum; intro j _
  apply ContDiff.mul
  · apply ContDiff.sum; intro k _
    apply ContDiff.mul
    · apply ContDiff.sum; intro l _
      exact (ht i l).mul (MomentCoordinates.smooth_pd (MomentCoordinates.smooth_pd hf l) k)
    · exact ht k j
  · exact MomentCoordinates.smooth_pd (MomentCoordinates.smooth_pd hf j) i

lemma compact_henergy {τ : Space ι → Matrix ι ι ℝ}
    {f : Space ι → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (henergy τ f) := by
  unfold henergy Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  apply compact_sum; intro i
  apply compact_sum; intro j
  exact (compact_D (compact_D hf _) _).mul_left

lemma hess_congr {f g : Space ι → ℝ} {x : Space ι} (h : f =ᶠ[𝓝 x] g) :
    MomentCoordinates.hess f x = MomentCoordinates.hess g x := by
  ext i j
  exact (D_eventuallyEq (D_eventuallyEq h (e i)) (e j)).eq_of_nhds

lemma eigen_hessian_zero (μ : Measure (Space ι)) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {τ : Space ι → Matrix ι ι ℝ}
    (hts : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (htp : ∀ x, (τ x).PosDef)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hupper : ∀ x, (Λ • (1 : Matrix ι ι ℝ)-τ x).PosSemidef)
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    (hidentity : ∀ f : Space ι → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, henergy τ f x ∂μ) = (∫ x, (A τ f x)^2 ∂μ)-(∫ x, f x*A τ f x ∂μ))
    {v : Space ι → ℝ} (hv : ContDiff ℝ ∞ v)
    (hiv : Integrable (fun x => v x^2) μ) (hAv : A τ v = v) :
    ∀ x, MomentCoordinates.hess v x = 0 := by
  let f (k : ℕ) : Space ι → ℝ := fun x => SmoothCutoff.seq k x*v x
  have hs (k : ℕ) : ContDiff ℝ ∞ (f k) := (SmoothCutoff.seq_smooth k).mul hv
  have hc (k : ℕ) : HasCompactSupport (f k) := (SmoothCutoff.seq_compact k).mul_right
  have hi (k : ℕ) : Integrable (henergy τ (f k)) μ :=
    (smooth_henergy hts (hs k)).continuous.integrable_of_hasCompactSupport (compact_henergy (hc k))
  obtain ⟨h1,h2⟩ := eigen_graph_integrals μ hts (fun x => (htp x).posSemidef) hΛ hupper hibp hv hiv hAv
  have ht : Tendsto (fun k => ∫ x, henergy τ (f k) x ∂μ) atTop (𝓝 0) := by
    simp only [hidentity _ (hs _) (hc _)]
    simpa only [sub_self] using h1.sub h2
  have he : henergy τ v = 0 := by
    apply DensityLimit.zero_of_local_limit μ (smooth_henergy hts hv).continuous
      (fun k => (smooth_henergy hts (hs k)).continuous)
      (henergy_nonneg (fun x => (htp x).posSemidef) hv)
      (fun k => henergy_nonneg (fun x => (htp x).posSemidef) (hs k)) hi _ ht
    intro x
    filter_upwards [cutoff_product_eventually v x] with k hk
    unfold henergy
    rw [hess_congr hk]
  intro x
  apply MomentMatrix.trace_conjugate_eq_zero (htp x)
  · ext i j; exact MomentCoordinates.hess_symm hv x j i
  · exact congrFun he x

theorem eigen_linear (μ : Measure (Space ι)) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {τ : Space ι → Matrix ι ι ℝ}
    (hts : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (htp : ∀ x, (τ x).PosDef)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hupper : ∀ x, (Λ • (1 : Matrix ι ι ℝ)-τ x).PosSemidef)
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    (hidentity : ∀ f : Space ι → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, henergy τ f x ∂μ) = (∫ x, (A τ f x)^2 ∂μ)-(∫ x, f x*A τ f x ∂μ))
    {v : Space ι → ℝ} (hv : ContDiff ℝ ∞ v)
    (hiv : Integrable (fun x => v x^2) μ) (hAv : A τ v = v) :
    ∃ b : ι → ℝ, ∀ x, v x = ∑ i, x i*b i := by
  have hh := eigen_hessian_zero μ hts htp hΛ hupper hibp hidentity hv hiv hAv
  have hg (i : ι) (x : Space ι) : D (e i) v x = D (e i) v 0 := by
    apply is_const_of_fderiv_eq_zero ((smooth_D hv (e i)).differentiable (by simp))
    intro y
    apply fderiv_zero_of_grad_zero
    funext j
    exact congrArg (fun M : Matrix ι ι ℝ => M i j) (hh y)
  refine ⟨fun i => D (e i) v 0, fun x => ?_⟩
  have hAx := congrFun hAv x
  have hz (i j : ι) : D (e i) (D (e j) v) x = 0 :=
    congrArg (fun M : Matrix ι ι ℝ => M j i) (hh x)
  simpa only [A,hz,mul_zero,Finset.sum_const_zero,sub_zero,hg] using hAx.symm


omit [Fintype ι] [DecidableEq ι] in
lemma compact_pow_succ {f : Space ι → ℝ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (fun x => f x^(n+1)) := by
  have hh : HasCompactSupport (fun x => f x^n*f x) := hf.mul_left
  simpa only [pow_succ] using hh

lemma kernel_cutoff_pointwise {τ : Space ι → Matrix ι ι ℝ} (htp : ∀ x, (τ x).PosSemidef)
    {η g : Space ι → ℝ} (hη : ContDiff ℝ ∞ η) (hg : ContDiff ℝ ∞ g)
    {D K : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hηn : ∀ x, 0 ≤ η x) (hηl : ∀ x, η x ≤ 1)
    (hηA : ∀ x, |A τ η x| ≤ K) (hηΓ : ∀ x, gamma τ η η x ≤ D) (x : Space ι) :
    η x^4*(A τ g x)^2 ≤
      2*(A τ g x*(A τ (fun y => η y^4*g y) x-η x^4*g x)) +
      2*(1+4*K+12*D)^2*g x^2+128*D*η x^2*gamma τ g g x := by
  have ht (y : Space ι) : (τ y)ᵀ = τ y := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (htp y).isHermitian.eq
  have hnΓ := gamma_nonneg htp η x
  have hgΓ := gamma_nonneg htp g x
  have hη2 : η x^2 ≤ 1 := by simpa using pow_le_pow_left₀ (hηn x) (hηl x) 2
  have hηA' : |η x*A τ η x| ≤ K := by
    rw [abs_mul,abs_of_nonneg (hηn x)]
    exact (mul_le_mul_of_nonneg_left (hηA x) (hηn x)).trans (by nlinarith [hηl x])
  have he := abs_le.mp hηA'
  have hq : |4*η x*A τ η x-12*gamma τ η η x-η x^2| ≤ 1+4*K+12*D := by
    rw [abs_le]
    constructor <;> nlinarith [hηΓ x,sq_nonneg (η x)]
  have hq2 : (4*η x*A τ η x-12*gamma τ η η x-η x^2)^2 ≤ (1+4*K+12*D)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hq
  have hqg := mul_le_mul_of_nonneg_right hq2 (sq_nonneg (g x))
  have hΓ := (gamma_cs htp η g x).trans (mul_le_mul_of_nonneg_right (hηΓ x) hgΓ)
  have hΓη := mul_le_mul_of_nonneg_left hΓ (sq_nonneg (η x))
  rw [A_mul ht (hη.pow 4) hg, A_pow_succ ht hη 2, gamma_pow_left hη 3]
  norm_num
  nlinarith [sq_nonneg (η x^2*A τ g x/2+g x*(4*η x*A τ η x-12*gamma τ η η x-η x^2)),
    sq_nonneg (η x^2*A τ g x/2-8*η x*gamma τ η g x)]

lemma kernel_A_square_integrable (μ : Measure (Space ι)) [IsFiniteMeasure μ]
    {τ : Space ι → Matrix ι ι ℝ}
    (hts : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (htp : ∀ x, (τ x).PosSemidef)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hupper : ∀ x, (Λ • (1 : Matrix ι ι ℝ)-τ x).PosSemidef)
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    {g : Space ι → ℝ} (hg : ContDiff ℝ ∞ g) (hig : Integrable (fun x => g x^2) μ)
    (hweak : ∀ h : Space ι → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
      (∫ x, A τ g x*(A τ h x-h x) ∂μ) = 0) :
    Integrable (fun x => (A τ g x)^2) μ := by
  obtain ⟨D,hD,hDb⟩ := cutoff_gamma_bound hΛ hupper
  obtain ⟨K,hK,hKb⟩ := cutoff_A_bound htp hΛ hupper
  let v := A τ g
  have hv : ContDiff ℝ ∞ v := smooth_A hts hg
  let η (k : ℕ) : Space ι → ℝ := SmoothCutoff.seq k
  have hs (k : ℕ) : ContDiff ℝ ∞ (η k) := SmoothCutoff.seq_smooth k
  have hc (k : ℕ) : HasCompactSupport (η k) := SmoothCutoff.seq_compact k
  have hbΓ (k : ℕ) (x : Space ι) : gamma τ (η k) (η k) x ≤ D := by
    apply (hDb _ (by positivity) x).trans
    exact div_le_self hD (by have := Nat.cast_nonneg (α:=ℝ) k; nlinarith)
  have hbA (k : ℕ) (x : Space ι) : |A τ (η k) x| ≤ K :=
    hKb _ (by have := Nat.cast_nonneg (α:=ℝ) k; linarith) x
  let G := ∫ x, g x^2 ∂μ
  let X (k : ℕ) := ∫ x, (η k x)^4*(v x)^2 ∂μ
  let Y (k : ℕ) := ∫ x, (η k x)^2*gamma τ g g x ∂μ
  let c := 256*(D+1)
  let a := 1+4*K+12*D
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : 1 ≤ c-128*D := by dsimp [c]; linarith
  have hG : 0 ≤ G := integral_nonneg (fun x => sq_nonneg (g x))
  have hiX (k : ℕ) : Integrable (fun x => η k x^4*v x^2) μ :=
    (((hs k).pow 4).mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport
      (compact_pow_succ (hc k) _).mul_right
  have hiY (k : ℕ) : Integrable (fun x => η k x^2*gamma τ g g x) μ :=
    (((hs k).pow 2).mul (smooth_gamma hts hg hg)).continuous.integrable_of_hasCompactSupport
      (compact_pow_succ (hc k) _).mul_right
  have hiT (k : ℕ) : Integrable (fun x => η k x^2*g x*v x) μ :=
    ((((hs k).pow 2).mul hg).mul hv).continuous.integrable_of_hasCompactSupport
      ((compact_pow_succ (hc k) _).mul_right).mul_right
  have hx (k : ℕ) : X k ≤ 2*a^2*G+128*D*Y k := by
    let q : Space ι → ℝ := fun x => η k x^4*g x
    have hqs : ContDiff ℝ ∞ q := ((hs k).pow 4).mul hg
    have hqc : HasCompactSupport q := (compact_pow_succ (hc k) _).mul_right
    have hiJ : Integrable (fun x => v x*(A τ q x-q x)) μ :=
      (hv.mul ((smooth_A hts hqs).sub hqs)).continuous.integrable_of_hasCompactSupport
        ((compact_A hqc).sub hqc).mul_left
    have hh := integral_mono (hiX k)
      (((hiJ.const_mul 2).add (hig.const_mul (2*a^2))).add ((hiY k).const_mul (128*D)))
      (fun x => by
        simpa only [Pi.add_apply,mul_assoc] using kernel_cutoff_pointwise htp (hs k) hg hD hK
          (SmoothCutoff.seq_nonneg k) (SmoothCutoff.seq_le_one k) (hbA k) (hbΓ k) x)
    simp only [Pi.add_apply] at hh
    change X k ≤ (∫ x, (2*(v x*(A τ q x-q x))+(2*a^2)*(g x^2)) + (128*D)*(η k x^2*gamma τ g g x) ∂μ) at hh
    have hadd₁ := integral_add ((hiJ.const_mul 2).add (hig.const_mul (2*a^2))) ((hiY k).const_mul (128*D))
    have hadd₂ := integral_add (hiJ.const_mul 2) (hig.const_mul (2*a^2))
    simp only [Pi.add_apply] at hadd₁
    rw [hadd₁,hadd₂,integral_const_mul,integral_const_mul,integral_const_mul] at hh
    have hw : (∫ x, v x*(A τ q x-q x) ∂μ) = 0 := hweak q hqs hqc
    simpa only [hw,mul_zero,zero_add] using hh
  have hy (k : ℕ) : c*Y k ≤ X k+(c^2+4*c*D)*G := by
    have he := energy_estimate μ hts htp hibp (hs k) (hc k) hg hig (hbΓ k)
    have he' := mul_le_mul_of_nonneg_left he hc0
    have hyoung := integral_mono ((hiT k).const_mul (2*c))
      ((hiX k).add (hig.const_mul (c^2))) (fun x => by
        simp only [Pi.add_apply]
        nlinarith [sq_nonneg (η k x^2*v x-c*g x)])
    simp only [Pi.add_apply] at hyoung
    rw [integral_add (hiX k) (hig.const_mul (c^2))] at hyoung
    simp only [integral_const_mul] at hyoung
    change c*Y k ≤ _
    dsimp [Y,X,G] at *
    nlinarith
  let C := (2*c*a^2+128*D*(c^2+4*c*D))*G
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (k : ℕ) : X k ≤ C := by
    have hX : 0 ≤ X k := integral_nonneg (fun x => mul_nonneg (pow_nonneg (SmoothCutoff.seq_nonneg k x) 4) (sq_nonneg _))
    have hx' := mul_le_mul_of_nonneg_left (hx k) hc0
    have hy' := mul_le_mul_of_nonneg_left (hy k) (by positivity : 0 ≤ 128*D)
    have hcX := mul_le_mul_of_nonneg_right hc1 hX
    dsimp [C]
    nlinarith
  exact (SmoothCutoff.integrable_of_cutoff_bound μ (hv.pow 2).continuous
    (fun x => sq_nonneg (v x)) 4 hC hbound hiX).1


lemma A_zero_of_not_tsupport {τ : Space ι → Matrix ι ι ℝ} {f : Space ι → ℝ} {x : Space ι}
    (hx : x ∉ tsupport f) : A τ f x = 0 := by
  have he : f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [A_congr he]
  have hz (i : ι) : D (e i) (fun _ : Space ι => (0 : ℝ)) = 0 := by
    ext y; simp [D]
  have hz' (i : ι) : D (e i) (0 : Space ι → ℝ) = 0 := hz i
  simp only [A,hz,hz',Pi.zero_apply,mul_zero,Finset.sum_const_zero,sub_zero]

lemma local_symmetry (μ : Measure (Space ι))
    {τ : Space ι → Matrix ι ι ℝ} (ht : ∀ x, (τ x)ᵀ = τ x)
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    {f g : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport f) :
    (∫ x, g x*A τ f x ∂μ) = ∫ x, f x*A τ g x ∂μ := by
  obtain ⟨R,hR⟩ := hfc.isBounded.subset_closedBall (0:Space ι)
  let r : ℝ := max R 0+1
  have hr : 0 < r := by dsimp [r]; positivity
  let g' : Space ι → ℝ := fun x => SmoothCutoff.cutoff r x*g x
  have hs : ContDiff ℝ ∞ g' := (SmoothCutoff.smooth r).mul hg
  have hc : HasCompactSupport g' := (SmoothCutoff.compact hr).mul_right
  have he (x : Space ι) (hx : x ∈ tsupport f) : g' =ᶠ[𝓝 x] g := by
    have hxR : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hR hx
    have hxr : ‖x‖ < r := by dsimp [r]; have := le_max_left R 0; linarith
    filter_upwards [SmoothCutoff.eventually_one hr hxr] with y hy
    change SmoothCutoff.cutoff r y*g y = g y
    rw [hy,one_mul]
  have hleft : (fun x => g' x*A τ f x) = fun x => g x*A τ f x := by
    ext x
    by_cases hx : x ∈ tsupport f
    · rw [(he x hx).eq_of_nhds]
    · rw [A_zero_of_not_tsupport hx,mul_zero,mul_zero]
  have hright : gamma τ g' f = gamma τ g f := by
    ext x
    by_cases hx : x ∈ tsupport f
    · unfold gamma; rw [grad_congr (he x hx)]
    · unfold gamma; rw [grad_zero_of_not_tsupport hx]
      simp only [Matrix.mulVec_zero,dotProduct_zero]
  rw [← hleft,hibp f g' hf hs hfc hc,hright,extend_integration μ hibp hg hf hfc]
  congr 1
  ext x
  exact gamma_symm ht g f x

lemma weak_kernel_of_eigen (μ : Measure (Space ι)) [IsFiniteMeasure μ]
    {τ : Space ι → Matrix ι ι ℝ}
    (hts : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (ht : ∀ x, (τ x)ᵀ = τ x)
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    {v : Space ι → ℝ} (hv : ContDiff ℝ ∞ v) (hAv : A τ v = v)
    {h : Space ι → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    (∫ x, v x*(A τ h x-h x) ∂μ) = 0 := by
  have hi1 : Integrable (fun x => v x*A τ h x) μ :=
    (hv.mul (smooth_A hts hh)).continuous.integrable_of_hasCompactSupport (compact_A hc).mul_left
  have hi2 : Integrable (fun x => v x*h x) μ :=
    (hv.mul hh).continuous.integrable_of_hasCompactSupport hc.mul_left
  simp_rw [mul_sub]
  rw [integral_sub hi1 hi2,local_symmetry μ ht hibp hh hv hc,hAv]
  simp only [mul_comm,sub_self]


lemma A_sub {τ : Space ι → Matrix ι ι ℝ} {f g : Space ι → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : A τ (f-g) = A τ f-A τ g := by
  have hd (i : ι) : D (e i) (f-g) = D (e i) f-D (e i) g :=
    D_sub (hf.differentiable (by simp)) (hg.differentiable (by simp)) _
  have hdd (i j : ι) : D (e i) (D (e j) f-D (e j) g) = D (e i) (D (e j) f)-D (e i) (D (e j) g) := by
    exact D_sub ((smooth_D hf _).differentiable (by simp)) ((smooth_D hg _).differentiable (by simp)) _
  ext x
  simp only [A,hdd,hd,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
  ring

theorem smooth_kernel_affine (μ : Measure (Space ι)) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {τ : Space ι → Matrix ι ι ℝ}
    (hts : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (htp : ∀ x, (τ x).PosDef)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hupper : ∀ x, (Λ • (1 : Matrix ι ι ℝ)-τ x).PosSemidef)
    (hibp : ∀ f h : Space ι → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      HasCompactSupport f → HasCompactSupport h →
      (∫ x, h x*A τ f x ∂μ) = ∫ x, gamma τ h f x ∂μ)
    (hidentity : ∀ f : Space ι → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, henergy τ f x ∂μ) = (∫ x, (A τ f x)^2 ∂μ)-(∫ x, f x*A τ f x ∂μ))
    {g : Space ι → ℝ} (hg : ContDiff ℝ ∞ g) (hig : Integrable (fun x => g x^2) μ)
    (hP : A τ (A τ g-g) = 0) :
    ∃ c : ℝ, ∃ b : ι → ℝ, ∀ x, g x = c+∑ i, x i*b i := by
  let v := A τ g
  have hv : ContDiff ℝ ∞ v := smooth_A hts hg
  have hAv : A τ v = v := by
    rw [A_sub hv hg,sub_eq_zero] at hP
    exact hP
  have ht (x : Space ι) : (τ x)ᵀ = τ x := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (htp x).isHermitian.eq
  have hiv : Integrable (fun x => v x^2) μ :=
    kernel_A_square_integrable μ hts (fun x => (htp x).posSemidef) hΛ hupper hibp hg hig
      (fun h hh hc => weak_kernel_of_eigen μ hts ht hibp hv hAv hh hc)
  let w := g-v
  have hw : ContDiff ℝ ∞ w := hg.sub hv
  have hiw : Integrable (fun x => w x^2) μ := by
    apply ((hig.const_mul 2).add (hiv.const_mul 2)).mono' (hw.pow 2).continuous.aestronglyMeasurable
    apply ae_of_all; intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (w x))]
    change (g x-v x)^2 ≤ 2*g x^2+2*v x^2
    nlinarith [sq_nonneg (g x+v x)]
  have hAw : A τ w = 0 := by rw [A_sub hg hv,hAv]; exact sub_self _
  have hc := harmonic_constant μ hts htp hΛ hupper hibp hw hiw hAw
  obtain ⟨b,hb⟩ := eigen_linear μ hts htp hΛ hupper hibp hidentity hv hiv hAv
  refine ⟨w 0,b,fun x => ?_⟩
  have hwx := hc x 0
  change g x-v x = w 0 at hwx
  rw [← hb x]
  linarith

end DensityEnergy

namespace MomentKernel

section
open MeasureTheory Matrix WeightedCalculus MomentCoordinates TargetCoordinates
open scoped ContDiff
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma A_eq_density {φ f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f)
    (Φ : Space ι ≃ₜ Space ι) :
    MomentOperator.A Φ φ f = DensityEnergy.A (MomentOperator.tau Φ φ) f := by
  ext x
  unfold MomentOperator.A DensityEnergy.A
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hess_symm hf x i j]
  rfl

lemma smooth_flux {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (Φ : Space ι ≃ₜ Space ι) (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (i : ι) :
    ContDiff ℝ ∞ (MomentOperator.flux Φ φ f i) :=
  smooth_sum _ (fun j => (smooth_tau hφ Φ hInv i j).mul (smooth_pd hf j))

lemma compact_flux {φ f : Space ι → ℝ} (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (i : ι) : HasCompactSupport (MomentOperator.flux Φ φ f i) :=
  compact_sum _ (fun j => (compact_D hfc (basis j)).mul_left)

variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

lemma integration_formula {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {c Z : ℝ} (hZ : 0 < Z)
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    {f h : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (hfc : HasCompactSupport f) :
    (∫ x, h x*DensityEnergy.A (MomentOperator.tau Φ φ) f x ∂targetMeasure μ V Z) =
      ∫ x, DensityEnergy.gamma (MomentOperator.tau Φ φ) h f x ∂targetMeasure μ V Z := by
  rw [target_integral μ hV hZ, target_integral μ hV hZ]
  unfold normalizedE
  congr 1
  rw [← A_eq_density hf Φ, ← MomentOperator.A_divergence hφ hV hf hne heq Φ hΦ hInv,
    divergence_adjoint μ basis _ hV (smooth_flux hφ hf Φ hInv) hh (compact_flux hfc Φ)]
  have he : DensityEnergy.gamma (MomentOperator.tau Φ φ) h f =
      fun x => ∑ i, D (basis i) h x*MomentOperator.flux Φ φ f i x := rfl
  rw [he, expectation_sum μ hV _ (fun i => ((smooth_D hh _).mul (smooth_flux hφ hf Φ hInv i)).continuous)
    (fun i => (compact_flux hfc Φ i).mul_left)]

lemma henergy_eq {φ f : Space ι → ℝ} (Φ : Space ι ≃ₜ Space ι) (x : Space ι) :
    DensityEnergy.henergy (MomentOperator.tau Φ φ) f x =
      ∑ a, ∑ k, (MomentOperator.tau Φ φ x*hess f x) k a *
        (MomentOperator.tau Φ φ x*hess f x) a k := by
  unfold DensityEnergy.henergy
  rw [Matrix.mul_assoc (MomentOperator.tau Φ φ x*hess f x)]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma hessian_identity {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z)
    [IsFiniteMeasure (targetMeasure μ V Z)]
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmap : Measure.map (grad φ) (sourceMeasure μ φ) = targetMeasure μ V Z)
    {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (∫ x, DensityEnergy.henergy (MomentOperator.tau Φ φ) f x ∂targetMeasure μ V Z) =
      (∫ x, (DensityEnergy.A (MomentOperator.tau Φ φ) f x)^2 ∂targetMeasure μ V Z)-
        (∫ x, f x*DensityEnergy.A (MomentOperator.tau Φ φ) f x ∂targetMeasure μ V Z) := by
  have hid := MomentOperator.hessian_identity_target μ hφ hV hf hfc hZ Φ hΦ hmap
  rw [← target_integral μ hV hZ, ← target_integral μ hV hZ] at hid
  rw [A_eq_density hf Φ] at hid
  have ha := DensityEnergy.smooth_A (smooth_tau hφ Φ hInv) hf
  have hc := DensityEnergy.compact_A (τ:=MomentOperator.tau Φ φ) hfc
  have hi₁ : Integrable (fun x => (DensityEnergy.A (MomentOperator.tau Φ φ) f x)^2) (targetMeasure μ V Z) :=
    (ha.pow 2).continuous.integrable_of_hasCompactSupport (DensityEnergy.compact_pow_succ hc 1)
  have hi₂ : Integrable (fun x => f x*DensityEnergy.A (MomentOperator.tau Φ φ) f x) (targetMeasure μ V Z) :=
    (hf.mul ha).continuous.integrable_of_hasCompactSupport hfc.mul_right
  have he : (fun x => DensityEnergy.A (MomentOperator.tau Φ φ) f x *
      (DensityEnergy.A (MomentOperator.tau Φ φ) f x-f x)) =
      fun x => (DensityEnergy.A (MomentOperator.tau Φ φ) f x)^2-f x*DensityEnergy.A (MomentOperator.tau Φ φ) f x := by
    ext x; ring
  rw [he,integral_sub hi₁ hi₂] at hid
  simpa only [henergy_eq] using hid.symm

theorem smooth_kernel_affine {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hpos : ∀ z, (hess φ z).PosDef) {c Z Λ : ℝ} (hZ : 0 < Z)
    [IsFiniteMeasure (targetMeasure μ V Z)] [Measure.IsOpenPosMeasure (targetMeasure μ V Z)]
    (hΛ : 0 ≤ Λ) (hupper : ∀ z, (Λ • (1 : Matrix ι ι ℝ)-hess φ z).PosSemidef)
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmap : Measure.map (grad φ) (sourceMeasure μ φ) = targetMeasure μ V Z)
    {g : Space ι → ℝ} (hg : ContDiff ℝ ∞ g)
    (hig : Integrable (fun x => g x^2) (targetMeasure μ V Z))
    (hP : DensityEnergy.A (MomentOperator.tau Φ φ)
      (DensityEnergy.A (MomentOperator.tau Φ φ) g-g) = 0) :
    ∃ a : ℝ, ∃ b : ι → ℝ, ∀ x, g x = a+∑ i, x i*b i := by
  apply DensityEnergy.smooth_kernel_affine (targetMeasure μ V Z) (smooth_tau hφ Φ hInv)
    (fun x => hpos (Φ.symm x)) hΛ (fun x => hupper (Φ.symm x))
    (fun _ _ hf hh hc _ => integration_formula μ hφ hV (fun z => (hpos z).det_pos.ne') hZ heq Φ hΦ hInv hf hh hc)
    (fun _ hf hc => hessian_identity μ hφ hV hZ Φ hΦ hInv hmap hf hc) hg hig hP

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

omit [DecidableEq ι] in
theorem integration_by_parts_rightcompact {V f g : Space ι → ℝ} (hV : ContDiff ℝ ∞ V)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (v : Space ι) :
    expectation μ V (fun x => D v g x * f x) =
      expectation μ V (fun x => g x * adjoint V v f x) := by
  let fw : Space ι → ℝ := fun x => f x * weight V x
  have hfw : ContDiff ℝ ∞ fw := hf.mul (smooth_weight hV)
  have hi₁ : Integrable (fun x => D v fw x * g x) μ :=
    ((smooth_D hfw v).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      hgc.mul_left
  have hi₂ : Integrable (fun x => fw x * D v g x) μ :=
    (hfw.continuous.mul (smooth_D hg v).continuous).integrable_of_hasCompactSupport
      (compact_D hgc v).mul_left
  have hi₃ : Integrable (fun x => fw x * g x) μ :=
    (hfw.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun x _ => hfw.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)
  calc
    _ = ∫ x, fw x * D v g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [expectation, fw]
      ring
    _ = -∫ x, D v fw x * g x ∂μ := hp
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [fw] at *
      rw [D_mul (hf.differentiable (by simp))
        ((smooth_weight hV).differentiable (by simp)), D_weight hV v]
      dsimp [adjoint]
      ring

lemma integration_formula_rightcompact {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {c Z : ℝ} (hZ : 0 < Z)
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    {f h : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) :
    (∫ x, h x*DensityEnergy.A (MomentOperator.tau Φ φ) f x ∂targetMeasure μ V Z) =
      ∫ x, DensityEnergy.gamma (MomentOperator.tau Φ φ) h f x ∂targetMeasure μ V Z := by
  rw [target_integral μ hV hZ, target_integral μ hV hZ]
  unfold normalizedE
  congr 1
  rw [← A_eq_density hf Φ, ← MomentOperator.A_divergence hφ hV hf hne heq Φ hΦ hInv]
  have he : (fun x => h x * divergence V basis (MomentOperator.flux Φ φ f) x) =
      fun x => ∑ i, h x * adjoint V (basis i) (MomentOperator.flux Φ φ f i) x := by
    ext x; simp only [divergence, Finset.mul_sum]
  have hg : DensityEnergy.gamma (MomentOperator.tau Φ φ) h f =
      fun x => ∑ i, D (basis i) h x*MomentOperator.flux Φ φ f i x := rfl
  rw [he, hg, expectation_sum μ hV _
    (fun i => (hh.mul (smooth_adjoint hV (smooth_flux hφ hf Φ hInv i) _)).continuous)
    (fun _ => hhc.mul_right), expectation_sum μ hV _
    (fun i => ((smooth_D hh _).mul (smooth_flux hφ hf Φ hInv i)).continuous)
    (fun i => (compact_D hhc (basis i)).mul_right)]
  apply Finset.sum_congr rfl
  intro i _
  exact (integration_by_parts_rightcompact μ hV (smooth_flux hφ hf Φ hInv i) hh hhc (basis i)).symm

lemma A_selfadjoint_onecompact {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {c Z : ℝ} (hZ : 0 < Z)
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    {f g : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport f) :
    (∫ x, g x*DensityEnergy.A (MomentOperator.tau Φ φ) f x ∂targetMeasure μ V Z) =
      ∫ x, f x*DensityEnergy.A (MomentOperator.tau Φ φ) g x ∂targetMeasure μ V Z := by
  rw [integration_formula μ hφ hV hne hZ heq Φ hΦ hInv hf hg hfc,
    integration_formula_rightcompact μ hφ hV hne hZ heq Φ hΦ hInv hg hf hfc]
  congr 1; ext x
  exact DensityEnergy.gamma_symm (fun x => MomentEquation.hess_transpose hφ (Φ.symm x)) g f x

lemma P_selfadjoint_onecompact {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {c Z : ℝ} (hZ : 0 < Z)
    [IsFiniteMeasure (targetMeasure μ V Z)]
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    {f g : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport f) :
    (∫ x, g x*DensityEnergy.A (MomentOperator.tau Φ φ)
      (DensityEnergy.A (MomentOperator.tau Φ φ) f-f) x ∂targetMeasure μ V Z) =
      ∫ x, f x*DensityEnergy.A (MomentOperator.tau Φ φ)
        (DensityEnergy.A (MomentOperator.tau Φ φ) g-g) x ∂targetMeasure μ V Z := by
  let A := DensityEnergy.A (MomentOperator.tau Φ φ)
  have hs := smooth_tau hφ Φ hInv
  have hAf := DensityEnergy.smooth_A hs hf
  have hAg := DensityEnergy.smooth_A hs hg
  have hAfC := DensityEnergy.compact_A (τ:=MomentOperator.tau Φ φ) hfc
  have hi₁ : Integrable (fun x => A f x*A g x) (targetMeasure μ V Z) :=
    (hAf.mul hAg).continuous.integrable_of_hasCompactSupport hAfC.mul_right
  have hi₂ : Integrable (fun x => f x*A g x) (targetMeasure μ V Z) :=
    (hf.mul hAg).continuous.integrable_of_hasCompactSupport hfc.mul_right
  have hi₃ : Integrable (fun x => f x*A (A g) x) (targetMeasure μ V Z) :=
    (hf.mul (DensityEnergy.smooth_A hs hAg)).continuous.integrable_of_hasCompactSupport hfc.mul_right
  have hadj := A_selfadjoint_onecompact μ hφ hV hne hZ heq Φ hΦ hInv
    (f := A f-f) (g := g) (hAf.sub hf) hg (hAfC.sub hfc)
  change (∫ x, g x*A (A f-f) x ∂targetMeasure μ V Z) = _ at hadj
  rw [hadj]
  change (∫ x, (A f x-f x)*A g x ∂targetMeasure μ V Z) =
    ∫ x, f x*A (A g-g) x ∂targetMeasure μ V Z
  simp_rw [sub_mul]
  rw [integral_sub hi₁ hi₂]
  have ha := A_selfadjoint_onecompact μ hφ hV hne hZ heq Φ hΦ hInv hf hAg hfc
  simp only [mul_comm (A f _)]
  change (∫ x, A g x*A f x ∂targetMeasure μ V Z)-_ = _
  rw [ha]
  change _ = ∫ x, f x * DensityEnergy.A (MomentOperator.tau Φ φ)
    (DensityEnergy.A (MomentOperator.tau Φ φ) g - g) x ∂targetMeasure μ V Z
  rw [DensityEnergy.A_sub hAg hg]
  simp only [Pi.sub_apply, mul_sub]
  exact (integral_sub hi₃ hi₂).symm

lemma smooth_weak_kernel_equation {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {c Z : ℝ} (hZ : 0 < Z)
    [IsFiniteMeasure (targetMeasure μ V Z)] [Measure.IsOpenPosMeasure (targetMeasure μ V Z)]
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    {g : Space ι → ℝ} (hg : ContDiff ℝ ∞ g)
    (hweak : ∀ f : Space ι → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, g x*DensityEnergy.A (MomentOperator.tau Φ φ)
        (DensityEnergy.A (MomentOperator.tau Φ φ) f-f) x ∂targetMeasure μ V Z) = 0) :
    DensityEnergy.A (MomentOperator.tau Φ φ)
      (DensityEnergy.A (MomentOperator.tau Φ φ) g-g) = 0 := by
  have hs := smooth_tau hφ Φ hInv
  have hPg := DensityEnergy.smooth_A hs ((DensityEnergy.smooth_A hs hg).sub hg)
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := targetMeasure μ V Z) hPg.continuous.locallyIntegrable
    (fun f hf hc => ?_)
  · exact MeasureTheory.Measure.eq_of_ae_eq hae hPg.continuous continuous_zero
  · change (∫ x, f x*DensityEnergy.A (MomentOperator.tau Φ φ)
      (DensityEnergy.A (MomentOperator.tau Φ φ) g-g) x ∂targetMeasure μ V Z) = 0
    rw [← P_selfadjoint_onecompact μ hφ hV hne hZ heq Φ hΦ hInv hf hg hc]
    exact hweak f hf hc

end

open MeasureTheory Matrix WeightedCalculus MomentCoordinates TargetCoordinates
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_A_eq (τ : Space ι → Matrix ι ι ℝ) (f : Space ι → ℝ) :
    MatrixOperator.A τ f = DensityEnergy.A τ f := rfl

theorem weak_kernel_affine {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hpos : ∀ z, (hess φ z).PosDef) {c Z Λ m : ℝ} (hZ : 0 < Z)
    [IsFiniteMeasure (targetMeasure volume V Z)] [Measure.IsOpenPosMeasure (targetMeasure volume V Z)]
    (hVlower : ∀ x, m ≤ V x)
    (hΛ : 0 ≤ Λ) (hupper : ∀ z, (Λ • (1 : Matrix ι ι ℝ)-hess φ z).PosSemidef)
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmap : Measure.map (grad φ) (sourceMeasure volume φ) = targetMeasure volume V Z)
    {g : Space ι → ℝ} (hg : MemLp g 2 (targetMeasure volume V Z))
    (hweak : ∀ f : Space ι → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, g x*DensityEnergy.A (MomentOperator.tau Φ φ)
        (DensityEnergy.A (MomentOperator.tau Φ φ) f-f) x ∂targetMeasure volume V Z) = 0) :
    ∃ a : ℝ, ∃ b : ι → ℝ, g =ᵐ[targetMeasure volume V Z] (fun x => a+∑ i, x i*b i) := by
  obtain ⟨w,hws,hwe⟩ := weak_kernel_smooth (ι:=ι) hφ hV hpos hZ hVlower Φ hInv hg hweak
  have hwe : g =ᵐ[targetMeasure volume V Z] w := hwe
  have hwLp : MemLp w 2 (targetMeasure volume V Z) := (memLp_congr_ae hwe).mp hg
  have hP := smooth_weak_kernel_equation (ι:=ι) (φ:=φ) (V:=V) (Z:=Z) (c:=c) (g:=w) volume hφ hV (fun z => (hpos z).det_pos.ne') hZ
    heq Φ hΦ hInv hws (by
      intro f hf hc
      calc
        _ = ∫ x, g x*DensityEnergy.A (MomentOperator.tau Φ φ)
          (DensityEnergy.A (MomentOperator.tau Φ φ) f-f) x ∂targetMeasure volume V Z := by
            apply integral_congr_ae
            filter_upwards [hwe] with x hx
            rw [hx]
        _ = 0 := hweak f hf hc)
  obtain ⟨a,b,hab⟩ := smooth_kernel_affine (ι:=ι) (φ:=φ) (V:=V) (Z:=Z) (Λ:=Λ) (c:=c) (g:=w) volume hφ hV hpos hZ hΛ hupper heq Φ hΦ hInv hmap
    hws hwLp.integrable_sq hP
  refine ⟨a,b,?_⟩
  filter_upwards [hwe] with x hx
  exact hx.trans (hab x)


end MomentKernel

namespace RealSmoothOperator
open MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

lemma squareLp_coe (ts : List (Term E)) (f : tests (E:=E)) :
    (squareLp μ ts f : E → ℝ) =ᵐ[μ] operator ts (operator ts f-f) := testsLp_coe μ _

lemma orthogonal_weak (ts : List (Term E)) {g : Lp ℝ 2 μ}
    (hg : g ∈ (squareRange μ ts)ᗮ) :
    ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, operator ts (operator ts f-f) x*g x ∂μ)=0 := by
  intro f hf hc
  have hh := hg (squareLp μ ts ⟨f,hf,hc⟩) ⟨⟨f,hf,hc⟩,rfl⟩
  rw [L2.inner_def] at hh
  calc
    _ = ∫ x, inner ℝ (squareLp μ ts ⟨f,hf,hc⟩ x) (g x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [squareLp_coe μ ts ⟨f,hf,hc⟩] with x hx
      rw [hx,real_inner_comm]
      rfl
    _ = 0 := hh

end RealSmoothOperator

namespace EvenClosure
open MeasureTheory
open scoped InnerProductSpace
variable {ι : Type*} [Fintype ι]
variable (μ : Measure (Space ι)) [IsFiniteMeasure μ]

lemma pair_affine_zero
    (hreflect : ∀ q : Space ι → ℝ, (∫ x, q (-x) ∂μ) = ∫ x, q x ∂μ)
    {F : Space ι → ℝ} (hF : MemLp F 2 μ) (hFe : ∀ x, F (-x) = F x)
    (hFc : (∫ x, F x ∂μ)=0) (a : ℝ) (b : ι → ℝ)
    (hg : MemLp (fun x : Space ι => a+∑ i, x i*b i) 2 μ) :
    (∫ x, F x*(a+∑ i, x i*b i) ∂μ)=0 := by
  let q : Space ι → ℝ := fun x => F x*(a+∑ i, x i*b i)
  have hqi : Integrable q μ := hF.integrable_mul hg
  have hFi : Integrable F μ := MemLp.integrable (by norm_num) hF
  have he (x : Space ι) : q (-x) = (2*a)*F x-q x := by
    dsimp [q]
    rw [hFe]
    simp only [neg_mul,Finset.sum_neg_distrib]
    ring
  have hi := hreflect q
  simp_rw [he] at hi
  rw [integral_sub (hFi.const_mul _) hqi,integral_const_mul,hFc,mul_zero] at hi
  change (∫ x, q x ∂μ)=0
  linarith

theorem mem_closure_of_affine_orthogonal
    (hreflect : ∀ q : Space ι → ℝ, (∫ x, q (-x) ∂μ) = ∫ x, q x ∂μ)
    (S : Submodule ℝ (Lp ℝ 2 μ))
    (hkernel : ∀ g : Lp ℝ 2 μ, g ∈ Sᗮ →
      ∃ a : ℝ, ∃ b : ι → ℝ, (g : Space ι → ℝ) =ᵐ[μ] (fun x => a+∑ i, x i*b i))
    {F : Space ι → ℝ} (hF : MemLp F 2 μ) (hFe : ∀ x, F (-x)=F x)
    (hFc : (∫ x, F x ∂μ)=0) :
    hF.toLp F ∈ closure (S : Set (Lp ℝ 2 μ)) := by
  change hF.toLp F ∈ S.topologicalClosure
  rw [← S.orthogonal_orthogonal_eq_closure]
  intro g hg
  obtain ⟨a,b,hab⟩ := hkernel g hg
  have hga : MemLp (fun x : Space ι => a+∑ i, x i*b i) 2 μ := (memLp_congr_ae hab).mp (Lp.memLp g)
  rw [L2.inner_def]
  calc
    _ = ∫ x, F x*(a+∑ i, x i*b i) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp,hab] with x hx hy
      rw [hx,hy]
      rfl
    _ = 0 := pair_affine_zero μ hreflect hF hFe hFc a b hga

end EvenClosure

namespace MomentKernel
open MeasureTheory Matrix WeightedCalculus MomentCoordinates TargetCoordinates
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma target_integral_reflect {V : Space ι → ℝ} (hV : ContDiff ℝ ∞ V)
    (hVe : ∀ x, V (-x)=V x) {Z : ℝ} (hZ : 0 < Z) (q : Space ι → ℝ) :
    (∫ x, q (-x) ∂targetMeasure volume V Z) = ∫ x, q x ∂targetMeasure volume V Z := by
  apply WeightedRegularity.integral_reflect (E:=Space ι) volume
    (ρ:=fun x : Space ι => weight V x/Z)
    ((smooth_weight hV).div_const Z).continuous.measurable
    (fun x : Space ι => (div_pos (Real.exp_pos _) hZ).le) (f:=q)
  intro x
  dsimp [weight]
  rw [hVe]

theorem centered_even_mem_closure {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hVe : ∀ x, V (-x)=V x)
    (hpos : ∀ z, (hess φ z).PosDef) {c Z Λ m : ℝ} (hZ : 0 < Z)
    [IsFiniteMeasure (targetMeasure volume V Z)] [Measure.IsOpenPosMeasure (targetMeasure volume V Z)]
    (hVlower : ∀ x, m ≤ V x)
    (hΛ : 0 ≤ Λ) (hupper : ∀ z, (Λ • (1 : Matrix ι ι ℝ)-hess φ z).PosSemidef)
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmap : Measure.map (grad φ) (sourceMeasure volume φ) = targetMeasure volume V Z)
    {F : Space ι → ℝ} (hF : MemLp F 2 (targetMeasure volume V Z))
    (hFe : ∀ x, F (-x)=F x) (hFc : (∫ x, F x ∂targetMeasure volume V Z)=0) :
    hF.toLp F ∈ closure ((RealSmoothOperator.squareRange (E:=Space ι) (targetMeasure volume V Z)
      (MatrixOperator.principal (MomentOperator.tau Φ φ) (smooth_tau hφ Φ hInv)++
        MatrixOperator.drift)) : Set (Lp ℝ 2 (targetMeasure volume V Z))) := by
  refine EvenClosure.mem_closure_of_affine_orthogonal (ι:=ι) (targetMeasure volume V Z)
    (S := RealSmoothOperator.squareRange (E:=Space ι) (targetMeasure volume V Z)
      (MatrixOperator.principal (MomentOperator.tau Φ φ) (smooth_tau hφ Φ hInv)++
        MatrixOperator.drift (ι:=ι))) ?_ ?_ hF hFe hFc
  · exact target_integral_reflect hV hVe hZ
  · intro g hg
    apply weak_kernel_affine (ι:=ι) (φ:=φ) (V:=V) (Z:=Z) (Λ:=Λ) (c:=c) (m:=m) (g:=g) hφ hV hpos hZ hVlower hΛ hupper heq Φ hΦ hInv hmap (Lp.memLp g)
    intro f hf hc
    have hw := RealSmoothOperator.orthogonal_weak (E:=Space ι) (targetMeasure volume V Z)
      (MatrixOperator.principal (MomentOperator.tau Φ φ) (smooth_tau hφ Φ hInv)++
        MatrixOperator.drift) hg f hf hc
    rw [MatrixOperator.operator_actual,MatrixOperator.operator_actual] at hw
    simpa only [matrix_A_eq,mul_comm] using hw

end MomentKernel

end

open Matrix
open scoped BigOperators Kronecker
noncomputable section

namespace SoftSlab

section
open WeightedCalculus MomentCoordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma linear_apply (p x : ι → ℝ) : linear p x = ∑ i, p i * x i := by
  simp [linear]

lemma linear_basis (p : ι → ℝ) (i : ι) : linear p (basis i) = p i := by
  simp [linear_apply, basis, Pi.single_apply]

omit [DecidableEq ι] in
lemma smooth_summand (p : ι → ℝ) (h : ℝ) (q : ℕ) : ContDiff ℝ ∞ (summand p h q) :=
  ((linear p).contDiff.div_const h).pow q

omit [DecidableEq ι] in
lemma summand_even {q : ℕ} (hq : Even q) (p : ι → ℝ) (h : ℝ) :
    Function.Even (summand p h q) := by
  intro x
  simp only [summand, map_neg, neg_div, hq.neg_pow]

omit [DecidableEq ι] in
lemma summand_nonneg {q : ℕ} (hq : Even q) (p : ι → ℝ) (h : ℝ) (x : Space ι) :
    0 ≤ summand p h q x := hq.pow_nonneg _

end

open MeasureTheory WeightedCalculus MomentCoordinates
open scoped BigOperators ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
lemma smooth_potential (ε : ℝ) (p : κ → ι → ℝ) (h : κ → ℝ) (q : ℕ) :
    ContDiff ℝ ∞ (potential ε p h q) := by
  apply ContDiff.add
  · exact contDiff_const.mul (ContDiff.sum (fun j _ => (contDiff_apply ℝ ℝ j).pow 2))
  · exact ContDiff.sum (fun i _ => smooth_summand (p i) (h i) q)

omit [DecidableEq ι] in
lemma potential_even {q : ℕ} (hq : Even q) (ε : ℝ) (p : κ → ι → ℝ) (h : κ → ℝ) :
    Function.Even (potential ε p h q) := by
  intro x
  simp only [potential, Pi.neg_apply, neg_sq]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => summand_even hq (p i) (h i) x)

omit [DecidableEq ι] in
lemma potential_lower {q : ℕ} (hq : Even q) (ε : ℝ) (p : κ → ι → ℝ) (h : κ → ℝ) (x : Space ι) :
    ε/2*(∑ j, x j^2) ≤ potential ε p h q x := by
  unfold potential
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => summand_nonneg hq (p i) (h i) x))


end SoftSlab
end

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace GaussianPolynomial
section
variable {ι : Type*} [Fintype ι]

lemma gaussian_product (b : ℝ) (x : ι → ℝ) :
    Real.exp (-b * ∑ i, x i ^ 2) = ∏ i, Real.exp (-b * x i ^ 2) := by
  rw [Finset.mul_sum, Real.exp_sum]

lemma monomial_integrable {b : ℝ} (hb : 0 < b) (d : ι → ℕ) :
    Integrable (fun x : ι → ℝ => (∏ i, x i ^ d i) * Real.exp (-b * ∑ i, x i^2)) := by
  have hi (i : ι) : Integrable (fun x : ℝ => x ^ d i * Real.exp (-b * x^2)) := by
    simpa only [Real.rpow_natCast] using
      integrable_rpow_mul_exp_neg_mul_sq hb (by have := Nat.cast_nonneg (α := ℝ) (d i); linarith : (-1:ℝ) < (d i : ℝ))
  have hp := Integrable.fintype_prod hi
  have he : (fun x : ι → ℝ => (∏ i, x i ^ d i) * Real.exp (-b * ∑ i, x i^2)) =
      (fun x : ι → ℝ => ∏ i, x i ^ d i * Real.exp (-b * x i^2)) := by
    funext x
    rw [gaussian_product, Finset.prod_mul_distrib]
  rw [he]
  exact hp

lemma polynomial_integrable {b : ℝ} (hb : 0 < b) (P : MvPolynomial ι ℝ) :
    Integrable (fun x : ι → ℝ => MvPolynomial.eval x P * Real.exp (-b * ∑ i, x i^2)) := by
  have hi : Integrable (fun x : ι → ℝ => ∑ d ∈ P.support,
      P.coeff d * ((∏ i, x i ^ d i) * Real.exp (-b * ∑ i, x i^2))) := by
    exact integrable_finsetSum _ (fun d _ => (monomial_integrable hb d).const_mul _)
  convert hi using 1
  funext x
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  ring

lemma dominated_polynomial {V : (ι → ℝ) → ℝ} (hV : Continuous V)
    {b c : ℝ} (hb : 0 < b) (hlower : ∀ x, b * (∑ i, x i^2) - c ≤ V x)
    (P : MvPolynomial ι ℝ) :
    Integrable (fun x : ι → ℝ => MvPolynomial.eval x P * Real.exp (-V x)) := by
  have hmaj := (polynomial_integrable hb P).norm.const_mul (Real.exp c)
  apply hmaj.mono' (((MvPolynomial.continuous_eval P).mul (Real.continuous_exp.comp hV.neg)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖MvPolynomial.eval x P * Real.exp (-V x)‖ ≤
    Real.exp c * ‖MvPolynomial.eval x P * Real.exp (-b * ∑ i, x i^2)‖
  simp only [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-V x) ≤ Real.exp c * Real.exp (-b * ∑ i, x i^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hlower x]
  calc
    _ ≤ ‖MvPolynomial.eval x P‖ * (Real.exp c * Real.exp (-b * ∑ i, x i^2)) :=
      mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ = _ := by ring

lemma partition_integrable {V : (ι → ℝ) → ℝ} (hV : Continuous V)
    {b c : ℝ} (hb : 0 < b) (hlower : ∀ x, b * (∑ i, x i^2) - c ≤ V x) :
    Integrable (fun x => Real.exp (-V x)) := by
  simpa using dominated_polynomial hV hb hlower (1 : MvPolynomial ι ℝ)

end

open MeasureTheory
variable {ι : Type*} [Fintype ι]

lemma normalized_polynomial {V : (ι → ℝ) → ℝ} (hV : Continuous V)
    {b c Z : ℝ} (hb : 0 < b) (hZ : 0 < Z)
    (hlower : ∀ x, b * (∑ i, x i^2) - c ≤ V x) (P : MvPolynomial ι ℝ) :
    Integrable (fun x => MvPolynomial.eval x P)
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)/Z))) := by
  have hm : Measurable (fun x : ι → ℝ => ENNReal.ofReal (Real.exp (-V x)/Z)) :=
    ((Real.continuous_exp.comp hV.neg).div_const Z).measurable.ennreal_ofReal
  apply (integrable_withDensity_iff_integrable_smul' (μ:=volume) hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have he (x : ι → ℝ) : (ENNReal.ofReal (Real.exp (-V x)/Z)).toReal • MvPolynomial.eval x P =
      (MvPolynomial.eval x P*Real.exp (-V x))/Z := by
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le), smul_eq_mul]
    ring
  simp_rw [he]
  exact (dominated_polynomial hV hb hlower P).div_const Z

lemma partition_pos {V : (ι → ℝ) → ℝ} (hV : Continuous V)
    {b c : ℝ} (hb : 0 < b) (hlower : ∀ x, b * (∑ i, x i^2) - c ≤ V x) :
    0 < ∫ x, Real.exp (-V x) :=
  integral_exp_pos (partition_integrable hV hb hlower)

lemma normalized_probability {V : (ι → ℝ) → ℝ} (hV : Continuous V)
    {b c : ℝ} (hb : 0 < b) (hlower : ∀ x, b * (∑ i, x i^2) - c ≤ V x) :
    IsProbabilityMeasure (volume.withDensity
      (fun x => ENNReal.ofReal (Real.exp (-V x)/(∫ y, Real.exp (-V y))))) := by
  have hZ := partition_pos hV hb hlower
  apply isProbabilityMeasure_iff.mpr
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · simp only [integral_div, div_self (ne_of_gt hZ), ENNReal.ofReal_one]
  · exact (partition_integrable hV hb hlower).div_const _
  · exact Filter.Eventually.of_forall (fun x => div_nonneg (Real.exp_pos _).le hZ.le)

end GaussianPolynomial

namespace SoftSlab
open MeasureTheory WeightedCalculus MomentCoordinates
open scoped BigOperators ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
lemma eval_linearPolynomial (p : ι → ℝ) (h : ℝ) (x : Space ι) :
    MvPolynomial.eval x (linearPolynomial p h) = linear p x/h := by
  simp [linearPolynomial, linear_apply, map_sum, div_eq_mul_inv]

omit [DecidableEq ι] in
lemma potential_partition_pos {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) : 0 < ∫ x, Real.exp (-potential ε p h q x) :=
  GaussianPolynomial.partition_pos (c:=0) (smooth_potential ε p h q).continuous (half_pos hε)
    (by intro x; simpa using potential_lower hq ε p h x)

omit [DecidableEq ι] in
lemma potential_probability {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) : IsProbabilityMeasure (law ε p h q) :=
  GaussianPolynomial.normalized_probability (c:=0) (smooth_potential ε p h q).continuous (half_pos hε)
    (by intro x; simpa using potential_lower hq ε p h x)

omit [DecidableEq ι] in
lemma polynomial_moment {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (P : MvPolynomial ι ℝ) :
    Integrable (fun x => MvPolynomial.eval x P) (law ε p h q) :=
  GaussianPolynomial.normalized_polynomial (c:=0) (smooth_potential ε p h q).continuous (half_pos hε)
    (potential_partition_pos hq hε p h) (by intro x; simpa using potential_lower hq ε p h x) P

omit [DecidableEq ι] in
lemma integrable_summand {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (v : ι → ℝ) (r : ℝ) (m : ℕ) :
    Integrable (summand v r m) (law ε p h q) := by
  change Integrable (fun x => (linear v x/r)^m) _
  simpa only [map_pow, eval_linearPolynomial] using
    polynomial_moment hq hε p h ((linearPolynomial v r)^m)

lemma mean_summand_pos {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) {v : ι → ℝ} (hv : v ≠ 0) {r : ℝ} (hr : r ≠ 0)
    {m : ℕ} (hm : Even m) : 0 < ∫ x, summand v r m x ∂law ε p h q := by
  have hZ := potential_partition_pos hq hε p h
  have hV := (smooth_potential ε p h q).continuous
  have hi : Integrable (fun x => summand v r m x*Real.exp (-potential ε p h q x)) := by
    simpa only [map_pow, eval_linearPolynomial, summand] using
      GaussianPolynomial.dominated_polynomial (c:=0) hV (half_pos hε)
        (by intro x; simpa using potential_lower hq ε p h x) ((linearPolynomial v r)^m)
  have hp : 0 < ∫ x, summand v r m x*Real.exp (-potential ε p h q x) := by
    obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv (funext hc)
    apply integral_pos_of_integrable_nonneg_nonzero
      ((smooth_summand v r m).continuous.mul (Real.continuous_exp.comp hV.neg)) hi
      (fun x => mul_nonneg (summand_nonneg hm v r x) (Real.exp_pos _).le) (x:=basis j)
    exact mul_ne_zero (pow_ne_zero _ (div_ne_zero (by simpa only [linear_basis] using hj) hr))
      (Real.exp_ne_zero _)
  change 0 < ∫ x, summand v r m x ∂volume.withDensity _
  have hmeas : Measurable (fun x : Space ι => ENNReal.ofReal (Real.exp (-potential ε p h q x)/
      (∫ y, Real.exp (-potential ε p h q y)))) :=
    ((Real.continuous_exp.comp hV.neg).div_const _).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he (x : Space ι) : (ENNReal.ofReal (Real.exp (-potential ε p h q x)/
      (∫ y, Real.exp (-potential ε p h q y)))).toReal • summand v r m x =
      (summand v r m x*Real.exp (-potential ε p h q x))/(∫ y, Real.exp (-potential ε p h q y)) := by
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le), smul_eq_mul]
    ring
  simp_rw [he]
  rw [integral_div]
  exact div_pos hp hZ

end SoftSlab
end

open scoped BigOperators InnerProductSpace Topology

noncomputable section
namespace VarianceDuality

variable {ι : Type*} [Fintype ι]

lemma quadratic_cs (a b c : ℝ) (h : ∀ t : ℝ, 0 ≤ c - 2*t*b + t^2*a) :
    b^2 ≤ a*c := by
  have hd := discrim_le_zero (a := a) (b := -2*b) (c := c) (fun t => by
    have ht := h t
    nlinarith)
  dsimp [discrim] at hd
  nlinarith

lemma weighted_coefficient_cs (a b d : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (∑ i, b i * d i)^2 ≤ (∑ i, b i^2 * a i) * (∑ i, d i^2 / a i) := by
  apply quadratic_cs
  intro t
  calc
    _ = ∑ i, (d i - t * a i * b i)^2 / a i := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [ne_of_gt (ha i)]
      ring
    _ ≥ 0 := Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (ha i).le)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem extend_dual_bound (a : ι → ℝ) (ψ : ι → E) (S : Set E)
    (hS : ∀ u ∈ S, ∑ i, ⟪u, ψ i⟫_ℝ ^ 2 / a i ≤ ‖u‖^2)
    {u : E} (hu : u ∈ closure S) :
    ∑ i, ⟪u, ψ i⟫_ℝ ^ 2 / a i ≤ ‖u‖^2 := by
  have hc : IsClosed {u : E | ∑ i, ⟪u, ψ i⟫_ℝ ^ 2 / a i ≤ ‖u‖^2} := by
    apply isClosed_le
    · exact continuous_finsetSum _ (fun i _ =>
        ((continuous_id.inner continuous_const).pow 2).div_const (a i))
    · exact continuous_norm.pow 2
  exact hc.closure_subset_iff.mpr hS hu

end VarianceDuality

namespace LpVariance
open MeasureTheory
open scoped InnerProductSpace
variable {X : Type*} {ι : Type*} [MeasurableSpace X] [Fintype ι]
variable (μ : Measure X)

lemma lp_inner (f g : Lp ℝ 2 μ) : inner ℝ f g = ∫ x, f x*g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [real_inner_comm]
  rfl

lemma lp_norm_sq (f : Lp ℝ 2 μ) : ‖f‖^2 = ∫ x, (f x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,lp_inner]
  simp only [sq]

lemma toLp_inner {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x*g x ∂μ := by
  rw [lp_inner]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  rw [hx,hy]

lemma toLp_norm_sq {f : X → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,toLp_inner]
  simp only [sq]

theorem integral_dual_extend (a : ι → ℝ) (ψ : ι → X → ℝ) (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (S : Set (Lp ℝ 2 μ))
    (hS : ∀ u ∈ S, (∑ i, (∫ x, u x*ψ i x ∂μ)^2/a i) ≤ ∫ x, (u x)^2 ∂μ)
    {F : X → ℝ} (hF : MemLp F 2 μ) (hclosure : hF.toLp F ∈ closure S) :
    (∑ i, (∫ x, F x*ψ i x ∂μ)^2/a i) ≤ ∫ x, (F x)^2 ∂μ := by
  have hd := VarianceDuality.extend_dual_bound a (fun i => (hψ i).toLp (ψ i)) S (by
    intro u hu
    have hi (i : ι) : inner ℝ u ((hψ i).toLp (ψ i)) = ∫ x, u x*ψ i x ∂μ := by
      rw [lp_inner]
      apply integral_congr_ae
      filter_upwards [(hψ i).coeFn_toLp] with x hx
      rw [hx]
    simp_rw [hi,lp_norm_sq]
    exact hS u hu) hclosure
  simpa only [toLp_inner,toLp_norm_sq] using hd

variable [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma sum_memLp (ψ : ι → X → ℝ) (hψ : ∀ i, MemLp (ψ i) 2 μ) (b : ι → ℝ) :
    MemLp (sumPotential ψ b) 2 μ := by
  apply memLp_finsetSum
  intro i _
  exact (hψ i).const_mul (b i)

lemma centered_memLp {f : X → ℝ} (hf : MemLp f 2 μ) : MemLp (centered μ f) 2 μ :=
  hf.sub (memLp_const _)

lemma centered_integral {f : X → ℝ} (hf : Integrable f μ) : (∫ x, centered μ f x ∂μ)=0 := by
  change (∫ x, f x-(∫ y, f y ∂μ) ∂μ)=0
  rw [integral_sub hf (integrable_const _),integral_const]
  simp

lemma centered_sq {f : X → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, (centered μ f x)^2 ∂μ) = (∫ x, (f x)^2 ∂μ)-(∫ x, f x ∂μ)^2 := by
  have hfi : Integrable f μ := MemLp.integrable (by norm_num) hf
  have he (x : X) : (centered μ f x)^2 = (f x)^2-(2*(∫ y, f y ∂μ))*f x+(∫ y, f y ∂μ)^2 := by
    dsimp [centered]
    ring
  simp_rw [he]
  rw [integral_add (f:=fun x => (f x)^2-(2*(∫ y, f y ∂μ))*f x)
      (g:=fun _ => (∫ y, f y ∂μ)^2)
      (hf.integrable_sq.sub (hfi.const_mul _)) (integrable_const _),
    integral_sub hf.integrable_sq (hfi.const_mul _),integral_const_mul,integral_const]
  simp only [probReal_univ,one_smul]
  ring

lemma centered_pair_sum (ψ : ι → X → ℝ) (hψ : ∀ i, MemLp (ψ i) 2 μ) (b : ι → ℝ) :
    (∑ i, b i*(∫ x, centered μ (sumPotential ψ b) x*ψ i x ∂μ)) =
      ∫ x, (centered μ (sumPotential ψ b) x)^2 ∂μ := by
  let F := sumPotential ψ b
  have hF : MemLp F 2 μ := sum_memLp μ ψ hψ b
  have hC := centered_memLp μ hF
  have hCi : Integrable (centered μ F) μ := MemLp.integrable (by norm_num) hC
  have hpair : (∫ x, centered μ F x*F x ∂μ) = ∫ x, (centered μ F x)^2 ∂μ := by
    have he (x : X) : centered μ F x*F x = (centered μ F x)^2 + (∫ y, F y ∂μ)*centered μ F x := by
      dsimp [centered]
      ring
    simp_rw [he]
    rw [integral_add hC.integrable_sq (hCi.const_mul _),integral_const_mul,
      centered_integral μ (MemLp.integrable (by norm_num) hF)]
    ring
  rw [← hpair]
  change _ = ∫ x, centered μ F x*(∑ i, b i*ψ i x) ∂μ
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => by
    simpa only [Pi.mul_apply,mul_left_comm] using (hC.integrable_mul (hψ i)).const_mul (b i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem variance_of_centered_dual (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (ψ : ι → X → ℝ) (hψ : ∀ i, MemLp (ψ i) 2 μ) (b : ι → ℝ)
    (hd : (∑ i, (∫ x, centered μ (sumPotential ψ b) x*ψ i x ∂μ)^2/a i) ≤
      ∫ x, (centered μ (sumPotential ψ b) x)^2 ∂μ) :
    (∫ x, (sumPotential ψ b x)^2 ∂μ)-(∫ x, sumPotential ψ b x ∂μ)^2 ≤ ∑ i, b i^2*a i := by
  let d (i : ι) := ∫ x, centered μ (sumPotential ψ b) x*ψ i x ∂μ
  let v := ∫ x, (centered μ (sumPotential ψ b) x)^2 ∂μ
  have hv : 0 ≤ v := integral_nonneg (fun x => sq_nonneg _)
  have hpair : (∑ i, b i*d i)=v := centered_pair_sum μ ψ hψ b
  have hc := VarianceDuality.weighted_coefficient_cs a b d ha
  rw [hpair] at hc
  have hnon : 0 ≤ ∑ i, b i^2*a i := Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (ha i).le)
  have hm := mul_le_mul_of_nonneg_left hd hnon
  have hvbound : v ≤ ∑ i, b i^2*a i := by
    by_cases hv0 : v=0
    · simpa [hv0] using hnon
    · have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
      change v^2 ≤ _ at hc
      change _ ≤ (∑ i, b i^2*a i)*v at hm
      nlinarith
  rw [← centered_sq μ (sum_memLp μ ψ hψ b)]
  exact hvbound

end LpVariance

namespace PositiveDensity
open MeasureTheory
variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]

lemma isOpenPos (μ : Measure E) [Measure.IsOpenPosMeasure μ] {ρ : E → ℝ}
    (hm : Measurable ρ) (hp : ∀ x, 0 < ρ x) :
    Measure.IsOpenPosMeasure (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  have hac : μ ≪ μ.withDensity (fun x => ENNReal.ofReal (ρ x)) :=
    withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hm).aemeasurable
      (Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hp x)).ne')
  constructor
  intro U hU hne hz
  exact hU.measure_ne_zero μ hne (hac hz)

end PositiveDensity

namespace SoftSlab
open MeasureTheory WeightedCalculus MomentCoordinates TargetCoordinates
open scoped ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
lemma summand_memLp {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (v : ι → ℝ) (r : ℝ) (m : ℕ) :
    MemLp (summand v r m) 2 (law ε p h q) := by
  rw [memLp_two_iff_integrable_sq ((smooth_summand v r m).continuous.aestronglyMeasurable)]
  have hi := integrable_summand hq hε p h v r (m*2)
  change Integrable (fun x => (linear v x/r)^(m*2)) _ at hi
  simpa only [summand,pow_mul] using hi

omit [DecidableEq ι] in
lemma potential_nonneg {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 ≤ ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (x : Space ι) : 0 ≤ potential ε p h q x := by
  apply le_trans _ (potential_lower hq ε p h x)
  exact mul_nonneg (div_nonneg hε (by norm_num)) (Finset.sum_nonneg (fun i _ => sq_nonneg _))

omit [DecidableEq ι] in
lemma law_openPos {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) : Measure.IsOpenPosMeasure (law ε p h q) := by
  apply PositiveDensity.isOpenPos volume
  · exact ((smooth_weight (smooth_potential ε p h q)).div_const _).continuous.measurable
  · exact fun x => div_pos (Real.exp_pos _) (potential_partition_pos hq hε p h)

end SoftSlab

namespace MomentSlab
open MeasureTheory WeightedCalculus MomentCoordinates TargetCoordinates SoftSlab FullTensor
open scoped ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem variance_from_moment_oai {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (hp : ∀ i, p i ≠ 0) (hh : ∀ i, 0 < h i)
    {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ z, (hess φ z).PosDef)
    (hupper : ∀ z, ((4/ε) • (1 : Matrix ι ι ℝ)-hess φ z).PosSemidef)
    (heq : ∀ z, Real.log (hess φ z).det = potential ε p h (q+2) (grad φ z)+
      Real.log (∫ x, Real.exp (-potential ε p h (q+2) x))-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmap : Measure.map (grad φ) (sourceMeasure volume φ) = law ε p h (q+2)) (b : κ → ℝ) :
    (∫ x, (∑ i, b i*summand (p i) (h i) (q+2) x)^2 ∂law ε p h (q+2))-
      (∫ x, ∑ i, b i*summand (p i) (h i) (q+2) x ∂law ε p h (q+2))^2 ≤
      ∑ i, b i^2*(∫ x, summand (p i) (h i) (q+2) x ∂law ε p h (q+2)) := by
  let V := potential ε p h (q+2)
  let Z := ∫ x, Real.exp (-V x)
  let μ := law ε p h (q+2)
  let ψ (i : κ) := summand (p i) (h i) (q+2)
  have hqe := hq.add even_two
  let : IsProbabilityMeasure μ := potential_probability hqe hε p h
  let : Measure.IsOpenPosMeasure μ := law_openPos hqe hε p h
  let : IsProbabilityMeasure (targetMeasure volume V Z) := potential_probability hqe hε p h
  let : Measure.IsOpenPosMeasure (targetMeasure volume V Z) := law_openPos hqe hε p h
  have hψ (i : κ) : MemLp (ψ i) 2 μ := summand_memLp hqe hε p h (p i) (h i) (q+2)
  let F := LpVariance.centered μ (LpVariance.sumPotential ψ b)
  have hF : MemLp F 2 μ := LpVariance.centered_memLp μ (LpVariance.sum_memLp μ ψ hψ b)
  have hFe : ∀ x, F (-x)=F x := by
    intro x
    change (∑ i, b i*ψ i (-x)) - _ = (∑ i, b i*ψ i x) - _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show ψ i (-x)=ψ i x from summand_even hqe (p i) (h i) x]
  have hFc : (∫ x, F x ∂μ)=0 :=
    LpVariance.centered_integral μ (MemLp.integrable (by norm_num) (LpVariance.sum_memLp μ ψ hψ b))
  have hclosure := MomentKernel.centered_even_mem_closure (ι:=ι) (φ:=φ) (V:=V) (Z:=Z)
    (Λ:=4/ε) (m:=0) hφ (smooth_potential ε p h (q+2)) (potential_even hqe ε p h)
    hpos (potential_partition_pos hqe hε p h) (potential_nonneg hqe hε.le p h)
    (div_nonneg (by norm_num) hε.le) hupper heq Φ hΦ hInv hmap hF hFe hFc
  apply LpVariance.variance_of_centered_dual μ (fun i => ∫ x, ψ i x ∂μ)
    (fun i => mean_summand_pos hqe hε p h (hp i) (ne_of_gt (hh i)) hqe) ψ hψ b
  apply LpVariance.integral_dual_extend μ (fun i => ∫ x, ψ i x ∂μ) ψ hψ
    ((RealSmoothOperator.squareRange (E:=Space ι) μ (MatrixOperator.principal (MomentOperator.tau Φ φ)
      (MomentKernel.smooth_tau hφ Φ hInv)++MatrixOperator.drift)) : Set (Lp ℝ 2 μ))
    (fun u hu => range_dual_bound hq hε p h hp hh hφ hpos hupper heq Φ hΦ hInv hmap u hu) hF
  exact hclosure

end MomentSlab
end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MomentSlab.variance_from_moment_oai.{u_1, u_2} := @OAI.MomentSlab.variance_from_moment_oai.{u_1, u_2}

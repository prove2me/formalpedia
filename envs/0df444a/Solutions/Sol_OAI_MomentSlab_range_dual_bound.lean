-- Prove2me | solution 1 for OAI.MomentSlab.range_dual_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T05:23:35.990723+00:00
-- url     : https://prove2.me/submissions/5564fc31-4a01-45d3-9630-87d17ef302aa

import Mathlib
import Definitions.Def_OAIW2LB000

section
-- module Solutions.OAIW2_LogBM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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

lemma compact_divergence {V : E → ℝ} {e : ι → E} {W : ι → E → ℝ}
    (hW : ∀ i, HasCompactSupport (W i)) :
    HasCompactSupport (divergence V e W) :=
  compact_sum _ (fun i => compact_adjoint (V := V) (hW i) (e i))

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
lemma expectation_add {V f g : E → ℝ} (hV : ContDiff ℝ ∞ V)
    (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    expectation μ V (fun x => f x + g x) = expectation μ V f + expectation μ V g := by
  simp only [expectation, add_mul]
  exact integral_add (integrable_weighted μ hV hf hfc) (integrable_weighted μ hV hg hgc)

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

theorem bochner {V : E → ℝ} (e : ι → E) (W : ι → E → ℝ)
    (hV : ContDiff ℝ ∞ V) (hW : ∀ i, ContDiff ℝ ∞ (W i))
    (hWc : ∀ i, HasCompactSupport (W i)) :
    expectation μ V (fun x => (divergence V e W x)^2) =
      (∑ j, ∑ i, expectation μ V (fun x =>
        D (e j) (D (e i) V) x * W i x * W j x)) +
      ∑ j, ∑ i, expectation μ V (fun x => D (e i) (W j) x * D (e j) (W i) x) := by
  have hstep (j : ι) :
      expectation μ V (fun x => D (e j) (divergence V e W) x * W j x) =
        (∑ i, expectation μ V (fun x => D (e j) (D (e i) V) x * W i x * W j x)) +
        ∑ i, expectation μ V (fun x => D (e i) (W j) x * D (e j) (W i) x) := by
    rw [D_divergence hV hW]
    simp_rw [Finset.sum_mul, add_mul]
    rw [expectation_sum μ hV _]
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [expectation_add μ hV]
      · congr 1
        have heq : (fun x => adjoint V (e i) (D (e j) (W i)) x * W j x) =
            fun x => W j x * adjoint V (e i) (D (e j) (W i)) x := by
          funext x; ring
        rw [heq]
        exact (integration_by_parts μ hV (smooth_D (hW i) (e j)) (hW j)
          (compact_D (hWc i) (e j)) (e i)).symm
      · exact (((smooth_D (smooth_D hV (e i)) (e j)).continuous.mul
          (hW i).continuous).mul (hW j).continuous)
      · exact (smooth_adjoint hV (smooth_D (hW i) (e j)) (e i)).continuous.mul
          (hW j).continuous
      · exact (hWc j).mul_left
      · exact (hWc j).mul_left
    · intro i
      exact ((((smooth_D (smooth_D hV (e i)) (e j)).continuous.mul
        (hW i).continuous).mul (hW j).continuous).add
        ((smooth_adjoint hV (smooth_D (hW i) (e j)) (e i)).continuous.mul
          (hW j).continuous))
    · intro i
      exact ((hWc j).mul_left).add ((hWc j).mul_left)
  simp_rw [pow_two]
  rw [divergence_adjoint μ e W hV hW (smooth_divergence hV hW) hWc]
  simp_rw [hstep]
  exact Finset.sum_add_distrib


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

lemma smooth_W {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (a : ι) : ContDiff ℝ ∞ (W φ f a) :=
  smooth_divergence hφ (smooth_P hφ hf a)

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

lemma W_derivative_symm {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (a b : ι) :
    pd b (W φ f a) = pd a (W φ f b) := by
  simp_rw [W_gradient hφ hf]
  exact pd_comm ((smooth_pullA hφ hf).sub (hf.comp (smooth_grad hφ))) b a

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

lemma compact_W {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) (a : ι) :
    HasCompactSupport (W φ f a) :=
  compact_divergence (compact_P hφ hf hfc Φ hΦ a)

lemma hess_transpose {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (z : Space ι) :
    (hess f z)ᵀ = hess f z := by
  ext i j
  exact hess_symm hf z j i

lemma B_symm {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (z : Space ι) (a l : ι) :
    B φ f a l z = B φ f l a z := by
  have ht : (hess φ z * hess f (grad φ z) * hess φ z)ᵀ =
      hess φ z * hess f (grad φ z) * hess φ z := by
    simp only [Matrix.transpose_mul, hess_transpose hφ, hess_transpose hf, Matrix.mul_assoc]
  have heq := congrFun (congrFun ht l) a
  exact heq

lemma W_derivative {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (a l : ι) :
    pd l (W φ f a) = fun z => B φ f a l z + R φ f a l z := by
  change D (basis l) (divergence φ basis (P φ f a)) = _
  rw [D_divergence hφ (smooth_P hφ hf a)]
  funext z
  simp only [B, R, divergence, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  change hess φ z k l * P φ f a k z = P φ f a k z * hess φ z k l
  ring

lemma R_symm {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (z : Space ι) (a l : ι) :
    R φ f a l z = R φ f l a z := by
  have hw := congrFun (W_derivative_symm hφ hf a l) z
  rw [W_derivative hφ hf a l, W_derivative hφ hf l a] at hw
  dsimp at hw
  rw [B_symm hφ hf z a l] at hw
  linarith

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

lemma smooth_adjugate_entry {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z => A z i j)) (i j : ι) :
    ContDiff ℝ ∞ (fun z => (A z).adjugate i j) := by
  simp_rw [Matrix.adjugate_apply]
  apply smooth_matrix_det
  intro k l
  by_cases h : j = k
  · subst k
    simp only [Matrix.updateRow_apply, ite_true]
    exact contDiff_const
  · simpa only [Matrix.updateRow_apply, ite_eq_right (Ne.symm h)] using hA k l

lemma smooth_inverse_entry {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z => A z i j))
    (hne : ∀ z, (A z).det ≠ 0) (i j : ι) :
    ContDiff ℝ ∞ (fun z => (A z)⁻¹ i j) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((smooth_matrix_det hA).inv hne).mul (smooth_adjugate_entry hA i j)

omit [DecidableEq ι] in
lemma md_mul {A B : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z => A z i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun z => B z i j)) (v z : E) :
    md v (fun z => A z * B z) z = md v A z * B z + A z * md v B z := by
  ext i j
  simp only [md, Matrix.mul_apply, Matrix.add_apply]
  rw [fderiv_fun_sum (A := fun k z => A z i k * B z k j) (fun k _ => ((hA i k).differentiable (by simp) z).mul
    ((hB k j).differentiable (by simp) z))]
  simp only [_root_.sum_apply, fderiv_fun_mul ((hA _ _).differentiable (by simp) z)
    ((hB _ _).differentiable (by simp) z), _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma md_const (v z : E) (A : Matrix ι ι ℝ) : md v (fun _ : E => A) z = 0 := by
  ext i j
  simp [md]

theorem md_inverse {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z => A z i j))
    (hne : ∀ z, (A z).det ≠ 0) (v z : E) :
    md v (fun z => (A z)⁻¹) z = -(A z)⁻¹ * md v A z * (A z)⁻¹ := by
  have hAA : (fun z => A z * (A z)⁻¹) = fun _ => (1 : Matrix ι ι ℝ) := by
    funext z
    exact Matrix.mul_nonsing_inv (A z) (isUnit_iff_ne_zero.mpr (hne z))
  have hd := md_mul hA (smooth_inverse_entry hA hne) v z
  rw [hAA, md_const] at hd
  have hm := congrArg (fun B => (A z)⁻¹ * B) hd
  rw [Matrix.mul_zero, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul (A z) (isUnit_iff_ne_zero.mpr (hne z)), Matrix.one_mul] at hm
  have he := eq_neg_of_add_eq_zero_right hm.symm
  simpa only [Matrix.neg_mul, Matrix.mul_assoc] using he

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

lemma C_apply (φ : Space ι → ℝ) (i : ι) (z : Space ι) (a b : ι) :
    C φ i z a b = pd i (fun z => hess φ z a b) z := rfl

lemma smooth_C {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (i a b : ι) :
    ContDiff ℝ ∞ (fun z => C φ i z a b) := smooth_pd (smooth_hess hφ a b) i

lemma C_symm_last {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : ι)
    (z : Space ι) (a b : ι) : C φ i z a b = C φ i z b a := by
  simp only [C_apply]
  congr 1
  funext y
  exact hess_symm hφ y a b

lemma C_symm_first {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : ι)
    (z : Space ι) (a b : ι) : C φ i z a b = C φ a z i b := by
  change pd i (pd b (pd a φ)) z = pd a (pd b (pd i φ)) z
  rw [pd_comm (smooth_pd hφ a) i b, pd_comm (smooth_pd hφ i) a b,
    pd_comm hφ i a]

lemma pd_trace {A : Space ι → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z => A z i j)) (i : ι) :
    pd i (fun z => (A z).trace) = fun z => (md (basis i) A z).trace := by
  change pd i (fun z => ∑ j, A z j j) = _
  rw [pd_sum _ (fun j => hA j j)]
  rfl

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

omit [DecidableEq ι] in
lemma smooth_matrix_product {A B : Space ι → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z => A z i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun z => B z i j)) (i j : ι) :
    ContDiff ℝ ∞ (fun z => (A z * B z) i j) :=
  smooth_sum _ (fun k => (hA i k).mul (hB k j))

omit [DecidableEq ι] in
lemma trace_cyclic_four (A B C D : Matrix ι ι ℝ) :
    (A * B * C * D).trace = (C * D * A * B).trace := by
  rw [Matrix.mul_assoc A B C, Matrix.mul_assoc A (B*C) D,
    Matrix.trace_mul_comm A (B*C*D)]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm B (C * (D*A))]
  simp only [Matrix.mul_assoc]

theorem pd_jacobian_term {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hne : ∀ z, (hess φ z).det ≠ 0) (i j : ι) :
    pd j (fun z => ((hess φ z)⁻¹ * C φ i z).trace) = fun z =>
      ((hess φ z)⁻¹ * md (basis j) (C φ i) z).trace -
        ((hess φ z)⁻¹ * C φ i z * (hess φ z)⁻¹ * C φ j z).trace := by
  rw [pd_trace (smooth_matrix_product (smooth_inverse_entry (smooth_hess hφ) hne)
      (smooth_C hφ i)) j]
  funext z
  rw [md_mul (smooth_inverse_entry (smooth_hess hφ) hne) (smooth_C hφ i),
    md_inverse (smooth_hess hφ) hne]
  change (-((hess φ z)⁻¹) * C φ j z * (hess φ z)⁻¹ * C φ i z +
    (hess φ z)⁻¹ * md (basis j) (C φ i) z).trace = _
  simp only [Matrix.trace_add, Matrix.neg_mul, Matrix.trace_neg]
  rw [trace_cyclic_four (hess φ z)⁻¹ (C φ j z) (hess φ z)⁻¹ (C φ i z)]
  ring

lemma pd_hess_gradient {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (i j : ι) :
    pd j (fun z => ∑ k, hess φ z i k * pd k V (grad φ z)) = fun z =>
      (∑ k, C φ j z i k * pd k V (grad φ z)) +
        (hess φ z * hess V (grad φ z) * hess φ z) i j := by
  erw [pd_sum _ (fun k => (smooth_hess hφ i k).mul
    ((smooth_pd hV k).comp (smooth_grad hφ)))]
  simp_rw [pd_mul (smooth_hess hφ i _) ((smooth_pd hV _).comp (smooth_grad hφ)),
    pd_comp_grad (smooth_pd hV _) hφ]
  funext z
  simp only [Finset.sum_add_distrib]
  congr 1
  change (∑ k, hess φ z i k * ∑ l, hess φ z j l * hess V (grad φ z) k l) = _
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hess_symm hφ z j k]
  ring

theorem twice_moment_raw {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {k : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + k - φ z)
    (i j : ι) (z : Space ι) :
    (hess φ z * hess V (grad φ z) * hess φ z) i j = hess φ z i j +
      ((hess φ z)⁻¹ * md (basis j) (C φ i) z).trace -
      ((hess φ z)⁻¹ * C φ i z * (hess φ z)⁻¹ * C φ j z).trace -
      ∑ l, C φ j z i l * pd l V (grad φ z) := by
  have he : (fun z => ∑ l, hess φ z i l * pd l V (grad φ z)) =
      (fun z => grad φ z i + ((hess φ z)⁻¹ * C φ i z).trace) :=
    funext (first_moment hφ hV hne heq i)
  have hd := congrArg (fun f => pd j f z) he
  have hs : ContDiff ℝ ∞ (fun z => ((hess φ z)⁻¹ * C φ i z).trace) :=
    smooth_sum _ (fun l => smooth_matrix_product
      (smooth_inverse_entry (smooth_hess hφ) hne) (smooth_C hφ i) l l)
  change pd j (fun z => ∑ l, hess φ z i l * pd l V (grad φ z)) z =
    pd j (fun z => pd i φ z + ((hess φ z)⁻¹ * C φ i z).trace) z at hd
  rw [pd_hess_gradient hφ hV i j, pd_add (smooth_pd hφ i) hs,
    pd_jacobian_term hφ hne i j] at hd
  change _ + _ = hess φ z i j + (_ - _) at hd
  linarith

lemma hess_transpose {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (z : Space ι) :
    (hess φ z)ᵀ = hess φ z := by
  ext i j
  exact hess_symm hφ z j i

lemma inverse_transpose {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (z : Space ι) :
    ((hess φ z)⁻¹)ᵀ = (hess φ z)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, hess_transpose hφ]

lemma inverse_symm {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (z : Space ι) (i j : ι) :
    (hess φ z)⁻¹ i j = (hess φ z)⁻¹ j i := by
  exact congrArg (fun M : Matrix ι ι ℝ => M j i) (inverse_transpose hφ z)

omit [DecidableEq ι] in
lemma cubic_div_contract (M : Matrix ι ι ℝ) (C : ι → Matrix ι ι ℝ)
    (hC : ∀ d a b, C d a b = C b a d) (k : ι) :
    (∑ d, (M * C d * M) d k) = ∑ b, (M * C b).trace * M b k := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro a _
  rw [hC d a b]

theorem inverse_divergence {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hne : ∀ z, (hess φ z).det ≠ 0) (k : ι) (z : Space ι) :
    (∑ d, pd d (fun y => (hess φ y)⁻¹ d k) z) =
      -∑ b, ((hess φ z)⁻¹ * C φ b z).trace * (hess φ z)⁻¹ b k := by
  have hd (d : ι) : pd d (fun y => (hess φ y)⁻¹ d k) z =
      -((hess φ z)⁻¹ * C φ d z * (hess φ z)⁻¹) d k := by
    have hm := congrArg (fun M : Matrix ι ι ℝ => M d k)
      (md_inverse (smooth_hess hφ) hne (basis d) z)
    simpa only [md, C, pd, D, Matrix.neg_mul, Matrix.neg_apply] using hm
  simp_rw [hd, Finset.sum_neg_distrib]
  congr 1
  apply cubic_div_contract
  intro d a b
  rw [C_symm_last hφ d z a b, C_symm_first hφ d z b a,
    C_symm_last hφ b z d a]

theorem inverse_first_moment {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {k : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + k - φ z)
    (a : ι) (z : Space ι) :
    pd a V (grad φ z) = ∑ d,
      (grad φ z d + ((hess φ z)⁻¹ * C φ d z).trace) * (hess φ z)⁻¹ d a := by
  have hv : hess φ z *ᵥ grad V (grad φ z) =
      fun d => grad φ z d + ((hess φ z)⁻¹ * C φ d z).trace := by
    ext d
    exact first_moment hφ hV hne heq d z
  have hm := congrArg (fun v => ((hess φ z)⁻¹ *ᵥ v) a) hv
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (hne z)), Matrix.one_mulVec] at hm
  change grad V (grad φ z) a = _
  rw [hm]
  apply Finset.sum_congr rfl
  intro d _
  change (hess φ z)⁻¹ a d * (grad φ z d + ((hess φ z)⁻¹ * C φ d z).trace) = _
  erw [inverse_symm hφ z a d]
  ring

theorem weighted_inverse_divergence {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {k : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + k - φ z)
    (a : ι) (z : Space ι) :
    (∑ d, (pd d (fun y => (hess φ y)⁻¹ d a) z - grad φ z d * (hess φ z)⁻¹ d a)) =
      -pd a V (grad φ z) := by
  rw [Finset.sum_sub_distrib, inverse_divergence hφ hne a z,
    inverse_first_moment hφ hV hne heq a z]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

lemma pd_C_swap {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (i j k d : ι) :
    pd j (fun z => C φ i z k d) = pd d (fun z => C φ i z j k) := by
  change pd j (pd i (pd d (pd k φ))) = pd d (pd i (pd k (pd j φ)))
  rw [pd_comm (smooth_pd (smooth_pd hφ k) d) j i,
    pd_comm (smooth_pd hφ k) j d,
    pd_comm (smooth_pd (smooth_pd hφ k) j) i d,
    pd_comm hφ j k]

lemma trace_fourth {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (i j : ι) (z : Space ι) :
    ((hess φ z)⁻¹ * md (basis j) (C φ i) z).trace =
      ∑ d, ∑ k, (hess φ z)⁻¹ d k * pd d (fun z => C φ i z j k) z := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro k _
  change (hess φ z)⁻¹ d k * pd j (fun z => C φ i z k d) z = _
  rw [pd_C_swap hφ i j k d]

theorem divergence_cubic {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {k : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + k - φ z)
    (i j : ι) (z : Space ι) :
    (∑ d, (pd d (fun y => ∑ a, (hess φ y)⁻¹ d a * C φ i y j a) z -
      grad φ z d * ∑ a, (hess φ z)⁻¹ d a * C φ i z j a)) =
    ((hess φ z)⁻¹ * md (basis j) (C φ i) z).trace -
      ∑ a, C φ j z i a * pd a V (grad φ z) := by
  have hsM := smooth_inverse_entry (smooth_hess hφ) hne
  have hd (d : ι) : pd d (fun y => ∑ a, (hess φ y)⁻¹ d a * C φ i y j a) z =
      ∑ a, (pd d (fun y => (hess φ y)⁻¹ d a) z * C φ i z j a +
        (hess φ z)⁻¹ d a * pd d (fun y => C φ i y j a) z) := by
    rw [pd_sum _ (fun a => (hsM d a).mul (smooth_C hφ i j a))]
    apply Finset.sum_congr rfl
    intro a _
    exact congrFun (pd_mul (hsM d a) (smooth_C hφ i j a) d) z
  simp_rw [hd]
  rw [trace_fourth hφ i j z]
  have halg : (∑ d, ((∑ a, (pd d (fun y => (hess φ y)⁻¹ d a) z * C φ i z j a +
        (hess φ z)⁻¹ d a * pd d (fun y => C φ i y j a) z)) -
      grad φ z d * ∑ a, (hess φ z)⁻¹ d a * C φ i z j a)) =
      (∑ d, ∑ a, (hess φ z)⁻¹ d a * pd d (fun y => C φ i y j a) z) +
      ∑ a, (∑ d, (pd d (fun y => (hess φ y)⁻¹ d a) z -
        grad φ z d * (hess φ z)⁻¹ d a)) * C φ i z j a := by
    simp only [Finset.mul_sum, Finset.sum_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun d a => pd d (fun y => (hess φ y)⁻¹ d a) z * C φ i z j a)]
    have hc : (∑ d, ∑ a, grad φ z d * ((hess φ z)⁻¹ d a * C φ i z j a)) =
        ∑ a, ∑ d, grad φ z d * (hess φ z)⁻¹ d a * C φ i z j a := by
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    rw [hc]
    ring
  rw [halg]
  simp_rw [weighted_inverse_divergence hφ hV hne heq]
  have hr : (∑ a, -pd a V (grad φ z) * C φ i z j a) =
      -(∑ a, C φ j z i a * pd a V (grad φ z)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [C_symm_first hφ i z j a]
    ring
  rw [hr]
  ring

theorem twice_moment {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {k : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + k - φ z)
    (i j : ι) (z : Space ι) :
    (hess φ z * hess V (grad φ z) * hess φ z - hess φ z) i j =
      (∑ d, (pd d (fun y => ∑ a, (hess φ y)⁻¹ d a * C φ i y j a) z -
        grad φ z d * ∑ a, (hess φ z)⁻¹ d a * C φ i z j a)) -
      ((hess φ z)⁻¹ * C φ i z * (hess φ z)⁻¹ * C φ j z).trace := by
  rw [divergence_cubic hφ hV hne heq, Matrix.sub_apply,
    twice_moment_raw hφ hV hne heq i j z]
  ring

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

lemma A_target {φ f : Space ι → ℝ}
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    A Φ φ f = target Φ (pullA φ f) := by
  funext x
  obtain ⟨z,rfl⟩ := Φ.surjective x
  rw [hΦ, target_apply Φ hΦ]
  exact congrFun (A_pull Φ hΦ) z

lemma smooth_A {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (Φ : Space ι ≃ₜ Space ι)
    (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) : ContDiff ℝ ∞ (A Φ φ f) := by
  rw [A_target Φ hΦ]
  exact smooth_target hInv (smooth_pullA hφ hf)

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

lemma W_flux {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (Φ : Space ι ≃ₜ Space ι)
    (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (a : ι) :
    target Φ (W φ f a) = flux Φ φ (A Φ φ f - f) a := by
  funext x
  obtain ⟨z,rfl⟩ := Φ.surjective x
  rw [hΦ, target_apply Φ hΦ]
  have he : pullA φ f - f ∘ grad φ = (A Φ φ f - f) ∘ grad φ := by
    rw [← A_pull Φ hΦ]
    rfl
  rw [W_gradient hφ hf a]
  change pd a (pullA φ f - f ∘ grad φ) z = _
  rw [he]
  change pd a ((fun x => A Φ φ f x - f x) ∘ grad φ) z = _
  rw [pd_comp_grad ((smooth_A hφ hf Φ hΦ hInv).sub hf) hφ]
  change (∑ j, hess φ z a j * pd j (A Φ φ f - f) (grad φ z)) =
    ∑ j, hess φ (Φ.symm (grad φ z)) a j * pd j (A Φ φ f - f) (grad φ z)
  have hc : Φ.symm (grad φ z) = z := by rw [← hΦ]; exact Φ.symm_apply_apply z
  rw [hc]

lemma double_divergence {φ V f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0) {c : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + c - φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) :
    divergence V basis (fun a => target Φ (W φ f a)) = A Φ φ (A Φ φ f - f) := by
  simp_rw [W_flux hφ hf Φ hΦ hInv]
  exact A_divergence hφ hV ((smooth_A hφ hf Φ hΦ hInv).sub hf) hne heq Φ hΦ hInv

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

lemma trace_energy_nonneg {M H B : Matrix ι ι ℝ} (hM : M.PosSemidef)
    (hH : H.PosSemidef) (hB : Bᵀ = B) : 0 ≤ (M * B * H * B).trace := by
  have hc : (B * H * B).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hB] using
      hH.conjTranspose_mul_mul_same B
  simpa only [Matrix.mul_assoc] using trace_mul_nonneg hM hc

lemma quadratic_cs (a b c : ℝ) (h : ∀ t : ℝ, 0 ≤ c - 2 * t * b + t^2 * a) :
    b^2 ≤ a * c := by
  have hd := discrim_le_zero (a := a) (b := -2 * b) (c := c) (fun t => by
    have ht := h t
    nlinarith)
  dsimp [discrim] at hd
  nlinarith

lemma trace_energy_quadratic (M T H B : Matrix ι ι ℝ)
    (hMT : M * T = 1) (hTM : T * M = 1) (t : ℝ) :
    (M * (B - t • T) * H * (B - t • T)).trace =
      (M * B * H * B).trace - 2 * t * (B * H).trace +
      t^2 * (T * H).trace := by
  have hc₁ : (M * B * H * T).trace = (B * H).trace := by
    rw [Matrix.trace_mul_cycle (M * B) H T, ← Matrix.mul_assoc T M B,
      hTM, Matrix.one_mul]
  have hc₂ : (M * T * H * B).trace = (B * H).trace := by
    rw [hMT, Matrix.one_mul, Matrix.trace_mul_comm H B]
  have hc₃ : (M * T * H * T).trace = (T * H).trace := by
    rw [hMT, Matrix.one_mul, Matrix.trace_mul_comm H T]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul, hc₁, hc₂, hc₃]
  ring

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
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

lemma integral_quadratic_cs {a b c : X → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : Integrable c μ)
    (h : ∀ t x, 0 ≤ c x - 2 * t * b x + t^2 * a x) :
    (∫ x, b x ∂μ)^2 ≤ (∫ x, a x ∂μ) * (∫ x, c x ∂μ) := by
  apply quadratic_cs
  intro t
  have ht : 0 ≤ ∫ x, c x - 2 * t * b x + t^2 * a x ∂μ :=
    integral_nonneg (fun x => h t x)
  rw [integral_add (f := fun x => c x - 2*t*b x) (g := fun x => t^2*a x)
      (hc.sub (hb.const_mul (2*t))) (ha.const_mul (t^2)),
    integral_sub (f := c) (g := fun x => 2*t*b x) hc (hb.const_mul (2*t)),
    integral_const_mul, integral_const_mul] at ht
  exact ht

theorem integral_trace_cs {M T H B : X → Matrix ι ι ℝ}
    (hM : ∀ x, (M x).PosSemidef) (hH : ∀ x, (H x).PosSemidef)
    (hT : ∀ x, (T x)ᵀ = T x) (hB : ∀ x, (B x)ᵀ = B x)
    (hMT : ∀ x, M x * T x = 1) (hTM : ∀ x, T x * M x = 1)
    (hi₁ : Integrable (fun x => (T x * H x).trace) μ)
    (hi₂ : Integrable (fun x => (B x * H x).trace) μ)
    (hi₃ : Integrable (fun x => (M x * B x * H x * B x).trace) μ) :
    (∫ x, (B x * H x).trace ∂μ)^2 ≤
      (∫ x, (T x * H x).trace ∂μ) * (∫ x, (M x * B x * H x * B x).trace ∂μ) := by
  apply integral_quadratic_cs μ hi₁ hi₂ hi₃
  intro t x
  rw [← trace_energy_quadratic (M x) (T x) (H x) (B x) (hMT x) (hTM x) t]
  apply trace_energy_nonneg (hM x) (hH x)
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, hB x, hT x]

omit [DecidableEq ι] in

theorem integral_form_cs {H : X → Matrix ι ι ℝ} {v w : X → ι → ℝ}
    (hH : ∀ x, (H x).PosSemidef)
    (hi₁ : Integrable (fun x => v x ⬝ᵥ (H x *ᵥ v x)) μ)
    (hi₂ : Integrable (fun x => v x ⬝ᵥ (H x *ᵥ w x)) μ)
    (hi₃ : Integrable (fun x => w x ⬝ᵥ (H x *ᵥ w x)) μ) :
    (∫ x, v x ⬝ᵥ (H x *ᵥ w x) ∂μ)^2 ≤
      (∫ x, v x ⬝ᵥ (H x *ᵥ v x) ∂μ) * (∫ x, w x ⬝ᵥ (H x *ᵥ w x) ∂μ) := by
  apply integral_quadratic_cs μ hi₁ hi₂ hi₃
  intro t x
  have hs : (H x)ᵀ = H x := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (hH x).isHermitian.eq
  rw [← form_quadratic hs (v x) (w x) t]
  exact form_nonneg (hH x) _


end MomentMatrix

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

lemma seq_derivative_bounds : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ x : E,
    ‖fderiv ℝ (seq k) x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (seq k)) x‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := derivative_bounds (E:=E)
  refine ⟨C,hC,fun k x => ?_⟩
  have hk : (1:ℝ) ≤ (k:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) k; linarith
  have hh := h ((k:ℝ)+1) (by positivity) x
  constructor
  · exact hh.1.trans ((div_le_self hC.le hk))
  · exact hh.2.trans (div_le_self hC.le (by nlinarith))

end

end SmoothCutoff

end

noncomputable section

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

end

end

open MeasureTheory Matrix WeightedCalculus MomentCoordinates TargetCoordinates
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_A_eq (τ : Space ι → Matrix ι ι ℝ) (f : Space ι → ℝ) :
    MatrixOperator.A τ f = DensityEnergy.A τ f := rfl


end MomentKernel

namespace RealSmoothOperator
open MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

lemma squareLp_coe (ts : List (Term E)) (f : tests (E:=E)) :
    (squareLp μ ts f : E → ℝ) =ᵐ[μ] operator ts (operator ts f-f) := testsLp_coe μ _

end RealSmoothOperator

namespace SteinExtension
open MeasureTheory Filter
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem extend (μ : Measure E) {b : E → ℝ} {v : E → E}
    (hb : Continuous b) (hv : Continuous v) {Λ : ℝ}
    (hbound : ∀ x, ‖v x‖ ≤ Λ)
    (hstein : ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, b x * f x ∂μ) = ∫ x, fderiv ℝ f x (v x) ∂μ)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hi : Integrable f μ)
    (hib : Integrable (fun x => b x*f x) μ)
    (hid : Integrable (fun x => fderiv ℝ f x (v x)) μ) :
    (∫ x, b x*f x ∂μ) = ∫ x, fderiv ℝ f x (v x) ∂μ := by
  let η := SmoothCutoff.seq (E:=E)
  have hη (k : ℕ) := SmoothCutoff.seq_smooth (E:=E) k
  have hηc (k : ℕ) := SmoothCutoff.seq_compact (E:=E) k
  have hηnorm (k : ℕ) (x : E) : ‖η k x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (SmoothCutoff.seq_nonneg k x)]
    exact SmoothCutoff.seq_le_one k x
  obtain ⟨C,hC,hCbound⟩ := SmoothCutoff.seq_derivative_bounds (E:=E)
  have he (k : ℕ) (x : E) :
      fderiv ℝ (fun y => η k y*f y) x (v x) =
        η k x * fderiv ℝ f x (v x) + f x * fderiv ℝ (η k) x (v x) := by
    rw [fderiv_fun_mul ((hη k).differentiable (by simp) x) (hf.differentiable (by simp) x)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hleft : Tendsto (fun k => ∫ x, b x*(η k x*f x) ∂μ) atTop
      (𝓝 (∫ x, b x*f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖b x*f x‖)
      (fun k => (hb.mul ((hη k).continuous.mul hf.continuous)).aestronglyMeasurable)
      hib.norm
    · intro k
      exact Filter.Eventually.of_forall (fun x => by
        change ‖b x*(η k x*f x)‖ ≤ ‖b x*f x‖
        rw [show b x*(η k x*f x) = η k x*(b x*f x) by ring, norm_mul]
        exact (mul_le_mul_of_nonneg_right (hηnorm k x) (norm_nonneg _)).trans_eq (one_mul _))
    · exact Filter.Eventually.of_forall (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [SmoothCutoff.seq_eventually x] with k hk
        change b x*f x = b x*(η k x*f x)
        rw [show η k x = 1 from hk.1, one_mul])
  have hright : Tendsto (fun k => ∫ x, fderiv ℝ (fun y => η k y*f y) x (v x) ∂μ) atTop
      (𝓝 (∫ x, fderiv ℝ f x (v x) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖fderiv ℝ f x (v x)‖ + (C*Λ)*‖f x‖)
    · intro k
      exact (((((hη k).mul hf).fderiv_right (m:=∞) (by simp)).continuous).clm_apply hv).aestronglyMeasurable
    · exact hid.norm.add (hi.norm.const_mul _)
    · intro k
      exact Filter.Eventually.of_forall (fun x => by
        rw [he]
        calc
          _ ≤ ‖η k x * fderiv ℝ f x (v x)‖ + ‖f x * fderiv ℝ (η k) x (v x)‖ := norm_add_le _ _
          _ ≤ ‖fderiv ℝ f x (v x)‖ + (C*Λ)*‖f x‖ := by
            simp only [norm_mul]
            apply add_le_add
            · exact (mul_le_mul_of_nonneg_right (hηnorm k x) (norm_nonneg _)).trans_eq (one_mul _)
            · have hvd : ‖fderiv ℝ (η k) x (v x)‖ ≤ C*Λ :=
                ((fderiv ℝ (η k) x).le_opNorm _).trans
                  (mul_le_mul (hCbound k x).1 (hbound x) (norm_nonneg _) hC.le)
              simpa only [mul_comm (C*Λ)] using mul_le_mul_of_nonneg_left hvd (norm_nonneg (f x)))
    · exact Filter.Eventually.of_forall (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [SmoothCutoff.seq_eventually x] with k hk
        rw [he]
        simp only [η, hk.1, hk.2.1, _root_.zero_apply, mul_zero, add_zero, one_mul])
  have hid' (k : ℕ) := hstein (fun y => η k y*f y) ((hη k).mul hf) (hηc k).mul_right
  exact tendsto_nhds_unique hleft (hright.congr (fun k => (hid' k).symm))

end SteinExtension
end

open Matrix
open scoped BigOperators Kronecker
noncomputable section
namespace MetricTensor
variable {ι : Type*} [Fintype ι]

lemma pair_expand (T : Matrix ι ι ℝ) (A B : Tensor ι) :
    pair T A B = ∑ p, ∑ q, kernel T p q * A p * B q := by
  simp only [pair, dotProduct, Matrix.mulVec, Finset.mul_sum]
  congr 1
  ext p
  apply Finset.sum_congr rfl
  intro q _
  ring

omit [Fintype ι] in
lemma kernel_symm {T : Matrix ι ι ℝ} (hT : Tᵀ = T) : (kernel T)ᵀ = kernel T := by
  ext ⟨i,j,k⟩ ⟨a,b,c⟩
  have hs (a b : ι) : T a b = T b a := congrArg (fun M : Matrix ι ι ℝ => M b a) hT
  simp only [kernel, Matrix.transpose_apply, Matrix.kronecker_apply]
  rw [hs a i, hs b j, hs c k]

lemma pair_comm {T : Matrix ι ι ℝ} (hT : Tᵀ = T) (A B : Tensor ι) :
    pair T A B = pair T B A := by
  rw [pair_expand, pair_expand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  have hs := congrArg (fun M : Matrix (Idx ι) (Idx ι) ℝ => M p q) (kernel_symm hT)
  change kernel T q p = kernel T p q at hs
  rw [hs]
  ring

lemma sq_nonneg {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (A : Tensor ι) : 0 ≤ sq T A := by
  have hp : (kernel T).PosSemidef := hT.kronecker (hT.kronecker hT)
  simpa only [sq, pair, star_trivial] using hp.dotProduct_mulVec_nonneg A

lemma pair_comp (T : Matrix ι ι ℝ) (e : Idx ι ≃ Idx ι)
    (he : ∀ p q, kernel T (e p) (e q) = kernel T p q) (A B : Tensor ι) :
    pair T (A ∘ e) (B ∘ e) = pair T A B := by
  simp only [pair_expand, Function.comp_apply]
  apply Fintype.sum_equiv e
  intro p
  apply Fintype.sum_equiv e
  intro q
  rw [he]

lemma pair_swap (T : Matrix ι ι ℝ) (A B : Tensor ι) :
    pair T (swap A) (swap B) = pair T A B := by
  apply pair_comp
  rintro ⟨i,j,k⟩ ⟨a,b,c⟩
  simp only [sw, Equiv.coe_fn_mk, kernel, Matrix.kronecker_apply]
  ring

lemma pair_cycle (T : Matrix ι ι ℝ) (A B : Tensor ι) :
    pair T (cycle A) (cycle B) = pair T A B := by
  apply pair_comp
  rintro ⟨i,j,k⟩ ⟨a,b,c⟩
  simp only [cy, Equiv.coe_fn_mk, kernel, Matrix.kronecker_apply]
  ring

lemma pair_add_left (T : Matrix ι ι ℝ) (A B C : Tensor ι) :
    pair T (A+B) C = pair T A C + pair T B C := by
  exact add_dotProduct _ _ _
lemma pair_add_right (T : Matrix ι ι ℝ) (A B C : Tensor ι) :
    pair T A (B+C) = pair T A B + pair T A C := by
  simp only [pair, Matrix.mulVec_add, dotProduct_add]
lemma pair_smul_left (T : Matrix ι ι ℝ) (r : ℝ) (A B : Tensor ι) :
    pair T (r • A) B = r * pair T A B := by
  simp only [pair, smul_dotProduct, smul_eq_mul]
lemma pair_smul_right (T : Matrix ι ι ℝ) (r : ℝ) (A B : Tensor ι) :
    pair T A (r • B) = r * pair T A B := by
  simp only [pair, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma sq_add {T : Matrix ι ι ℝ} (hT : Tᵀ = T) (A B : Tensor ι) :
    sq T (A+B) = sq T A + 2*pair T A B + sq T B := by
  unfold sq
  rw [pair_add_left, pair_add_right, pair_add_right, pair_comm hT B A]
  ring
lemma sq_sub {T : Matrix ι ι ℝ} (hT : Tᵀ = T) (A B : Tensor ι) :
    sq T (A-B) = sq T A - 2*pair T A B + sq T B := by
  have he : A-B = A + (-1 : ℝ) • B := by ext p; simp [sub_eq_add_neg]
  rw [he, sq_add hT, pair_smul_right]
  unfold sq
  rw [pair_smul_left, pair_smul_right]
  ring
lemma sq_smul (T : Matrix ι ι ℝ) (r : ℝ) (A : Tensor ι) :
    sq T (r • A) = r^2 * sq T A := by
  unfold sq
  rw [pair_smul_left, pair_smul_right]
  ring

omit [Fintype ι] in
lemma cycle_swap_of_last (A : Tensor ι) (hA : ∀ i j k, A (i,j,k) = A (i,k,j)) :
    cycle (swap A) = A := by
  ext ⟨i,j,k⟩
  exact hA i k j
omit [Fintype ι] in
lemma swap_cycle_of_last (A : Tensor ι) (hA : ∀ i j k, A (i,j,k) = A (i,k,j)) :
    swap (cycle A) = cycle A := by
  ext ⟨i,j,k⟩
  exact hA k j i
lemma pair_cyc_eq {T : Matrix ι ι ℝ} (hT : Tᵀ = T) (A : Tensor ι)
    (hA : ∀ i j k, A (i,j,k) = A (i,k,j)) :
    pair T A (cycle A) = pair T A (swap A) := by
  rw [← pair_cycle T A (swap A), cycle_swap_of_last A hA, pair_comm hT]
lemma pair_swap_cyc {T : Matrix ι ι ℝ} (hT : Tᵀ = T) (A : Tensor ι)
    (hA : ∀ i j k, A (i,j,k) = A (i,k,j)) :
    pair T (swap A) (cycle A) = pair T A (swap A) := by
  rw [← swap_cycle_of_last A hA, pair_swap, pair_cyc_eq hT A hA]
lemma sq_sym {T : Matrix ι ι ℝ} (hT : Tᵀ = T) (A : Tensor ι)
    (hA : ∀ i j k, A (i,j,k) = A (i,k,j)) :
    sq T (sym A) = (sq T A + 2*pair T A (swap A))/3 := by
  rw [sym, sq_smul, sq_add hT, sq_add hT, pair_add_left,
    pair_cyc_eq hT A hA, pair_swap_cyc hT A hA]
  have hs : sq T (swap A) = sq T A := pair_swap T A A
  have hc : sq T (cycle A) = sq T A := pair_cycle T A A
  rw [hs, hc]
  ring
lemma pair_sym {T : Matrix ι ι ℝ} (S A : Tensor ι)
    (hS₁ : swap S = S) (hS₂ : cycle S = S) :
    pair T S (sym A) = pair T S A := by
  have hs : pair T S (swap A) = pair T S A := by
    rw [← hS₁, pair_swap, hS₁]
  have hc : pair T S (cycle A) = pair T S A := by
    rw [← hS₂, pair_cycle, hS₂]
  rw [sym, pair_smul_right, pair_add_right, pair_add_right, hs, hc]
  ring

theorem tensor_squares {T : Matrix ι ι ℝ} (hT : Tᵀ = T) (S J : Tensor ι)
    (hS₁ : swap S = S) (hS₂ : cycle S = S)
    (hJ : ∀ i j k, J (i,j,k) = J (i,k,j)) :
    2*sq T S + 4*pair T S J + sq T J + pair T J (swap J) =
      2*sq T (S + sym J) + (1/6 : ℝ)*sq T (J - swap J) := by
  rw [sq_add hT, pair_sym S J hS₁ hS₂, sq_sym hT J hJ, sq_sub hT]
  have hs : sq T (swap J) = sq T J := pair_swap T J J
  rw [hs]
  ring

theorem remainder_nonneg {T : Matrix ι ι ℝ} (hT : T.PosSemidef) (S J : Tensor ι)
    (hS₁ : swap S = S) (hS₂ : cycle S = S)
    (hJ : ∀ i j k, J (i,j,k) = J (i,k,j)) :
    0 ≤ 2*sq T S + 4*pair T S J + sq T J + pair T J (swap J) := by
  have hs : Tᵀ = T := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hT.isHermitian.eq
  rw [tensor_squares hs S J hS₁ hS₂ hJ]
  positivity [sq_nonneg hT (S + sym J), sq_nonneg hT (J - swap J)]

lemma act_apply (A B C : Matrix ι ι ℝ) (X : Tensor ι) (i j k : ι) :
    act A B C X (i,j,k) = ∑ a, ∑ b, ∑ c, A i a * B j b * C k c * X (a,b,c) := by
  simp only [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

lemma act_comp (A B C D E F : Matrix ι ι ℝ) (X : Tensor ι) :
    act A B C (act D E F X) = act (A*D) (B*E) (C*F) X := by
  unfold act
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

lemma act_dot (A B C : Matrix ι ι ℝ) (X Y : Tensor ι) :
    act A B C X ⬝ᵥ Y = X ⬝ᵥ act Aᵀ Bᵀ Cᵀ Y := by
  change ((A ⊗ₖ (B ⊗ₖ C)) *ᵥ X) ⬝ᵥ Y = _
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm,
    ← Matrix.mulVec_transpose]
  congr 2

lemma pair_act (T A B C D E F : Matrix ι ι ℝ) (X Y : Tensor ι) :
    pair T (act A B C X) (act D E F Y) =
      X ⬝ᵥ act (Aᵀ*T*D) (Bᵀ*T*E) (Cᵀ*T*F) Y := by
  change act A B C X ⬝ᵥ act T T T (act D E F Y) = _
  rw [act_dot, act_comp, act_comp]

lemma swap_act (A B C : Matrix ι ι ℝ) (X : Tensor ι) :
    swap (act A B C X) = act B A C (swap X) := by
  ext ⟨i,j,k⟩
  change act A B C X (j,i,k) = _
  rw [act_apply, act_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  change A j a * B i b * C k c * X (a,b,c) = B i b * A j a * C k c * X (a,b,c)
  ring

lemma act_last_symm (A B : Matrix ι ι ℝ) (X : Tensor ι)
    (hX : ∀ i j k, X (i,j,k) = X (i,k,j)) (i j k : ι) :
    act A B B X (i,j,k) = act A B B X (i,k,j) := by
  rw [act_apply, act_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [hX a c b]
  ring

lemma cycle_act (A B C : Matrix ι ι ℝ) (X : Tensor ι) :
    cycle (act A B C X) = act B C A (cycle X) := by
  ext ⟨i,j,k⟩
  change act A B C X (k,i,j) = _
  rw [act_apply, act_apply]
  have hr (f : ι → ι → ι → ℝ) :
      (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
  rw [hr]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  change A k a * B i b * C j c * X (a,b,c) = B i b * C j c * A k a * X (a,b,c)
  ring

lemma dot_swap (X Y : Tensor ι) : swap X ⬝ᵥ swap Y = X ⬝ᵥ Y :=
  comp_equiv_dotProduct_comp_equiv X Y sw
lemma dot_cycle (X Y : Tensor ι) : cycle X ⬝ᵥ cycle Y = X ⬝ᵥ Y :=
  comp_equiv_dotProduct_comp_equiv X Y cy

variable [DecidableEq ι]
lemma pair_J (T M h : Matrix ι ι ℝ) (hTM : T*M = 1) (S C : Tensor ι) :
    pair T S (act h M M C) = S ⬝ᵥ act (T*h) 1 1 C := by
  change S ⬝ᵥ act T T T (act h M M C) = _
  rw [act_comp, hTM]

lemma sq_J (T M h : Matrix ι ι ℝ) (hM : Mᵀ=M) (hh : hᵀ=h)
    (hMT : M*T=1) (C : Tensor ι) :
    sq T (act h M M C) = C ⬝ᵥ act (h*T*h) M M C := by
  unfold sq
  rw [pair_act, hh, hM, hMT, Matrix.one_mul]

lemma pair_J_swap (T M h : Matrix ι ι ℝ) (hM : Mᵀ=M) (hh : hᵀ=h)
    (hMT : M*T=1) (hTM : T*M=1) (C : Tensor ι) (hC : swap C=C) :
    pair T (act h M M C) (swap (act h M M C)) = C ⬝ᵥ act h h M C := by
  rw [swap_act, hC, pair_act, hh, hM, hMT, Matrix.one_mul,
    Matrix.mul_assoc h T M, hTM, Matrix.mul_one, Matrix.one_mul]

lemma dot_slot₂ (A : Matrix ι ι ℝ) (S C : Tensor ι) (hS : swap S=S) (hC : swap C=C) :
    S ⬝ᵥ act 1 A 1 C = S ⬝ᵥ act A 1 1 C := by
  rw [← dot_swap, hS, swap_act, hC]

lemma dot_slot₃ (A : Matrix ι ι ℝ) (S C : Tensor ι) (hS : cycle S=S) (hC : cycle C=C) :
    S ⬝ᵥ act 1 1 A C = S ⬝ᵥ act A 1 1 C := by
  rw [← dot_cycle, hS, cycle_act, hC, ← dot_cycle, hS, cycle_act, hC]

lemma invariant_cross (T M h : Matrix ι ι ℝ) (hT : Tᵀ=T) (hTM : T*M=1)
    (S C : Tensor ι) (hS : cycle S=S) (hC : cycle C=C) :
    (act 1 1 T S) ⬝ᵥ (act 1 1 h C + act T T 1 S) =
      sq T S + pair T S (act h M M C) := by
  rw [dotProduct_add, act_dot, act_dot, act_comp, act_comp]
  simp only [Matrix.transpose_one, hT, Matrix.one_mul, Matrix.mul_one]
  rw [dot_slot₃ (T*h) S C hS hC, pair_J T M h hTM]
  change _ + sq T S = _
  ring

lemma invariant_derivative (T M h : Matrix ι ι ℝ) (hT : Tᵀ=T)
    (hM : Mᵀ=M) (hh : hᵀ=h) (hTM : T*M=1) (hMT : M*T=1)
    (S C : Tensor ι) (hS : swap S=S) (hC : swap C=C) :
    (act 1 (h*T) T S + act (h*T) 1 T S + act h h 1 C) ⬝ᵥ act 1 1 M C =
      2*pair T S (act h M M C) + pair T (act h M M C) (swap (act h M M C)) := by
  rw [add_dotProduct, add_dotProduct, act_dot, act_dot, act_dot,
    act_comp, act_comp, act_comp]
  simp only [Matrix.transpose_one, Matrix.transpose_mul, hT, hh,
    Matrix.one_mul, Matrix.mul_one, hTM]
  rw [dot_slot₂ (T*h) S C hS hC, pair_J T M h hTM, pair_J_swap T M h hM hh hMT hTM C hC]
  ring

theorem invariant_remainder_nonneg (T M h : Matrix ι ι ℝ) (hT : T.PosSemidef)
    (hM : Mᵀ=M) (hh : hᵀ=h) (hTM : T*M=1) (hMT : M*T=1)
    (S C : Tensor ι) (hS₁ : swap S=S) (hS₂ : cycle S=S)
    (hC₁ : swap C=C) (hC₂ : cycle C=C)
    (hC₃ : ∀ i j k, C (i,j,k)=C (i,k,j)) :
    0 ≤ 2*((act 1 1 T S) ⬝ᵥ (act 1 1 h C + act T T 1 S)) +
      (act 1 (h*T) T S + act (h*T) 1 T S + act h h 1 C) ⬝ᵥ act 1 1 M C +
      C ⬝ᵥ act (h*T*h) M M C := by
  have ht : Tᵀ=T := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hT.isHermitian.eq
  rw [invariant_cross T M h ht hTM S C hS₂ hC₂,
    invariant_derivative T M h ht hM hh hTM hMT S C hS₁ hC₁,
    ← sq_J T M h hM hh hMT C]
  have hn := remainder_nonneg hT S (act h M M C) hS₁ hS₂ (act_last_symm h M C hC₃)
  linarith

end MetricTensor

namespace TensorEstimate
open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation Matrix MetricTensor
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma cube_swap {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (z : Space ι) :
    swap (cube f z) = cube f z := by
  ext ⟨i,j,k⟩
  exact C_symm_last hf k z j i
lemma cube_cycle {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (z : Space ι) :
    cycle (cube f z) = cube f z := by
  ext ⟨i,j,k⟩
  change C f j z k i = C f k z i j
  rw [C_symm_first hf j z k i, C_symm_last hf k z j i]
lemma cube_last {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (z : Space ι) (i j k : ι) :
    cube f z (i,j,k) = cube f z (i,k,j) := by
  change C f k z i j = C f j z i k
  rw [C_symm_last hf k z i j, C_symm_first hf k z j i, C_symm_last hf j z k i]

lemma act₃_apply (A : Matrix ι ι ℝ) (X : Tensor ι) (i j k : ι) :
    act 1 1 A X (i,j,k) = ∑ c, A k c * X (i,j,c) := by
  simp [act_apply, Matrix.one_apply, mul_ite, ite_mul]
lemma act₁₃_apply (A B : Matrix ι ι ℝ) (X : Tensor ι) (i j k : ι) :
    act A 1 B X (i,j,k) = ∑ a, ∑ c, A i a * B k c * X (a,j,c) := by
  simp [act_apply, Matrix.one_apply, mul_ite, ite_mul]
lemma act₁₂_apply (A B : Matrix ι ι ℝ) (X : Tensor ι) (i j k : ι) :
    act A B 1 X (i,j,k) = ∑ a, ∑ b, A i a * B j b * X (a,b,k) := by
  simp [act_apply, Matrix.one_apply, mul_ite, ite_mul]
lemma act₂₃_apply (A B : Matrix ι ι ℝ) (X : Tensor ι) (i j k : ι) :
    act 1 A B X (i,j,k) = ∑ b, ∑ c, A j b * B k c * X (i,b,c) := by
  simp [act_apply, Matrix.one_apply, ite_mul]

lemma smooth_pulledH {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (i j : ι) :
    ContDiff ℝ ∞ (fun z => pulledH φ f z i j) :=
  (smooth_hess hf i j).comp (smooth_grad hφ)

lemma derivative_h {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (z : Space ι) :
    (fun p : Idx ι => pd p.2.2 (fun y => pulledH φ f y p.1 p.2.1) z) =
      act 1 1 (hess φ z) (cube f (grad φ z)) := by
  ext ⟨i,j,k⟩
  change pd k ((fun x => hess f x i j) ∘ grad φ) z = _
  rw [pd_comp_grad (smooth_hess hf i j) hφ k, act₃_apply]
  rfl

lemma derivative_P_swap {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (z : Space ι) :
    (fun p : Idx ι => pd p.2.1 (P φ f p.1 p.2.2) z) =
      act 1 1 (pulledH φ f z) (cube φ z) +
      act (hess φ z) (hess φ z) 1 (cube f (grad φ z)) := by
  ext ⟨a,l,k⟩
  change pd l (fun y => ∑ i, hess φ y a i * pulledH φ f y i k) z = _
  rw [pd_sum _ (fun i => (smooth_hess hφ a i).mul (smooth_pulledH hφ hf i k))]
  have hd (i : ι) := congrFun (pd_mul (smooth_hess hφ a i) (smooth_pulledH hφ hf i k) l) z
  simp_rw [hd]
  rw [Finset.sum_add_distrib]
  change _ = act 1 1 (pulledH φ f z) (cube φ z) (a,l,k) +
    act (hess φ z) (hess φ z) 1 (cube f (grad φ z)) (a,l,k)
  rw [act₃_apply, act₁₂_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    change C φ l z a i * hess f (grad φ z) i k =
      hess f (grad φ z) k i * C φ i z a l
    rw [hess_symm hf _ i k, C_symm_last hφ l z a i,
      C_symm_first hφ l z i a, C_symm_last hφ i z l a]
    ring
  · apply Finset.sum_congr rfl
    intro i _
    change hess φ z a i * pd l ((fun x => hess f x i k) ∘ grad φ) z = _
    rw [pd_comp_grad (smooth_hess hf i k) hφ l, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change hess φ z a i * (hess φ z l b * C f b (grad φ z) i k) =
      hess φ z a i * hess φ z l b * C f k (grad φ z) i b
    rw [C_symm_last hf b _ i k, C_symm_first hf b _ k i, C_symm_last hf k _ b i]
    ring

lemma smooth_Q {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (i j : ι) : ContDiff ℝ ∞ (fun z => Q φ f z i j) :=
  smooth_matrix_product (smooth_matrix_product (smooth_pulledH hφ hf) (smooth_hess hφ))
    (smooth_pulledH hφ hf) i j

lemma derivative_Q {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (z : Space ι) :
    (fun p : Idx ι => pd p.2.2 (fun y => Q φ f y p.1 p.2.1) z) =
      act 1 (pulledH φ f z * hess φ z) (hess φ z) (cube f (grad φ z)) +
      act (pulledH φ f z * hess φ z) 1 (hess φ z) (cube f (grad φ z)) +
      act (pulledH φ f z) (pulledH φ f z) 1 (cube φ z) := by
  ext ⟨i,j,d⟩
  have hd := md_mul
    (smooth_matrix_product (smooth_pulledH hφ hf) (smooth_hess hφ))
    (smooth_pulledH hφ hf) (basis d) z
  rw [md_mul (smooth_pulledH hφ hf) (smooth_hess hφ), Matrix.add_mul] at hd
  have hde (a b : ι) : md (basis d) (pulledH φ f) z a b =
      ∑ c, hess φ z d c * cube f (grad φ z) (a,b,c) := by
    have he := congrFun (derivative_h hφ hf z) (a,b,d)
    simpa only [act₃_apply, pd, D, md] using he
  have hc : md (basis d) (hess φ) z = C φ d z := rfl
  change md (basis d) (fun y => pulledH φ f y * hess φ y * pulledH φ f y) z i j = _
  rw [hd, Matrix.add_apply, Matrix.add_apply, hc]
  change _ = act 1 (pulledH φ f z * hess φ z) (hess φ z) (cube f (grad φ z)) (i,j,d) +
    act (pulledH φ f z * hess φ z) 1 (hess φ z) (cube f (grad φ z)) (i,j,d) +
    act (pulledH φ f z) (pulledH φ f z) 1 (cube φ z) (i,j,d)
  have he₁ : (md (basis d) (pulledH φ f) z * hess φ z * pulledH φ f z) i j =
      act 1 (pulledH φ f z * hess φ z) (hess φ z) (cube f (grad φ z)) (i,j,d) := by
    rw [Matrix.mul_assoc, Matrix.mul_apply, act₂₃_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [hde, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    have ht : (hess φ z * pulledH φ f z)ᵀ = pulledH φ f z * hess φ z := by
      rw [Matrix.transpose_mul, MomentCoordinates.hess_transpose hφ]
      change (hess f (grad φ z))ᵀ * hess φ z = _
      rw [MomentCoordinates.hess_transpose hf]
      rfl
    have he := congrArg (fun A : Matrix ι ι ℝ => A j a) ht
    change (hess φ z * pulledH φ f z) a j = (pulledH φ f z * hess φ z) j a at he
    rw [he]
    ring
  have he₂ : (pulledH φ f z * hess φ z * md (basis d) (pulledH φ f) z) i j =
      act (pulledH φ f z * hess φ z) 1 (hess φ z) (cube f (grad φ z)) (i,j,d) := by
    rw [Matrix.mul_apply, act₁₃_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [hde, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  have he₃ : (pulledH φ f z * C φ d z * pulledH φ f z) i j =
      act (pulledH φ f z) (pulledH φ f z) 1 (cube φ z) (i,j,d) := by
    simp only [Matrix.mul_apply, Finset.sum_mul, act₁₂_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    change hess f (grad φ z) i a * C φ d z a b * hess f (grad φ z) b j =
      hess f (grad φ z) i a * hess f (grad φ z) j b * C φ d z a b
    rw [hess_symm hf _ b j]
    ring
  rw [he₁, he₂, he₃]
  ring

omit [DecidableEq ι] in

lemma cubic_trace (Q M : Matrix ι ι ℝ) (hM : Mᵀ=M) (X : Tensor ι)
    (hX : ∀ i j k, X (i,j,k)=X (i,k,j)) :
    (∑ i, ∑ j, Q i j * (M * slice X i * M * slice X j).trace) =
      X ⬝ᵥ act Q M M X := by
  let e : (ι × ι × ι × ι × ι × ι) ≃ (ι × ι × ι × ι × ι × ι) :=
    { toFun := fun (i,j,k,b,l,a) => (i,a,l,j,k,b)
      invFun := fun (i,a,l,j,k,b) => (i,j,k,b,l,a)
      left_inv := by rintro ⟨i,j,k,b,l,a⟩; rfl
      right_inv := by rintro ⟨i,a,l,j,k,b⟩; rfl }
  have hs (a b : ι) : M a b = M b a := congrArg (fun N : Matrix ι ι ℝ => N b a) hM
  calc
    _ = ∑ p : ι × ι × ι × ι × ι × ι,
        (fun (i,j,k,b,l,a) => Q i j * (M k a * X (i,a,l) * M l b * X (j,b,k))) p := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul,
        Finset.mul_sum, Fintype.sum_prod_type, slice]
    _ = ∑ p : ι × ι × ι × ι × ι × ι,
        (fun (i,a,l,j,k,b) => X (i,a,l) * (Q i j * M a k * M l b * X (j,k,b))) p := by
      apply Fintype.sum_equiv e
      rintro ⟨i,j,k,b,l,a⟩
      dsimp [e]
      rw [hs k a, hX j b k]
      ring
    _ = _ := by
      simp only [dotProduct, Fintype.sum_prod_type, act_apply, Finset.mul_sum]

lemma cube_eq_C {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (z : Space ι) (i j k : ι) :
    cube φ z (i,j,k) = C φ i z j k := by
  change C φ k z i j = C φ i z j k
  rw [C_symm_first hφ k z i j, C_symm_last hφ i z k j]

lemma cross_eq {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (z : Space ι) :
    cross φ f z = (act 1 1 (hess φ z) (cube f (grad φ z))) ⬝ᵥ
      (act 1 1 (pulledH φ f z) (cube φ z) +
        act (hess φ z) (hess φ z) 1 (cube f (grad φ z))) := by
  rw [← derivative_h hφ hf z, ← derivative_P_swap hφ hf z]
  simp only [dotProduct, Fintype.sum_prod_type, cross]

lemma qder_eq {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (z : Space ι) :
    qder φ f z =
      (act 1 (pulledH φ f z * hess φ z) (hess φ z) (cube f (grad φ z)) +
       act (pulledH φ f z * hess φ z) 1 (hess φ z) (cube f (grad φ z)) +
       act (pulledH φ f z) (pulledH φ f z) 1 (cube φ z)) ⬝ᵥ
       act 1 1 (hess φ z)⁻¹ (cube φ z) := by
  rw [← derivative_Q hφ hf z]
  simp only [qder, dotProduct, Fintype.sum_prod_type, act₃_apply, cube_eq_C hφ]

lemma cubic_eq {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (z : Space ι) :
    cubic φ f z = cube φ z ⬝ᵥ act (Q φ f z) (hess φ z)⁻¹ (hess φ z)⁻¹ (cube φ z) := by
  rw [← cubic_trace (Q φ f z) _ (inverse_transpose hφ z) _ (cube_last hφ z)]
  have hs (i : ι) : slice (cube φ z) i = C φ i z := by
    ext j k
    exact cube_eq_C hφ z i j k
  change (∑ i, ∑ j, Q φ f z i j *
    ((hess φ z)⁻¹ * C φ i z * (hess φ z)⁻¹ * C φ j z).trace) = _
  simp_rw [hs]

theorem pointwise_remainder {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hpos : ∀ z, (hess φ z).PosDef) (z : Space ι) :
    0 ≤ 2*cross φ f z + qder φ f z + cubic φ f z := by
  rw [cross_eq hφ hf z, qder_eq hφ hf z, cubic_eq hφ z]
  apply invariant_remainder_nonneg _ _ _ (hpos z).posSemidef
    (inverse_transpose hφ z) (MomentCoordinates.hess_transpose hf (grad φ z))
  · exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_gt (hpos z).det_pos))
  · exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt (hpos z).det_pos))
  · exact cube_swap hf _
  · exact cube_cycle hf _
  · exact cube_swap hφ _
  · exact cube_cycle hφ _
  · exact cube_last hφ _

end TensorEstimate

namespace MomentTrace
open Matrix
variable {ι : Type*} [Fintype ι]

lemma cyclic_four (A B C D : Matrix ι ι ℝ) :
    (A*B*C*D).trace = (D*A*B*C).trace := by
  rw [Matrix.trace_mul_comm (A*B*C) D]
  simp only [Matrix.mul_assoc]

lemma expansion (M B R h : Matrix ι ι ℝ) (hrel : M*B*M=h) :
    ((B+R)*M*((B+R)*M)).trace =
      (M*B*M*B).trace + 2*(h*R).trace + (M*R*M*R).trace := by
  have h₁ : (B*M*B*M).trace = (M*B*M*B).trace := cyclic_four _ _ _ _
  have h₂ : (B*M*R*M).trace = (h*R).trace := by
    rw [cyclic_four, hrel]
  have h₃ : (R*M*B*M).trace = (h*R).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc, hrel]
  have h₄ : (R*M*R*M).trace = (M*R*M*R).trace := cyclic_four _ _ _ _
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, ← Matrix.mul_assoc]
  rw [h₁, h₂, h₃, h₄]
  ring

variable [DecidableEq ι]

lemma inverse_sandwich (T M h : Matrix ι ι ℝ) (hMT : M*T=1) (hTM : T*M=1) :
    M*(T*h*T)*M=h := by
  simp only [Matrix.mul_assoc, hTM, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hMT, Matrix.one_mul]

lemma coefficient_identity (T M h H : Matrix ι ι ℝ) (hMT : M*T=1) :
    (M*(T*h*T)*H*(T*h*T)).trace = ((h*T*h)*(T*H*T)).trace := by
  calc
    _ = (h*(T*H*T)*(h*T)).trace := by
      simp only [← Matrix.mul_assoc, hMT, Matrix.one_mul]
    _ = _ := Matrix.trace_mul_cycle h (T*H*T) (h*T)

lemma base_identity (T M h : Matrix ι ι ℝ) (hMT : M*T=1) (hTM : T*M=1) :
    (M*(T*h*T)*M*(T*h*T)).trace = ((h*T*h)*T).trace := by
  rw [inverse_sandwich T M h hMT hTM]
  simp only [Matrix.mul_assoc]

omit [DecidableEq ι] in
lemma trace_contract_symm (Q L : Matrix ι ι ℝ) (hL : Lᵀ=L) :
    (Q*L).trace = ∑ i, ∑ j, Q i j * L i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he := congrArg (fun A : Matrix ι ι ℝ => A i j) hL
  change L j i = L i j at he
  rw [he]

lemma H_expansion (T M h H : Matrix ι ι ℝ) (hT : Tᵀ=T) (hH : Hᵀ=H)
    (hMT : M*T=1) (hTM : T*M=1) :
    (M*(T*h*T)*H*(T*h*T)).trace = (M*(T*h*T)*M*(T*h*T)).trace +
      ∑ i, ∑ j, (h*T*h) i j * (T*H*T-T) i j := by
  have hL : (T*H*T-T)ᵀ = T*H*T-T := by
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, hT, hH, Matrix.mul_assoc]
  rw [coefficient_identity T M h H hMT, base_identity T M h hMT hTM,
    ← trace_contract_symm (h*T*h) _ hL, Matrix.mul_sub, Matrix.trace_sub]
  ring

end MomentTrace

namespace IntegratedTensor
open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation TensorEstimate Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma compact_pulledH {φ f : Space ι → ℝ} (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) (i j : ι) :
    HasCompactSupport (fun z => pulledH φ f z i j) := by
  change HasCompactSupport ((pd j (pd i f)) ∘ grad φ)
  rw [← hΦ]
  exact (compact_D (compact_D hfc (basis i)) (basis j)).comp_homeomorph Φ

omit [DecidableEq ι] in
lemma compact_matrix_mul_left {A B : Space ι → Matrix ι ι ℝ}
    (hA : ∀ i j, HasCompactSupport (fun z => A z i j)) (i j : ι) :
    HasCompactSupport (fun z => (A z * B z) i j) :=
  compact_sum _ (fun k => (hA i k).mul_right)

omit [DecidableEq ι] in
lemma compact_matrix_mul_right {A B : Space ι → Matrix ι ι ℝ}
    (hB : ∀ i j, HasCompactSupport (fun z => B z i j)) (i j : ι) :
    HasCompactSupport (fun z => (A z * B z) i j) :=
  compact_sum _ (fun k => (hB k j).mul_left)

omit [DecidableEq ι] in
lemma smooth_matrix_trace {A : Space ι → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z => A z i j)) :
    ContDiff ℝ ∞ (fun z => (A z).trace) := smooth_sum _ (fun i => hA i i)

omit [DecidableEq ι] in
lemma compact_matrix_trace {A : Space ι → Matrix ι ι ℝ}
    (hA : ∀ i j, HasCompactSupport (fun z => A z i j)) :
    HasCompactSupport (fun z => (A z).trace) := compact_sum _ (fun i => hA i i)

lemma compact_Q {φ f : Space ι → ℝ} (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) (i j : ι) :
    HasCompactSupport (fun z => Q φ f z i j) :=
  compact_matrix_mul_right (compact_pulledH hfc Φ hΦ) i j

lemma smooth_R {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (a l : ι) : ContDiff ℝ ∞ (R φ f a l) :=
  smooth_divergence hφ (fun k => smooth_pd (smooth_P hφ hf a k) l)

lemma compact_R {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) (a l : ι) :
    HasCompactSupport (R φ f a l) :=
  compact_divergence (fun k => compact_D (compact_P hφ hf hfc Φ hΦ a k) (basis l))

lemma smooth_cross {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (cross φ f) :=
  smooth_sum _ (fun a => smooth_sum _ (fun l => smooth_sum _ (fun k =>
    (smooth_pd (smooth_pulledH hφ hf a l) k).mul (smooth_pd (smooth_P hφ hf a k) l))))

lemma compact_cross {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    HasCompactSupport (cross φ f) :=
  compact_sum _ (fun a => compact_sum _ (fun l => compact_sum _ (fun k =>
    (compact_D (compact_P hφ hf hfc Φ hΦ a k) (basis l)).mul_left)))

lemma rmat_symm {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (z : Space ι) : (rmat φ f z)ᵀ = rmat φ f z := by
  ext a l
  exact R_symm hφ hf z l a

variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

lemma mixed_integral {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    expectation μ φ (mixed φ f) = expectation μ φ (cross φ f) := by
  have he : mixed φ f = fun z => ∑ a, ∑ l, pulledH φ f z a l * R φ f a l z := by
    funext z
    exact MomentTrace.trace_contract_symm _ _ (rmat_symm hφ hf z)
  rw [he]
  rw [expectation_sum μ hφ _
    (fun a => (smooth_sum _ (fun l => (smooth_pulledH hφ hf a l).mul (smooth_R hφ hf a l))).continuous)
    (fun a => compact_sum _ (fun l => (compact_R hφ hf hfc Φ hΦ a l).mul_left))]
  change _ = expectation μ φ (fun z => ∑ a, ∑ l, ∑ k,
    pd k (fun y => pulledH φ f y a l) z * pd l (P φ f a k) z)
  rw [expectation_sum μ hφ _
    (fun a => (smooth_sum _ (fun l => smooth_sum _ (fun k =>
      (smooth_pd (smooth_pulledH hφ hf a l) k).mul (smooth_pd (smooth_P hφ hf a k) l)))).continuous)
    (fun a => compact_sum _ (fun l => compact_sum _ (fun k =>
      (compact_D (compact_P hφ hf hfc Φ hΦ a k) (basis l)).mul_left)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [expectation_sum μ hφ _
    (fun l => ((smooth_pulledH hφ hf a l).mul (smooth_R hφ hf a l)).continuous)
    (fun l => (compact_R hφ hf hfc Φ hΦ a l).mul_left)]
  rw [expectation_sum μ hφ _
    (fun l => (smooth_sum _ (fun k =>
      (smooth_pd (smooth_pulledH hφ hf a l) k).mul (smooth_pd (smooth_P hφ hf a k) l))).continuous)
    (fun l => compact_sum _ (fun k =>
      (compact_D (compact_P hφ hf hfc Φ hΦ a k) (basis l)).mul_left))]
  apply Finset.sum_congr rfl
  intro l _
  rw [expectation_sum μ hφ _
    (fun k => ((smooth_pd (smooth_pulledH hφ hf a l) k).mul (smooth_pd (smooth_P hφ hf a k) l)).continuous)
    (fun k => (compact_D (compact_P hφ hf hfc Φ hΦ a k) (basis l)).mul_left)]
  exact divergence_adjoint μ basis _ hφ (fun k => smooth_pd (smooth_P hφ hf a k) l)
    (smooth_pulledH hφ hf a l)
    (fun k => compact_D (compact_P hφ hf hfc Φ hΦ a k) (basis l))

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

lemma smooth_L {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hne : ∀ z, (hess φ z).det ≠ 0) (i j d : ι) : ContDiff ℝ ∞ (L φ i j d) :=
  smooth_sum _ (fun k => (smooth_inverse_entry (smooth_hess hφ) hne d k).mul (smooth_C hφ i j k))

lemma smooth_qder {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0) :
    ContDiff ℝ ∞ (qder φ f) :=
  smooth_sum _ (fun i => smooth_sum _ (fun j => smooth_sum _ (fun d =>
    (smooth_pd (smooth_Q hφ hf i j) d).mul (smooth_L hφ hne i j d))))

lemma compact_qder {φ f : Space ι → ℝ} (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    HasCompactSupport (qder φ f) :=
  compact_sum _ (fun i => compact_sum _ (fun j => compact_sum _ (fun d =>
    (compact_D (compact_Q hfc Φ hΦ i j) (basis d)).mul_right)))

lemma smooth_cubic {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0) :
    ContDiff ℝ ∞ (cubic φ f) := by
  have hM := smooth_inverse_entry (smooth_hess hφ) hne
  exact smooth_sum _ (fun i => smooth_sum _ (fun j =>
    (smooth_Q hφ hf i j).mul (smooth_matrix_trace
      (smooth_matrix_product (smooth_matrix_product (smooth_matrix_product hM
        (smooth_C hφ i)) hM) (smooth_C hφ j)))))

lemma compact_cubic {φ f : Space ι → ℝ} (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    HasCompactSupport (cubic φ f) :=
  compact_sum _ (fun i => compact_sum _ (fun j => (compact_Q hfc Φ hΦ i j).mul_right))

lemma smooth_divterm {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0) :
    ContDiff ℝ ∞ (divterm φ f) :=
  smooth_sum _ (fun i => smooth_sum _ (fun j => (smooth_Q hφ hf i j).mul
    (smooth_divergence hφ (smooth_L hφ hne i j))))

lemma compact_divterm {φ f : Space ι → ℝ} (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    HasCompactSupport (divterm φ f) :=
  compact_sum _ (fun i => compact_sum _ (fun j => (compact_Q hfc Φ hΦ i j).mul_right))

lemma divterm_integral {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0) (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    expectation μ φ (divterm φ f) = expectation μ φ (qder φ f) := by
  have he : divterm φ f = fun z => ∑ i, ∑ j, ∑ d,
      Q φ f z i j * adjoint φ (basis d) (L φ i j d) z := by
    funext z
    simp only [divterm, divergence, Finset.mul_sum]
  rw [he]
  change _ = expectation μ φ (fun z => ∑ i, ∑ j, ∑ d,
    pd d (fun y => Q φ f y i j) z * L φ i j d z)
  have hl (i j d : ι) : ContDiff ℝ ∞ (fun z =>
      Q φ f z i j * adjoint φ (basis d) (L φ i j d) z) :=
    (smooth_Q hφ hf i j).mul (smooth_adjoint hφ (smooth_L hφ hne i j d) (basis d))
  have hr (i j d : ι) : ContDiff ℝ ∞ (fun z =>
      pd d (fun y => Q φ f y i j) z * L φ i j d z) :=
    (smooth_pd (smooth_Q hφ hf i j) d).mul (smooth_L hφ hne i j d)
  rw [expectation_sum μ hφ _ (fun i => (smooth_sum _ (fun j => smooth_sum _ (hl i j))).continuous)
    (fun i => compact_sum _ (fun j => compact_sum _ (fun _ => (compact_Q hfc Φ hΦ i j).mul_right)))]
  rw [expectation_sum μ hφ _ (fun i => (smooth_sum _ (fun j => smooth_sum _ (hr i j))).continuous)
    (fun i => compact_sum _ (fun j => compact_sum _ (fun d =>
      (compact_D (compact_Q hfc Φ hΦ i j) (basis d)).mul_right)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [expectation_sum μ hφ _ (fun j => (smooth_sum _ (hl i j)).continuous)
    (fun j => compact_sum _ (fun _ => (compact_Q hfc Φ hΦ i j).mul_right))]
  rw [expectation_sum μ hφ _ (fun j => (smooth_sum _ (hr i j)).continuous)
    (fun j => compact_sum _ (fun d => (compact_D (compact_Q hfc Φ hΦ i j) (basis d)).mul_right))]
  apply Finset.sum_congr rfl
  intro j _
  rw [expectation_sum μ hφ _ (fun d => (hl i j d).continuous)
    (fun _ => (compact_Q hfc Φ hΦ i j).mul_right)]
  rw [expectation_sum μ hφ _ (fun d => (hr i j d).continuous)
    (fun d => (compact_D (compact_Q hfc Φ hΦ i j) (basis d)).mul_right)]
  apply Finset.sum_congr rfl
  intro d _
  exact (integration_by_parts_rightcompact μ hφ (smooth_L hφ hne i j d)
    (smooth_Q hφ hf i j) (compact_Q hfc Φ hΦ i j) (basis d)).symm

lemma smooth_bmat {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (i j : ι) : ContDiff ℝ ∞ (fun z => bmat φ f z i j) :=
  smooth_matrix_product (smooth_matrix_product (smooth_hess hφ) (smooth_pulledH hφ hf))
    (smooth_hess hφ) i j

lemma compact_bmat {φ f : Space ι → ℝ} (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) (i j : ι) :
    HasCompactSupport (fun z => bmat φ f z i j) :=
  compact_matrix_mul_left (compact_matrix_mul_right (compact_pulledH hfc Φ hΦ)) i j

lemma smooth_base {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0) : ContDiff ℝ ∞ (base φ f) := by
  have hM := smooth_inverse_entry (smooth_hess hφ) hne
  exact smooth_matrix_trace (smooth_matrix_product
    (smooth_matrix_product (smooth_matrix_product hM (smooth_bmat hφ hf)) hM) (smooth_bmat hφ hf))

lemma compact_base {φ f : Space ι → ℝ} (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    HasCompactSupport (base φ f) :=
  compact_matrix_trace (compact_matrix_mul_right (compact_bmat hfc Φ hΦ))

lemma smooth_rterm {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0) : ContDiff ℝ ∞ (rterm φ f) := by
  have hM := smooth_inverse_entry (smooth_hess hφ) hne
  exact smooth_matrix_trace (smooth_matrix_product
    (smooth_matrix_product (smooth_matrix_product hM (smooth_R hφ hf)) hM) (smooth_R hφ hf))

lemma compact_rterm {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    HasCompactSupport (rterm φ f) :=
  compact_matrix_trace (compact_matrix_mul_right (compact_R hφ hf hfc Φ hΦ))

lemma smooth_mixed {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (mixed φ f) :=
  smooth_matrix_trace (smooth_matrix_product (smooth_pulledH hφ hf) (smooth_R hφ hf))

lemma compact_mixed {φ f : Space ι → ℝ} (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    HasCompactSupport (mixed φ f) :=
  compact_matrix_trace (compact_matrix_mul_left (compact_pulledH hfc Φ hΦ))

lemma traceL_expansion {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0) (z : Space ι) :
    traceL φ f z = base φ f z + 2*mixed φ f z + rterm φ f z := by
  have he : jacW φ f z = bmat φ f z + rmat φ f z := by
    ext a l
    change pd l (W φ f a) z = _
    rw [W_derivative hφ hf a l]
    rfl
  have hrel : (hess φ z)⁻¹ * bmat φ f z * (hess φ z)⁻¹ = pulledH φ f z :=
    MomentTrace.inverse_sandwich _ _ _
      (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hne z)))
      (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hne z)))
  unfold traceL
  rw [he, MomentTrace.expansion _ _ _ _ hrel]
  rfl

lemma traceH_expansion {φ V f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hne : ∀ z, (hess φ z).det ≠ 0) {c : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + c - φ z) (z : Space ι) :
    traceH φ V f z = base φ f z - divterm φ f z - cubic φ f z := by
  have ht (i j : ι) : (hess φ z * hess V (grad φ z) * hess φ z - hess φ z) i j =
      -divergence φ basis (L φ i j) z -
      ((hess φ z)⁻¹ * C φ i z * (hess φ z)⁻¹ * C φ j z).trace := by
    rw [twice_moment hφ hV hne heq]
    congr 1
    change (∑ d, (pd d (L φ i j d) z - pd d φ z * L φ i j d z)) =
      -(∑ d, (pd d φ z * L φ i j d z - pd d (L φ i j d) z))
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  unfold traceH bmat
  rw [MomentTrace.H_expansion _ _ _ _ (MomentCoordinates.hess_transpose hφ z)
    (MomentCoordinates.hess_transpose hV (grad φ z))
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hne z)))
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hne z)))]
  simp only [ht, mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  change base φ f z + (-divterm φ f z - cubic φ f z) = _
  ring

lemma rterm_nonneg {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hpos : ∀ z, (hess φ z).PosDef) (z : Space ι) :
    0 ≤ rterm φ f z :=
  MomentMatrix.trace_conjugate_nonneg (hpos z).inv.posSemidef (rmat_symm hφ hf z)

omit [DecidableEq ι] [Fintype ι] [Measure.IsAddHaarMeasure μ] in
lemma expectation_const_mul (V F : Space ι → ℝ) (a : ℝ) :
    expectation μ V (fun z => a*F z) = a * expectation μ V F := by
  simp only [expectation, mul_assoc, integral_const_mul]

omit [DecidableEq ι] in
lemma expectation_sub {V F G : Space ι → ℝ} (hV : ContDiff ℝ ∞ V)
    (hF : Continuous F) (hG : Continuous G) (hFc : HasCompactSupport F) (hGc : HasCompactSupport G) :
    expectation μ V (fun z => F z-G z) = expectation μ V F - expectation μ V G := by
  simp only [expectation, sub_mul]
  exact integral_sub (integrable_weighted μ hV hF hFc) (integrable_weighted μ hV hG hGc)

omit [DecidableEq ι] [Fintype ι] [Measure.IsAddHaarMeasure μ] in
lemma expectation_nonneg {V F : Space ι → ℝ} (hF : ∀ z, 0 ≤ F z) :
    0 ≤ expectation μ V F :=
  integral_nonneg (fun z => mul_nonneg (hF z) (le_of_lt (Real.exp_pos _)))

theorem tensor_estimate {φ V f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hpos : ∀ z, (hess φ z).PosDef) {c : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + c - φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    expectation μ φ (traceH φ V f) ≤ expectation μ φ (traceL φ f) := by
  have hne (z : Space ι) := ne_of_gt (hpos z).det_pos
  have sbase := (smooth_base hφ hf hne).continuous
  have cbase := compact_base hfc Φ hΦ
  have smixed := (smooth_mixed hφ hf).continuous
  have cmixed := compact_mixed hfc Φ hΦ
  have sr := (smooth_rterm hφ hf hne).continuous
  have cr := compact_rterm hφ hf hfc Φ hΦ
  have sd := (smooth_divterm hφ hf hne).continuous
  have cd := compact_divterm hfc Φ hΦ
  have sc := (smooth_cubic hφ hf hne).continuous
  have cc := compact_cubic hfc Φ hΦ
  have sx := (smooth_cross hφ hf).continuous
  have cx := compact_cross hφ hf hfc Φ hΦ
  have sq := (smooth_qder hφ hf hne).continuous
  have cq := compact_qder hfc Φ hΦ
  have hleft : expectation μ φ (traceL φ f) = expectation μ φ (base φ f) +
      2*expectation μ φ (cross φ f) + expectation μ φ (rterm φ f) := by
    have he : traceL φ f = fun z => base φ f z + 2*mixed φ f z + rterm φ f z :=
      funext (traceL_expansion hφ hf hne)
    rw [he, expectation_add μ hφ (f := fun z => base φ f z + 2*mixed φ f z) (g := rterm φ f) (sbase.add (continuous_const.mul smixed)) sr
      (cbase.add cmixed.mul_left) cr,
      expectation_add μ hφ (f := base φ f) (g := fun z => 2*mixed φ f z) sbase (continuous_const.mul smixed) cbase cmixed.mul_left,
      expectation_const_mul, mixed_integral μ hφ hf hfc Φ hΦ]
  have hright : expectation μ φ (traceH φ V f) = expectation μ φ (base φ f) -
      expectation μ φ (qder φ f) - expectation μ φ (cubic φ f) := by
    have he : traceH φ V f = fun z => base φ f z - divterm φ f z - cubic φ f z :=
      funext (traceH_expansion hφ hV hne heq)
    rw [he, expectation_sub μ hφ (F := fun z => base φ f z-divterm φ f z) (G := cubic φ f) (sbase.sub sd) sc (cbase.sub cd) cc,
      expectation_sub μ hφ sbase sd cbase cd, divterm_integral μ hφ hf hne hfc Φ hΦ]
  have hr := expectation_nonneg μ (V := φ) (rterm_nonneg hφ hf hpos)
  have hp := expectation_nonneg μ (V := φ) (TensorEstimate.pointwise_remainder hφ hf hpos)
  rw [expectation_add μ hφ (f := fun z => 2*cross φ f z+qder φ f z) (g := cubic φ f) ((continuous_const.mul sx).add sq) sc
      (cx.mul_left.add cq) cc,
    expectation_add μ hφ (f := fun z => 2*cross φ f z) (g := qder φ f) (continuous_const.mul sx) sq cx.mul_left cq,
    expectation_const_mul] at hp
  rw [hleft, hright]
  linarith

end IntegratedTensor

namespace FullTensor
open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation IntegratedTensor TargetCoordinates Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma jacobian_pull {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (z : Space ι) :
    jacobian (wField Φ φ f) (grad φ z) = jacW φ f z * (hess φ z)⁻¹ := by
  ext a l
  change pd l (target Φ (W φ f a)) (grad φ z) = _
  rw [pd_target hφ (smooth_W hφ hf a) hne Φ hΦ hInv]
  change (∑ k, (hess φ z)⁻¹ l k * pd k (W φ f a) z) =
    ∑ k, pd k (W φ f a) z * (hess φ z)⁻¹ k l
  apply Finset.sum_congr rfl
  intro k _
  rw [inverse_symm hφ z l k]
  ring

lemma squareTrace_pull {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) :
    squareTrace (wField Φ φ f) ∘ grad φ = traceL φ f := by
  funext z
  change (jacobian (wField Φ φ f) (grad φ z) * jacobian (wField Φ φ f) (grad φ z)).trace = _
  rw [jacobian_pull hφ hf hne Φ hΦ hInv]
  rfl

lemma hEnergy_pull {φ V f : Space ι → ℝ}
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) :
    hEnergy Φ φ V f ∘ grad φ = traceH φ V f := by
  funext z
  have he : Φ.symm (grad φ z) = z := by rw [← hΦ]; exact Φ.symm_apply_apply z
  simp only [Function.comp_apply, hEnergy, mField, bField, he, traceH]

lemma wField_divergence {φ V f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0) {c : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + c - φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (a : ι) :
    divergence V basis (fun j x => bField Φ φ f x a j) = wField Φ φ f a := by
  funext x
  obtain ⟨z, rfl⟩ := Φ.surjective x
  rw [hΦ]
  have hr := row_adjoint hφ hV hne heq Φ hΦ hInv (P φ f a) (smooth_P hφ hf a) z
  change divergence V basis (fun j => target Φ (fun y => ∑ k, P φ f a k y * hess φ y k j))
    (grad φ z) = target Φ (W φ f a) (grad φ z)
  rw [hr, target_apply Φ hΦ]
  rfl

variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

lemma bochner_trace {V : Space ι → ℝ} (hV : ContDiff ℝ ∞ V)
    (Y : ι → Space ι → ℝ) (hY : ∀ i, ContDiff ℝ ∞ (Y i))
    (hYc : ∀ i, HasCompactSupport (Y i)) :
    expectation μ V (fun x => (divergence V basis Y x)^2) =
      expectation μ V (wEnergy V Y) + expectation μ V (squareTrace Y) := by
  have h₁ : expectation μ V (wEnergy V Y) =
      ∑ j, ∑ i, expectation μ V (fun x => hess V x i j * Y i x * Y j x) := by
    unfold wEnergy
    rw [expectation_sum μ hV _ (fun j =>
      (smooth_sum _ (fun i => ((smooth_hess hV i j).mul (hY i)).mul (hY j))).continuous)
      (fun j => compact_sum _ (fun _ => (hYc j).mul_left))]
    apply Finset.sum_congr rfl
    intro j _
    exact expectation_sum μ hV _
      (fun i => (((smooth_hess hV i j).mul (hY i)).mul (hY j)).continuous)
      (fun _ => (hYc j).mul_left)
  have h₂ : expectation μ V (squareTrace Y) =
      ∑ j, ∑ i, expectation μ V (fun x => pd i (Y j) x * pd j (Y i) x) := by
    have he : squareTrace Y = fun x => ∑ j, ∑ i, pd i (Y j) x * pd j (Y i) x := rfl
    rw [he, expectation_sum μ hV _ (fun j =>
      (smooth_sum _ (fun i => (smooth_pd (hY j) i).mul (smooth_pd (hY i) j))).continuous)
      (fun j => compact_sum _ (fun i => (compact_D (hYc j) (basis i)).mul_right))]
    apply Finset.sum_congr rfl
    intro j _
    exact expectation_sum μ hV _
      (fun i => ((smooth_pd (hY j) i).mul (smooth_pd (hY i) j)).continuous)
      (fun i => (compact_D (hYc j) (basis i)).mul_right)
  rw [h₁, h₂]
  exact bochner μ basis Y hV hY hYc

theorem tensor_energy {φ V f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hpos : ∀ z, (hess φ z).PosDef) {c Z : ℝ} (hZ : 0 < Z)
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z) + c - φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmap : Measure.map (grad φ) (sourceMeasure μ φ) = targetMeasure μ V Z) :
    normalizedE μ V Z (hEnergy Φ φ V f) ≤ normalizedE μ V Z (squareTrace (wField Φ φ f)) ∧
    normalizedE μ V Z (hEnergy Φ φ V f) + normalizedE μ V Z (wEnergy V (wField Φ φ f)) ≤
      normalizedE μ V Z (fun x => (divergence V basis (wField Φ φ f) x)^2) := by
  have ht := IntegratedTensor.tensor_estimate μ hφ hV hf hfc hpos heq Φ hΦ
  have hne (z : Space ι) := ne_of_gt (hpos z).det_pos
  rw [← hEnergy_pull (V := V) (f := f) Φ hΦ,
    ← squareTrace_pull hφ hf hne Φ hΦ hInv,
    expectation_transport μ hφ hV hZ Φ hΦ hmap,
    expectation_transport μ hφ hV hZ Φ hΦ hmap] at ht
  refine ⟨ht, ?_⟩
  have hs (i : ι) : ContDiff ℝ ∞ (wField Φ φ f i) := smooth_target hInv (smooth_W hφ hf i)
  have hc (i : ι) : HasCompactSupport (wField Φ φ f i) :=
    (compact_W hφ hf hfc Φ hΦ i).comp_homeomorph Φ.symm
  have hb := bochner_trace μ hV (wField Φ φ f) hs hc
  have hb' : normalizedE μ V Z (fun x => (divergence V basis (wField Φ φ f) x)^2) =
      normalizedE μ V Z (wEnergy V (wField Φ φ f)) +
      normalizedE μ V Z (squareTrace (wField Φ φ f)) := by
    unfold normalizedE
    rw [hb, add_div]
  rw [hb']
  linarith

end FullTensor

namespace DualEnergy
open MeasureTheory WeightedCalculus MomentCoordinates MomentDifferential MomentEquation
  IntegratedTensor TargetCoordinates FullTensor MomentMatrix TensorEstimate
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

lemma integral_divergence {V g : Space ι → ℝ} (hV : ContDiff ℝ ∞ V)
    {Z : ℝ} (hZ : 0 < Z) (Y : ι → Space ι → ℝ)
    (hY : ∀ i, ContDiff ℝ ∞ (Y i)) (hYc : ∀ i, HasCompactSupport (Y i))
    (hg : ContDiff ℝ ∞ g) :
    (∫ x, g x * divergence V basis Y x ∂targetMeasure μ V Z) =
      ∑ i, ∫ x, pd i g x * Y i x ∂targetMeasure μ V Z := by
  simp only [target_integral μ hV hZ, normalizedE]
  rw [divergence_adjoint μ basis Y hV hY hg hYc, Finset.sum_div]
  rfl

lemma smooth_bField {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (Φ : Space ι ≃ₜ Space ι)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (i j : ι) :
    ContDiff ℝ ∞ (fun x => bField Φ φ f x i j) :=
  (smooth_bmat hφ hf i j).comp hInv

lemma compact_bField {φ f : Space ι → ℝ} (hfc : HasCompactSupport f)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ) (i j : ι) :
    HasCompactSupport (fun x => bField Φ φ f x i j) :=
  (compact_bmat hfc Φ hΦ i j).comp_homeomorph Φ.symm

lemma smooth_mField {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ z, (hess φ z).PosDef) (Φ : Space ι ≃ₜ Space ι)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (i j : ι) :
    ContDiff ℝ ∞ (fun x => mField Φ φ x i j) :=
  (smooth_inverse_entry (smooth_hess hφ) (fun z => ne_of_gt (hpos z).det_pos) i j).comp hInv

lemma bField_symm {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (Φ : Space ι ≃ₜ Space ι) (x : Space ι) :
    (bField Φ φ f x)ᵀ = bField Φ φ f x := by
  unfold bField bmat pulledH
  simp only [Matrix.transpose_mul, Matrix.mul_assoc, Function.comp_apply]
  rw [MomentEquation.hess_transpose hφ, MomentEquation.hess_transpose hf]

lemma pairings {φ V f ψ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hψ : ContDiff ℝ ∞ ψ) (hne : ∀ z, (hess φ z).det ≠ 0) {c Z : ℝ} (hZ : 0 < Z)
    [IsFiniteMeasure (targetMeasure μ V Z)]
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) :
    (∫ x, ψ x * divergence V basis (wField Φ φ f) x ∂targetMeasure μ V Z) =
      (∫ x, ∑ i, pd i ψ x*wField Φ φ f i x ∂targetMeasure μ V Z) ∧
    (∫ x, ψ x * divergence V basis (wField Φ φ f) x ∂targetMeasure μ V Z) =
      ∫ x, (bField Φ φ f x * hess ψ x).trace ∂targetMeasure μ V Z := by
  have hW i : ContDiff ℝ ∞ (wField Φ φ f i) := smooth_target hInv (smooth_W hφ hf i)
  have hWc i : HasCompactSupport (wField Φ φ f i) :=
    (compact_W hφ hf hfc Φ hΦ i).comp_homeomorph Φ.symm
  have hi i : Integrable (fun x => pd i ψ x*wField Φ φ f i x) (targetMeasure μ V Z) :=
    ((smooth_D hψ (basis i)).mul (hW i)).continuous.integrable_of_hasCompactSupport (hWc i).mul_left
  have he := integral_divergence μ hV hZ (wField Φ φ f) hW hWc hψ
  refine ⟨he.trans (integral_finsetSum _ (fun i _ => hi i)).symm, ?_⟩
  rw [he]
  have hr (i : ι) :
      (∫ x, pd i ψ x*wField Φ φ f i x ∂targetMeasure μ V Z) =
        ∑ j, ∫ x, hess ψ x i j*bField Φ φ f x i j ∂targetMeasure μ V Z := by
    rw [← wField_divergence hφ hV hf hne heq Φ hΦ hInv i]
    exact integral_divergence μ hV hZ _ (smooth_bField hφ hf Φ hInv i)
      (compact_bField hfc Φ hΦ i) (smooth_D hψ (basis i))
  simp_rw [hr]
  have hij (i j : ι) : Integrable (fun x => hess ψ x i j*bField Φ φ f x i j) (targetMeasure μ V Z) :=
    ((smooth_hess hψ i j).mul (smooth_bField hφ hf Φ hInv i j)).continuous.integrable_of_hasCompactSupport
      (compact_bField hfc Φ hΦ i j).mul_left
  have hti : (fun x => (bField Φ φ f x*hess ψ x).trace) =
      fun x => ∑ i, ∑ j, hess ψ x i j*bField Φ φ f x i j := by
    funext x
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hess_symm hψ x j i]
    ring
  rw [hti,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hij i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum _ (fun j _ => hij i j)).symm

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

omit [Measure.IsAddHaarMeasure μ] in
lemma trace_pair_integrable {φ V f ψ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hψ : ContDiff ℝ ∞ ψ) {Z : ℝ}
    [IsFiniteMeasure (targetMeasure μ V Z)]
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) :
    Integrable (fun x => (bField Φ φ f x*hess ψ x).trace) (targetMeasure μ V Z) := by
  apply (smooth_matrix_trace (smooth_matrix_product (smooth_bField hφ hf Φ hInv) (smooth_hess hψ))).continuous.integrable_of_hasCompactSupport
  exact compact_matrix_trace (compact_matrix_mul_left (compact_bField hfc Φ hΦ))

omit [Measure.IsAddHaarMeasure μ] in
lemma first_energy_integrable {φ V f ψ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hψ : ContDiff ℝ ∞ ψ)
    (hpos : ∀ z, (hess φ z).PosDef) {Z : ℝ} [IsFiniteMeasure (targetMeasure μ V Z)]
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) :
    Integrable (hEnergy Φ φ ψ f) (targetMeasure μ V Z) := by
  apply (smooth_matrix_trace (smooth_matrix_product (smooth_matrix_product
    (smooth_matrix_product (smooth_mField hφ hpos Φ hInv) (smooth_bField hφ hf Φ hInv))
    (smooth_hess hψ)) (smooth_bField hφ hf Φ hInv))).continuous.integrable_of_hasCompactSupport
  exact compact_matrix_trace (compact_matrix_mul_right (compact_bField hfc Φ hΦ))

omit [Measure.IsAddHaarMeasure μ] in
lemma second_energy_integrable {φ V f ψ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hψ : ContDiff ℝ ∞ ψ)
    {Z : ℝ} [IsFiniteMeasure (targetMeasure μ V Z)]
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) :
    Integrable (wEnergy ψ (wField Φ φ f)) (targetMeasure μ V Z) := by
  apply (smooth_sum _ (fun j => smooth_sum _ (fun i =>
    ((smooth_hess hψ i j).mul (smooth_target hInv (smooth_W hφ hf i))).mul
      (smooth_target hInv (smooth_W hφ hf j))))).continuous.integrable_of_hasCompactSupport
  exact compact_sum _ (fun j => compact_sum _ (fun _ =>
    ((compact_W hφ hf hfc Φ hΦ j).comp_homeomorph Φ.symm).mul_left))

lemma first_cs {φ V f ψ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hψ : ContDiff ℝ ∞ ψ) (hpos : ∀ z, (hess φ z).PosDef)
    (hψpos : ∀ x, (hess ψ x).PosSemidef) {c Z : ℝ} (hZ : 0 < Z)
    [IsFiniteMeasure (targetMeasure μ V Z)]
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmi : Integrable (fun x => (tau Φ φ x*hess ψ x).trace) (targetMeasure μ V Z)) :
    (∫ x, ψ x*divergence V basis (wField Φ φ f) x ∂targetMeasure μ V Z)^2 ≤
      (∫ x, (tau Φ φ x*hess ψ x).trace ∂targetMeasure μ V Z) *
        (∫ x, hEnergy Φ φ ψ f x ∂targetMeasure μ V Z) := by
  rw [(pairings μ hφ hV hf hfc hψ (fun z => ne_of_gt (hpos z).det_pos) hZ heq Φ hΦ hInv).2]
  apply integral_trace_cs (targetMeasure μ V Z) (M:=mField Φ φ) (T:=tau Φ φ)
    (H:=hess ψ) (B:=bField Φ φ f)
    (fun x => (hpos (Φ.symm x)).inv.posSemidef) hψpos
    (fun x => MomentEquation.hess_transpose hφ (Φ.symm x)) (bField_symm hφ hf Φ)
  · intro x
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt (hpos (Φ.symm x)).det_pos))
  · intro x
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_gt (hpos (Φ.symm x)).det_pos))
  · exact hmi
  · exact trace_pair_integrable μ hφ hf hfc hψ Φ hΦ hInv
  · exact first_energy_integrable μ hφ hf hfc hψ hpos Φ hΦ hInv

lemma wEnergy_form (ψ : Space ι → ℝ) (Y : ι → Space ι → ℝ) (x : Space ι) :
    (fun i => Y i x) ⬝ᵥ (hess ψ x *ᵥ (fun i => Y i x)) = wEnergy ψ Y x := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, wEnergy]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma second_cs {φ V f ψ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hψ : ContDiff ℝ ∞ ψ) (hpos : ∀ z, (hess φ z).PosDef)
    (hψpos : ∀ x, (hess ψ x).PosSemidef) {c Z q : ℝ} (hZ : 0 < Z)
    [IsFiniteMeasure (targetMeasure μ V Z)]
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hiψ : Integrable ψ (targetMeasure μ V Z))
    (hEuler : ∀ x, (∑ i, x i*pd i ψ x) = q*ψ x)
    (hHessEuler : ∀ x i, (∑ j, hess ψ x i j*x j) = (q-1)*pd i ψ x) :
    (q-1)^2*(∫ x, ψ x*divergence V basis (wField Φ φ f) x ∂targetMeasure μ V Z)^2 ≤
      ((q-1)*q*(∫ x, ψ x ∂targetMeasure μ V Z)) *
        (∫ x, wEnergy ψ (wField Φ φ f) x ∂targetMeasure μ V Z) := by
  have h₁ (x : Space ι) : x ⬝ᵥ (hess ψ x *ᵥ x) = ((q-1)*q)*ψ x := by
    change (∑ i, x i*(∑ j, hess ψ x i j*x j)) = _
    simp_rw [hHessEuler]
    rw [show (∑ i, x i*((q-1)*pd i ψ x)) = (q-1)*(∑ i, x i*pd i ψ x) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring, hEuler]
    ring
  have h₂ (x : Space ι) : x ⬝ᵥ (hess ψ x *ᵥ (fun i => wField Φ φ f i x)) =
      (q-1)*(∑ i, pd i ψ x*wField Φ φ f i x) := by
    rw [form_symm (MomentEquation.hess_transpose hψ x)]
    change (∑ i, wField Φ φ f i x*(∑ j, hess ψ x i j*x j)) = _
    simp_rw [hHessEuler]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hg : Integrable (fun x => ∑ i, pd i ψ x*wField Φ φ f i x) (targetMeasure μ V Z) := by
    apply integrable_finsetSum
    intro i _
    exact ((smooth_pd hψ i).mul (smooth_target hInv (smooth_W hφ hf i))).continuous.integrable_of_hasCompactSupport
      ((compact_W hφ hf hfc Φ hΦ i).comp_homeomorph Φ.symm).mul_left
  have hc := integral_form_cs (targetMeasure μ V Z) (v:=fun x => x)
    (w:=fun x i => wField Φ φ f i x) hψpos
    (by simpa only [h₁] using hiψ.const_mul ((q-1)*q))
    (by simpa only [h₂] using hg.const_mul (q-1))
    (by simpa only [wEnergy_form] using second_energy_integrable μ hφ hf hfc hψ Φ hΦ hInv)
  simp_rw [h₁,h₂,wEnergy_form,integral_const_mul] at hc
  rw [← (pairings μ hφ hV hf hfc hψ (fun z => ne_of_gt (hpos z).det_pos) hZ heq Φ hΦ hInv).1] at hc
  simpa only [mul_pow] using hc

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

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
    have hh := MomentMatrix.form_nonneg hT (basis j-t • basis i)
    rw [MomentMatrix.form_quadratic hs] at hh
    simpa [basis, Matrix.mulVec, dotProduct, Pi.single_apply] using hh
  have hle := mul_le_mul (hd i) (hd j) (hT.diag_nonneg (i:=j)) hΛ
  apply (sq_le_sq₀ (abs_nonneg _) hΛ).mp
  rw [sq_abs]
  nlinarith

lemma smooth_tau {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (Φ : Space ι ≃ₜ Space ι) (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (i j : ι) :
    ContDiff ℝ ∞ (fun x => tau Φ φ x i j) := (smooth_hess hφ i j).comp hInv

lemma fderiv_tau_row (Φ : Space ι ≃ₜ Space ι) (φ g : Space ι → ℝ) (i : ι) (x : Space ι) :
    fderiv ℝ g x (fun j => tau Φ φ x i j) = ∑ j, pd j g x*tau Φ φ x i j :=
  linear_coordinates _ _

lemma compact_stein {φ V g : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hne : ∀ z, (hess φ z).det ≠ 0) {c Z : ℝ} (hZ : 0 < Z)
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (i : ι) :
    (∫ x, x i*g x ∂targetMeasure μ V Z) =
      ∫ x, fderiv ℝ g x (fun j => tau Φ φ x i j) ∂targetMeasure μ V Z := by
  have hdiv (x : Space ι) : divergence V basis (fun j y => tau Φ φ y i j) x = x i := by
    obtain ⟨z,rfl⟩ := Φ.surjective x
    rw [hΦ]
    exact stein hφ hV hne heq Φ hΦ hInv i z
  have hid : expectation μ V (fun x => x i*g x) =
      expectation μ V (fun x => fderiv ℝ g x (fun j => tau Φ φ x i j)) := by
    simp_rw [fderiv_tau_row]
    rw [expectation_sum μ hV _ (fun j => ((smooth_pd hg j).mul (smooth_tau hφ Φ hInv i j)).continuous)
      (fun j => (compact_D hgc (basis j)).mul_right)]
    have he (j : ι) : expectation μ V (fun x => pd j g x*tau Φ φ x i j) =
        expectation μ V (fun x => g x*adjoint V (basis j) (fun y => tau Φ φ y i j) x) :=
      integration_by_parts_rightcompact μ hV (smooth_tau hφ Φ hInv i j) hg hgc (basis j)
    have heSum := Finset.sum_congr (s₁:=Finset.univ) rfl (fun j _ => he j)
    rw [heSum]
    rw [← expectation_sum μ hV _ (fun j => (hg.mul (smooth_adjoint hV (smooth_tau hφ Φ hInv i j) (basis j))).continuous)
      (fun _ => hgc.mul_right)]
    congr 1
    funext x
    rw [← Finset.mul_sum]
    change x i*g x = g x*divergence V basis (fun j y => tau Φ φ y i j) x
    rw [hdiv]
    ring
  simp only [target_integral μ hV hZ, normalizedE, hid]

omit [Measure.IsAddHaarMeasure μ] in
lemma tau_hessian_integrable {φ V ψ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ z, (hess φ z).PosDef) {Z Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hupper : ∀ z, (Λ • (1 : Matrix ι ι ℝ)-hess φ z).PosSemidef)
    (Φ : Space ι ≃ₜ Space ι) (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hi : ∀ i j, Integrable (fun x => hess ψ x i j) (targetMeasure μ V Z)) (i j : ι) :
    Integrable (fun x => tau Φ φ x i j*hess ψ x i j) (targetMeasure μ V Z) := by
  apply (hi i j).bdd_mul (smooth_tau hφ Φ hInv i j).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs]
    exact entries_bound (hpos (Φ.symm x)).posSemidef hΛ (hupper (Φ.symm x)) i j)

lemma homogeneous_trace_moment {φ V ψ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hψ : ContDiff ℝ ∞ ψ)
    (hpos : ∀ z, (hess φ z).PosDef) {c Z q Λ : ℝ} (hZ : 0 < Z) (hΛ : 0 ≤ Λ)
    (hupper : ∀ z, (Λ • (1 : Matrix ι ι ℝ)-hess φ z).PosSemidef)
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hiD : ∀ i, Integrable (pd i ψ) (targetMeasure μ V Z))
    (hiXD : ∀ i, Integrable (fun x => x i*pd i ψ x) (targetMeasure μ V Z))
    (hiH : ∀ i j, Integrable (fun x => hess ψ x i j) (targetMeasure μ V Z))
    (hEuler : ∀ x, (∑ i, x i*pd i ψ x) = q*ψ x) :
    Integrable (fun x => (tau Φ φ x*hess ψ x).trace) (targetMeasure μ V Z) ∧
    (∫ x, (tau Φ φ x*hess ψ x).trace ∂targetMeasure μ V Z) = q*(∫ x, ψ x ∂targetMeasure μ V Z) := by
  have hi (i j : ι) := tau_hessian_integrable μ hφ hpos hΛ hupper Φ hInv hiH i j
  have htr (x : Space ι) : (tau Φ φ x*hess ψ x).trace = ∑ i, ∑ j, tau Φ φ x i j*hess ψ x i j := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hess_symm hψ x j i]
  have hd (i : ι) : (fun x => fderiv ℝ (pd i ψ) x (fun j => tau Φ φ x i j)) =
      fun x => ∑ j, tau Φ φ x i j*hess ψ x i j := by
    funext x
    rw [fderiv_tau_row]
    apply Finset.sum_congr rfl
    intro j _
    change pd j (pd i ψ) x*tau Φ φ x i j = tau Φ φ x i j*pd j (pd i ψ) x
    ring
  have hs (i : ι) : (∫ x, x i*pd i ψ x ∂targetMeasure μ V Z) =
      ∫ x, ∑ j, tau Φ φ x i j*hess ψ x i j ∂targetMeasure μ V Z := by
    rw [← hd]
    apply SteinExtension.extend (targetMeasure μ V Z) (continuous_apply i)
      (continuous_pi (fun j => (smooth_tau hφ Φ hInv i j).continuous))
    · intro x
      apply (pi_norm_le_iff_of_nonneg hΛ).mpr
      intro j
      rw [Real.norm_eq_abs]
      exact entries_bound (hpos (Φ.symm x)).posSemidef hΛ (hupper (Φ.symm x)) i j
    · intro g hg hgc
      exact compact_stein μ hφ hV hg hgc (fun z => ne_of_gt (hpos z).det_pos) hZ heq Φ hΦ hInv i
    · exact smooth_pd hψ i
    · exact hiD i
    · exact hiXD i
    · rw [hd]
      exact integrable_finsetSum _ (fun j _ => hi i j)
  refine ⟨?_, ?_⟩
  · simp_rw [htr]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
  · simp_rw [htr]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    simp_rw [← hs]
    rw [← integral_finsetSum _ (fun i _ => hiXD i)]
    simp_rw [hEuler,integral_const_mul]

end

variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

omit [DecidableEq ι] in
lemma trace_energy_subsum (M B H : Matrix ι ι ℝ) (Hs : κ → Matrix ι ι ℝ) :
    (M*B*(H-∑ i, Hs i)*B).trace = (M*B*H*B).trace-∑ i, (M*B*Hs i*B).trace := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.trace_sub, Matrix.trace_sum]

omit [DecidableEq ι] in
lemma form_subsum (v : ι → ℝ) (H : Matrix ι ι ℝ) (Hs : κ → Matrix ι ι ℝ) :
    v ⬝ᵥ ((H-∑ i, Hs i)*ᵥ v) = v ⬝ᵥ (H*ᵥ v)-∑ i, v ⬝ᵥ (Hs i*ᵥ v) := by
  simp only [Matrix.sub_mulVec, Matrix.sum_mulVec, dotProduct_sub, dotProduct_sum]

lemma discard_energy {φ V f : Space ι → ℝ} (ψ : κ → Space ι → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hpos : ∀ z, (hess φ z).PosDef)
    (hrem : ∀ x, (hess V x-∑ i, hess (ψ i) x).PosSemidef) {c Z : ℝ} (hZ : 0 < Z)
    [IsFiniteMeasure (targetMeasure μ V Z)]
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmap : Measure.map (grad φ) (sourceMeasure μ φ) = targetMeasure μ V Z) :
    (∑ i, ((∫ x, hEnergy Φ φ (ψ i) f x ∂targetMeasure μ V Z)+
      (∫ x, wEnergy (ψ i) (wField Φ φ f) x ∂targetMeasure μ V Z))) ≤
      ∫ x, (divergence V basis (wField Φ φ f) x)^2 ∂targetMeasure μ V Z := by
  have he₁ (i : κ) := first_energy_integrable μ hφ hf hfc (hψ i) hpos Φ hΦ hInv (V:=V) (Z:=Z)
  have he₂ (i : κ) := second_energy_integrable μ hφ hf hfc (hψ i) Φ hΦ hInv (V:=V) (Z:=Z)
  have heV₁ := first_energy_integrable μ hφ hf hfc hV hpos Φ hΦ hInv (V:=V) (Z:=Z)
  have heV₂ := second_energy_integrable μ hφ hf hfc hV Φ hΦ hInv (V:=V) (Z:=Z)
  have hp₁ (x : Space ι) : (∑ i, hEnergy Φ φ (ψ i) f x) ≤ hEnergy Φ φ V f x := by
    have hp := trace_energy_nonneg ((hpos (Φ.symm x)).inv.posSemidef) (hrem x) (bField_symm hφ hf Φ x)
    rw [trace_energy_subsum] at hp
    exact sub_nonneg.mp hp
  have hp₂ (x : Space ι) : (∑ i, wEnergy (ψ i) (wField Φ φ f) x) ≤ wEnergy V (wField Φ φ f) x := by
    have hp := form_nonneg (hrem x) (fun j => wField Φ φ f j x)
    rw [form_subsum] at hp
    simp_rw [wEnergy_form] at hp
    exact sub_nonneg.mp hp
  have h₁ := integral_mono (integrable_finsetSum _ (fun i _ => he₁ i)) heV₁ hp₁
  have h₂ := integral_mono (integrable_finsetSum _ (fun i _ => he₂ i)) heV₂ hp₂
  rw [integral_finsetSum _ (fun i _ => he₁ i)] at h₁
  rw [integral_finsetSum _ (fun i _ => he₂ i)] at h₂
  have ht := (tensor_energy μ hφ hV hf hfc hpos hZ heq Φ hΦ hInv hmap).2
  simp_rw [← target_integral μ hV hZ] at ht
  rw [Finset.sum_add_distrib]
  linarith

end DualEnergy

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

lemma pd_summand (p : ι → ℝ) (h : ℝ) (q : ℕ) (i : ι) :
    pd i (summand p h q) = fun x => (q : ℝ) * (linear p x / h)^(q-1) * (p i / h) := by
  funext x
  have hd : HasFDerivAt (summand p h q)
      (((q : ℝ) * (linear p x / h)^(q-1)) • (h⁻¹ • linear p)) x := by
    unfold summand
    simpa only [div_eq_mul_inv, nsmul_eq_mul] using (((linear p).hasFDerivAt (x := x)).mul_const h⁻¹).pow q
  change fderiv ℝ (summand p h q) x (basis i) = _
  rw [hd.fderiv]
  simp [linear_basis, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma hess_summand (p : ι → ℝ) (h : ℝ) (q : ℕ) (x : Space ι) (i j : ι) :
    hess (summand p h (q+2)) x i j =
      ((q+2 : ℕ) : ℝ) * ((q+1 : ℕ) : ℝ) * (linear p x / h)^q * (p i/h) * (p j/h) := by
  change pd j (pd i (summand p h (q+2))) x = _
  rw [pd_summand]
  simp only [show q+2-1=q+1 by omega]
  have hbase : HasFDerivAt (fun y => (linear p y / h)^(q+1))
      ((((q+1 : ℕ) : ℝ) * (linear p x / h)^q) • (h⁻¹ • linear p)) x := by
    simpa only [div_eq_mul_inv, Nat.add_sub_cancel, nsmul_eq_mul] using
      (((linear p).hasFDerivAt (x := x)).mul_const h⁻¹).pow (q+1)
  have hd := hbase.const_mul (((q+2 : ℕ) : ℝ))
  have hd' := hd.mul_const (p i / h)
  change fderiv ℝ (fun y => ((q+2 : ℕ) : ℝ) * (linear p y / h)^(q+1) * (p i / h)) x (basis j) = _
  rw [hd'.fderiv]
  simp [linear_basis, smul_eq_mul, div_eq_mul_inv]
  ring

omit [DecidableEq ι] in
lemma summand_nonneg {q : ℕ} (hq : Even q) (p : ι → ℝ) (h : ℝ) (x : Space ι) :
    0 ≤ summand p h q x := hq.pow_nonneg _

lemma hess_summand_posSemidef {q : ℕ} (hq : Even q) (p : ι → ℝ) (h : ℝ) (x : Space ι) :
    (hess (summand p h (q+2)) x).PosSemidef := by
  let c : ℝ := ((q+2 : ℕ) : ℝ) * ((q+1 : ℕ) : ℝ) * (linear p x / h)^q
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg (by positivity) (by positivity)) (hq.pow_nonneg _)
  have he : hess (summand p h (q+2)) x = c • Matrix.vecMulVec (fun i => p i/h) (fun i => p i/h) := by
    ext i j
    rw [hess_summand]
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, c]
    ring
  rw [he]
  apply Matrix.PosSemidef.smul _ hc
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (fun i => p i/h)

lemma euler_summand (p : ι → ℝ) (h : ℝ) (q : ℕ) (x : Space ι) :
    (∑ i, x i * pd i (summand p h (q+1)) x) = ((q+1 : ℕ) : ℝ) * summand p h (q+1) x := by
  simp only [pd_summand, Nat.add_sub_cancel, summand]
  have he : (∑ i, x i * (((q+1 : ℕ) : ℝ) * (linear p x / h)^q * (p i/h))) =
      (((q+1 : ℕ) : ℝ) * (linear p x / h)^q) * (linear p x / h) := by
    rw [linear_apply, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, pow_succ]
  ring

lemma hessian_euler (p : ι → ℝ) (h : ℝ) (q : ℕ) (x : Space ι) (i : ι) :
    (∑ j, hess (summand p h (q+2)) x i j * x j) =
      ((q+1 : ℕ) : ℝ) * pd i (summand p h (q+2)) x := by
  simp only [hess_summand, pd_summand, show q+2-1=q+1 by omega]
  have he : (∑ j, (((q+2 : ℕ) : ℝ) * ((q+1 : ℕ) : ℝ) * (linear p x / h)^q *
      (p i/h) * (p j/h)) * x j) =
      (((q+2 : ℕ) : ℝ) * ((q+1 : ℕ) : ℝ) * (linear p x / h)^q * (p i/h)) * (linear p x / h) := by
    rw [linear_apply, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, pow_succ]
  ring

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
lemma potential_lower {q : ℕ} (hq : Even q) (ε : ℝ) (p : κ → ι → ℝ) (h : κ → ℝ) (x : Space ι) :
    ε/2*(∑ j, x j^2) ≤ potential ε p h q x := by
  unfold potential
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => summand_nonneg hq (p i) (h i) x))

lemma pd_quadratic (ε : ℝ) (i : ι) :
    pd i (fun x : Space ι => ε/2*(∑ j, x j^2)) = fun x => ε*x i := by
  funext x
  have hj (j : ι) : HasFDerivAt (fun x : Space ι => x j^2)
      ((2*x j) • (ContinuousLinearMap.proj j : Space ι →L[ℝ] ℝ)) x := by
    simpa using
      ((ContinuousLinearMap.proj j : Space ι →L[ℝ] ℝ).hasFDerivAt (x:=x) |>.pow 2)
  have hd := (HasFDerivAt.sum (u:=Finset.univ) (fun j _ => hj j)).const_mul (ε/2)
  have hd' : HasFDerivAt (fun x : Space ι => ε/2*(∑ j, x j^2))
      ((ε/2) • ∑ j, (2*x j) • (ContinuousLinearMap.proj j : Space ι →L[ℝ] ℝ)) x := by
    simpa only [Finset.sum_apply] using hd
  change fderiv ℝ (fun x : Space ι => ε/2*(∑ j, x j^2)) x (basis i) = _
  rw [hd'.fderiv]
  simp [basis, Pi.single_apply]
  ring

lemma hess_quadratic (ε : ℝ) (x : Space ι) :
    hess (fun x : Space ι => ε/2*(∑ j, x j^2)) x = ε • (1 : Matrix ι ι ℝ) := by
  ext i j
  change pd j (pd i (fun x : Space ι => ε/2*(∑ k, x k^2))) x = _
  rw [pd_quadratic]
  change fderiv ℝ (ε • (ContinuousLinearMap.proj i : Space ι →L[ℝ] ℝ)) x (basis j) = _
  rw [ContinuousLinearMap.fderiv]
  simp [basis, Pi.single_apply, Matrix.one_apply]

lemma hess_add {f g : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Space ι) :
    hess (fun y => f y+g y) x = hess f x+hess g x := by
  ext i j
  change D (basis j) (D (basis i) (fun y => f y+g y)) x = _
  rw [D_add (hf.differentiable (by simp)) (hg.differentiable (by simp)),
    D_add ((smooth_D hf _).differentiable (by simp)) ((smooth_D hg _).differentiable (by simp))]
  rfl

lemma hess_sum (f : κ → Space ι → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (x : Space ι) :
    hess (fun y => ∑ i, f i y) x = ∑ i, hess (f i) x := by
  ext j k
  change D (basis k) (D (basis j) (fun y => ∑ i, f i y)) x = _
  rw [D_sum _ (fun i => (hf i).differentiable (by simp)),
    D_sum _ (fun i => (smooth_D (hf i) _).differentiable (by simp))]
  simp only [Matrix.sum_apply]
  rfl

lemma hess_potential (ε : ℝ) (p : κ → ι → ℝ) (h : κ → ℝ) (q : ℕ) (x : Space ι) :
    hess (potential ε p h q) x = ε • (1 : Matrix ι ι ℝ) + ∑ i, hess (summand (p i) (h i) q) x := by
  unfold potential
  rw [hess_add, hess_quadratic, hess_sum]
  · exact fun i => smooth_summand (p i) (h i) q
  · exact contDiff_const.mul (ContDiff.sum (fun j _ => (contDiff_apply ℝ ℝ j).pow 2))
  · exact ContDiff.sum (fun i _ => smooth_summand (p i) (h i) q)


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

lemma integrable_pd_summand {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (v : ι → ℝ) (r : ℝ) (m : ℕ) (j : ι) :
    Integrable (pd j (summand v r m)) (law ε p h q) := by
  rw [pd_summand]
  exact ((integrable_summand hq hε p h v r (m-1)).const_mul (m:ℝ)).mul_const (v j/r)

lemma integrable_x_pd_summand {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (v : ι → ℝ) (r : ℝ) (m : ℕ) (j : ι) :
    Integrable (fun x => x j*pd j (summand v r m) x) (law ε p h q) := by
  let P : MvPolynomial ι ℝ := MvPolynomial.X j *
    (MvPolynomial.C (m:ℝ)*(linearPolynomial v r)^(m-1)*MvPolynomial.C (v j/r))
  have he (x : Space ι) : MvPolynomial.eval x P = x j*pd j (summand v r m) x := by
    rw [pd_summand]
    simp only [P, MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_C,
      MvPolynomial.eval_X, eval_linearPolynomial]
  have hi := polynomial_moment hq hε p h P
  simpa only [he] using hi

lemma integrable_hess_summand {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (v : ι → ℝ) (r : ℝ) (m : ℕ) (j k : ι) :
    Integrable (fun x => hess (summand v r (m+2)) x j k) (law ε p h q) := by
  simp_rw [hess_summand]
  exact (((integrable_summand hq hε p h v r m).const_mul
    (((m+2:ℕ):ℝ)*((m+1:ℕ):ℝ))).mul_const (v j/r)).mul_const (v k/r)

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

theorem combine_energies (q E : ℝ) (a d e₁ e₂ : ι → ℝ)
    (hq : 1 < q) (ha : ∀ i, 0 < a i)
    (h₁ : ∀ i, d i ^ 2 ≤ (q * a i) * e₁ i)
    (h₂ : ∀ i, (q-1)^2 * d i^2 ≤ ((q-1) * (q*a i)) * e₂ i)
    (hE : ∑ i, (e₁ i + e₂ i) ≤ E) :
    ∑ i, d i^2 / a i ≤ E := by
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) hE
  have hq0 : 0 < q := by linarith
  have hm : 0 < q*a i := mul_pos hq0 (ha i)
  have hqm : 0 < q-1 := by linarith
  have he₁ : d i^2 / (q*a i) ≤ e₁ i := (div_le_iff₀ hm).mpr (by nlinarith [h₁ i])
  have he₂ : (q-1)*d i^2 / (q*a i) ≤ e₂ i := by
    apply (div_le_iff₀ hm).mpr
    have hh := h₂ i
    have ht : (q-1)*((q-1)*d i^2) ≤ (q-1)*((q*a i)*e₂ i) := by nlinarith [hh]
    exact le_of_mul_le_mul_left (by simpa only [mul_comm (e₂ i) (q * a i)] using ht) hqm
  calc
    d i^2 / a i = d i^2 / (q*a i) + (q-1)*d i^2 / (q*a i) := by
      field_simp
      ring
    _ ≤ e₁ i + e₂ i := add_le_add he₁ he₂

end VarianceDuality

namespace DualEnergy
open MeasureTheory Matrix WeightedCalculus MomentCoordinates MomentDifferential MomentEquation
  IntegratedTensor TargetCoordinates FullTensor MomentMatrix TensorEstimate
open scoped BigOperators ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

lemma compact_dual_generic {φ V f : Space ι → ℝ} (ψ : κ → Space ι → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hpos : ∀ z, (hess φ z).PosDef) (hψpos : ∀ i x, (hess (ψ i) x).PosSemidef)
    {c Z q : ℝ} (hZ : 0 < Z) [IsFiniteMeasure (targetMeasure μ V Z)] (hq : 1 < q)
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmap : Measure.map (grad φ) (sourceMeasure μ φ) = targetMeasure μ V Z)
    (hiψ : ∀ i, Integrable (ψ i) (targetMeasure μ V Z))
    (hmean : ∀ i, 0 < ∫ x, ψ i x ∂targetMeasure μ V Z)
    (hEuler : ∀ i x, (∑ j, x j*pd j (ψ i) x) = q*ψ i x)
    (hHessEuler : ∀ i x j, (∑ k, hess (ψ i) x j k*x k) = (q-1)*pd j (ψ i) x)
    (hmi : ∀ i, Integrable (fun x => (tau Φ φ x*hess (ψ i) x).trace) (targetMeasure μ V Z))
    (hm : ∀ i, (∫ x, (tau Φ φ x*hess (ψ i) x).trace ∂targetMeasure μ V Z) =
      q*(∫ x, ψ i x ∂targetMeasure μ V Z))
    (hrem : ∀ x, (hess V x-∑ i, hess (ψ i) x).PosSemidef) :
    (∑ i, (∫ x, ψ i x*divergence V basis (wField Φ φ f) x ∂targetMeasure μ V Z)^2 /
      (∫ x, ψ i x ∂targetMeasure μ V Z)) ≤
      ∫ x, (divergence V basis (wField Φ φ f) x)^2 ∂targetMeasure μ V Z := by
  apply VarianceDuality.combine_energies
    (e₁:=fun i => ∫ x, hEnergy Φ φ (ψ i) f x ∂targetMeasure μ V Z)
    (e₂:=fun i => ∫ x, wEnergy (ψ i) (wField Φ φ f) x ∂targetMeasure μ V Z) q
  · exact hq
  · exact hmean
  · intro i
    have hc := first_cs μ hφ hV hf hfc (hψ i) hpos (hψpos i) hZ heq Φ hΦ hInv (hmi i)
    rw [hm i] at hc
    exact hc
  · intro i
    have hc := second_cs μ hφ hV hf hfc (hψ i) hpos (hψpos i) hZ heq Φ hΦ hInv
      (hiψ i) (hEuler i) (hHessEuler i)
    simpa only [mul_assoc] using hc
  · exact discard_energy μ ψ hφ hV hf hfc hψ hpos hrem hZ heq Φ hΦ hInv hmap

end DualEnergy

namespace MomentSlab
open MeasureTheory WeightedCalculus MomentCoordinates MomentDifferential MomentEquation
  IntegratedTensor TargetCoordinates FullTensor MomentMatrix TensorEstimate DualEnergy SoftSlab
open scoped BigOperators ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem summand_trace_moment {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ)
    {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ z, (hess φ z).PosDef)
    (hupper : ∀ z, ((4/ε) • (1 : Matrix ι ι ℝ)-hess φ z).PosSemidef)
    (heq : ∀ z, Real.log (hess φ z).det = potential ε p h (q+2) (grad φ z)+
      Real.log (∫ x, Real.exp (-potential ε p h (q+2) x))-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (i : κ) :
    Integrable (fun x => (tau Φ φ x*hess (summand (p i) (h i) (q+2)) x).trace) (law ε p h (q+2)) ∧
      (∫ x, (tau Φ φ x*hess (summand (p i) (h i) (q+2)) x).trace ∂law ε p h (q+2)) =
        ((q+2:ℕ):ℝ)*(∫ x, summand (p i) (h i) (q+2) x ∂law ε p h (q+2)) := by
  have hqe : Even (q+2) := hq.add even_two
  let : IsProbabilityMeasure (law ε p h (q+2)) := potential_probability hqe hε p h
  apply homogeneous_trace_moment volume hφ (smooth_potential ε p h (q+2))
    (smooth_summand (p i) (h i) (q+2)) hpos (potential_partition_pos hqe hε p h)
    (div_nonneg (by norm_num) hε.le) hupper heq Φ hΦ hInv
  · exact fun j => integrable_pd_summand hqe hε p h (p i) (h i) (q+2) j
  · exact fun j => integrable_x_pd_summand hqe hε p h (p i) (h i) (q+2) j
  · exact fun j k => integrable_hess_summand hqe hε p h (p i) (h i) q j k
  · exact euler_summand (p i) (h i) (q+1)

theorem compact_dual_bound {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (hp : ∀ i, p i ≠ 0) (hh : ∀ i, 0 < h i)
    {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hpos : ∀ z, (hess φ z).PosDef)
    (hupper : ∀ z, ((4/ε) • (1 : Matrix ι ι ℝ)-hess φ z).PosSemidef)
    (heq : ∀ z, Real.log (hess φ z).det = potential ε p h (q+2) (grad φ z)+
      Real.log (∫ x, Real.exp (-potential ε p h (q+2) x))-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmap : Measure.map (grad φ) (sourceMeasure volume φ) = law ε p h (q+2)) :
    (∑ i, (∫ x, summand (p i) (h i) (q+2) x *
        divergence (potential ε p h (q+2)) basis (wField Φ φ f) x ∂law ε p h (q+2))^2 /
      (∫ x, summand (p i) (h i) (q+2) x ∂law ε p h (q+2))) ≤
      ∫ x, (divergence (potential ε p h (q+2)) basis (wField Φ φ f) x)^2 ∂law ε p h (q+2) := by
  let V := potential ε p h (q+2)
  let Z := ∫ x, Real.exp (-V x)
  let ψ (i : κ) := summand (p i) (h i) (q+2)
  have hqe : Even (q+2) := hq.add even_two
  have hV : ContDiff ℝ ∞ V := smooth_potential ε p h (q+2)
  have hZ : 0 < Z := potential_partition_pos hqe hε p h
  have hψ (i : κ) : ContDiff ℝ ∞ (ψ i) := smooth_summand (p i) (h i) (q+2)
  have hψpos (i : κ) (x : Space ι) : (hess (ψ i) x).PosSemidef := hess_summand_posSemidef hq (p i) (h i) x
  let : IsProbabilityMeasure (targetMeasure volume V Z) := potential_probability hqe hε p h
  have hhom (i : κ) (x : Space ι) : (∑ j, x j*pd j (ψ i) x) = ((q+2:ℕ):ℝ)*ψ i x :=
    euler_summand (p i) (h i) (q+1) x
  have hhom₂ (i : κ) (x : Space ι) (j : ι) :
      (∑ k, hess (ψ i) x j k*x k) = (((q+2:ℕ):ℝ)-1)*pd j (ψ i) x :=
    by
      have he : (((q+2:ℕ):ℝ)-1) = ((q+1:ℕ):ℝ) := by push_cast; ring
      rw [he]
      exact hessian_euler (p i) (h i) q x j
  have hm (i : κ) := summand_trace_moment hq hε p h hφ hpos hupper heq Φ hΦ hInv i
  apply compact_dual_generic (q := ((q+2 : ℕ) : ℝ)) (φ := φ) (V := V) (f := f)
    (Z := Z) (c := Real.log Z) volume ψ hφ hV hf hfc hψ hpos hψpos hZ
    (by exact_mod_cast (show 1 < q+2 by omega)) heq Φ hΦ hInv hmap
  · exact fun i => integrable_summand hqe hε p h (p i) (h i) (q+2)
  · exact fun i => mean_summand_pos hqe hε p h (hp i) (ne_of_gt (hh i)) hqe
  · exact hhom
  · exact hhom₂
  · exact fun i => (hm i).1
  · exact fun i => (hm i).2
  · intro x
    change (hess (potential ε p h (q+2)) x-∑ i, hess (ψ i) x).PosSemidef
    rw [hess_potential]
    change (ε • (1 : Matrix ι ι ℝ)+(∑ i, hess (ψ i) x)-(∑ i, hess (ψ i) x)).PosSemidef
    rw [add_sub_cancel_right]
    exact Matrix.PosSemidef.one.smul hε.le

end MomentSlab

namespace MomentSlab
open MeasureTheory WeightedCalculus MomentCoordinates TargetCoordinates SoftSlab FullTensor
open scoped ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

lemma square_double_divergence {φ V f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (hne : ∀ z, (hess φ z).det ≠ 0) {c : ℝ}
    (heq : ∀ z, Real.log (hess φ z).det = V (grad φ z)+c-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) :
    RealSmoothOperator.operator (MatrixOperator.principal (MomentOperator.tau Φ φ)
      (MomentKernel.smooth_tau hφ Φ hInv)++MatrixOperator.drift)
      (RealSmoothOperator.operator (MatrixOperator.principal (MomentOperator.tau Φ φ)
        (MomentKernel.smooth_tau hφ Φ hInv)++MatrixOperator.drift) f-f) =
      divergence V basis (wField Φ φ f) := by
  rw [MatrixOperator.operator_actual,MatrixOperator.operator_actual,
    MomentKernel.matrix_A_eq,MomentKernel.matrix_A_eq,← MomentKernel.A_eq_density (φ:=φ) hf Φ]
  change DensityEnergy.A (MomentOperator.tau Φ φ) (fun x => MomentOperator.A Φ φ f x-f x) = _
  rw [← MomentKernel.A_eq_density (φ:=φ) ((MomentOperator.smooth_A hφ hf Φ hΦ hInv).sub hf) Φ]
  exact (MomentOperator.double_divergence hφ hV hf hne heq Φ hΦ hInv).symm

lemma range_dual_bound_oai {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (hp : ∀ i, p i ≠ 0) (hh : ∀ i, 0 < h i)
    {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ z, (hess φ z).PosDef)
    (hupper : ∀ z, ((4/ε) • (1 : Matrix ι ι ℝ)-hess φ z).PosSemidef)
    (heq : ∀ z, Real.log (hess φ z).det = potential ε p h (q+2) (grad φ z)+
      Real.log (∫ x, Real.exp (-potential ε p h (q+2) x))-φ z)
    (Φ : Space ι ≃ₜ Space ι) (hΦ : (Φ : Space ι → Space ι) = grad φ)
    (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    (hmap : Measure.map (grad φ) (sourceMeasure volume φ) = law ε p h (q+2))
    [IsFiniteMeasureOnCompacts (law ε p h (q+2))]
    (u : Lp ℝ 2 (law ε p h (q+2)))
    (hu : u ∈ RealSmoothOperator.squareRange (E:=Space ι) (law ε p h (q+2))
      (MatrixOperator.principal (MomentOperator.tau Φ φ) (MomentKernel.smooth_tau hφ Φ hInv)++
        MatrixOperator.drift)) :
    (∑ i, (∫ x, u x*summand (p i) (h i) (q+2) x ∂law ε p h (q+2))^2 /
      (∫ x, summand (p i) (h i) (q+2) x ∂law ε p h (q+2))) ≤
      ∫ x, (u x)^2 ∂law ε p h (q+2) := by
  obtain ⟨f,rfl⟩ := hu
  have hae := RealSmoothOperator.squareLp_coe (E:=Space ι) (law ε p h (q+2))
    (MatrixOperator.principal (MomentOperator.tau Φ φ) (MomentKernel.smooth_tau hφ Φ hInv)++
        MatrixOperator.drift) f
  rw [square_double_divergence hφ (smooth_potential ε p h (q+2))
    (RealSmoothOperator.tests_smooth f) (fun z => (hpos z).det_pos.ne') heq Φ hΦ hInv] at hae
  have hd := compact_dual_bound hq hε p h hp hh hφ (RealSmoothOperator.tests_smooth f)
    (RealSmoothOperator.tests_compact f) hpos hupper heq Φ hΦ hInv hmap
  convert hd using 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 2
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx,mul_comm]
  · apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]

end MomentSlab
end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MomentSlab.range_dual_bound_oai.{u_1, u_2} := @OAI.MomentSlab.range_dual_bound_oai.{u_1, u_2}

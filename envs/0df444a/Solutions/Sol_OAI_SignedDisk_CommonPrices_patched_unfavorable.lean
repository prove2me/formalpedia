-- Prove2me | solution 1 for OAI.SignedDisk.CommonPrices.patched_unfavorable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:36:14.897411+00:00
-- url     : https://prove2.me/submissions/340fd22f-ed11-4593-8012-66d71cdc89ef

import Mathlib
import Definitions.Def_OAIW2SD000
import Theorems.Thm_OAI_SignedDisk_LocalCancellation_direction_majorant

section
-- module Solutions.OAIW2_SignedDisk.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskGeometry2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace

noncomputable section

namespace SignedDisk

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff

namespace DiskMoments

lemma integral_translate_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (x : ℂ) (r : ℝ) :
    (∫ z in Metric.ball 0 r, f (x + z)) = ∫ y in Metric.ball x r, f y := by
  have hpre : (fun z : ℂ => x + z) ⁻¹' Metric.ball x r = Metric.ball 0 r := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  have h := (measurePreserving_add_left volume x).setIntegral_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding f (Metric.ball x r)
  rwa [hpre] at h

lemma integral_scale_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) {t : ℝ} (ht : 0 < t) :
    (∫ z in Metric.ball (0 : ℂ) 1, f (t • z)) =
      (t^2)⁻¹ • ∫ z in Metric.ball (0 : ℂ) t, f z := by
  convert Measure.setIntegral_comp_smul_of_pos volume f (Metric.ball 0 1) ht using 1
  rw [Complex.finrank_real_complex, smul_ball ht.ne', smul_zero, Real.norm_eq_abs, abs_of_pos ht, mul_one]

lemma signedAverage_fixedDomain (g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    signedAverage g x t = (∫ z in Metric.ball (0 : ℂ) 1, g (x + t • z)) / Real.pi := by
  rw [integral_scale_ball (fun z => g (x+z)) ht, integral_translate_ball]
  simp only [signedAverage, smul_eq_mul]
  ring

end DiskMoments

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskMaximalTools1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ScalarCancellation

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {ι : Type*} [Fintype ι]

lemma roots_abs_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, |roots μ w f k q x| ∂μ) = |∫ x, refined w f k q x ∂μ| := by
  cases k with
  | zero => exact (root_spec (hf q)).2.2.1
  | succ k =>
    have hs := root_spec (integrable_finsetSum Finset.univ
      (fun s _ => (roots_integrable w hf k s).const_mul (w k q s)))
    change (∫ x, |root μ _ x| ∂μ) = _
    rw [hs.2.2.1,← hs.2.1]
    exact congrArg abs (roots_mass w hf (k+1) q)

/-- The whole scalar cancellation tree is built by backward splitting. Each
nonterminal zero-mass piece costs at most its positive refinement norm defect. -/
theorem errors_cost (w : ℕ → ι → ι → ℝ) (hw : ∀ k q s, 0 ≤ w k q s)
    {f : ι → α → ℝ} (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, |errors μ w f (k+1) q x| ∂μ) ≤
      (∑ s, w k q s*|∫ x, refined w f k s x ∂μ|)-|∫ x, refined w f (k+1) q x ∂μ| := by
  have hi : Integrable (fun x => ∑ s, w k q s*roots μ w f k s x) μ :=
    integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _)
  have hs := root_spec hi
  change (∫ x, |(∑ s, w k q s*roots μ w f k s x)-root μ _ x| ∂μ) ≤ _
  rw [hs.2.2.2.1]
  have hm : (∫ x, ∑ s, w k q s*roots μ w f k s x ∂μ) = ∫ x, refined w f (k+1) q x ∂μ := by
    rw [← hs.2.1]
    exact roots_mass w hf (k+1) q
  rw [hm]
  apply sub_le_sub_right
  calc
    _ ≤ ∫ x, ∑ s, w k q s*|roots μ w f k s x| ∂μ := by
      apply integral_mono hi.abs (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).abs.const_mul _))
      intro x
      calc
        _ ≤ ∑ s, |w k q s*roots μ w f k s x| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp_rw [abs_mul,abs_of_nonneg (hw k q _)]
    _ = _ := by
      rw [integral_finsetSum _ (fun s _ => (roots_integrable w hf k s).abs.const_mul _)]
      simp_rw [integral_const_mul,roots_abs_mass w hf]

lemma errors_terminal_cost (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (q : ι) :
    (∫ x, |errors μ w f 0 q x| ∂μ) = (∫ x, |f q x| ∂μ)-|∫ x, f q x ∂μ| :=
  (root_spec (hf q)).2.2.2.1

end ScalarCancellation

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_ScalarCancellation1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal

noncomputable section

namespace SignedDisk

namespace ScalarCancellation
open Finset
variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]

/-- Exact expansion in a coherent family of refinement coefficients. The
finite zero-mass pieces are the explicitly constructed `errors`, not merely
scalar mass certificates. -/
theorem telescoped_decomposition [DecidableEq ι] (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ)
    (Λ : ℕ → ℕ → ι → ι → ℝ)
    (hdiag : ∀ k q s, Λ k k q s = if q = s then 1 else 0)
    (hstep : ∀ k j q s, j ≤ k → Λ (k+1) j q s = ∑ a, w k q a*Λ k j a s)
    (k : ℕ) (q : ι) (x : α) :
    refined w f k q x = roots μ w f k q x +
      ∑ j ∈ range (k+1), ∑ s, Λ k j q s*errors μ w f j s x := by
  classical
  induction k generalizing q with
  | zero =>
    simp only [Nat.zero_add,Finset.range_one,sum_singleton,hdiag,ite_mul,one_mul,zero_mul]
    rw [sum_ite_eq univ q]
    simp only [Finset.mem_univ,ite_true,errors,refined]
    ring
  | succ k ih =>
    rw [sum_range_succ]
    have hlast : (∑ s, Λ (k+1) (k+1) q s*errors μ w f (k+1) s x) = errors μ w f (k+1) q x := by
      simp only [hdiag,ite_mul,one_mul,zero_mul]
      simp
    rw [hlast,errors,refined]
    simp_rw [ih]
    simp only [mul_add,sum_add_distrib]
    have hsum : (∑ a, w k q a*(∑ j ∈ range (k+1), ∑ s, Λ k j a s*errors μ w f j s x)) =
        ∑ j ∈ range (k+1), ∑ s, Λ (k+1) j q s*errors μ w f j s x := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      rw [hstep k j q s (Nat.le_of_lt_succ (mem_range.mp hj)),sum_mul]
      apply sum_congr rfl
      intro a _
      ring
    rw [hsum]
    ring

end ScalarCancellation

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace DyadicHats

lemma step_column (q : ℤ × ℤ) : (∑' p : ℤ × ℤ, step p q) = 1 := by
  calc
    _ = ∑' p, hat 1 p (((q.1:ℝ)/2 : ℂ)+((q.2:ℝ)/2 : ℂ)*Complex.I) := by
      apply tsum_congr
      intro p
      simp [step,hat]
    _ = 1 := tsum_hat _ _

end DyadicHats

open MeasureTheory Set Metric
open scoped ENNReal NNReal

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_PlanePotential1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal

open Finset
open scoped RealInnerProductSpace

namespace FiniteLabels
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma law_le_one (μ : Law ι) (i : ι) : μ i ≤ 1 := by
  rw [← μ.total]
  exact single_le_sum (fun j _ => μ.nonneg j) (mem_univ i)

lemma move_apply (μ : Law ι) (P : ι → Law κ) (j : κ) :
    move μ P j = ∑ i, μ i*P i j := rfl

end FiniteLabels

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_VectorRefinement1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace VectorRefinement

/-- Exact quadratic defect of a positive vector refinement, including zero parent mass. -/
theorem quadratic_defect {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w a : ι → ℝ) (θ : ι → E) (n : E) (A : ℝ)
    (hn : ‖n‖ = 1) (hθ : ∀ i, ‖θ i‖ = 1)
    (href : A • n = ∑ i, (w i*a i) • θ i) :
    (∑ i, w i*a i)-A = (1/2:ℝ)*∑ i, w i*a i*‖θ i-n‖^2 := by
  have hinner : A = ∑ i, w i*a i*⟪θ i,n⟫ := by
    have h := congrArg (fun v : E => ⟪v,n⟫) href
    simpa only [real_inner_smul_left,sum_inner,real_inner_self_eq_norm_sq,hn,one_pow,mul_one] using h
  rw [hinner,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_sub_sq_real,hθ i,hn]
  ring

lemma sq_norm_triangle {E : Type*} [SeminormedAddCommGroup E] (x y z : E) :
    ‖x-z‖^2 ≤ 2*(‖x-y‖^2+‖z-y‖^2) := by
  have h := norm_sub_le_norm_sub_add_norm_sub x y z
  rw [norm_sub_rev y z] at h
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h
  nlinarith [sq_nonneg (‖x-y‖-‖z-y‖)]

/-- Two sufficiently represented children cannot have a large angular disagreement
without spending the actual parent's triangle defect. -/
theorem pair_defect_bound {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w a : ι → ℝ) (θ : ι → E) (n : E) (A : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i)
    (hn : ‖n‖ = 1) (hθ : ∀ i, ‖θ i‖ = 1)
    (href : A • n = ∑ i, (w i*a i) • θ i)
    {q s : ι} (hwaq : 1/4 ≤ w q) (hwas : 9/64 ≤ w s) (has : a q ≤ a s) :
    a q*‖θ q-θ s‖^2 ≤ 48*((∑ i, w i*a i)-A) := by
  let D := (∑ i, w i*a i)-A
  have hD := quadratic_defect w a θ n A hn hθ href
  have hi (i : ι) : w i*a i*‖θ i-n‖^2 ≤ 2*D := by
    have hs : w i*a i*‖θ i-n‖^2 ≤ ∑ j, w j*a j*‖θ j-n‖^2 :=
      Finset.single_le_sum (fun j _ => mul_nonneg (mul_nonneg (hw j) (ha j)) (sq_nonneg ‖θ j-n‖)) (Finset.mem_univ i)
    dsimp [D]
    linarith
  have hD0 : 0 ≤ D := by
    have hs : 0 ≤ ∑ i, w i*a i*‖θ i-n‖^2 := Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (hw i) (ha i)) (sq_nonneg _)
    dsimp [D]; linarith
  have hq : a q*‖θ q-n‖^2 ≤ 8*D := by
    have hm := mul_le_mul_of_nonneg_right hwaq (mul_nonneg (ha q) (sq_nonneg ‖θ q-n‖))
    nlinarith [hi q]
  have hs : a q*‖θ s-n‖^2 ≤ (128/9:ℝ)*D := by
    have hm := mul_le_mul_of_nonneg_right hwas (mul_nonneg (ha s) (sq_nonneg ‖θ s-n‖))
    have hmas := mul_le_mul_of_nonneg_right has (sq_nonneg ‖θ s-n‖)
    nlinarith [hi s]
  have ht := mul_le_mul_of_nonneg_left (sq_norm_triangle (θ q) n (θ s)) (ha q)
  change _ ≤ 48*D
  nlinarith

end VectorRefinement

open MeasureTheory Set
open scoped ENNReal NNReal Topology

open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

open scoped RealInnerProductSpace

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LabelSwitches1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff

noncomputable section

namespace SignedDisk

open Finset

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace DiskMoments

lemma hasFDerivAt_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasFDerivAt (fun x => signedAverage g x t)
      ((1/Real.pi) • ∫ z in Metric.ball 0 1, fderiv ℝ g (x+t • z)) x := by
  let F : ℂ → ℂ → ℝ := fun x z => g (x+t • z)
  have hFi : IntegrableOn (F x) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1)
      (hg.continuous.comp (by fun_prop)).continuousOn).mono_set Metric.ball_subset_closedBall
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Metric.ball (0:ℂ) 1)) (F := F)
    (F' := fun x z => fderiv ℝ g (x+t • z)) (bound := fun _ => D)
    (s := univ) (x₀ := x) univ_mem
    (Eventually.of_forall (fun x => (hg.continuous.comp (by fun_prop)).aestronglyMeasurable))
    hFi ((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ (fun z x _ => hD (x+t • z))) (integrableOn_const (by finiteness))
    (ae_of_all _ (fun z x _ => by
      simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq,F] using
        (hg.differentiable one_ne_zero (x+t • z)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (t • z))))
  convert! hd.const_mul (1/Real.pi) using 1
  · funext y
    simpa only [F,div_eq_mul_inv,one_div,mul_comm,mul_one] using signedAverage_fixedDomain g y ht

end DiskMoments

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DyadicHats1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

noncomputable section

namespace SignedDisk

namespace DyadicHats

lemma boxNorm_le_norm (x : ℂ) : boxNorm x ≤ ‖x‖ :=
  max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
lemma boxNorm_add_le (x y : ℂ) : boxNorm (x+y) ≤ boxNorm x+boxNorm y := by
  apply max_le
  · exact (abs_add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (abs_add_le _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _))
lemma boxNorm_neg (x : ℂ) : boxNorm (-x) = boxNorm x := by simp [boxNorm]
lemma boxNorm_sub_comm (x y : ℂ) : boxNorm (x-y) = boxNorm (y-x) := by
  rw [← neg_sub y x,boxNorm_neg]

/-- Globally uniform spatial Lipschitz bound for the literal bilinear hats. -/
lemma lipschitz_hat {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) :
    LipschitzWith (Real.toNNReal (2/r)) (hat r p) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  let a := tent (x.re/r-p.1)
  let b := tent (x.im/r-p.2)
  let c := tent (y.re/r-p.1)
  let d := tent (y.im/r-p.2)
  have h1 : |a-c| ≤ ‖x-y‖/r := by
    have h := lipschitz_tent.dist_le_mul (x.re/r-p.1) (y.re/r-p.1)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_sub_sub_cancel_right,← sub_div,
      abs_div,abs_of_pos hr] at h
    exact h.trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm (x-y)) hr.le)
  have h2 : |b-d| ≤ ‖x-y‖/r := by
    have h := lipschitz_tent.dist_le_mul (x.im/r-p.2) (y.im/r-p.2)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_sub_sub_cancel_right,← sub_div,
      abs_div,abs_of_pos hr] at h
    exact h.trans (div_le_div_of_nonneg_right (Complex.abs_im_le_norm (x-y)) hr.le)
  have hab : |a*b-c*d| ≤ |a-c|+|b-d| := by
    calc
      _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
      _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
      _ = |a-c| *b+c*|b-d| := by rw [abs_mul,abs_mul,abs_of_nonneg (tent_nonneg _),abs_of_nonneg (tent_nonneg _)]
      _ ≤ |a-c| *1+1*|b-d| := add_le_add
        (mul_le_mul_of_nonneg_left (tent_le_one _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (tent_le_one _) (abs_nonneg _))
      _ = _ := by ring
  change |a*b-c*d| ≤ _
  rw [Real.coe_toNNReal (2/r) (by positivity),dist_eq_norm]
  calc
    _ ≤ ‖x-y‖/r+‖x-y‖/r := hab.trans (add_le_add h1 h2)
    _ = _ := by ring

open scoped BigOperators

lemma scalarMass_le_integral {h : ℂ → ℂ} (r : ℝ) (p : ℤ × ℤ) :
    scalarMass h r p ≤ ∫ y, hat r p y * ‖h y‖ := by
  unfold scalarMass vectorMass
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hat_nonneg _ _ _)] using
    norm_integral_le_integral_norm (fun y => hat r p y • h y)

/-- Any finite set of roots carries at most the total L1 density, uniformly
in the scale. This proves the full-grid mass budget once finite support is used. -/
lemma sum_scalarMass_le {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ) (S : Finset (ℤ × ℤ)) :
    ∑ p ∈ S, scalarMass h r p ≤ ∫ y, ‖h y‖ := by
  have hi (p : ℤ × ℤ) : Integrable (fun y => hat r p y * ‖h y‖) := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hat_nonneg _ _ _)] using
      (integrable_hat_smul hh r p).norm
  calc
    _ ≤ ∑ p ∈ S, ∫ y, hat r p y * ‖h y‖ := Finset.sum_le_sum (fun p _ => scalarMass_le_integral r p)
    _ = ∫ y, ∑ p ∈ S, hat r p y * ‖h y‖ := (integral_finsetSum _ (fun p _ => hi p)).symm
    _ ≤ ∫ y, ‖h y‖ := by
      apply integral_mono (integrable_finsetSum _ (fun p _ => hi p)) hh.norm
      intro y
      change (∑ p ∈ S, hat r p y * ‖h y‖) ≤ ‖h y‖
      rw [← Finset.sum_mul]
      have hs := Summable.sum_le_tsum S (fun p _ => hat_nonneg r p y) (summable_hat r y)
      rw [tsum_hat] at hs
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (norm_nonneg (h y))

end DyadicHats

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff

open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace DyadicHats

lemma parent_in_box {N : ℕ} {p q : ℤ × ℤ} (hq : q ∈ indexBox N) (hpq : step p q ≠ 0) :
    p ∈ indexBox N := by
  have hq1 : -(N:ℤ) ≤ q.1 ∧ q.1 ≤ N := Finset.mem_Icc.mp (Finset.mem_product.mp hq).1
  have hq2 : -(N:ℤ) ≤ q.2 ∧ q.2 ≤ N := Finset.mem_Icc.mp (Finset.mem_product.mp hq).2
  have hh : 0 < step p q := lt_of_le_of_ne (step_nonneg p q) (Ne.symm hpq)
  have h1 := (tent_pos_iff _).mp (pos_of_mul_pos_left hh (tent_nonneg _))
  have h2 := (tent_pos_iff _).mp (pos_of_mul_pos_right hh (tent_nonneg _))
  have hbound (j k : ℤ) (hk : -(N:ℤ) ≤ k ∧ k ≤ N) (ha : |(k:ℝ)/2-j| < 1) :
      j ∈ Finset.Icc (-(N:ℤ)) N := by
    have hlo : -(N:ℝ) ≤ k := by exact_mod_cast hk.1
    have hhi : (k:ℝ) ≤ N := by exact_mod_cast hk.2
    have hj := abs_lt.mp ha
    simp only [Finset.mem_Icc]
    constructor
    · by_contra hn
      have : j ≤ -(N:ℤ)-1 := by omega
      have : (j:ℝ) ≤ -(N:ℝ)-1 := by exact_mod_cast this
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    · by_contra hn
      have : (N:ℤ)+1 ≤ j := by omega
      have : (N:ℝ)+1 ≤ j := by exact_mod_cast this
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact Finset.mem_product.mpr ⟨hbound _ _ hq1 h1,hbound _ _ hq2 h2⟩

/-- Restriction to a finite box retains the exact column normalization of the
positive dyadic refinement matrix; it does not normalize its rows. -/
lemma grid_step_column (N : ℕ) (q : Grid N) : (∑ p : Grid N, step p q) = 1 := by
  have he := step_column q.val
  rw [tsum_eq_sum (s := indexBox N)] at he
  · exact (Finset.sum_coe_sort (indexBox N) (fun p => step p q)).trans he
  · intro p hp
    by_contra hn
    exact hp (parent_in_box q.property hn)

lemma density_partition_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (x : ℂ) :
    (∑ p : Grid N, hat r p x*h x) = h x := by
  have he : (∑' p : ℤ × ℤ, hat r p x*h x) = ∑ p ∈ indexBox N, hat r p x*h x :=
    tsum_eq_sum (fun p hp => hat_mul_zero_outside hr hN hs hp x)
  rw [Finset.sum_coe_sort (indexBox N) (fun p => hat r p x*h x),← he,
    tsum_mul_right,tsum_hat,one_mul]

end DyadicHats

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DyadicHats2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DyadicHats

section
open scoped BigOperators

variable {N : ℕ}

lemma densityRoot_abs_mass {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    (∫ x, |densityRoot N r h k q x|) = |∫ x, hat (scale r k) q x*h x| := by
  have he := ScalarCancellation.roots_abs_mass (weights N) (pieces_integrable hh r) k q
  simpa only [densityRoot,refined_eq_density hr hR hN hs] using he

lemma densityError_cost {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    (∫ x, |densityError N r h k q x|) ≤ 2*densityDefect N r h k q := by
  cases k with
  | zero =>
    have he := ScalarCancellation.errors_terminal_cost (weights N) (pieces_integrable hh r) q
    simp only [pieces,abs_mul,abs_of_nonneg (hat_nonneg r q _)] at he
    rw [densityDefect]
    change (∫ x, |ScalarCancellation.errors volume (weights N) (pieces N r h) 0 q x|) ≤ _
    rw [he]
    linarith
  | succ k =>
    have he := ScalarCancellation.errors_cost (weights N) (fun _ p s => step_nonneg p s)
      (pieces_integrable hh r) k q
    simp only [refined_eq_density hr hR hN hs,weights] at he
    change (∫ x, |ScalarCancellation.errors volume (weights N) (pieces N r h) (k+1) q x|) ≤ _
    rw [densityDefect]
    linarith

end

open Finset

lemma coeff_nonneg (N d : ℕ) (p q : Grid N) : 0 ≤ coeff N d p q := by
  induction d generalizing p with
  | zero => simp only [coeff]; split_ifs <;> norm_num
  | succ d ih => exact sum_nonneg fun a _ => mul_nonneg (step_nonneg p a) (ih a)

lemma coeff_column (N d : ℕ) (q : Grid N) : (∑ p : Grid N, coeff N d p q) = 1 := by
  induction d with
  | zero => simp [coeff]
  | succ d ih =>
    simp only [coeff]
    rw [Finset.sum_comm]
    simp_rw [← sum_mul,grid_step_column,one_mul]
    exact ih

/-- All lower-level error densities, with their actual coherent coefficients,
reconstruct the genuine coarse hat density exactly. -/
theorem density_decomposition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (q : Grid N) (x : ℂ) :
    hat (scale r k) q x*h x = densityRoot N r h k q x+
      ∑ j ∈ range (k+1), ∑ s : Grid N, coeff N (k-j) q s*densityError N r h j s x := by
  rw [← refined_eq_density hr hR hN hs]
  apply ScalarCancellation.telescoped_decomposition (weights N) (pieces N r h)
    (fun k j p s => coeff N (k-j) p s)
  · intro j p s
    simp only [Nat.sub_self,coeff]
  · intro k j p s hj
    rw [show k+1-j = k-j+1 by omega,coeff]
    rfl

lemma terminal_abs_sum {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) :
    (∑ q : Grid N, ∫ x, hat r q x*|h x|) = ∫ x, |h x| := by
  rw [← integral_finsetSum (Finset.univ : Finset (Grid N)) (fun q _ => integrable_hat_mul hh.abs r q)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  apply density_partition_grid hr hN
  intro y hy
  exact hs y (fun hz => hy (by rw [hz,abs_zero]))

lemma densityDefect_sum_succ (N : ℕ) (r : ℝ) (h : ℂ → ℝ) (k : ℕ) :
    (∑ q : Grid N, densityDefect N r h (k+1) q) =
      ((∑ q : Grid N, |∫ x, hat (scale r k) q x*h x|)-
       (∑ q : Grid N, |∫ x, hat (scale r (k+1)) q x*h x|))/2 := by
  simp only [densityDefect]
  rw [← sum_div,sum_sub_distrib]
  congr 2
  rw [Finset.sum_comm]
  simp_rw [← sum_mul,grid_step_column,one_mul]

/-- Exact telescoping of the literal scalar defects, including the finest
terminal split. No depth-dependent or terminal remainder is discarded. -/
theorem densityDefect_budget_eq {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q : Grid N, densityDefect N r h k q) =
      ((∫ x, |h x|)-(∑ q : Grid N, |∫ x, hat (scale r n) q x*h x|))/2 := by
  induction n with
  | zero =>
    simp only [Nat.zero_add,range_one,sum_singleton,densityDefect,
      scale,pow_zero,one_mul]
    rw [← sum_div,sum_sub_distrib]
    rw [terminal_abs_sum hr hN hh hs]
  | succ n ih =>
    rw [sum_range_succ,ih,densityDefect_sum_succ]
    ring

lemma densityDefect_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ densityDefect N r h k q := by
  have he := densityError_cost hr hR hN hh hs k q
  have hn : 0 ≤ ∫ x, |densityError N r h k q x| := integral_nonneg (fun x => abs_nonneg _)
  linarith

lemma densityDefect_budget {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q : Grid N, densityDefect N r h k q) ≤ (∫ x, |h x|)/2 := by
  rw [densityDefect_budget_eq hr hN hh hs]
  have he : 0 ≤ ∑ q : Grid N, |∫ x, hat (scale r n) q x*h x| := sum_nonneg fun _ _ => abs_nonneg _
  linarith

lemma scalarPrice_sum (N : ℕ) (r : ℝ) (h : ℂ → ℝ) (ρ : ℝ) (k : ℕ) :
    (∑ q : Grid N, scalarPrice N r h ρ k q) =
      ∑ j ∈ range (k+1), ρ^(k-j)*∑ s : Grid N, densityDefect N r h j s := by
  simp only [scalarPrice]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← mul_sum,Finset.sum_comm]
  congr 1
  simp_rw [← sum_mul,coeff_column,one_mul]

open Finset

lemma discount_recurrence (ρ : ℝ) (a : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ range (k+2), ρ^(k+1-j)*a j) =
      a (k+1)+ρ*(∑ j ∈ range (k+1), ρ^(k-j)*a j) := by
  rw [sum_range_succ]
  simp only [Nat.sub_self,pow_zero,one_mul,mul_sum]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [show k+1-j = (k-j)+1 by have := mem_range.mp hj; omega,pow_succ]
  ring

lemma triangle_discount_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ j ∈ range (k+1), ρ^(k-j)*a j) ≤
      (1-ρ)⁻¹*∑ j ∈ range (n+1), a j := by
  let b : ℕ → ℝ := fun k => ∑ j ∈ range (k+1), ρ^(k-j)*a j
  have hb : ∀ k, 0 ≤ b k := fun k => sum_nonneg fun j _ => mul_nonneg (pow_nonneg hρ _) (ha j)
  have hi : ∀ n, (1-ρ)*(∑ k ∈ range (n+1), b k) =
      (∑ j ∈ range (n+1), a j)-ρ*b n := by
    intro n
    induction n with
    | zero => simp [b]; ring
    | succ n ih =>
      rw [sum_range_succ (f := b) (n := n+1),sum_range_succ (f := a) (n := n+1),mul_add,ih]
      have he : b (n+1) = a (n+1)+ρ*b n := discount_recurrence ρ a n
      rw [he]
      ring
  have hle : (1-ρ)*(∑ k ∈ range (n+1), b k) ≤ ∑ j ∈ range (n+1), a j := by
    rw [hi]
    exact sub_le_self _ (mul_nonneg hρ (hb n))
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (sub_pos.mpr hρ1)).mpr (by rwa [mul_comm])

theorem scalarPrice_budget {N : ℕ} {r R ρ : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q : Grid N, scalarPrice N r h ρ k q) ≤
      (1-ρ)⁻¹*((∫ x, |h x|)/2) := by
  simp_rw [scalarPrice_sum]
  apply (triangle_discount_bound hρ hρ1
    (fun j => sum_nonneg fun q _ => densityDefect_nonneg hr hR hN hh hs j q) n).trans
  exact mul_le_mul_of_nonneg_left (densityDefect_budget hr hN hh hs n)
    (inv_nonneg.mpr (sub_nonneg.mpr hρ1.le))

open Finset

lemma activeIndices_card (r : ℝ) (x : ℂ) : (activeIndices r x).card ≤ 4 := by
  change (({⌊x.re/r⌋,⌊x.re/r⌋+1} : Finset ℤ) ×ˢ
    ({⌊x.im/r⌋,⌊x.im/r⌋+1} : Finset ℤ)).card ≤ 4
  rw [Finset.card_product]
  exact (Nat.mul_le_mul (card_insert_le ..) (card_insert_le ..)).trans (by simp)

lemma interpolate_eq_sum (r : ℝ) (f : ℤ × ℤ → ℝ) (x : ℂ)
    (S : Finset (ℤ × ℤ)) (hS : activeIndices r x ⊆ S) :
    interpolate r f x = ∑ p ∈ S, hat r p x*f p := by
  apply tsum_eq_sum
  intro p hp
  rw [hat_zero_of_not_active r x (fun hn => hp (hS hn)),zero_mul]

lemma interpolate_add (r : ℝ) (f g : ℤ × ℤ → ℝ) (x : ℂ) :
    interpolate r (fun p => f p+g p) x = interpolate r f x+interpolate r g x := by
  simp only [interpolate,mul_add]
  exact (summable_weighted_hat r x f).tsum_add (summable_weighted_hat r x g)

/-- Only eight tents can contribute to a difference of two interpolated values.
This is the quantitative global Lipschitz bound with no grid cardinality loss. -/
theorem interpolate_lipschitz {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    {f : ℤ × ℤ → ℝ} (hf : ∀ p, |f p| ≤ B) :
    LipschitzWith (Real.toNNReal (16*B/r)) (interpolate r f) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  let S := activeIndices r x ∪ activeIndices r y
  have hcard : S.card ≤ 8 := (Finset.card_union_le (activeIndices r x) (activeIndices r y)).trans
    (by have := activeIndices_card r x; have := activeIndices_card r y; omega)
  have hsum : |interpolate r f x-interpolate r f y| ≤
      (S.card:ℝ)*((2/r)*‖x-y‖*B) := by
    rw [interpolate_eq_sum r f x S subset_union_left,interpolate_eq_sum r f y S subset_union_right,
      ← sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ S, |hat r p x*f p-hat r p y*f p| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ S, (2/r)*‖x-y‖*B := by
        apply sum_le_sum
        intro p _
        rw [← sub_mul,abs_mul]
        have hb := (lipschitz_hat hr p).dist_le_mul x y
        rw [Real.dist_eq,Real.coe_toNNReal (2/r) (by positivity),dist_eq_norm] at hb
        exact mul_le_mul hb (hf p) (abs_nonneg _) (by positivity)
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  rw [Real.dist_eq,Real.coe_toNNReal (16*B/r) (by positivity),dist_eq_norm]
  have hcard' : (S.card:ℝ) ≤ 8 := by exact_mod_cast hcard
  calc
    _ ≤ (8:ℝ)*((2/r)*‖x-y‖*B) := hsum.trans (mul_le_mul_of_nonneg_right hcard' (by positivity))
    _ = _ := by ring

end DyadicHats

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_FiniteLabels1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace FiniteLabels
open DyadicHats
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma delta_diff_le_one (i j k : ι) : |delta i k-delta j k| ≤ 1 := by
  exact abs_sub_le_iff.mpr ⟨by linarith [(delta i).nonneg k,law_le_one (delta i) k,(delta j).nonneg k],
    by linarith [(delta j).nonneg k,law_le_one (delta j) k,(delta i).nonneg k]⟩

lemma spatialRow_component_lipschitz (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hpB : ∀ z, p z ≤ B) (j : ι) :
    LipschitzWith (Real.toNNReal (16*B/r)) (fun x => spatialRow old target p hp0 hp1 r x j) := by
  have hl := interpolate_lipschitz hr hB (f := fun z => p z*(delta (target z) j-delta old j))
    (fun z => by rw [abs_mul,abs_of_nonneg (hp0 z)]; exact
      (mul_le_mul_of_nonneg_left (delta_diff_le_one _ _ _) (hp0 z)).trans (by simpa using hpB z))
  change LipschitzWith (Real.toNNReal (16*B/r))
    (fun x => delta old j+interpolate r (fun z => p z*(delta (target z) j-delta old j)) x)
  simpa only [zero_add] using (LipschitzWith.const (delta old j)).add hl

end FiniteLabels

namespace DyadicHats
open Finset Filter

lemma interpolate_congr_on (r : ℝ) (x : ℂ) {f g : ℤ × ℤ → ℝ}
    (h : ∀ p, hat r p x ≠ 0 → f p = g p) : interpolate r f x = interpolate r g x := by
  apply tsum_congr
  intro p
  by_cases hp : hat r p x = 0
  · simp only [hp,zero_mul]
  · rw [h p hp]

lemma hat_vertex_local {r : ℝ} (hr : 0 < r) {x q : ℂ}
    (hx : boxNorm (x-q) < 199*r) {p : ℤ × ℤ} (hp : hat r p x ≠ 0) :
    boxNorm (point r p-q) ≤ 200*r := by
  have hd := (hat_ne_zero_iff hr p x).mp hp
  have ht := boxNorm_add_le (point r p-x) (x-q)
  rw [sub_add_sub_cancel,boxNorm_sub_comm (point r p) x] at ht
  linarith

end DyadicHats

namespace FiniteLabels

lemma probability_lt_one_iff {τ d : ℝ} (hτ : 0 < τ) : probability τ d < 1 ↔ d < 2*τ := by
  rw [probability,min_lt_iff]
  constructor
  · intro h
    rcases h with h|h
    · exact (lt_irrefl _ h).elim
    have hm := le_max_left (d-τ) 0
    have hn : 0 ≤ τ⁻¹*max (d-τ) 0 := by positivity
    have ht : τ⁻¹*max (d-τ) 0 < 1 := by nlinarith
    rw [inv_mul_eq_div,div_lt_one hτ] at ht
    linarith
  · intro h
    right
    have hm : max (d-τ) 0 < τ := max_lt (by linarith) hτ
    have hn : 0 ≤ τ⁻¹*max (d-τ) 0 := by positivity
    have ht : τ⁻¹*max (d-τ) 0 < 1 := by rw [inv_mul_eq_div,div_lt_one hτ]; exact hm
    nlinarith

open DyadicHats

end FiniteLabels

namespace DyadicHats
open Finset

lemma hat_at_point {r : ℝ} (hr : r ≠ 0) (p q : ℤ × ℤ) :
    hat r p (point r q) = if p=q then 1 else 0 := by
  have ht (a b : ℤ) : tent ((b:ℝ)-(a:ℝ)) = if a=b then 1 else 0 := by
    by_cases h : a=b
    · simp [h,tent]
    · rw [ite_eq_right h]
      apply tent_eq_zero_of_one_le
      have hi : (1:ℤ) ≤ |b-a| := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm h))
      exact_mod_cast hi
  simp only [hat,point,mul_div_cancel_left₀ _ hr,ht]
  split_ifs <;> simp_all [Prod.ext_iff]

lemma hat_vertex_bound {r : ℝ} (hr : 0 < r) {N : ℕ} {x : ℂ}
    (hx1 : |x.re| ≤ r*N) (hx2 : |x.im| ≤ r*N)
    {p : ℤ × ℤ} (hp : hat r p x ≠ 0) : p ∈ indexBox N := by
  have h := (hat_ne_zero_iff hr p x).mp hp
  have h1 := lt_of_le_of_lt (le_max_left |(x-point r p).re| |(x-point r p).im|) h
  have h2 := lt_of_le_of_lt (le_max_right |(x-point r p).re| |(x-point r p).im|) h
  simp only [Complex.sub_re,Complex.sub_im,point] at h1 h2
  have hb (t : ℝ) (j : ℤ) (ht : |t| ≤ r*N) (hj : |t-r*j| < r) :
      j ∈ Finset.Icc (-(N:ℤ)) N := by
    have ht' := abs_le.mp ht
    have hj' := abs_lt.mp hj
    have hlo : -(N:ℝ)-1 < (j:ℝ) := by nlinarith
    have hhi : (j:ℝ) < (N:ℝ)+1 := by nlinarith
    have hlo' : -(N:ℤ)-1 < j := by exact_mod_cast hlo
    have hhi' : j < (N:ℤ)+1 := by exact_mod_cast hhi
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  exact Finset.mem_product.mpr ⟨hb _ _ hx1 h1,hb _ _ hx2 h2⟩

lemma velocity_bound_on_grid {N : ℕ} {r : ℝ} (hr : 0 < r) (k : ℕ) (q : Grid N) :
    |(point r q).re| ≤ scale r k*N ∧ |(point r q).im| ≤ scale r k*N := by
  have h1 := Finset.mem_Icc.mp (Finset.mem_product.mp q.property).1
  have h2 := Finset.mem_Icc.mp (Finset.mem_product.mp q.property).2
  have hh (j : ℤ) (hj : -(N:ℤ) ≤ j ∧ j ≤ N) : |r*j| ≤ scale r k*N := by
    have hj' : |(j:ℝ)| ≤ N := abs_le.mpr ⟨by exact_mod_cast hj.1,by exact_mod_cast hj.2⟩
    rw [abs_mul,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hj' hr.le).trans
      (mul_le_mul_of_nonneg_right (le_scale hr.le k) (Nat.cast_nonneg N))
  exact ⟨hh q.val.1 h1,hh q.val.2 h2⟩

end DyadicHats

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DyadicHats3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DyadicHats

lemma coeff_eq_hat {N : ℕ} {r : ℝ} (hr : 0 < r) (k : ℕ) (p q : Grid N) :
    coeff N k p q = hat (scale r k) p (point r q) := by
  induction k generalizing p with
  | zero =>
    simp only [coeff,scale,pow_zero,one_mul,hat_at_point hr.ne']
    by_cases hpq : p=q
    · rw [ite_eq_left hpq,ite_eq_left (congrArg Subtype.val hpq)]
    · rw [ite_eq_right hpq,ite_eq_right (fun h => hpq (Subtype.ext h))]
  | succ k ih =>
    rw [coeff,scale_succ,hat_refine,tsum_eq_sum (s := indexBox N)]
    · rw [← sum_coe_sort (indexBox N) (fun j => step p j*hat (scale r k) j (point r q))]
      apply sum_congr rfl
      intro j hj
      rw [ih]
    · intro j hj
      have hz : hat (scale r k) j (point r q) = 0 := by
        by_contra hn
        have hb := velocity_bound_on_grid hr k q
        exact hj (hat_vertex_bound (scale_pos hr k) hb.1 hb.2 hn)
      rw [hz,mul_zero]

lemma hat_refine_grid_at {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {x : ℂ} (hx : ‖x‖ ≤ R) (p : Grid N) :
    hat (2*r) p x = ∑ q : Grid N, step p q*hat r q x := by
  rw [hat_refine,tsum_eq_sum (s := indexBox N)]
  · exact (sum_coe_sort (indexBox N) (fun q => step p q*hat r q x)).symm
  · intro q hq
    have hz : hat r q x = 0 := by
      by_contra hn
      exact hq (mem_indexBox_of_le hr hN hx hn)
    rw [hz,mul_zero]

lemma vectorMass_grid_refine {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (p : Grid N) :
    vectorMass h (2*r) p = ∑ q : Grid N, step p q • vectorMass h r q := by
  let f := fun y => ∑ q : Grid N, step p q • (hat r q y • h y)
  have hf : (fun y => hat (2*r) p y • h y) = f := by
    funext y
    by_cases hy : h y=0
    · simp only [f,hy,smul_zero,sum_const_zero]
    · rw [hat_refine_grid_at hr hN (hs y hy) p,sum_smul]
      simp only [f,smul_smul]
  rw [vectorMass,hf]
  dsimp only [f]
  have hi (q : Grid N) : Integrable (fun y => step p q • (hat r q y • h y)) :=
    Integrable.smul (step p q) (integrable_hat_smul hh r q)
  rw [integral_finsetSum Finset.univ (fun q _ => hi q)]
  apply sum_congr rfl
  intro q hq
  rw [integral_smul]
  rfl

lemma vectorMass_coeff {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : Grid N) :
    vectorMass h (scale r k) p = ∑ q : Grid N, coeff N k p q • vectorMass h r q := by
  induction k generalizing p with
  | zero => simp [coeff,scale]
  | succ k ih =>
    rw [scale_succ,vectorMass_grid_refine (scale_pos hr k) (scale_index_bound hr hR hN k) hh hs]
    simp only [ih,smul_sum,smul_smul,coeff,sum_smul]
    exact Finset.sum_comm

lemma sum_scalarMass_grid_le {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ) :
    (∑ q : Grid N, scalarMass h r q) ≤ ∫ y, ‖h y‖ := by
  rw [sum_coe_sort (indexBox N) (fun q => scalarMass h r q)]
  exact sum_scalarMass_le hh r (indexBox N)

open Finset

lemma hat_lower {r a : ℝ} (hr : 0 < r) (ha : a ≤ 1) (p : ℤ × ℤ) (x : ℂ)
    (hx : boxNorm (x-point r p) ≤ a*r) : (1-a)^2 ≤ hat r p x := by
  have h1 := (le_max_left |(x-point r p).re| |(x-point r p).im|).trans hx
  have h2 := (le_max_right |(x-point r p).re| |(x-point r p).im|).trans hx
  simp only [Complex.sub_re,Complex.sub_im,point] at h1 h2
  have hh (t : ℝ) (j : ℤ) (h : |t-r*j| ≤ a*r) : 1-a ≤ tent (t/r-j) := by
    have he : t/r-j = (t-r*j)/r := by field_simp
    rw [he,tent,abs_div,abs_of_pos hr]
    have hd : |t-r*j|/r ≤ a := (div_le_iff₀ hr).mpr h
    exact (sub_le_sub_left hd 1).trans (le_max_left _ _)
  calc
    (1-a)^2 = (1-a)*(1-a) := by ring
    _ ≤ tent (x.re/r-p.1)*tent (x.im/r-p.2) :=
      mul_le_mul (hh _ _ h1) (hh _ _ h2) (sub_nonneg.mpr ha) (tent_nonneg _)
    _ = _ := rfl

lemma nearParent_int_bound (j : ℤ) : |j-4096*((j+2048)/4096)| ≤ 2048 := by
  rw [abs_le]
  omega

lemma nearParent_box {r : ℝ} (hr : 0 < r) (q : ℤ × ℤ) :
    boxNorm (point r q-point (4096*r) (nearParent q)) ≤ (1/2 : ℝ)*(4096*r) := by
  have hh (j : ℤ) : |r*j-(4096*r)*((j+2048)/4096:ℤ)| ≤ (1/2:ℝ)*(4096*r) := by
    have hi : |(j:ℝ)-4096*((j+2048)/4096:ℤ)| ≤ 2048 := by exact_mod_cast nearParent_int_bound j
    have he : r*j-(4096*r)*((j+2048)/4096:ℤ) = r*((j:ℝ)-4096*((j+2048)/4096:ℤ)) := by ring
    rw [he,abs_mul,abs_of_pos hr]
    nlinarith
  exact max_le (hh q.1) (hh q.2)

lemma nearParent_hat_lower {r : ℝ} (hr : 0 < r) (q w : ℤ × ℤ)
    (hw : boxNorm (point r w-point r q) ≤ 500*r) :
    1/4 ≤ hat (scale r 12) (nearParent q) (point r q) ∧
    9/64 ≤ hat (scale r 12) (nearParent q) (point r w) := by
  have hs : scale r 12 = 4096*r := by norm_num [scale]
  have hq := nearParent_box hr q
  have ht := boxNorm_add_le (point r w-point r q) (point r q-point (4096*r) (nearParent q))
  rw [sub_add_sub_cancel] at ht
  have hw' : boxNorm (point r w-point (4096*r) (nearParent q)) ≤ (5/8:ℝ)*(4096*r) := by
    linarith
  have h1 := hat_lower (by positivity : 0 < 4096*r) (by norm_num : (1/2:ℝ) ≤ 1) (nearParent q) (point r q) hq
  have h2 := hat_lower (by positivity : 0 < 4096*r) (by norm_num : (5/8:ℝ) ≤ 1) (nearParent q) (point r w) hw'
  rw [hs]
  norm_num at h1 h2 ⊢
  exact ⟨h1,h2⟩

lemma nearParent_fiber_card (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    (S.filter (fun q => nearParent q=p)).card ≤ 4097^2 := by
  let T := (Finset.Icc (4096*p.1-2048) (4096*p.1+2048)).product
    (Finset.Icc (4096*p.2-2048) (4096*p.2+2048))
  have hsub : S.filter (fun q => nearParent q=p) ⊆ T := by
    intro q hq
    have he := (Finset.mem_filter.mp hq).2
    have h1 := nearParent_int_bound q.1
    have h2 := nearParent_int_bound q.2
    have he1 : (q.1+2048)/4096=p.1 := congrArg Prod.fst he
    have he2 : (q.2+2048)/4096=p.2 := congrArg Prod.snd he
    rw [he1,abs_le] at h1
    rw [he2,abs_le] at h2
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,
      Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
  apply (Finset.card_le_card hsub).trans
  dsimp only [T]
  change ((Finset.Icc (4096*p.1-2048) (4096*p.1+2048)) ×ˢ
    (Finset.Icc (4096*p.2-2048) (4096*p.2+2048))).card ≤ 4097^2
  rw [Finset.card_product,Int.card_Icc,Int.card_Icc]
  have he (j : ℤ) : 4096*j+2048+1-(4096*j-2048)=4097 := by ring
  rw [he,he]
  change (4097:ℕ)*4097 ≤ 4097^2
  norm_num

end DyadicHats

namespace DirectionNeighbors
open DyadicHats Finset

lemma mem_window_iff {r : ℝ} (hr : 0 < r) (d : ℕ) (q z : ℤ × ℤ) :
    z ∈ window d q ↔ boxNorm (point r z-point r q) ≤ (d:ℝ)*r := by
  have hh (a b : ℤ) : |r*a-r*b| ≤ (d:ℝ)*r ↔ b-(d:ℤ) ≤ a ∧ a ≤ b+d := by
    rw [← mul_sub,abs_mul,abs_of_pos hr,mul_comm (d:ℝ) r,mul_le_mul_iff_right₀ hr]
    have hc : |(a:ℝ)-(b:ℝ)| ≤ (d:ℝ) ↔ |a-b| ≤ (d:ℤ) := by
      exact_mod_cast Iff.rfl
    rw [hc,abs_le]
    omega
  change (_ ∈ ((Finset.Icc _ _) ×ˢ (Finset.Icc _ _))) ↔ max _ _ ≤ _
  rw [Finset.mem_product,Finset.mem_Icc,Finset.mem_Icc,max_le_iff]
  exact (hh _ _).symm.and (hh _ _).symm

lemma maxVertex_mem (f : ℤ × ℤ → ℝ) (d : ℕ) (q : ℤ × ℤ) :
    maxVertex f d q ∈ window d q := (Classical.choose_spec (max_exists f d q)).1
lemma le_maxVertex (f : ℤ × ℤ → ℝ) (d : ℕ) (q : ℤ × ℤ) {z : ℤ × ℤ}
    (hz : z ∈ window d q) : f z ≤ f (maxVertex f d q) :=
  (Classical.choose_spec (max_exists f d q)).2 z hz

lemma energy_nonneg (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : 0 ≤ energy h r q := sq_nonneg _

lemma energy_controls {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q z : ℤ × ℤ)
    (hz : boxNorm (point r z-point r q) ≤ 200*r) :
    ‖Theta h r z-theta h r q‖^2 ≤ energy h r q := by
  apply le_maxVertex (fun z => ‖Theta h r z-theta h r q‖^2) 200 q
  exact (mem_window_iff hr 200 q z).mpr (by simpa using hz)

lemma worstVertex_near {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ) :
    boxNorm (point r (worstVertex h r q)-point r q) ≤ 200*r := by
  have hm := maxVertex_mem (fun z => ‖Theta h r z-theta h r q‖^2) 200 q
  simpa only [worstVertex,Nat.cast_ofNat] using (mem_window_iff hr 200 q _).mp hm

lemma chosen_near {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (z : ℤ × ℤ) :
    boxNorm (point r (chosen h r z)-point r z) ≤ 300*r := by
  simpa only [chosen,Nat.cast_ofNat] using
    (mem_window_iff hr 300 z _).mp (maxVertex_mem (scalarMass h r) 300 z)

/-- The actual chosen neighbor supplies at least the root's mass and is within
500 fine-grid units, precisely the inputs spent by the coarse triangle defect. -/
lemma worst_chosen_spec {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ) :
    scalarMass h r q ≤ scalarMass h r (chosen h r (worstVertex h r q)) ∧
    boxNorm (point r (chosen h r (worstVertex h r q))-point r q) ≤ 500*r := by
  let z := worstVertex h r q
  have hz : boxNorm (point r z-point r q) ≤ 200*r := worstVertex_near hr h q
  have hz' : boxNorm (point r q-point r z) ≤ 300*r := by
    rw [boxNorm_sub_comm]
    linarith
  have ha := le_maxVertex (scalarMass h r) 300 z ((mem_window_iff hr 300 z q).mpr (by simpa using hz'))
  have hw := chosen_near hr h z
  have ht := boxNorm_add_le (point r (chosen h r z)-point r z) (point r z-point r q)
  rw [sub_add_sub_cancel] at ht
  exact ⟨ha,by linarith⟩

open DyadicHats

lemma vectorMass_mem_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    {q : ℤ × ℤ} (hq : vectorMass h r q ≠ 0) : q ∈ indexBox N := by
  by_contra hn
  apply hq
  apply integral_eq_zero_of_ae
  filter_upwards with y
  by_cases hy : h y=0
  · simp only [hy,smul_zero,Pi.zero_apply]
  · have hh : hat r q y=0 := by
      by_contra hz
      exact hn (mem_indexBox_of_le hr hN (hs y hy) hz)
    simp only [hh,zero_smul,Pi.zero_apply]

lemma direction_refine {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (d : ℕ) (p : Grid N) :
    scalarMass h (scale r d) p • theta h (scale r d) p =
      ∑ q : Grid N, (coeff N d p q*scalarMass h r q) • theta h r q := by
  rw [show scalarMass h (scale r d) p • theta h (scale r d) p =
    vectorMass h (scale r d) p from IntrinsicMarks.mass_direction 1 _]
  rw [vectorMass_coeff hr hR hN hh hs]
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_smul]
  congr 1
  exact (IntrinsicMarks.mass_direction 1 _).symm

lemma coarseDefect_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (d : ℕ) (p : Grid N) :
    0 ≤ coarseDefect N h r d p := by
  have he := VectorRefinement.quadratic_defect (coeff N d p) (fun q : Grid N => scalarMass h r q)
    (fun q : Grid N => theta h r q) (theta h (scale r d) p) (scalarMass h (scale r d) p)
    (norm_theta _ _ _) (fun _ => norm_theta _ _ _) (direction_refine hr hR hN hh hs d p)
  rw [coarseDefect,he]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun q _ =>
    mul_nonneg (mul_nonneg (coeff_nonneg _ _ _ _) (norm_nonneg _)) (sq_nonneg _)

lemma coarseDefect_sum (N : ℕ) (h : ℂ → ℂ) (r : ℝ) (d : ℕ) :
    (∑ p : Grid N, coarseDefect N h r d p) =
      (∑ q : Grid N, scalarMass h r q)-(∑ p : Grid N, scalarMass h (scale r d) p) := by
  simp only [coarseDefect,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,coeff_column,one_mul]

/-- The actual maximally differing neighbor spends true vector cancellation,
not an independently postulated directional budget. -/
lemma neighbor_charge {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (q : Grid N) :
    scalarMass h r q*energy h r q ≤ 48*coarseDefect N h r 12 (parent N q) := by
  by_cases hq : scalarMass h r q=0
  · rw [hq,zero_mul]
    exact mul_nonneg (by norm_num) (coarseDefect_nonneg hr hR hN hh hs 12 _)
  have hqpos : 0 < scalarMass h r q := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq)
  let z := chosen h r (worstVertex h r q)
  have hz := worst_chosen_spec hr h q
  have hzpos : 0 < scalarMass h r z := hqpos.trans_le hz.1
  have hzmem : z ∈ indexBox N := vectorMass_mem_grid hr hN hs (norm_ne_zero_iff.mp (ne_of_gt hzpos))
  let s : Grid N := ⟨z,hzmem⟩
  have hweights := nearParent_hat_lower hr q z hz.2
  have hwq : 1/4 ≤ coeff N 12 (parent N q) q := by
    rw [coeff_eq_hat hr]
    exact hweights.1
  have hws : 9/64 ≤ coeff N 12 (parent N q) s := by
    rw [coeff_eq_hat hr]
    exact hweights.2
  have he := VectorRefinement.pair_defect_bound (coeff N 12 (parent N q))
    (fun p : Grid N => scalarMass h r p) (fun p : Grid N => theta h r p)
    (theta h (scale r 12) (parent N q)) (scalarMass h (scale r 12) (parent N q))
    (fun p => coeff_nonneg N 12 _ p) (fun _ => norm_nonneg _)
    (norm_theta _ _ _) (fun _ => norm_theta _ _ _)
    (direction_refine hr hR hN hh hs 12 _) hwq hws hz.1
  change scalarMass h r q*‖theta h r z-theta h r q‖^2 ≤ _
  rw [norm_sub_rev]
  exact he

lemma parent_fiber_card (N : ℕ) (p : Grid N) :
    (Finset.univ.filter (fun q : Grid N => parent N q=p)).card ≤ 4097^2 := by
  let F := Finset.univ.filter (fun q : Grid N => parent N q=p)
  let e : Grid N ↪ ℤ × ℤ := ⟨Subtype.val,Subtype.val_injective⟩
  have hm : F.map e ⊆ (indexBox N).filter (fun q => nearParent q=p.val) := by
    intro q hq
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp hq
    apply Finset.mem_filter.mpr
    exact ⟨s.property,congrArg Subtype.val (Finset.mem_filter.mp hs).2⟩
  calc
    _ = (F.map e).card := (Finset.card_map e).symm
    _ ≤ ((indexBox N).filter (fun q => nearParent q=p.val)).card := Finset.card_le_card hm
    _ ≤ 4097^2 := nearParent_fiber_card _ _

lemma parent_sum_bound (N : ℕ) (a : Grid N → ℝ) (ha : ∀ p, 0 ≤ a p) :
    (∑ q : Grid N, a (parent N q)) ≤ (4097:ℝ)^2*∑ p : Grid N, a p := by
  rw [← Finset.sum_fiberwise Finset.univ (parent N) (fun q => a (parent N q)),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  calc
    _ = ∑ q ∈ Finset.univ.filter (fun q => parent N q=p), a p := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    _ = ((Finset.univ.filter (fun q => parent N q=p)).card:ℝ)*a p := by simp
    _ ≤ (4097:ℝ)^2*a p := by
      apply mul_le_mul_of_nonneg_right _ (ha p)
      exact_mod_cast parent_fiber_card N p

/-- Uniform one-scale neighbor energy bound by the actual twelve-scale mass drop. -/
theorem level_energy_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) :
    (∑ q : Grid N, scalarMass h r q*energy h r q) ≤
      (48*(4097:ℝ)^2)*((∑ q : Grid N, scalarMass h r q)-
        ∑ p : Grid N, scalarMass h (scale r 12) p) := by
  have h1 := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Grid N))) =>
    neighbor_charge hr hR hN hh hs q)
  have h2 := parent_sum_bound N (coarseDefect N h r 12)
    (fun p => coarseDefect_nonneg hr hR hN hh hs 12 p)
  rw [← Finset.mul_sum] at h1
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 48))
  rw [coarseDefect_sum] at h3
  simpa only [mul_assoc] using h3

end DirectionNeighbors

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DirectionNeighbors1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DirectionNeighbors
open DyadicHats
lemma scale_scale (r : ℝ) (k d : ℕ) : scale (scale r k) d = scale r (k+d) := by
  simp only [scale,pow_add]
  ring

lemma shifted_mass_bound (A : ℕ → ℝ) {V : ℝ} (h0 : ∀ k, 0 ≤ A k)
    (hV : ∀ k, A k ≤ V) (m d : ℕ) :
    (∑ k ∈ Finset.range m, (A k-A (k+d))) ≤ d*V := by
  have he : (∑ k ∈ Finset.range m, A k)+(∑ k ∈ Finset.range d, A (k+m)) =
      (∑ k ∈ Finset.range d, A k)+(∑ k ∈ Finset.range m, A (k+d)) := by
    calc
      _ = ∑ k ∈ Finset.range (m+d), A k := by
        simpa only [Nat.add_comm] using (Finset.sum_range_add A m d).symm
      _ = ∑ k ∈ Finset.range (d+m), A k := by rw [Nat.add_comm m d]
      _ = _ := by simpa only [Nat.add_comm] using Finset.sum_range_add A d m
  have hprefix : (∑ k ∈ Finset.range d, A k) ≤ d*V := by
    calc
      _ ≤ ∑ _k ∈ Finset.range d, V := Finset.sum_le_sum (fun k _ => hV k)
      _ = _ := by simp
  have htail : 0 ≤ ∑ k ∈ Finset.range d, A (k+m) := Finset.sum_nonneg (fun k _ => h0 _)
  rw [Finset.sum_sub_distrib]
  linarith

theorem neighbor_energy_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) :
    (∑ k ∈ Finset.range m, ∑ q : Grid N,
      scalarMass h (scale r k) q*energy h (scale r k) q) ≤
      (576*(4097:ℝ)^2)*(∫ y, ‖h y‖) := by
  let A := fun k => ∑ q : Grid N, scalarMass h (scale r k) q
  have he (k : ℕ) :
      (∑ q : Grid N, scalarMass h (scale r k) q*energy h (scale r k) q) ≤
        (48*(4097:ℝ)^2)*(A k-A (k+12)) := by
    simpa only [scale_scale] using level_energy_budget (scale_pos hr k) hR
      (scale_index_bound hr hR hN k) hh hs
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range m) => he k)
  rw [← Finset.mul_sum] at hsum
  have hA0 (k : ℕ) : 0 ≤ A k := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hAV (k : ℕ) : A k ≤ ∫ y, ‖h y‖ := sum_scalarMass_grid_le hh _
  have hb := shifted_mass_bound A hA0 hAV m 12
  have hf := hsum.trans (mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ 48*(4097:ℝ)^2))
  norm_num at hf ⊢
  nlinarith only [hf]
end DirectionNeighbors

/-! Actual fixed palette and literal cone coordinates. -/

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace ConeCoordinates

lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
lemma sqrt3_bounds : 3/2 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 := by
  have := sqrt3_sq
  have := sqrt3_pos
  constructor <;> nlinarith
lemma inner_re (n z : ℂ) : inner ℝ n z = (star n*z).re := by
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.mul_re]
  ring
lemma coordinate_apply (n z : ℂ) (s : ℝ) :
    coordinate n s z = (star n*z).re / Real.sqrt 3 + s*(star n*z).im := by
  change (1/Real.sqrt 3)*inner ℝ n z + s*inner ℝ (Complex.I*n) z = _
  rw [inner_re,inner_im]
  ring
lemma expansion {n : ℂ} (hn : ‖n‖ = 1) (z : ℂ) :
    coordinate n 1 z • axis n 1 + coordinate n (-1) z • axis n (-1) = z := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt3_pos
  have hz : n*(star n*z) = z := by rw [← mul_assoc,mul_star_of_unit hn,one_mul]
  have he : coordinate n 1 z • axis n 1 + coordinate n (-1) z • axis n (-1) =
      n*(star n*z) := by
    apply Complex.ext <;> simp [axis,coordinate_apply,Complex.mul_re,Complex.mul_im] <;> field_simp <;> ring
  exact he.trans hz
lemma coordinate_norm_le {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : |s| ≤ 1) (z : ℂ) :
    |coordinate n s z| ≤ 2 * ‖z‖ := by
  have ha : |inner ℝ n z| ≤ ‖z‖ := by simpa [hn] using abs_real_inner_le_norm n z
  have hb : |inner ℝ (Complex.I*n) z| ≤ ‖z‖ := by
    simpa [norm_mul,hn] using abs_real_inner_le_norm (Complex.I*n) z
  have hr : 1 / Real.sqrt 3 ≤ 1 := by rw [div_le_one sqrt3_pos]; linarith [sqrt3_bounds]
  have hnon : 0 ≤ 1 / Real.sqrt 3 := (div_pos (by norm_num) sqrt3_pos).le
  calc
    |coordinate n s z| ≤ (1/Real.sqrt 3)*|inner ℝ n z| + |s| *|inner ℝ (Complex.I*n) z| := by
      change |(1/Real.sqrt 3)*inner ℝ n z + s*inner ℝ (Complex.I*n) z| ≤ _
      simpa only [abs_mul,abs_of_nonneg hnon] using
        abs_add_le ((1/Real.sqrt 3)*inner ℝ n z) (s*inner ℝ (Complex.I*n) z)
    _ ≤ 1*‖z‖+1*‖z‖ := add_le_add (mul_le_mul hr ha (abs_nonneg _) (by norm_num))
      (mul_le_mul hs hb (abs_nonneg _) (by norm_num))
    _ = 2*‖z‖ := by ring

lemma good_of_close {n z : ℂ} (hn : ‖n‖ = 1) (hclose : ‖z-n‖ ≤ 1/10) : Good n z := by
  have ha : |inner ℝ n (z-n)| ≤ 1/10 := by
    have h := abs_real_inner_le_norm n (z-n)
    simp only [hn,one_mul] at h
    exact h.trans hclose
  have hb : |inner ℝ (Complex.I*n) (z-n)| ≤ 1/10 := by
    have h := abs_real_inner_le_norm (Complex.I*n) (z-n)
    simp only [norm_mul,Complex.norm_I,hn,one_mul] at h
    exact h.trans hclose
  have hin : inner ℝ n n = 1 := by simp [hn]
  have hip : inner ℝ (Complex.I*n) n = 0 := by
    rw [inner_im,show star n*n = 1 by simpa [mul_comm] using mul_star_of_unit hn]
    simp
  simp only [inner_sub_right,hin,hip,sub_zero] at ha hb
  have hab := (abs_le.mp ha).1
  have hbb := abs_le.mp hb
  have hs := sqrt3_bounds
  have ha' : 1/10 ≤ inner ℝ n z / Real.sqrt 3 := by
    apply (le_div_iff₀ sqrt3_pos).2
    nlinarith
  change 0 ≤ (1/Real.sqrt 3)*inner ℝ n z + 1*inner ℝ (Complex.I*n) z ∧
    0 ≤ (1/Real.sqrt 3)*inner ℝ n z + (-1)*inner ℝ (Complex.I*n) z
  have hei : (1/Real.sqrt 3)*inner ℝ n z = inner ℝ n z / Real.sqrt 3 := by ring
  rw [hei]
  constructor <;> nlinarith

lemma quantize_close (z : ℂ) (hz : ‖z‖ = 1) : ‖z-(quantize z hz : ℂ)‖ < 1/2000 :=
  (Classical.choose_spec (fixedPalette.cover z hz)).2

end ConeCoordinates

namespace ConeScalar
open ConeCoordinates DyadicHats IntrinsicMarks

lemma root_mass_norm {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (∫ y, ‖densityRoot N r (fun x => coordinate n s (h x)) k q y • axis n s‖) =
      |coordinate n s (vectorMass h (scale r k) q)| := by
  simp only [norm_smul,axis_norm hn hs,Real.norm_eq_abs,mul_one]
  rw [densityRoot_abs_mass hr hR hN (scalar_integrable hh _) (scalar_support hsupp _),scalar_mass hh]

lemma root_bound {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (∫ y, ‖densityRoot N r (fun x => coordinate n s (h x)) k q y • axis n s‖) ≤
      2*scalarMass h (scale r k) q := by
  rw [root_mass_norm hr hR hN hh hsupp k q hn hs]
  apply coordinate_norm_le hn
  exact (abs_le_one_iff_mul_self_le_one).mpr (by nlinarith)

end ConeScalar

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_AffineDensities1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace AffineDensities

lemma mass_rescale (h : ℂ → ℂ) (p : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ X, ‖rescale p r h X‖) = r⁻¹*(∫ y, ‖h y‖) := by
  simp only [rescale,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le,integral_const_mul]
  have he := Measure.integral_comp_smul volume (fun y : ℂ => ‖h (p+y)‖) r
  simp only [Complex.finrank_real_complex,smul_eq_mul,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r))] at he
  rw [he, integral_add_left_eq_self (fun y : ℂ => ‖h y‖)]
  field_simp

end AffineDensities

namespace PricePieces
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities

lemma errorPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k j : ℕ) (hj : j ≤ k) (p : ℂ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (errorPiece hh hr k j hj p q n s).mass ≤ (scale r k)⁻¹*
      (2*densityDefect N r (fun x => coordinate n s (h x)) j q) := by
  change (∫ X, ‖rescale _ _ _ X‖) ≤ _
  rw [mass_rescale _ _ (scale_pos hr k)]
  simp only [norm_smul,axis_norm hn hs,mul_one,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (densityError_cost hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) j q)
    (inv_nonneg.mpr (scale_pos hr k).le)

end PricePieces

namespace LocalCancellation

lemma ErrorPiece.mass_weight {Cs : ℝ} (b : ErrorPiece Cs) {w : ℝ} (hw : 0 ≤ w) :
    (b.weight w).mass = w*b.mass := by
  simp only [ErrorPiece.mass,ErrorPiece.weight,norm_smul,Real.norm_eq_abs,abs_of_nonneg hw,
    integral_const_mul]

end LocalCancellation

namespace PricePieces
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities

lemma vector_decomposition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (q : Grid N) {n : ℂ} (hn : ‖n‖ = 1) (y : ℂ) :
    hat (scale r k) q y • h y = rootVector N r h k q n y+
      ∑ j ∈ Finset.range (k+1), ∑ s : Grid N, coeff N (k-j) q s • errorVector N r h j s n y := by
  have hp := density_decomposition hr hR hN (scalar_support hsupp (coordinate n 1)) k q y
  have hm := density_decomposition hr hR hN (scalar_support hsupp (coordinate n (-1))) k q y
  have hx := congrArg (fun z : ℂ => hat (scale r k) q y • z) (expansion hn (h y))
  rw [smul_add,smul_smul,smul_smul,hp,hm,add_smul,add_smul] at hx
  simp only [rootVector,errorVector,smul_add,smul_smul,Finset.sum_add_distrib]
  rw [← hx]
  simp only [Finset.sum_smul]
  abel

lemma rootVector_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) {n : ℂ} (hn : ‖n‖ = 1) :
    (∫ y, ‖rootVector N r h k q n y‖) ≤ 4*scalarMass h (scale r k) q := by
  calc
    _ ≤ (∫ y, ‖densityRoot N r (fun x => coordinate n 1 (h x)) k q y • axis n 1‖)+
      (∫ y, ‖densityRoot N r (fun x => coordinate n (-1) (h x)) k q y • axis n (-1)‖) :=
      by
        rw [← integral_add (root_vector_integrable hh r k q n 1).norm
          (root_vector_integrable hh r k q n (-1)).norm]
        exact integral_mono (rootVector_integrable hh r k q n).norm
          ((root_vector_integrable hh r k q n 1).norm.add
            (root_vector_integrable hh r k q n (-1)).norm) (fun y => norm_add_le _ _)
    _ ≤ 2*scalarMass h (scale r k) q+2*scalarMass h (scale r k) q :=
      add_le_add (root_bound hr hR hN hh hsupp k q hn (by norm_num))
        (root_bound hr hR hN hh hsupp k q hn (by norm_num))
    _ = _ := by ring

end PricePieces

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset

lemma rho_pos : 0 < rho := Real.rpow_pos_of_pos (by norm_num) _
lemma rho_lt_one : rho < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)

lemma scale_ratio {r : ℝ} (hr : 0 < r) {j k : ℕ} (hj : j ≤ k) :
    scale r j / scale r k = (1/2:ℝ)^(k-j) := by
  dsimp [scale]
  rw [mul_div_mul_right _ _ hr.ne']
  have hk : k = j+(k-j) := (Nat.add_sub_of_le hj).symm
  conv_lhs => rw [hk,pow_add]
  simp only [div_pow,one_pow]
  field_simp

lemma scale_discount {r : ℝ} (hr : 0 < r) {j k : ℕ} (hj : j ≤ k) :
    (scale r j / scale r k)^(1/100:ℝ) = rho^(k-j) := by
  rw [scale_ratio hr hj]
  unfold rho
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num),mul_comm ((k-j:ℕ):ℝ),
    Real.rpow_mul (by norm_num),Real.rpow_natCast]

lemma scalarPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ scalarPrice N r h rho k q := by
  apply sum_nonneg
  intro j _
  apply mul_nonneg (pow_nonneg rho_pos.le _)
  exact sum_nonneg (fun s _ => mul_nonneg (coeff_nonneg N (k-j) q s)
    (densityDefect_nonneg hr hR hN hh hsupp j s))

lemma rootPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ rootPrice N r h k q := by
  apply sum_nonneg
  intro n _
  exact add_nonneg
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)

lemma coordinate_total_le {h : ℂ → ℂ} (hh : Integrable h) {n : ℂ} (hn : ‖n‖ = 1)
    {s : ℝ} (hs : |s| ≤ 1) : (∫ x, |coordinate n s (h x)|) ≤ 2*(∫ x, ‖h x‖) := by
  rw [← integral_const_mul]
  exact integral_mono (scalar_integrable hh _).abs (hh.norm.const_mul 2)
    (fun x => coordinate_norm_le hn hs _)

lemma coordinate_price_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) {n : ℂ} (hn : ‖n‖ = 1)
    {s : ℝ} (hs : |s| ≤ 1) (m : ℕ) :
    (∑ k ∈ range (m+1), ∑ q : Grid N,
      scalarPrice N r (fun x => coordinate n s (h x)) rho k q) ≤
        (1-rho)⁻¹*(∫ x, ‖h x‖) := by
  apply (scalarPrice_budget hr hR hN (scalar_integrable hh _) (scalar_support hsupp _)
    rho_pos.le rho_lt_one m).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by linarith [rho_lt_one]))
  have he := coordinate_total_le hh hn hs
  linarith

/-- The genuine all-label root price has a uniform total budget, including
the terminal scalar splits at the finest scale. -/
theorem rootPrice_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) :
    (∑ k ∈ range (m+1), ∑ q : Grid N, rootPrice N r h k q) ≤
      (2*(fixedPalette.labels.card:ℝ)*(1-rho)⁻¹)*(∫ x, ‖h x‖) := by
  unfold rootPrice
  simp_rw [Finset.sum_comm (s := univ) (t := fixedPalette.labels)]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _n ∈ fixedPalette.labels, 2*((1-rho)⁻¹*(∫ x, ‖h x‖)) := by
      apply sum_le_sum
      intro n hn
      simp_rw [sum_add_distrib]
      have hp := coordinate_price_budget hr hR hN hh hsupp (fixedPalette.unit n hn)
        (by norm_num : |(1:ℝ)| ≤ 1) m
      have hm := coordinate_price_budget hr hR hN hh hsupp (fixedPalette.unit n hn)
        (by norm_num : |(-1:ℝ)| ≤ 1) m
      linarith
    _ = _ := by rw [sum_const,nsmul_eq_mul]; ring

end CommonPrices

namespace FiniteLabels
open DyadicHats
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spatialRow_mixture (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) (j : ι) :
    spatialRow old target p hp0 hp1 r x j =
      interpolate r (fun z => (1-p z)*delta old j+p z*delta (target z) j) x := by
  have he (z : ℤ × ℤ) : (1-p z)*delta old j+p z*delta (target z) j =
      delta old j+p z*(delta (target z) j-delta old j) := by ring
  simp_rw [he]
  rw [interpolate_add,interpolate_const]
  rfl

lemma spatialRow_vanish (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) (j : ι)
    (hj : ∀ z, hat r z x ≠ 0 → (1-p z)*delta old j+p z*delta (target z) j = 0) :
    spatialRow old target p hp0 hp1 r x j = 0 := by
  rw [spatialRow_mixture]
  have he : interpolate r (fun z => (1-p z)*delta old j+p z*delta (target z) j) x =
      interpolate r (fun _ => 0) x := interpolate_congr_on r x hj
  rw [he,interpolate_const]

end FiniteLabels

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats

lemma label_unit (n : Label) : ‖(n:ℂ)‖ = 1 := fixedPalette.unit n n.property

lemma target_close (h : ℂ → ℂ) (r : ℝ) (z : ℤ × ℤ) :
    ‖Theta h r z-(target h r z:ℂ)‖ < 1/2000 := quantize_close _ _

lemma nearby_sample_close {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (z : ℤ × ℤ) (hz : hat r z x ≠ 0) :
    ‖Theta h r z-theta h r q‖ ≤ 1/1000 := by
  have hloc : boxNorm (point r z-point r q) ≤ 200*r :=
    hat_vertex_local hr (by linarith) hz
  have he := energy_controls hr h q z hloc
  nlinarith [norm_nonneg (Theta h r z-theta h r q)]

lemma sampled_good {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (z : ℤ × ℤ) (hz : hat r z x ≠ 0) :
    Good (target h r z) (theta h r q) := by
  apply good_of_close (label_unit _)
  have he := nearby_sample_close hr h q hx hE z hz
  have ht := target_close h r z
  have hn : ‖theta h r q-(target h r z:ℂ)‖ ≤ ‖theta h r q-Theta h r z‖+‖Theta h r z-(target h r z:ℂ)‖ := by
    simpa only [dist_eq_norm] using dist_triangle (theta h r q) (Theta h r z) (target h r z:ℂ)
  have he' : ‖theta h r q-Theta h r z‖ ≤ 1/1000 := by simpa only [norm_sub_rev] using he
  linarith

lemma retained_good {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (z : ℤ × ℤ) (hz : hat r z x ≠ 0)
    (n : Label) (hp : switchChance h r n z < 1) : Good (n:ℂ) (theta h r q) := by
  have hd := (probability_lt_one_iff (by norm_num : (0:ℝ)<1/100)).mp hp
  have he := nearby_sample_close hr h q hx hE z hz
  apply good_of_close (label_unit n)
  have hn : ‖theta h r q-(n:ℂ)‖ ≤ ‖theta h r q-Theta h r z‖+‖Theta h r z-(n:ℂ)‖ := by
    simpa only [dist_eq_norm] using dist_triangle (theta h r q) (Theta h r z) (n:ℂ)
  have he' : ‖theta h r q-Theta h r z‖ ≤ 1/1000 := by simpa only [norm_sub_rev] using he
  have hd' : ‖Theta h r z-(n:ℂ)‖ < 2*(1/100:ℝ) := by simpa only [norm_sub_rev] using hd
  linarith

lemma initial_bad_zero {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (n : Label)
    (hn : ¬Good (n:ℂ) (theta h r q)) : initial h r x n = 0 := by
  apply spatialRow_vanish
  intro z hz
  have ht : n ≠ target h r z := fun ht => hn (ht ▸ sampled_good hr h q hx hE z hz)
  simp [delta,ht]

lemma row_bad_zero {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (old n : Label)
    (hn : ¬Good (n:ℂ) (theta h r q)) : row h r x old n = 0 := by
  apply spatialRow_vanish
  intro z hz
  have ht : n ≠ target h r z := fun ht => hn (ht ▸ sampled_good hr h q hx hE z hz)
  by_cases ho : n = old
  · subst n
    have hp : switchChance h r old z = 1 := le_antisymm (switchChance_le_one h r old z)
      (le_of_not_gt (fun hp => hn (retained_good hr h q hx hE z hz old hp)))
    simp [hp,delta,ht]
  · simp [delta,ho,ht]

theorem marginal_bad_zero (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (q : ℤ × ℤ) {x : ℂ} (hx : boxNorm (x-point (r k) q) ≤ 50*r k)
    (hE : energy h (r k) q ≤ (1/1000:ℝ)^2) (n : Label)
    (hn : ¬Good (n:ℂ) (theta h (r k) q)) : marginal h r k x n = 0 := by
  cases k with
  | zero => exact initial_bad_zero hr h q hx hE n hn
  | succ k =>
    simp only [marginal,move_apply,row_bad_zero hr h q hx hE _ n hn,mul_zero,Finset.sum_const_zero]

end ActualLabels

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_ActualMarkTrees1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

lemma sign_sq (b : Bool) : sign b^2 = 1 := by cases b <;> norm_num [sign]

lemma rootWeight_nonneg {N : ℕ} (S : Finset (Grid N)) (k j : ℕ) (s : Grid N) :
    0 ≤ rootWeight S k j s := sum_nonneg (fun q _ => coeff_nonneg N (k-j) q s)

lemma smallPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) (i : ErrorIndex N k) :
    (smallPiece hh hr k p S n i).mass ≤ (scale r k)⁻¹*2*
      (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1) := by
  rw [smallPiece,ErrorPiece.mass_weight _ (rootWeight_nonneg ..)]
  calc
    _ ≤ rootWeight S k i.1 i.2.1*((scale r k)⁻¹*
        (2*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) :=
      mul_le_mul_of_nonneg_left (errorPiece_mass hr hR hN hh hsupp k i.1
        (Nat.le_of_lt_succ i.1.isLt) p i.2.1 hn (sign_sq _)) (rootWeight_nonneg ..)
    _ = _ := by ring

lemma discounted_smallPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) (i : ErrorIndex N k) :
    (smallPiece hh hr k p S n i).size^(1/100:ℝ)*(smallPiece hh hr k p S n i).mass ≤
      (scale r k)⁻¹*2*(rho^(k-i.1)*
        (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) := by
  have hs : (smallPiece hh hr k p S n i).size^(1/100:ℝ) = rho^(k-i.1) :=
    scale_discount hr (Nat.le_of_lt_succ i.1.isLt)
  rw [hs]
  calc
    _ ≤ rho^(k-i.1)*((scale r k)⁻¹*2*
        (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) :=
      mul_le_mul_of_nonneg_left (smallPiece_mass hr hR hN hh hsupp k p S hn i) (pow_nonneg rho_pos.le _)
    _ = _ := by ring

lemma weighted_defect_sum {N : ℕ} (r : ℝ) (h : ℂ → ℝ) (k : ℕ) (S : Finset (Grid N)) :
    (∑ j : Fin (k+1), ∑ s : Grid N, rho^(k-j.val)*(rootWeight S k j s*densityDefect N r h j s)) =
      ∑ q ∈ S, scalarPrice N r h rho k q := by
  simp only [rootWeight,sum_mul,mul_sum]
  simp_rw [Finset.sum_comm (s := univ) (t := S)]
  apply sum_congr rfl
  intro q _
  unfold scalarPrice
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  rw [mul_sum]

lemma smallPiece_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) :
    errorPrice (smallPiece hh hr k p S n) (1/100) ≤ (scale r k)⁻¹*2*
      ∑ q ∈ S, (scalarPrice N r (fun x => coordinate n 1 (h x)) rho k q+
        scalarPrice N r (fun x => coordinate n (-1) (h x)) rho k q) := by
  apply (sum_le_sum (fun i _ => discounted_smallPiece_mass hr hR hN hh hsupp k p S hn i)).trans_eq
  rw [← mul_sum]
  congr 1
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,sign,Bool.false_eq_true,
    ite_false,ite_true,sum_add_distrib]
  rw [weighted_defect_sum,weighted_defect_sum,← sum_add_distrib]

lemma smallPiece_common_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : n ∈ fixedPalette.labels) :
    errorPrice (smallPiece hh hr k p S n) (1/100) ≤ (scale r k)⁻¹*2*cellPrice N r h k S := by
  apply (smallPiece_price hr hR hN hh hsupp k p S (fixedPalette.unit n hn)).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (inv_nonneg.mpr (scale_pos hr k).le) (by norm_num))
  apply sum_le_sum
  intro q _
  apply single_le_sum _ hn
  intro n _
  exact add_nonneg
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)

open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

lemma rootSum_partition {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) (y : ℂ) :
    rootSum h r k (goodRoots h r k S n) n y+rootSum h r k (badRoots h r k S n) n y = rootSum h r k S n y := by
  classical
  exact sum_filter_add_sum_filter_not S (fun q => Good n (DirectionNeighbors.theta h (scale r k) q)) _

lemma rootSum_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) :
    (∫ y, ‖rootSum h r k S n y‖) ≤ 4*∑ q ∈ S, scalarMass h (scale r k) q := by
  calc
    _ ≤ ∫ y, ∑ q ∈ S, ‖rootVector N r h k q n y‖ :=
      integral_mono (rootSum_integrable hh r k S n).norm
        (integrable_finsetSum S (fun _ _ => (rootVector_integrable hh r k _ n).norm))
        (fun y => norm_sum_le _ _)
    _ = ∑ q ∈ S, ∫ y, ‖rootVector N r h k q n y‖ :=
      integral_finsetSum S (fun _ _ => (rootVector_integrable hh r k _ n).norm)
    _ ≤ _ := by rw [mul_sum]; exact sum_le_sum (fun q _ => rootVector_mass hr hR hN hh hsupp k q hn)

lemma badPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) :
    (badPiece hr hh k p S n).mass ≤ (scale r k)⁻¹*4*badPrice h r k S n := by
  change (∫ X, ‖rescale p (scale r k) (rootSum h r k (badRoots h r k S n) n) X‖) ≤ _
  rw [mass_rescale _ _ (scale_pos hr k)]
  simpa only [mul_assoc,badPrice] using mul_le_mul_of_nonneg_left
    (rootSum_mass hr hR hN hh hsupp k (badRoots h r k S n) hn) (inv_nonneg.mpr (scale_pos hr k).le)

lemma cellErrors_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : n ∈ fixedPalette.labels) :
    errorPrice (cellErrors hr hh k p S n) (1/100) ≤
      (scale r k)⁻¹*(4*badPrice h r k S n+2*cellPrice N r h k S) := by
  simp only [errorPrice,Fintype.sum_option,cellErrors,show (badPiece hr hh k p S n).size = 1 from rfl,
    Real.one_rpow,one_mul]
  have h1 := badPiece_mass hr hR hN hh hsupp k p S (fixedPalette.unit n hn)
  have h2 := smallPiece_common_price hr hR hN hh hsupp k p S hn
  unfold errorPrice at h2
  linarith

open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

lemma smallPiece_pair_sum {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) (j : Fin (k+1)) (q : Grid N) (X : ℂ) :
    (∑ b : Bool, (smallPiece hh hr k p S n (j,q,b)).density X) =
      rootWeight S k j q • rescale p (scale r k) (errorVector N r h j q n) X := by
  simp only [Fintype.sum_bool,smallPiece,ErrorPiece.weight,errorPiece,sign,
    Bool.false_eq_true,ite_false,ite_true,rescale,errorVector]
  module

lemma smallPiece_sum {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) (X : ℂ) :
    (∑ i : ErrorIndex N k, (smallPiece hh hr k p S n i).density X) =
      rescale p (scale r k) (fun y => ∑ q ∈ S, ∑ j ∈ range (k+1),
        ∑ s : Grid N, coeff N (k-j) q s • errorVector N r h j s n y) X := by
  simp only [Fintype.sum_prod_type,smallPiece_pair_sum,rootWeight,sum_smul,rescale,smul_sum]
  simp_rw [Finset.sum_comm (s := univ) (t := S)]
  apply sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro s _
  module

/-- Exact cell decomposition before imposing the local partition-of-unity
region. Both its scalar coordinates and all error densities are the actual
finite dyadic construction. -/
theorem cell_decomposition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s = 1 ∨ s = -1) (X : ℂ) :
    (goodCone hr hR hN hh hsupp k p S hn hs).density X+
      (∑ i, (cellErrors hr hh k p S n i).density X) =
      rescale p (scale r k) (fun y => (∑ q ∈ S, hat (scale r k) q y) • h y) X := by
  rw [Fintype.sum_option]
  change rescale p (scale r k) (rootSum h r k (goodRoots h r k S n) n) X+
    (rescale p (scale r k) (rootSum h r k (badRoots h r k S n) n) X+
      ∑ i : ErrorIndex N k, (smallPiece hh hr k p S n i).density X) = _
  rw [smallPiece_sum]
  simp only [rescale,← smul_add,← add_assoc,rootSum_partition]
  rw [sum_smul]
  congr 1
  simp only [rootSum,← sum_add_distrib]
  exact sum_congr rfl (fun q _ => (vector_decomposition hr hR hN hsupp k q hn _).symm)

end CommonPrices

namespace DirectionNeighbors
open DyadicHats
lemma mem_window_comm (d : ℕ) (p q : ℤ × ℤ) : p ∈ window d q ↔ q ∈ window d p := by
  rw [mem_window_iff (by norm_num : (0:ℝ) < 1),mem_window_iff (by norm_num : (0:ℝ) < 1),boxNorm_sub_comm]

lemma card_window (d : ℕ) (q : ℤ × ℤ) : (window d q).card = (2*d+1)^2 := by
  change ((Finset.Icc (q.1-(d:ℤ)) (q.1+d)) ×ˢ
    (Finset.Icc (q.2-(d:ℤ)) (q.2+d))).card = _
  rw [Finset.card_product,Int.card_Icc,Int.card_Icc]
  have hq (z : ℤ) : (z+(d:ℤ)+1-(z-d)).toNat = 2*d+1 := by omega
  rw [hq,hq,pow_two]

end DirectionNeighbors

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_CommonPrices1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DirectionNeighbors

lemma cellPrice_spatial {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, cellPrice N r h k (cellRoots N p)) ≤ 1681*∑ q : Grid N, rootPrice N r h k q := by
  simp only [cellPrice,cellRoots,sum_filter]
  rw [Finset.sum_comm]
  rw [mul_sum]
  apply sum_le_sum
  intro q _
  have hn := rootPrice_nonneg hr hR hN hh hsupp k q
  have hs : P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p) ⊆ window 20 q := by
    intro p hp
    exact (mem_window_comm 20 _ _).mp (mem_filter.mp hp).2
  have hc : ((P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p)).card : ℝ) ≤ 1681 := by
    have hc := Finset.card_le_card hs
    rw [card_window] at hc
    exact_mod_cast hc
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hc hn

/-- The common geometric price has a genuine uniform spatial-and-scale
budget, including every desired finite set of observation cells. -/
theorem cellPrice_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) :
    (∑ k ∈ range (m+1), ∑ p ∈ P k, cellPrice N r h k (cellRoots N p)) ≤
      1681*((fixedPalette.labels.card:ℝ)*2/(1-rho))*(∫ y, ‖h y‖) := by
  calc
    _ ≤ ∑ k ∈ range (m+1), 1681*∑ q : Grid N, rootPrice N r h k q :=
      sum_le_sum (fun k _ => cellPrice_spatial hr hR hN hh hsupp k (P k))
    _ = 1681*(∑ k ∈ range (m+1), ∑ q : Grid N, rootPrice N r h k q) := by rw [mul_sum]
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_left (rootPrice_budget hr hR hN hh hsupp m) (by norm_num : (0:ℝ) ≤ 1681)
      have he : 1681*(2*(fixedPalette.labels.card:ℝ)*(1-rho)⁻¹*(∫ y, ‖h y‖)) =
          1681*((fixedPalette.labels.card:ℝ)*2/(1-rho))*(∫ y, ‖h y‖) := by ring
      exact ht.trans_eq he

end CommonPrices

namespace AffineDensities
lemma gradient_affine {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) (r : ℝ) (X : ℂ) :
    gradient (fun Y => g (p+r • Y)) X = rescale p r (gradient g) X := by
  have hA : HasFDerivAt (fun Y : ℂ => p+r • Y) (r • ContinuousLinearMap.id ℝ ℂ) X :=
    ((hasFDerivAt_id X).const_smul r).const_add p
  have hc := (hg (p+r • X)).hasFDerivAt.comp X hA
  change HasFDerivAt (fun Y => g (p+r • Y)) _ X at hc
  apply (InnerProductSpace.toDual ℝ ℂ).injective
  simp only [toDual_gradient,rescale,map_smul]
  rw [hc.fderiv]
  ext z
  simp
end AffineDensities

namespace DyadicHats
open Finset
lemma vector_partition_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (x : ℂ) :
    (∑ p : Grid N, hat r p x) • h x = h x := by
  by_cases hx : h x = 0
  · simp only [hx,smul_zero]
  · have he := density_partition_grid hr hN (h := fun y => ‖h y‖)
      (fun y hy => hs y (fun hh => hy (by rw [hh,norm_zero]))) x
    rw [← sum_mul] at he
    have hsum : (∑ p : Grid N, hat r p x) = 1 := by
      apply mul_right_cancel₀ (norm_ne_zero_iff.mpr hx)
      simpa only [one_mul] using he
    rw [hsum,one_smul]
end DyadicHats

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments

lemma hat_mem_cellRoots {N : ℕ} {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) (X : ℂ) (hX : ‖X‖ ≤ 12)
    (q : Grid N) (hq : hat r q (point r p+r • X) ≠ 0) : q ∈ cellRoots N p := by
  have hl := (hat_ne_zero_iff hr q (point r p+r • X)).mp hq
  have hnorm : boxNorm (r • X) ≤ 12*r := by
    apply (boxNorm_le_norm _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    nlinarith
  have hh := boxNorm_add_le (point r q-(point r p+r • X)) (r • X)
  rw [boxNorm_sub_comm (point r q)] at hh
  have hie : point r q-(point r p+r • X)+r • X = point r q-point r p := by abel
  rw [hie] at hh
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  rw [mem_window_iff hr 20]
  norm_num
  linarith

lemma cell_partition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hN : R/r+1 ≤ (N:ℝ))
    {h : ℂ → ℂ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (p : ℤ × ℤ) (X : ℂ) (hX : ‖X‖ ≤ 12) :
    (∑ q ∈ cellRoots N p, hat r q (point r p+r • X)) • h (point r p+r • X) = h (point r p+r • X) := by
  have he : (∑ q ∈ cellRoots N p, hat r q (point r p+r • X)) =
      ∑ q : Grid N, hat r q (point r p+r • X) := by
    apply sum_subset (subset_univ _)
    intro q _ hq
    by_contra hh
    exact hq (hat_mem_cellRoots hr p X hX q hh)
  rw [he]
  exact vector_partition_grid hr hN hs _

lemma cell_decomposition_gradient {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {g : ℂ → ℝ} (hg : Differentiable ℝ g)
    (hh : Integrable (gradient g)) (hsupp : ∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (p : ℤ × ℤ) {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (X : ℂ) (hX : ‖X‖ ≤ 12) :
    (goodCone hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn hs).density X+
      (∑ i, (cellErrors hr hh k (point (scale r k) p) (cellRoots N p) n i).density X) =
      gradient (fun Y => g (point (scale r k) p+scale r k • Y)) X := by
  rw [cell_decomposition hr hR hN hh hsupp k _ _ hn hs,gradient_affine hg]
  simp only [rescale]
  rw [cell_partition (scale_pos hr k) (scale_index_bound hr hR hN k) hsupp p X hX]

/-- The hard directional local price, instantiated with the actual common-price
cone decomposition on the actual neighboring grid roots. -/
theorem directional_cell_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ {s : ℝ}, (s = 1 ∨ s = -1) →
    ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ X in Q, F X) ≤ ENNReal.ofReal (C*(scale r k)⁻¹*
        (badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ X, ‖X‖ ≤ 2 → ∀ t,
        NeighborhoodRadius (fun Y => g (point (scale r k) p+scale r k • Y)) X t →
        ENNReal.ofReal (max 0 (-inner ℝ (axis n s)
          (∫ Y in Metric.ball X t, gradient (fun Z => g (point (scale r k) p+scale r k • Z)) Y))) ≤ F X := by
  obtain ⟨C,hC,hmajor⟩ := direction_majorant (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 1/2)
  refine ⟨4*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hsupp k p n hn s hs Q hQ
  have hnu := fixedPalette.unit n hn
  let a := goodCone hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hnu hs
  let b := cellErrors hr hh k (point (scale r k) p) (cellRoots N p) n
  have hg' : ContDiff ℝ 1 (fun Y => g (point (scale r k) p+scale r k • Y)) := hg.comp (by fun_prop)
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor a b (axis_norm hnu (by rcases hs with rfl | rfl <;> norm_num)) _ hg' Q hQ
  refine ⟨F,hFm,?_,?_⟩
  · apply hFi.trans
    apply ENNReal.ofReal_le_ofReal
    have hb := cellErrors_price hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn
    have hD : 0 ≤ cellPrice N r (gradient g) k (cellRoots N p) :=
      sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
    change errorPrice b (1/100) ≤ _ at hb
    have hrk := scale_pos hr k
    nlinarith [mul_le_mul_of_nonneg_left hb hC.le,inv_nonneg.mpr hrk.le,
      mul_nonneg (inv_nonneg.mpr hrk.le) hD]
  · intro X hX t ht
    apply hFb X _ t ht
    filter_upwards with Y hY
    apply cell_decomposition_gradient hr hR hN (hg.differentiable one_ne_zero) hh hsupp k p hnu hs
    have hy : ‖Y-X‖ < 3 := by simpa only [Metric.mem_ball,dist_eq_norm] using hY
    have htri := norm_add_le (Y-X) X
    rw [sub_add_cancel] at htri
    linarith

end CommonPrices

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_ActualLabels1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DyadicHats
lemma point_mem_neighborhood {r : ℝ} (hr : 0 ≤ r) (q : ℤ × ℤ) : point r q ∈ neighborhood r q := by
  change boxNorm (point r q-point r q) ≤ _
  simp only [sub_self,boxNorm]
  simpa using (mul_nonneg (by norm_num : (0:ℝ) ≤ 25) hr)
end DyadicHats

namespace DyadicHats
lemma localSup_le {f : ℂ → ℝ} {r A : ℝ} (hr : 0 ≤ r) (q : ℤ × ℤ)
    (h : ∀ x ∈ neighborhood r q, f x ≤ A) : localSup f r q ≤ A := by
  apply csSup_le (Set.Nonempty.image f ⟨point r q,point_mem_neighborhood hr q⟩)
  rintro z ⟨x,hx,rfl⟩
  exact h x hx
lemma le_localSup {f : ℂ → ℝ} {r A : ℝ} (q : ℤ × ℤ)
    (h : ∀ x ∈ neighborhood r q, f x ≤ A) {x : ℂ} (hx : x ∈ neighborhood r q) :
    f x ≤ localSup f r q := le_csSup ⟨A,by rintro z ⟨y,hy,rfl⟩; exact h y hy⟩ ⟨x,hx,rfl⟩
lemma localSup_nonneg {f : ℂ → ℝ} {r A : ℝ} (hr : 0 ≤ r) (q : ℤ × ℤ)
    (h0 : ∀ x, 0 ≤ f x) (h : ∀ x ∈ neighborhood r q, f x ≤ A) : 0 ≤ localSup f r q :=
  (h0 (point r q)).trans (le_localSup q h (point_mem_neighborhood hr q))
end DyadicHats

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskMaximalTools2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace AffineDensities
lemma fderiv_affine_bound {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) (r : ℝ)
    {D : ℝ} (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) :
    ∃ B : ℝ, ∀ X, ‖fderiv ℝ (fun Y => g (p+r • Y)) X‖ ≤ B := by
  refine ⟨D*|r|,?_⟩
  intro X
  have hA : HasFDerivAt (fun Y : ℂ => p+r • Y)
      (r • ContinuousLinearMap.id ℝ ℂ) X := by
    simpa using ((hasFDerivAt_id X).const_smul r).const_add p
  have hd := (hg (p+r • X)).hasFDerivAt.comp X hA
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_id, mul_one]
  exact mul_le_mul_of_nonneg_right (hD _) (abs_nonneg _)
end AffineDensities

namespace PhysicalCells
open MeasureTheory Set

lemma unitCell_measurable : MeasurableSet unitCell :=
  (Complex.measurable_re measurableSet_Ico).inter (Complex.measurable_im measurableSet_Ico)
lemma toUnit_continuous (p : ℂ) (r : ℝ) : Continuous (toUnit p r) := by unfold toUnit; fun_prop
lemma cell_measurable (p : ℂ) (r : ℝ) : MeasurableSet (cell p r) :=
  (toUnit_continuous p r).measurable unitCell_measurable
lemma volume_unitCell : volume unitCell = 1 := by
  have he := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet
  change volume unitCell = _ at he
  rw [he]
  change (volume.prod volume) (Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) = 1
  rw [Measure.prod_prod]
  norm_num
lemma norm_unitCell {X : ℂ} (hX : X ∈ unitCell) : ‖X‖ ≤ 2 := by
  have h := Complex.norm_le_abs_re_add_abs_im X
  rw [abs_of_nonneg hX.1.1,abs_of_nonneg hX.2.1] at h
  linarith [hX.1.2,hX.2.2]
lemma toUnit_affine (p : ℂ) {r : ℝ} (hr : r ≠ 0) (X : ℂ) : toUnit p r (p+r • X) = X := by
  simp [toUnit,hr]
lemma affine_toUnit (p : ℂ) {r : ℝ} (hr : r ≠ 0) (y : ℂ) : p+r • toUnit p r y = y := by
  simp [toUnit,hr]

lemma lintegral_smul (F : ℂ → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ X : ℂ, F (r • X)) = ENNReal.ofReal ((r^2)⁻¹)*(∫⁻ y, F y) := by
  have he := (lintegral_map_equiv (μ := volume) F
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr).unit).toMeasurableEquiv).symm
  change (∫⁻ X : ℂ, F (r • X)) = ∫⁻ y, F y ∂Measure.map (fun X : ℂ => r • X) volume at he
  rw [he,Measure.map_addHaar_smul volume hr,lintegral_smul_measure]
  simp only [Complex.finrank_real_complex,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)),smul_eq_mul]

lemma lintegral_toUnit (F : ℂ → ℝ≥0∞) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y : ℂ, F (toUnit p r y)) = ENNReal.ofReal (r^2)*(∫⁻ X, F X) := by
  calc
    (∫⁻ y : ℂ, F (r⁻¹ • (y-p))) = ∫⁻ y : ℂ, F (r⁻¹ • y) :=
      lintegral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun y : ℂ => F (r⁻¹ • y)) p
    _ = _ := by rw [lintegral_smul _ (inv_ne_zero hr),inv_pow,inv_inv]

/-- Exact physical-space change of variables, with the two-dimensional volume
factor and no integrability or measurability assumptions on the majorant. -/
lemma lintegral_cell (F : ℂ → ℝ≥0∞) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y in cell p r, F y) = ENNReal.ofReal (r^2)*∫⁻ X in unitCell, F (p+r • X) := by
  rw [← lintegral_indicator (cell_measurable p r),← lintegral_indicator unitCell_measurable]
  have he (y : ℂ) : (cell p r).indicator F y =
      unitCell.indicator (fun X => F (p+r • X)) (toUnit p r y) := by
    by_cases hy : y ∈ cell p r
    · rw [Set.indicator_of_mem hy,Set.indicator_of_mem (show toUnit p r y ∈ unitCell from hy),affine_toUnit p hr]
    · rw [Set.indicator_of_notMem hy,Set.indicator_of_notMem (show toUnit p r y ∉ unitCell from hy)]
  simp_rw [he]
  exact lintegral_toUnit _ p hr

lemma cell_majorant {F : ℂ → ℝ≥0∞} (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y in cell p r, F (toUnit p r y)) = ENNReal.ofReal (r^2)*∫⁻ X in unitCell, F X := by
  rw [lintegral_cell _ p hr]
  simp only [toUnit_affine p hr]
end PhysicalCells

namespace DiskMoments
lemma signedAverage_affine (g : ℂ → ℝ) (p X : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    signedAverage (fun Y => g (p+r • Y)) X t = signedAverage g (p+r • X) (r*t) := by
  rw [signedAverage_fixedDomain _ _ ht,signedAverage_fixedDomain _ _ (mul_pos hr ht)]
  congr 1
  apply setIntegral_congr_fun measurableSet_ball
  intro Z _
  change g (p+r • (X+t • Z)) = g (p+r • X+(r*t) • Z)
  congr 1
  rw [smul_add,smul_smul]
  abel

lemma gradient_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    gradient (fun y => signedAverage g y t) x =
      (Real.pi*t^2)⁻¹ • ∫ y in Metric.ball x t, gradient g y := by
  have hi : IntegrableOn (fun z : ℂ => fderiv ℝ g (x+t • z)) (Metric.ball 0 1) :=
    (((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0:ℂ) 1)).mono_set Metric.ball_subset_closedBall
  rw [gradient,(hasFDerivAt_signedAverage hg hD x ht).fderiv,map_smul]
  have he := (InnerProductSpace.toDual ℝ ℂ).symm.toContinuousLinearMap.integral_comp_comm hi
  change (∫ z in Metric.ball (0:ℂ) 1, (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ g (x+t • z))) =
    (InnerProductSpace.toDual ℝ ℂ).symm (∫ z in Metric.ball (0:ℂ) 1, fderiv ℝ g (x+t • z)) at he
  rw [← he]
  change (1/Real.pi) • (∫ z in Metric.ball (0:ℂ) 1, gradient g (x+t • z)) = _
  rw [integral_scale_ball (fun z => gradient g (x+z)) ht,integral_translate_ball,smul_smul]
  congr 1
  ring

lemma gradient_average_affine {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (p X : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    gradient (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) X =
      r • gradient (fun y => signedAverage g y (r*t)) (p+r • X) := by
  have he : (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) =
      (fun Y => signedAverage g (p+r • Y) (r*t)) := by
    funext Y
    exact signedAverage_affine g p Y hr ht
  rw [he]
  exact AffineDensities.gradient_affine (fun y =>
    (hasFDerivAt_signedAverage hg hD y (mul_pos hr ht)).differentiableAt) p r X

lemma neighborhoodRadius_affine {g : ℂ → ℝ} (p X : ℂ) {r t : ℝ} (hr : 0 < r)
    (ht : PhysicalNeighborhoodRadius g r (p+r • X) (r*t)) :
    NeighborhoodRadius (fun Y => g (p+r • Y)) X t := by
  have ht1 : 1 ≤ t := (le_of_mul_le_mul_left (by simpa only [mul_one] using ht.1.1) hr)
  have ht2 : t ≤ 2 := (le_of_mul_le_mul_left (by simpa only [mul_comm 2 r] using ht.1.2) hr)
  refine ⟨⟨ht1,ht2⟩,?_⟩
  intro s hs habs
  rw [signedAverage_affine _ _ _ hr hs,signedAverage_affine _ _ _ hr (by linarith)]
  apply ht.2 (r*s) (mul_pos hr hs)
  rw [← mul_sub,abs_mul,abs_of_pos hr]
  nlinarith

end DiskMoments

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_PhysicalCells1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace PhysicalCells
lemma derivative_majorant_integral {F : ℂ → ℝ≥0∞} {C P : ℝ} (p : ℂ) {r : ℝ}
    (hr : 0 < r) (hF : (∫⁻ X in unitCell, F X) ≤ ENNReal.ofReal (C*r⁻¹*P)) :
    (∫⁻ y in cell p r, ENNReal.ofReal r⁻¹*F (toUnit p r y)) ≤ ENNReal.ofReal (C*P) := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,cell_majorant p hr.ne']
  apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl hF)).trans_eq
  rw [← ENNReal.ofReal_mul (sq_nonneg r),← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  congr 1
  field_simp

end PhysicalCells

namespace DiskMoments

lemma average_gradient_negative_le {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x n : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    max 0 (-inner ℝ n (gradient (fun y => signedAverage g y t) x)) ≤
      max 0 (-inner ℝ n (∫ y in Metric.ball x t, gradient g y)) := by
  have hp : 0 < Real.pi*t^2 := mul_pos Real.pi_pos (sq_pos_of_pos (by linarith))
  have h1 : 1 ≤ Real.pi*t^2 := by nlinarith [Real.pi_gt_three,sq_nonneg (t-1)]
  rw [gradient_signedAverage hg hD x (by linarith),inner_smul_right,← mul_neg,
    ← mul_zero (Real.pi*t^2)⁻¹,← mul_max_of_nonneg _ _ (inv_nonneg.mpr hp.le)]
  simp only [mul_zero]
  exact mul_le_of_le_one_left (le_max_left _ _) ((inv_le_one₀ hp).mpr h1)

lemma physical_gradient_negative_majorant {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (p X n : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    {F : ℝ≥0∞}
    (hF : ENNReal.ofReal (max 0 (-inner ℝ n
      (gradient (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) X))) ≤ F) :
    ENNReal.ofReal (max 0 (-inner ℝ n (gradient (fun y => signedAverage g y (r*t)) (p+r • X)))) ≤
      ENNReal.ofReal r⁻¹*F := by
  have h : ENNReal.ofReal r⁻¹*_ ≤ ENNReal.ofReal r⁻¹*F := mul_le_mul' le_rfl hF
  rw [gradient_average_affine hg hD p X hr ht,inner_smul_right,← mul_neg,
    ← mul_zero r,← mul_max_of_nonneg _ _ hr.le,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),inv_mul_cancel_left₀ hr.ne'] at h
  simpa only [mul_zero] using h
end DiskMoments

namespace CommonPrices
open DyadicHats ConeCoordinates LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces PhysicalCells

theorem physical_directional_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ {s : ℝ}, (s = 1 ∨ s = -1) →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalNeighborhoodRadius g (scale r k) y t →
        ENNReal.ofReal (max 0 (-inner ℝ (axis n s) (gradient (fun z => signedAverage g z t) y))) ≤ F y := by
  obtain ⟨C,hC,hmajor⟩ := directional_cell_price
  refine ⟨C,hC,?_⟩
  intro N r R hr hR hN g hg hh hsupp hD k p n hn s hs
  obtain ⟨D,hD⟩ := hD
  obtain ⟨D',hD'⟩ := fderiv_affine_bound (hg.differentiable one_ne_zero) (point (scale r k) p) (scale r k) hD
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor hr hR hN hg hh hsupp k p hn hs unitCell (by rw [volume_unitCell]; norm_num)
  refine ⟨fun y => ENNReal.ofReal (scale r k)⁻¹*F (toUnit (point (scale r k) p) (scale r k) y),
    measurable_const.mul (hFm.comp (toUnit_continuous _ _).measurable),
    derivative_majorant_integral _ (scale_pos hr k) hFi,?_⟩
  intro y hy t ht
  let X := toUnit (point (scale r k) p) (scale r k) y
  have hX : ‖X‖ ≤ 2 := norm_unitCell hy
  have he : point (scale r k) p+scale r k • X = y := affine_toUnit _ (scale_pos hr k).ne' y
  have ht' : PhysicalNeighborhoodRadius g (scale r k)
      (point (scale r k) p+scale r k • X) (scale r k*(t/scale r k)) := by
    simpa only [he,mul_div_cancel₀ _ (scale_pos hr k).ne'] using ht
  have htn := neighborhoodRadius_affine _ X (scale_pos hr k) ht'
  have hg' : ContDiff ℝ 1 (fun Z => g (point (scale r k) p+scale r k • Z)) := hg.comp (by fun_prop)
  have hb := (ENNReal.ofReal_le_ofReal (average_gradient_negative_le hg' hD' X (axis n s) htn.1.1)).trans
    (hFb X hX _ htn)
  have hf := physical_gradient_negative_majorant hg hD (point (scale r k) p) X (axis n s)
    (scale_pos hr k) (by linarith [htn.1.1]) hb
  simpa only [he,mul_div_cancel₀ _ (scale_pos hr k).ne'] using hf

end CommonPrices

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_SignedRuns1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace ActualLabels
open FiniteLabels SignedAssembly Finset ConeCoordinates

lemma observation_lipschitz (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (n j : Label) : LipschitzWith (Real.toNNReal (16/r k)) (fun x => observation h r k x n j) := by
  cases k with
  | zero =>
    simpa only [mul_one,observation,initial,row] using spatialRow_component_lipschitz (quantize 1 (by norm_num))
      (target h (r 0)) (fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl) hr
      (by norm_num : (0:ℝ) ≤ 1) (fun _ => le_rfl) j
  | succ k =>
    simpa only [mul_one,observation,initial,row] using spatialRow_component_lipschitz n (target h (r (k+1)))
      (switchChance h (r (k+1)) n) (switchChance_nonneg h (r (k+1)) n)
      (switchChance_le_one h (r (k+1)) n) hr (by norm_num : (0:ℝ) ≤ 1)
      (switchChance_le_one h (r (k+1)) n) j

end ActualLabels

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_SignedRuns2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace PhysicalCells
open DyadicHats DirectionNeighbors CommonPrices Finset

lemma toUnit_point_re (r : ℝ) (hr : r ≠ 0) (p : ℤ × ℤ) (y : ℂ) :
    (toUnit (point r p) r y).re = y.re/r-p.1 := by
  simp only [toUnit,Complex.smul_re,Complex.sub_re,point,smul_eq_mul]
  field_simp

lemma toUnit_point_im (r : ℝ) (hr : r ≠ 0) (p : ℤ × ℤ) (y : ℂ) :
    (toUnit (point r p) r y).im = y.im/r-p.2 := by
  simp only [toUnit,Complex.smul_im,Complex.sub_im,point,smul_eq_mul]
  field_simp

lemma mem_index_cell {r : ℝ} (hr : 0 < r) (y : ℂ) :
    y ∈ cell (point r (gridIndex r y)) r := by
  change (toUnit _ r y).re ∈ Set.Ico (0:ℝ) 1 ∧ (toUnit _ r y).im ∈ Set.Ico (0:ℝ) 1
  rw [toUnit_point_re r hr.ne',toUnit_point_im r hr.ne']
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact sub_nonneg.mpr (Int.floor_le _)
  · dsimp only [gridIndex]; linarith [Int.lt_floor_add_one (y.re/r)]
  · exact sub_nonneg.mpr (Int.floor_le _)
  · dsimp only [gridIndex]; linarith [Int.lt_floor_add_one (y.im/r)]

lemma mem_cell_box {r : ℝ} (hr : 0 < r) {p : ℤ × ℤ} {y : ℂ}
    (hy : y ∈ cell (point r p) r) : boxNorm (y-point r p) ≤ r := by
  change (toUnit _ r y).re ∈ Set.Ico (0:ℝ) 1 ∧ (toUnit _ r y).im ∈ Set.Ico (0:ℝ) 1 at hy
  rw [toUnit_point_re r hr.ne',toUnit_point_im r hr.ne'] at hy
  have h (a : ℝ) (b : ℤ) (hab : a/r-b ∈ Set.Ico (0:ℝ) 1) : |a-r*b| ≤ r := by
    have hl : (b:ℝ) ≤ a/r := by linarith [hab.1]
    have hu : a/r < (b:ℝ)+1 := by linarith [hab.2]
    have hl' := (le_div_iff₀ hr).mp hl
    have hu' := (div_lt_iff₀ hr).mp hu
    apply abs_le.mpr
    constructor <;> nlinarith
  exact max_le (h y.re p.1 hy.1) (h y.im p.2 hy.2)

lemma tsum_ofReal_le {ι : Type*} (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (A : ℝ)
    (hbudget : ∀ s : Finset ι, ∑ i ∈ s, B i ≤ A) :
    (∑' i, ENNReal.ofReal (B i)) ≤ ENNReal.ofReal A := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hB i)]
  exact ENNReal.ofReal_le_ofReal (hbudget s)

end PhysicalCells

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_CommonPrices2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats DirectionNeighbors Finset ConeCoordinates

lemma cellRoots_budget {N : ℕ} (B : Grid N → ℝ) (hB : ∀ q, 0 ≤ B q)
    (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, ∑ q ∈ cellRoots N p, B q) ≤ 1681*∑ q, B q := by
  simp only [cellRoots,sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply sum_le_sum
  intro q _
  have hs : P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p) ⊆ window 20 q := by
    intro p hp
    exact (mem_window_comm 20 _ _).mp (mem_filter.mp hp).2
  have hc : ((P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p)).card : ℝ) ≤ 1681 := by
    have hc := Finset.card_le_card hs
    rw [card_window] at hc
    exact_mod_cast hc
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hc (hB q)

lemma badPrice_nonneg {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) :
    0 ≤ badPrice h r k S n := sum_nonneg (fun _ _ => norm_nonneg _)

lemma badPrice_le_rootMass {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) :
    badPrice h r k S n ≤ rootMass h r k S := by
  classical
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => norm_nonneg _)
end CommonPrices

namespace ActualLabels
open DyadicHats DirectionNeighbors FiniteLabels CommonPrices ConeCoordinates Finset

lemma marginal_localSup_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (n : Label) : 0 ≤ localSup (fun x => marginal h r k x n) (r k) p :=
  localSup_nonneg hr.le p (fun x => (marginal h r k x).nonneg n) (fun _ _ => law_le_one _ _)

lemma marginal_localSup_le_one (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (n : Label) : localSup (fun x => marginal h r k x n) (r k) p ≤ 1 :=
  localSup_le hr.le p (fun _ _ => law_le_one _ _)

lemma marginal_localSup_bad_zero {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (q : Grid N) (hq : q ∈ cellRoots N p)
    (hE : energy h (r k) q ≤ (1/1000:ℝ)^2) (n : Label)
    (hn : ¬Good (n:ℂ) (theta h (r k) q)) : localSup (fun x => marginal h r k x n) (r k) p = 0 := by
  apply le_antisymm _ (marginal_localSup_nonneg h r k hr p n)
  apply localSup_le hr.le p
  intro y hy
  have hqp : boxNorm (point (r k) p-point (r k) q) ≤ 20*r k := by
    rw [boxNorm_sub_comm]
    exact (mem_window_iff hr 20 p q).mp (mem_filter.mp hq).2
  have hb := boxNorm_add_le (y-point (r k) p) (point (r k) p-point (r k) q)
  rw [sub_add_sub_cancel] at hb
  have hy' : boxNorm (y-point (r k) p) ≤ 25*r k := hy
  rw [marginal_bad_zero h r k hr q (by linarith) hE n hn]

/-- The actual bad-root charge is paid by geometric energy, not a separately
assumed probability budget. -/
lemma marginal_badPrice_bound {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (base : ℝ)
    (k j : ℕ) (hr : 0 < r k) (hrj : r k = scale base j) (p : ℤ × ℤ) (n : Label) :
    localSup (fun x => marginal h r k x n) (r k) p*badPrice h base j (cellRoots N p) n ≤
      1000000*∑ q ∈ cellRoots N p, scalarMass h (r k) q*energy h (r k) q := by
  classical
  have hp0 := marginal_localSup_nonneg h r k hr p n
  have hp1 := marginal_localSup_le_one h r k hr p n
  unfold badPrice
  rw [mul_sum]
  calc
    _ ≤ ∑ q ∈ badRoots h base j (cellRoots N p) n,
        1000000*(scalarMass h (r k) q*energy h (r k) q) := by
      apply sum_le_sum
      intro q hq
      have hqp := (mem_filter.mp hq).1
      have hbad : ¬Good (n:ℂ) (theta h (r k) q) := by
        simpa only [hrj] using (mem_filter.mp hq).2
      rw [← hrj]
      by_cases hE : energy h (r k) q ≤ (1/1000:ℝ)^2
      · rw [marginal_localSup_bad_zero h r k hr p q hqp hE n hbad,zero_mul]
        exact mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _))
      · have he : 1 ≤ 1000000*energy h (r k) q := by norm_num at hE; linarith
        have hb := mul_le_mul_of_nonneg_right hp1 (norm_nonneg (vectorMass h (r k) q))
        have hc := mul_le_mul_of_nonneg_right he (norm_nonneg (vectorMass h (r k) q))
        dsimp only [scalarMass] at ⊢
        nlinarith
    _ ≤ _ := by
      rw [mul_sum]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ =>
        mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _)))
end ActualLabels

namespace PhysicalCells
open DyadicHats Finset

lemma patch_measurable (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p)) :
    Measurable (patch r F) :=
  Measurable.tsum (fun p => (hF p).indicator (cell_measurable _ _))

lemma le_patch (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (p : ℤ × ℤ) {x : ℂ}
    (hx : x ∈ cell (point r p) r) : F p x ≤ patch r F x := by
  have he := ENNReal.le_tsum (f := fun q => (cell (point r q) r).indicator (F q) x) p
  simpa only [patch,Set.indicator_of_mem hx] using he

lemma lintegral_patch (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p)) :
    (∫⁻ x, patch r F x) = ∑' p, ∫⁻ x in cell (point r p) r, F p x := by
  simp only [patch]
  rw [lintegral_tsum (f := fun p x => (cell (point r p) r).indicator (F p) x) (fun p => ((hF p).indicator (cell_measurable _ _)).aemeasurable)]
  simp_rw [lintegral_indicator (cell_measurable _ _)]

lemma lintegral_patch_budget (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    (B : (ℤ × ℤ) → ℝ) (hB : ∀ p, 0 ≤ B p) (A : ℝ)
    (hcell : ∀ p, (∫⁻ x in cell (point r p) r, F p x) ≤ ENNReal.ofReal (B p))
    (hbudget : ∀ P : Finset (ℤ × ℤ), ∑ p ∈ P, B p ≤ A) :
    (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A := by
  rw [lintegral_patch r F hF]
  exact (ENNReal.tsum_le_tsum hcell).trans (tsum_ofReal_le B hB A hbudget)

lemma patch_finite (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    {A : ℝ} (hi : (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A) :
    ∀ᵐ x, patch r F x ≠ ⊤ := by
  exact (ae_lt_top (patch_measurable r F hF) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi)).mono
    (fun _ hx => hx.ne)

lemma patch_integrable (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    {A : ℝ} (hi : (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A) :
    Integrable (fun x => (patch r F x).toReal) :=
  integrable_toReal_of_lintegral_ne_top (patch_measurable r F hF).aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi)

lemma real_le_patch {r : ℝ} (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (p : ℤ × ℤ) {x : ℂ}
    (hx : x ∈ cell (point r p) r) (hf : patch r F x ≠ ⊤) {a : ℝ}
    (hb : ENNReal.ofReal a ≤ F p x) : a ≤ (patch r F x).toReal := by
  exact (le_max_left a 0).trans (by
    rw [← ENNReal.toReal_ofReal']
    exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hf).mpr (hb.trans (le_patch r F p hx)))

/-- Take the cell supremum of a weight only after the local price has been
proved. This bounds all three spatial budgets by the corresponding local prices. -/
lemma weighted_patch_bound (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    (W : ℂ → ℝ≥0∞) (hW : Measurable W) (A B : (ℤ × ℤ) → ℝ)
    (hA : ∀ p, 0 ≤ A p) (_hB : ∀ p, 0 ≤ B p)
    (hcell : ∀ p, (∫⁻ x in cell (point r p) r, F p x) ≤ ENNReal.ofReal (B p))
    (hWB : ∀ p x, x ∈ cell (point r p) r → W x ≤ ENNReal.ofReal (A p)) :
    (∫⁻ x, W x*patch r F x) ≤ ∑' p, ENNReal.ofReal (A p*B p) := by
  simp only [patch,← ENNReal.tsum_mul_left]
  rw [lintegral_tsum (f := fun p x => W x*(cell (point r p) r).indicator (F p) x) (fun p => (hW.mul ((hF p).indicator (cell_measurable _ _))).aemeasurable)]
  apply ENNReal.tsum_le_tsum
  intro p
  have he : (fun x => W x*(cell (point r p) r).indicator (F p) x) =
      (cell (point r p) r).indicator (fun x => W x*F p x) := by
    funext x
    by_cases hx : x ∈ cell (point r p) r <;> simp [hx]
  rw [he,lintegral_indicator (cell_measurable _ _)]
  calc
    _ ≤ ∫⁻ x in cell (point r p) r, ENNReal.ofReal (A p)*F p x := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (cell_measurable (point r p) r)] with x hx
      exact mul_le_mul' (hWB p x hx) le_rfl
    _ = ENNReal.ofReal (A p)*(∫⁻ x in cell (point r p) r, F p x) :=
      lintegral_const_mul _ (hF p)
    _ ≤ ENNReal.ofReal (A p)*ENNReal.ofReal (B p) := mul_le_mul' le_rfl (hcell p)
    _ = _ := (ENNReal.ofReal_mul (hA p)).symm
end PhysicalCells

namespace ActualLabels
open DyadicHats FiniteLabels GeometricFilter Finset

lemma geometricRadii_pos {base : ℝ} (hb : 0 < base) (m k : ℕ) :
    0 < geometricRadii base m k := div_pos (scale_pos hb m) (by positivity)
lemma geometricRadii_eq (base : ℝ) {m k : ℕ} (hk : k ≤ m) :
    geometricRadii base m k = scale base (m-k) := by
  unfold geometricRadii scale
  rw [show m = (m-k)+k by omega,pow_add]
  field_simp
  rw [show m-k+k-k = m-k by omega]
  ring

end ActualLabels

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_CommonPrices3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates Finset

lemma priceConstant_nonneg : 0 ≤ priceConstant := by
  unfold priceConstant
  exact mul_nonneg (by norm_num) (div_nonneg (by positivity) (by linarith [rho_lt_one]))
lemma cellPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (S : Finset (Grid N)) :
    0 ≤ cellPrice N r h k S := sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
lemma rootMass_cell_budget {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ)
    (k : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, rootMass h r k (cellRoots N p)) ≤ 1681*(∫ y, ‖h y‖) := by
  exact (cellRoots_budget _ (fun q => norm_nonneg (vectorMass h (scale r k) q)) P).trans
    (mul_le_mul_of_nonneg_left (sum_scalarMass_grid_le hh _) (by norm_num))
end CommonPrices

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells CommonPrices DirectionNeighbors FiniteLabels Finset ActualMarkTrees

lemma geometricRadii_reverse (base : ℝ) {m j : ℕ} (hj : j ≤ m) :
    geometricRadii base m (m-j) = scale base j := by
  rw [geometricRadii_eq base (Nat.sub_le m j),Nat.sub_sub_self hj]

lemma marginal_bad_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) (n : Label) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p*
        badPrice h base j (cellRoots N p) n) ≤
      (1000000*1681*(576*(4097:ℝ)^2))*(∫ y, ‖h y‖) := by
  calc
    _ ≤ ∑ j ∈ range (m+1), 1000000*1681*∑ q : Grid N,
        scalarMass h (scale base j) q*energy h (scale base j) q := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      calc
        _ ≤ ∑ p ∈ P j, 1000000*∑ q ∈ cellRoots N p,
            scalarMass h (scale base j) q*energy h (scale base j) q := by
          apply sum_le_sum
          intro p _
          have ht := marginal_badPrice_bound (N := N) h (geometricRadii base m) base (m-j) j
            (geometricRadii_pos hb m (m-j)) (geometricRadii_reverse base hjm) p n
          simpa only [geometricRadii_reverse base hjm] using ht
        _ ≤ _ := by
          rw [← mul_sum,mul_assoc]
          exact mul_le_mul_of_nonneg_left (cellRoots_budget _
            (fun q => mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _)) (P j)) (by norm_num)
    _ ≤ _ := by
      rw [← mul_sum]
      have ht := mul_le_mul_of_nonneg_left (neighbor_energy_budget hb hR hN hh hsupp (m+1))
        (by norm_num : (0:ℝ) ≤ 1000000*1681)
      nlinarith only [ht]

lemma marginal_price_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) (n : Label) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p*
        cellPrice N base h j (cellRoots N p)) ≤ priceConstant*(∫ y, ‖h y‖) := by
  apply le_trans _ (cellPrice_budget hb hR hN hh hsupp m P)
  apply sum_le_sum
  intro j hj
  have hjm : j ≤ m := by have := mem_range.mp hj; omega
  apply sum_le_sum
  intro p _
  have hbnd : localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p ≤ 1 := by
    rw [← geometricRadii_reverse base hjm]
    exact marginal_localSup_le_one h _ (m-j) (geometricRadii_pos hb m (m-j)) p n
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hbnd (cellPrice_nonneg hb hR hN hh hsupp j _)

open DyadicHats PhysicalCells CommonPrices ActualMarkTrees Finset FiniteLabels

lemma directPriceConstant_pos : 0 < directPriceConstant := by
  unfold directPriceConstant
  have := priceConstant_nonneg
  positivity

lemma marginal_total_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) (n : Label) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p*
        (badPrice h base j (cellRoots N p) n+cellPrice N base h j (cellRoots N p))) ≤
      directPriceConstant*(∫ y, ‖h y‖) := by
  simp only [mul_add,sum_add_distrib]
  have h1 := marginal_bad_budget hb hR hN hh hsupp m P n
  have h2 := marginal_price_budget hb hR hN hh hsupp m P n
  unfold directPriceConstant
  nlinarith only [h1,h2]
end ActualLabels

namespace CommonPrices
open DyadicHats Finset
lemma cellPrice_level_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (j : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, cellPrice N base h j (cellRoots N p)) ≤ priceConstant*(∫ y, ‖h y‖) := by
  have hi := single_le_sum (s := range (j+1))
    (f := fun k => ∑ p ∈ P, cellPrice N base h k (cellRoots N p))
    (fun k _ => sum_nonneg (fun p _ => cellPrice_nonneg hb hR hN hh hsupp k _))
    (by simp : j ∈ range (j+1))
  exact hi.trans (cellPrice_budget hb hR hN hh hsupp j (fun _ => P))

lemma total_level_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (j : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, (rootMass h base j (cellRoots N p)+cellPrice N base h j (cellRoots N p))) ≤
      (1681+priceConstant)*(∫ y, ‖h y‖) := by
  rw [sum_add_distrib,add_mul]
  exact add_le_add (rootMass_cell_budget hh base j P) (cellPrice_level_budget hb hR hN hh hsupp j P)
end CommonPrices

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells FiniteLabels Finset

lemma marginal_continuous (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (k : ℕ) (n : Label) :
    Continuous (fun x => marginal h r k x n) := by
  induction k generalizing n with
  | zero => exact (observation_lipschitz h r 0 (hr 0) n n).continuous
  | succ k ih =>
    change Continuous (fun x => ∑ j : Label, marginal h r k x j*row h (r (k+1)) x j n)
    apply continuous_finsetSum
    intro j _
    exact (ih j).mul (observation_lipschitz h r (k+1) (hr (k+1)) j n).continuous

end ActualLabels

namespace PhysicalCells
open Finset
lemma sum_tsum_ofReal_le {ι κ : Type*} (s : Finset ι) (B : ι → κ → ℝ)
    (hB : ∀ i ∈ s, ∀ p, 0 ≤ B i p) (A : ℝ)
    (hbudget : ∀ P : Finset κ, ∑ i ∈ s, ∑ p ∈ P, B i p ≤ A) :
    (∑ i ∈ s, ∑' p, ENNReal.ofReal (B i p)) ≤ ENNReal.ofReal A := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => hB i hi _)]
  apply tsum_ofReal_le _ (fun p => sum_nonneg (fun i hi => hB i hi p))
  intro P
  rw [Finset.sum_comm]
  exact hbudget P

lemma integrated_weighted_patches {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (F : ι → (ℤ × ℤ) → ℂ → ℝ≥0∞)
    (hF : ∀ i ∈ s, ∀ p, Measurable (F i p))
    (W : ι → ℂ → ℝ≥0∞) (hW : ∀ i ∈ s, Measurable (W i))
    (A B : ι → (ℤ × ℤ) → ℝ) (hA : ∀ i ∈ s, ∀ p, 0 ≤ A i p)
    (hB : ∀ i ∈ s, ∀ p, 0 ≤ B i p)
    (hcell : ∀ i ∈ s, ∀ p, (∫⁻ x in cell (DyadicHats.point (r i) p) (r i), F i p x) ≤ ENNReal.ofReal (B i p))
    (hWB : ∀ i ∈ s, ∀ p x, x ∈ cell (DyadicHats.point (r i) p) (r i) → W i x ≤ ENNReal.ofReal (A i p))
    (C : ℝ) (hbudget : ∀ P : Finset (ℤ × ℤ), ∑ i ∈ s, ∑ p ∈ P, A i p*B i p ≤ C) :
    (∑ i ∈ s, ∫⁻ x, W i x*patch (r i) (F i) x) ≤ ENNReal.ofReal C := by
  apply le_trans (sum_le_sum (fun i hi => weighted_patch_bound (r i) (F i) (hF i hi)
    (W i) (hW i hi) (A i) (B i) (hA i hi) (hB i hi) (hcell i hi) (hWB i hi)))
  exact sum_tsum_ofReal_le s _ (fun i hi p => mul_nonneg (hA i hi p) (hB i hi p)) C hbudget
end PhysicalCells

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_CommonPrices4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

/-- Combine the two actual signed directional prices; the labels are unchanged. -/
theorem physical_unfavorable_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ) (n : Label),
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalNeighborhoodRadius g (scale r k) y t →
        ENNReal.ofReal (unfavorable n (gradient (fun z => signedAverage g z t) y)) ≤ F y := by
  obtain ⟨C,hC,hp⟩ := physical_directional_price
  refine ⟨2*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hs hd k p n
  obtain ⟨F,hFm,hFi,hFb⟩ := hp hr hR hN hg hh hs hd k p n.property (Or.inl rfl : (1:ℝ)=1 ∨ (1:ℝ)=-1)
  obtain ⟨G,hGm,hGi,hGb⟩ := hp hr hR hN hg hh hs hd k p n.property (Or.inr rfl : (-1:ℝ)=1 ∨ (-1:ℝ)=-1)
  have hn : 0 ≤ C*(badPrice (gradient g) r k (cellRoots N p) n+cellPrice N r (gradient g) k (cellRoots N p)) :=
    mul_nonneg hC.le (add_nonneg (badPrice_nonneg _ _ _ _ _) (cellPrice_nonneg hr hR hN hh hs k _))
  refine ⟨fun y => F y+G y,hFm.add hGm,?_,?_⟩
  · rw [lintegral_add_left hFm]
    calc
      _ ≤ ENNReal.ofReal (C*(_+_))+ENNReal.ofReal (C*(_+_)) := add_le_add hFi hGi
      _ = _ := by rw [← ENNReal.ofReal_add hn hn]; congr 1; ring
  · intro y hy t ht
    rw [unfavorable,ENNReal.ofReal_add (le_max_left _ _) (le_max_left _ _)]
    exact add_le_add (hFb y hy t ht) (hGb y hy t ht)

end CommonPrices

namespace PhysicalCells
open Finset

lemma real_weighted_patches {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (F : ι → (ℤ × ℤ) → ℂ → ℝ≥0∞)
    (hFi : ∀ i ∈ s, Integrable (fun x => (patch (r i) (F i) x).toReal))
    (W : ι → ℂ → ℝ) (hW : ∀ i ∈ s, Measurable (W i))
    (hW0 : ∀ i ∈ s, ∀ x, 0 ≤ W i x) (M : ℝ)
    (hWM : ∀ i ∈ s, ∀ x, W i x ≤ M) {C : ℝ} (hC : 0 ≤ C)
    (hf : (∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (W i x)*patch (r i) (F i) x) ≤ ENNReal.ofReal C) :
    (∑ i ∈ s, ∫ x, W i x*(patch (r i) (F i) x).toReal) ≤ C := by
  have hi (i : ι) (hi : i ∈ s) : Integrable (fun x => W i x*(patch (r i) (F i) x).toReal) := by
    apply (hFi i hi).bdd_mul (hW i hi).aestronglyMeasurable
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hW0 i hi x)]; exact hWM i hi x)
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => integral_nonneg (fun x => mul_nonneg (hW0 i hi x) ENNReal.toReal_nonneg))]
  apply le_trans _ hf
  apply sum_le_sum
  intro i his
  rw [ofReal_integral_eq_lintegral_ofReal (hi i his) (ae_of_all _ (fun x => mul_nonneg (hW0 i his x) ENNReal.toReal_nonneg))]
  apply lintegral_mono
  intro x
  change ENNReal.ofReal (W i x * (patch (r i) (F i) x).toReal) ≤ ENNReal.ofReal (W i x) * patch (r i) (F i) x
  rw [ENNReal.ofReal_mul (hW0 i his x)]
  exact mul_le_mul' le_rfl ENNReal.ofReal_toReal_le
end PhysicalCells

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

lemma bad_total_level_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (j : ℕ) (P : Finset (ℤ × ℤ)) (n : Label) :
    (∑ p ∈ P, (badPrice h base j (cellRoots N p) n+cellPrice N base h j (cellRoots N p))) ≤
      (1681+priceConstant)*(∫ y, ‖h y‖) := by
  apply le_trans _ (total_level_budget hb hR hN hh hsupp j P)
  apply sum_le_sum
  intro p hp
  exact add_le_add (badPrice_le_rootMass h base j (cellRoots N p) n) le_rfl

/-- Actual full-lattice unfavorable prices, with the genuine marginal law. -/
theorem patched_unfavorable_oai : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R) (hN : R/base+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    ∃ H : ℕ → Label → ℂ → ℝ,
      (∀ j n x, 0 ≤ H j n x) ∧ (∀ j n, Integrable (H j n)) ∧
      (∀ᵐ x, ∀ j n t, PhysicalNeighborhoodRadius g (scale base j) x t →
        unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H j n x) ∧
      (∀ m n, (∑ j ∈ range (m+1), ∫ x, marginal (gradient g) (geometricRadii base m) (m-j) x n*H j n x) ≤
        C*(∫ y, ‖gradient g y‖)) := by
  obtain ⟨c,hc,hp⟩ := physical_unfavorable_price
  refine ⟨c*directPriceConstant,mul_pos hc directPriceConstant_pos,?_⟩
  intro N base R hb hR hN g hg hh hs hd
  choose F hFm hFi hFb using fun j n p => hp hb hR hN hg hh hs hd j p n
  let B := fun j p n => badPrice (gradient g) base j (cellRoots N p) n+cellPrice N base (gradient g) j (cellRoots N p)
  have hB (j p n) : 0 ≤ B j p n := add_nonneg (badPrice_nonneg _ _ _ _ _) (cellPrice_nonneg hb hR hN hh hs j _)
  have hpi (j n) : (∫⁻ x, patch (scale base j) (F j n) x) ≤
      ENNReal.ofReal (c*((1681+priceConstant)*(∫ y, ‖gradient g y‖))) := by
    apply lintegral_patch_budget _ _ (hFm j n) (fun p => c*B j p n) (fun p => mul_nonneg hc.le (hB j p n)) _ (hFi j n)
    intro P
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (bad_total_level_budget hb hR hN hh hs j P n) hc.le
  let H := fun j n x => (patch (scale base j) (F j n) x).toReal
  have hHi (j n) : Integrable (H j n) := patch_integrable _ _ (hFm j n) (hpi j n)
  refine ⟨H,fun _ _ _ => ENNReal.toReal_nonneg,hHi,?_,?_⟩
  · have hfin : ∀ᵐ x, ∀ j n, patch (scale base j) (F j n) x ≠ ⊤ :=
      (ae_all_iff).mpr (fun j => (ae_all_iff).mpr (fun n => patch_finite _ _ (hFm j n) (hpi j n)))
    filter_upwards [hfin] with x hx
    intro j n t ht
    exact real_le_patch (F j n) (gridIndex (scale base j) x) (mem_index_cell (scale_pos hb j) x) (hx j n)
      (hFb j n _ x (mem_index_cell (scale_pos hb j) x) t ht)
  · intro m n
    let W := fun j x => marginal (gradient g) (geometricRadii base m) (m-j) x n
    let A := fun j p => localSup (W j) (scale base j) p
    have hA (j) (hj : j ∈ range (m+1)) (p) : 0 ≤ A j p := by
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      dsimp [A,W]
      rw [← geometricRadii_reverse base hjm]
      exact marginal_localSup_nonneg _ _ _ (geometricRadii_pos hb m (m-j)) p n
    have hwm (j) : Measurable (W j) := (marginal_continuous _ _ (geometricRadii_pos hb m) (m-j) n).measurable
    have hWB (j) (hj : j ∈ range (m+1)) (p x) (hx : x ∈ cell (point (scale base j) p) (scale base j)) :
        ENNReal.ofReal (W j x) ≤ ENNReal.ofReal (A j p) := by
      apply ENNReal.ofReal_le_ofReal
      apply le_localSup p (fun y _ => law_le_one _ _)
      change DyadicHats.boxNorm (x-point (scale base j) p) ≤ 25*scale base j
      have ht := mem_cell_box (scale_pos hb j) hx
      linarith [scale_pos hb j]
    have hwt := integrated_weighted_patches (range (m+1)) (scale base) (fun j => F j n)
      (fun j _ => hFm j n) (fun j x => ENNReal.ofReal (W j x)) (fun j _ => (hwm j).ennreal_ofReal)
      A (fun j p => c*B j p n) hA (fun j _ p => mul_nonneg hc.le (hB j p n))
      (fun j _ => hFi j n) hWB (c*directPriceConstant*(∫ y, ‖gradient g y‖)) (by
        intro P
        have hbgt := mul_le_mul_of_nonneg_left (marginal_total_budget hb hR hN hh hs m (fun _ => P) n) hc.le
        simpa only [A,W,B,mul_sum,mul_assoc,mul_left_comm] using hbgt)
    exact real_weighted_patches (range (m+1)) (scale base) (fun j => F j n) (fun j _ => hHi j n)
      W (fun j _ => hwm j) (fun j _ x => (marginal _ _ _ x).nonneg n) 1 (fun j _ x => law_le_one _ _)
      (mul_nonneg (mul_nonneg hc.le directPriceConstant_pos.le) (integral_nonneg (fun y => norm_nonneg _))) hwt

end CommonPrices

end SignedDisk

end

end OAI
end

theorem solution : type_of% @OAI.SignedDisk.CommonPrices.patched_unfavorable_oai := @OAI.SignedDisk.CommonPrices.patched_unfavorable_oai

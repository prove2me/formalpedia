-- Prove2me | solution 1 for OAI.SobolevBand.smooth_dyadic_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:40:36.085997+00:00
-- url     : https://prove2.me/submissions/d6cbacfd-2096-464e-81b9-a9d460b77494

import Mathlib
import Definitions.Def_OAIQWCDE000
import Theorems.Thm_OAI_CommonPrices_patched_unfavorable
import Theorems.Thm_OAI_CommonPrices_physical_joint_price

section
-- module Solutions.OAIQW_DiskMaximal.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Moments
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff

noncomputable section

namespace DiskMoments

attribute [local instance] OAI.DiskMoments.instFactEqNatFinrankRealComplexOfNat_solutions
lemma integral_translate_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (x : ℂ) (r : ℝ) :
    (∫ z in Metric.ball 0 r, f (x + z)) = ∫ y in Metric.ball x r, f y := by
  have hpre : (fun z : ℂ => x + z) ⁻¹' Metric.ball x r = Metric.ball 0 r := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  have h := (measurePreserving_add_left volume x).setIntegral_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding f (Metric.ball x r)
  rwa [hpre] at h

lemma continuous_gradient {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (gradient g) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hg.continuous_fderiv one_ne_zero)

lemma real_moment_integrand (g : ℂ → ℝ) (x z : ℂ) :
    (star z * gradient g x).re = (fderiv ℝ g x) z := by
  rw [← inner_gradient_left, Complex.inner]
  simp [mul_comm]

/-- Differentiate a disk average on its fixed unit-disk model. -/
theorem hasDerivAt_integral_unitDisk {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1, g (x + s • z))
      (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x + t • z)) z) t := by
  let F : ℝ → ℂ → ℝ := fun s z => g (x + s • z)
  let F' : ℝ → ℂ → ℝ := fun s z => (fderiv ℝ g (x + s • z)) z
  have hdc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (|t|+1)).exists_bound_of_continuousOn hdc.continuousOn
  have hFm (s : ℝ) : Continuous (F s) := hg.continuous.comp (by fun_prop)
  have hF'm (s : ℝ) : Continuous (F' s) := by
    unfold F'
    exact (hdc.comp (by fun_prop)).clm_apply continuous_id
  have hFi : IntegrableOn (F t) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1) (hFm t).continuousOn).mono_set
      Metric.ball_subset_closedBall
  have hdiff (z : ℂ) (s : ℝ) : HasDerivAt (fun s => F s z) (F' s z) s := by
    convert! ((hg.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt s
        (((hasDerivAt_id s).smul_const z).const_add x)) using 1
    simp [F', id_eq]
  have hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      ∀ s ∈ Metric.ball t 1, ‖F' s z‖ ≤ max C 0 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz s hs
    have hz' : ‖z‖ ≤ 1 := by simpa [Metric.mem_ball, dist_zero_right] using
      (show ‖z‖ < 1 by simpa [Metric.mem_ball, dist_zero_right] using hz).le
    have hs' : |s| ≤ |t| + 1 := by
      have hh : |s-t| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hs
      have hh' := abs_add_le (s-t) t
      rw [sub_add_cancel] at hh'
      linarith
    have hpos : x + s • z ∈ Metric.closedBall x (|t|+1) := by
      simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hz' (abs_nonneg s)).trans (by simpa using hs')
    exact ((fderiv ℝ g (x+s•z)).le_opNorm _).trans
      (by simpa only [mul_one] using (mul_le_mul ((hC _ hpos).trans (le_max_left C 0)) hz'
        (norm_nonneg _) (le_max_right C 0)))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Metric.ball (0 : ℂ) 1))
    (x₀ := t) (s := Metric.ball t 1) (F := F) (F' := F') (bound := fun _ => max C 0)
    (Metric.ball_mem_nhds _ zero_lt_one) (Filter.Eventually.of_forall (fun s => (hFm s).aestronglyMeasurable))
    hFi (hF'm t).aestronglyMeasurable hbound (integrableOn_const (by finiteness))
    (Filter.Eventually.of_forall (fun z s _ => hdiff z s))).2

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

lemma integral_fderiv_scale (g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z) =
      (t^3)⁻¹ * ∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x) := by
  have hi (z : ℂ) : (fderiv ℝ g (x+t•z)) z =
      t⁻¹ * (fderiv ℝ g (x+t•z)) (t•z) := by
    rw [map_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  simp_rw [hi]
  rw [integral_const_mul, integral_scale_ball (fun z => (fderiv ℝ g (x+z)) z) ht]
  have hh : (∫ z in Metric.ball (0 : ℂ) t, (fderiv ℝ g (x+z)) z) =
      ∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x) := by
    simpa using integral_translate_ball (fun y => (fderiv ℝ g y) (y-x)) x t
  rw [hh]
  simp only [smul_eq_mul]
  ring

lemma integral_fderiv_moment_real {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ) (t : ℝ) :
    (∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x)) =
      (∫ y in Metric.ball x t, star (y-x) * gradient g y).re := by
  have hi : IntegrableOn (fun y => star (y-x) * gradient g y) (Metric.ball x t) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall x t)
      ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul
        (continuous_gradient hg)).continuousOn).mono_set Metric.ball_subset_closedBall
  change _ = Complex.reCLM _
  rw [← Complex.reCLM.integral_comp_comm hi]
  congr 1
  funext y
  exact (real_moment_integrand g y (y-x)).symm

/-- The radial disk derivative is the real part of its complex moment. -/
theorem hasDerivAt_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (signedAverage g x)
      ((∫ y in Metric.ball x t, star (y-x) * gradient g y).re / (Real.pi * t^3)) t := by
  have hd := (hasDerivAt_integral_unitDisk hg x t).div_const Real.pi
  rw [integral_fderiv_scale g x ht, integral_fderiv_moment_real hg x t] at hd
  have he : (fun s => (∫ z in Metric.ball (0 : ℂ) 1, g (x+s•z)) / Real.pi)
      =ᶠ[𝓝 t] signedAverage g x := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (signedAverage_fixedDomain g x hs).symm
  convert! hd.congr_of_eventuallyEq he.symm using 1; try rfl
  ring

end DiskMoments

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

noncomputable section

namespace DiskMoments
open DiskKernels

lemma gradient_hasCompactSupport {g : ℂ → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (gradient g) := (hc.fderiv ℝ).comp_left (map_zero _)

end DiskMoments

end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.ScalarTrees
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

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

open MeasureTheory Set
open scoped ENNReal NNReal Topology
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Kernels
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

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
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

open Finset
open scoped RealInnerProductSpace
noncomputable section
namespace FiniteLabels
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma law_le_one (μ : Law ι) (i : ι) : μ i ≤ 1 := by
  rw [← μ.total]
  exact single_le_sum (fun j _ => μ.nonneg j) (mem_univ i)

lemma move_apply (μ : Law ι) (P : ι → Law κ) (j : κ) :
    move μ P j = ∑ i, μ i*P i j := rfl

lemma l1dist_nonneg (a b : ι → ℝ) : 0 ≤ l1dist a b := sum_nonneg (fun _ _ => abs_nonneg _)
lemma l1dist_triangle (a b c : ι → ℝ) : l1dist a c ≤ l1dist a b+l1dist b c := by
  unfold l1dist
  rw [← sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le (a i) (b i) (c i)

/-- Stochastic matrices contract the l1 norm of every signed row difference. -/
theorem move_contract (μ ν : Law ι) (P : ι → Law κ) :
    l1dist (move μ P) (move ν P) ≤ l1dist μ ν := by
  unfold l1dist
  calc
    _ = ∑ j, |∑ i, (μ i-ν i)*P i j| := by
      apply sum_congr rfl
      intro j _
      congr 1
      simp only [move_apply,sub_mul,sum_sub_distrib]
    _ ≤ ∑ j, ∑ i, |μ i-ν i| *P i j := by
      apply sum_le_sum
      intro j _
      calc
        _ ≤ ∑ i, |(μ i-ν i)*P i j| := abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul,abs_of_nonneg ((P _).nonneg _)]
    _ = _ := by
      rw [sum_comm]
      simp_rw [← mul_sum,(P _).total,mul_one]

lemma move_rows (μ : Law ι) (P Q : ι → Law κ) :
    l1dist (move μ P) (move μ Q) ≤ ∑ i, μ i*l1dist (P i) (Q i) := by
  unfold l1dist
  calc
    _ = ∑ j, |∑ i, μ i*(P i j-Q i j)| := by
      apply sum_congr rfl
      intro j _
      congr 1
      simp only [move_apply,mul_sub,sum_sub_distrib]
    _ ≤ ∑ j, ∑ i, μ i*|P i j-Q i j| := by
      apply sum_le_sum
      intro j _
      calc
        _ ≤ ∑ i, |μ i*(P i j-Q i j)| := abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul,abs_of_nonneg (μ.nonneg _)]
    _ = _ := by rw [sum_comm]; simp_rw [mul_sum]

lemma move_compare (μ ν : Law ι) (P Q : ι → Law κ) :
    l1dist (move μ P) (move ν Q) ≤ l1dist μ ν+∑ i, ν i*l1dist (P i) (Q i) := by
  exact (l1dist_triangle _ (move ν P) _).trans (add_le_add (move_contract μ ν P) (move_rows ν P Q))

lemma expectation_difference (μ ν : Law ι) {a : ι → ℝ} {C : ℝ}
    (ha : ∀ i, |a i| ≤ C) :
    |(∑ i, μ i*a i)-(∑ i, ν i*a i)| ≤ C*l1dist μ ν := by
  rw [← sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ i, |(μ i-ν i)*a i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C*|μ i-ν i| := sum_le_sum fun i _ => by
      rw [abs_mul,mul_comm C]
      exact mul_le_mul_of_nonneg_left (ha i) (abs_nonneg _)
    _ = _ := by rw [← mul_sum]; rfl

end FiniteLabels

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
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
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Marks
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace IntrinsicMarks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma debt_identity {e n : E} (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (v : E) :
    2*(‖v‖-⟪v,n⟫) = ‖v‖*‖direction e v-n‖^2 := by
  have hi : ‖v‖*⟪direction e v,n⟫ = ⟪v,n⟫ := by
    rw [← real_inner_smul_left,mass_direction]
  rw [norm_sub_sq_real,norm_direction he,hn]
  nlinarith

lemma marked_mass_le {e n : E} (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (v : E) {δ : ℝ} (hδ : 0 < δ) (hmark : δ < ‖direction e v-n‖) :
    ‖v‖ ≤ (2/δ^2)*(‖v‖-⟪v,n⟫) := by
  have hs : δ^2 ≤ ‖direction e v-n‖^2 :=
    (sq_le_sq₀ hδ.le (norm_nonneg _)).mpr hmark.le
  have hm := mul_le_mul_of_nonneg_left hs (norm_nonneg v)
  have hid := debt_identity he hn v
  have hd : 0 < δ^2 := sq_pos_of_pos hδ
  rw [div_mul_eq_mul_div,le_div_iff₀ hd]
  nlinarith

variable {ι : Type*} [Fintype ι]

omit [InnerProductSpace ℝ E] in
lemma norm_vector_le_terminalMass (t : Tree ι E) : ‖vector t‖ ≤ terminalMass t := by
  induction t with
  | leaf v => exact le_rfl
  | branch t ih =>
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ih i)

theorem markedCost_le {e : E} (he : ‖e‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (t : Tree ι E) {n : E} (hn : ‖n‖ = 1) :
    markedCost e δ t n ≤ (2/δ^2)*(terminalMass t-⟪vector t,n⟫) := by
  induction t generalizing n with
  | leaf v =>
    dsimp [markedCost,terminalMass,vector]
    split_ifs with hm
    · exact marked_mass_le he hn v hδ hm
    · have hi : ⟪v,n⟫ ≤ ‖v‖ := by simpa only [hn,mul_one] using real_inner_le_norm v n
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hi)
  | branch t ih =>
    let v := ∑ i, vector (t i)
    have hs (u : E) (hu : ‖u‖ = 1) :
        (∑ i, markedCost e δ (t i) u) ≤
          (2/δ^2)*((∑ i, terminalMass (t i))-⟪v,u⟫) := by
      calc
        _ ≤ ∑ i, (2/δ^2)*(terminalMass (t i)-⟪vector (t i),u⟫) :=
          Finset.sum_le_sum (fun i _ => ih i hu)
        _ = _ := by simp only [Finset.mul_sum,Finset.sum_sub_distrib,sum_inner,v,mul_sub]
    have hv := norm_direction he v
    change (if δ < ‖direction e v-n‖ then
      ‖v‖ + ∑ i, markedCost e δ (t i) (direction e v)
      else ∑ i, markedCost e δ (t i) n) ≤ _
    split_ifs with hm
    · have hms := marked_mass_le he hn v hδ hm
      have hss := hs (direction e v) hv
      have hinner : ⟪v,direction e v⟫ = ‖v‖ := by
        calc
          _ = ⟪‖v‖ • direction e v,direction e v⟫ := congrArg (fun w => ⟪w,direction e v⟫) (mass_direction e v).symm
          _ = _ := by rw [real_inner_smul_left,real_inner_self_eq_norm_sq,hv]; ring
      rw [hinner] at hss
      change _ ≤ (2/δ^2)*((∑ i, terminalMass (t i))-⟪v,n⟫)
      nlinarith
    · exact hs n hn

theorem costWithRoot_le {e : E} (he : ‖e‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (t : Tree ι E) : costWithRoot e δ t ≤ (1+2/δ^2)*terminalMass t := by
  cases t with
  | leaf v =>
    change ‖v‖ ≤ (1+2/δ^2)*‖v‖
    nlinarith [mul_nonneg (show 0 ≤ 2/δ^2 by positivity) (norm_nonneg v)]
  | branch t =>
    let v := ∑ i, vector (t i)
    have hv := norm_direction he v
    have hinner : ⟪v,direction e v⟫ = ‖v‖ := by
      calc
        _ = ⟪‖v‖ • direction e v,direction e v⟫ := congrArg (fun w => ⟪w,direction e v⟫) (mass_direction e v).symm
        _ = _ := by rw [real_inner_smul_left,real_inner_self_eq_norm_sq,hv]; ring
    have hs : (∑ i, markedCost e δ (t i) (direction e v)) ≤
        (2/δ^2)*((∑ i, terminalMass (t i))-‖v‖) := by
      calc
        _ ≤ ∑ i, (2/δ^2)*(terminalMass (t i)-⟪vector (t i),direction e v⟫) :=
          Finset.sum_le_sum (fun i _ => markedCost_le he hδ (t i) hv)
        _ = _ := by rw [← Finset.mul_sum,Finset.sum_sub_distrib,← sum_inner,hinner]
    have hn : ‖v‖ ≤ ∑ i, terminalMass (t i) := norm_vector_le_terminalMass (.branch t)
    change ‖v‖+∑ i, markedCost e δ (t i) (direction e v) ≤
      (1+2/δ^2)*(∑ i, terminalMass (t i))
    nlinarith [mul_nonneg (show 0 ≤ 2/δ^2 by positivity) (norm_nonneg v)]

end IntrinsicMarks

namespace IntrinsicMarks
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

lemma survival_nonneg (t : ι → Tree ι E) : 0 ≤ survival t := by
  unfold survival
  positivity

lemma survival_le_one (t : ι → Tree ι E) : survival t ≤ 1 := by
  unfold survival
  exact div_le_one_of_le₀ (norm_sum_le _ _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

lemma survival_capacity (t : ι → Tree ι E) :
    survival t * (∑ i, ‖vector (t i)‖) = ‖∑ i, vector (t i)‖ := by
  unfold survival
  by_cases h : (∑ i, ‖vector (t i)‖) = 0
  · have hn : ‖∑ i, vector (t i)‖ = 0 := by
      apply le_antisymm _ (norm_nonneg _)
      simpa only [h] using norm_sum_le Finset.univ (fun i => vector (t i))
    simp [h,hn]
  · exact div_mul_cancel₀ _ h

lemma rootEval_const (t : Tree ι E) (c : ℝ) :
    rootEval t (fun _ => c) = ‖vector t‖*c := by
  induction t with
  | leaf _ => rfl
  | branch t ih =>
    change survival t * (∑ i, rootEval (t i) (fun _ => c)) = _
    simp only [ih,← Finset.sum_mul]
    rw [← mul_assoc,survival_capacity]
    rfl

lemma rootEval_add (t : Tree ι E) (F G : List ι → ℝ) :
    rootEval t (fun p => F p+G p) = rootEval t F+rootEval t G := by
  induction t generalizing F G with
  | leaf _ => exact mul_add _ _ _
  | branch t ih => simp only [rootEval,ih,Finset.sum_add_distrib,mul_add]

lemma rootEval_smul (t : Tree ι E) (c : ℝ) (F : List ι → ℝ) :
    rootEval t (fun p => c*F p) = c*rootEval t F := by
  induction t generalizing F with
  | leaf _ => dsimp [rootEval]; ring
  | branch t ih => simp only [rootEval,ih,← Finset.mul_sum]; ring

lemma lateEval_const (t : Tree ι E) (c : ℝ) :
    lateEval t (fun _ _ => c) = (terminalMass t-‖vector t‖)*c := by
  induction t with
  | leaf _ => simp [lateEval,terminalMass,vector]
  | branch t ih =>
    change (1-survival t)*(∑ i, rootEval (t i) (fun _ => c)) +
      (∑ i, lateEval (t i) (fun _ _ => c)) = _
    simp only [ih,rootEval_const,← Finset.sum_mul,Finset.sum_sub_distrib]
    rw [sub_mul,one_mul,← mul_assoc,survival_capacity]
    simp only [terminalMass,vector]
    ring

lemma particleEval_const (t : Tree ι E) (c : ℝ) :
    particleEval t (fun _ _ => c) = terminalMass t*c := by
  rw [particleEval,rootEval_const,lateEval_const]
  ring

lemma lateEval_add (t : Tree ι E) (F G : List ι → ℕ → ℝ) :
    lateEval t (fun p b => F p b+G p b) = lateEval t F+lateEval t G := by
  induction t generalizing F G with
  | leaf _ => simp [lateEval]
  | branch t ih => simp only [lateEval,rootEval_add,ih,Finset.sum_add_distrib,mul_add]; ring

lemma lateEval_smul (t : Tree ι E) (c : ℝ) (F : List ι → ℕ → ℝ) :
    lateEval t (fun p b => c*F p b) = c*lateEval t F := by
  induction t generalizing F with
  | leaf _ => simp [lateEval]
  | branch t ih => simp only [lateEval,rootEval_smul,ih,← Finset.mul_sum]; ring

lemma particleEval_add (t : Tree ι E) (F G : List ι → ℕ → ℝ) :
    particleEval t (fun p b => F p b+G p b) = particleEval t F+particleEval t G := by
  simp only [particleEval,rootEval_add,lateEval_add]
  ring

lemma particleEval_smul (t : Tree ι E) (c : ℝ) (F : List ι → ℕ → ℝ) :
    particleEval t (fun p b => c*F p b) = c*particleEval t F := by
  simp only [particleEval,rootEval_smul,lateEval_smul,mul_add]

/-- Exact occupancy identity for every node charge. This includes all levels,
not only the terminal mass; populations created later are not charged earlier. -/
theorem particle_occupancy (t : Tree ι E) (C : List ι → ℝ) :
    particleEval t (pathCharge C) = nodeCharge t C := by
  induction t generalizing C with
  | leaf v => simp [particleEval,rootEval,lateEval,pathCharge,nodeCharge]
  | branch t ih =>
    simp only [particleEval,rootEval,lateEval,pathCharge,rootEval_add,rootEval_const,
      Finset.sum_add_distrib]
    have hs : (∑ i, particleEval (t i) (pathCharge (fun q => C (i::q)))) =
        ∑ i, nodeCharge (t i) (fun q => C (i::q)) :=
      Finset.sum_congr rfl (fun i _ => ih i _)
    simp only [particleEval,Finset.sum_add_distrib] at hs
    rw [← Finset.sum_mul,mul_add,← mul_assoc,survival_capacity]
    change _ = ‖∑ i, vector (t i)‖*C []+∑ i, nodeCharge (t i) (fun q => C (i::q))
    linarith

end IntrinsicMarks

namespace IntrinsicMarks
open Finset
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

lemma marked_occupancy (e : E) (δ : ℝ) (t : Tree ι E) (n : E) :
    nodeCharge t (markIndicator e δ t n) = markedCost e δ t n := by
  induction t generalizing n with
  | leaf v => simp only [nodeCharge,markIndicator,markedCost]; split_ifs <;> simp
  | branch t ih =>
    simp only [nodeCharge,markIndicator,markedCost]
    split_ifs with h
    · simp only [mul_one]
      congr 1
      exact sum_congr rfl (fun i _ => ih i _)
    · simp only [mul_zero,zero_add]
      exact sum_congr rfl (fun i _ => ih i _)

lemma root_marked_occupancy (e : E) (δ : ℝ) (t : Tree ι E) :
    nodeCharge t (rootMarkIndicator e δ t) = costWithRoot e δ t := by
  cases t with
  | leaf v => simp [nodeCharge,rootMarkIndicator,costWithRoot]
  | branch t => simp only [nodeCharge,rootMarkIndicator,costWithRoot,mul_one,marked_occupancy]

end IntrinsicMarks

namespace SignedAssembly
open Finset
open scoped RealInnerProductSpace
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma pathFlux_eq (t : JetTree ι E) (q : ℝ) (G : E) :
    pathFlux t q G = ⟪G,mean t⟫+q*flux t := by
  induction t generalizing q G with
  | leaf v => simp [pathFlux,mean,flux]
  | branch row c B t ih =>
    simp only [pathFlux,ih,inner_add_left,real_inner_smul_left,sum_add_distrib,
      ← mul_sum,mean,flux,inner_sum,real_inner_smul_right]
    simp only [mul_assoc, ← mul_sum]
    ring

lemma terminal_flux (t : JetTree ι E) : pathFlux t 1 0 = flux t := by
  rw [pathFlux_eq,inner_zero_left,one_mul,zero_add]

lemma mean_bound (t : JetTree ι E) (c : E) (B : ℝ) (h : TerminalBound t c B) :
    ‖mean t-c‖ ≤ B := by
  induction t with
  | leaf v => exact h
  | branch row _ _ t ih =>
    have he : mean (.branch row (0:E) 0 t)-c = ∑ i, row.law i • (mean (t i)-c) := by
      simp only [mean,smul_sub,sum_sub_distrib,← sum_smul,row.law.total,one_smul]
    change ‖mean (.branch row (0:E) 0 t)-c‖ ≤ B
    rw [he]
    calc
      _ ≤ ∑ i, ‖row.law i • (mean (t i)-c)‖ := norm_sum_le _ _
      _ = ∑ i, row.law i*‖mean (t i)-c‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (row.law.nonneg _)]
      _ ≤ ∑ i, row.law i*B := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (ih i (h i)) (row.law.nonneg i)
      _ = B := by rw [← sum_mul,row.law.total,one_mul]

/-- This is the exact zero-row-sum cancellation. No unsigned path-potential
bound is used and the parent prefix may be arbitrarily large. -/
lemma prefix_cancellation (row : RowJet ι E) (v : ι → E) (c : E) :
    (∑ i, ⟪row.grad i,v i⟫) = ∑ i, ⟪row.grad i,v i-c⟫ := by
  simp only [inner_sub_right,sum_sub_distrib,← sum_inner,row.total_grad,inner_zero_left,sub_zero]

lemma row_flux_bound (row : RowJet ι E) (v : ι → E) (c : E) (B : ℝ)
    (h : ∀ i, ‖v i-c‖ ≤ B) :
    |∑ i, ⟪row.grad i,v i⟫| ≤ (∑ i, ‖row.grad i‖)*B := by
  rw [prefix_cancellation row v c]
  calc
    _ ≤ ∑ i, |⟪row.grad i,v i-c⟫| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖row.grad i‖*B := sum_le_sum fun i _ =>
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (h i) (norm_nonneg _))
    _ = _ := by rw [← sum_mul]

/-- Full finite-history signed flux estimate, with all stochastic prefix
weights kept. The node bound is the tail oscillation, not the old envelope. -/
theorem signed_flux_bound (t : JetTree ι E) (ht : Controlled t) :
    |pathFlux t 1 0| ≤ cost t := by
  rw [terminal_flux]
  induction t with
  | leaf v => simp [flux,cost]
  | branch row c B t ih =>
    change |(∑ i, ⟪row.grad i,mean (t i)⟫)+∑ i, row.law i*flux (t i)| ≤ _
    calc
      _ ≤ |∑ i, ⟪row.grad i,mean (t i)⟫|+|∑ i, row.law i*flux (t i)| := abs_add_le _ _
      _ ≤ (∑ i, ‖row.grad i‖)*B+∑ i, row.law i*cost (t i) := by
        apply add_le_add (row_flux_bound row (fun i => mean (t i)) c B
          (fun i => mean_bound (t i) c B (ht.1 i)))
        calc
          _ ≤ ∑ i, |row.law i*flux (t i)| := abs_sum_le_sum_abs _ _
          _ = ∑ i, row.law i*|flux (t i)| := by
            simp only [abs_mul,abs_of_nonneg (row.law.nonneg _)]
          _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ih i (ht.2 i)) (row.law.nonneg i)
      _ = _ := rfl

end SignedAssembly

open scoped ContDiff

open Finset
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Refinement
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace RadiusEnvelope
variable {E : Type*}

lemma attains {u : ℝ → E → ℝ} {a b : ℝ} (hab : a ≤ b) (x : E)
    (hc : ContinuousOn (fun r => u r x) (Icc a b)) :
    ∃ r ∈ Icc a b, envelope u a b x = u r x ∧ ∀ t ∈ Icc a b, u t x ≤ u r x := by
  obtain ⟨r,hr,hm⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hc
  refine ⟨r,hr,?_,hm⟩
  apply le_antisymm
  · apply csSup_le ((Set.nonempty_Icc.mpr hab).image _)
    rintro _ ⟨t,ht,rfl⟩
    exact hm ht
  · apply le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    exact mem_image_of_mem _ hr

lemma le_envelope {u : ℝ → E → ℝ} {a b r : ℝ} (hr : r ∈ Icc a b) (x : E)
    (hc : ContinuousOn (fun r => u r x) (Icc a b)) : u r x ≤ envelope u a b x := by
  obtain ⟨t,ht,he,hm⟩ := attains (hr.1.trans hr.2) x hc
  rw [he]
  exact hm r hr

lemma lipschitz [NormedAddCommGroup E] {u : ℝ → E → ℝ} {a b : ℝ} {L : ℝ≥0} (hab : a ≤ b)
    (hc : ∀ x, ContinuousOn (fun r => u r x) (Icc a b))
    (hL : ∀ r ∈ Icc a b, LipschitzWith L (u r)) :
    LipschitzWith L (envelope u a b) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  obtain ⟨r,hr,her,hmr⟩ := attains hab x (hc x)
  obtain ⟨t,ht,het,hmt⟩ := attains hab y (hc y)
  rw [Real.dist_eq,abs_le]
  constructor
  · have h := (hL t ht).dist_le_mul x y
    rw [Real.dist_eq] at h
    rw [het]
    have hx := le_envelope ht x (hc x)
    have ha := (abs_le.mp h).1
    linarith
  · have h := (hL r hr).dist_le_mul x y
    rw [Real.dist_eq] at h
    rw [her]
    have hy := le_envelope hr y (hc y)
    have ha := (abs_le.mp h).2
    linarith

lemma zero_of_all_zero {u : ℝ → E → ℝ} {a b : ℝ} (hab : a ≤ b) {x : E}
    (hc : ContinuousOn (fun r => u r x) (Icc a b))
    (hz : ∀ r ∈ Icc a b, u r x = 0) : envelope u a b x = 0 := by
  obtain ⟨r,hr,he,_⟩ := attains hab x hc
  exact he.trans (hz r hr)

/-- Differentiable touching holds for every attaining radius; no derivative of
an argmax selector is taken. -/
theorem fderiv_touching [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℝ → E → ℝ} {a b r : ℝ} {x : E}
    (hr : r ∈ Icc a b) (hc : ∀ y, ContinuousOn (fun t => u t y) (Icc a b))
    (he : envelope u a b x = u r x)
    (hd : DifferentiableAt ℝ (envelope u a b) x) (hu : DifferentiableAt ℝ (u r) x) :
    fderiv ℝ (envelope u a b) x = fderiv ℝ (u r) x := by
  have hm : IsLocalMin (fun y => envelope u a b y-u r y) x := by
    apply IsMinOn.isLocalMin (s := univ) _ univ_mem
    intro y _
    change envelope u a b x-u r x ≤ envelope u a b y-u r y
    rw [he,sub_self]
    exact sub_nonneg.mpr (le_envelope hr y (hc y))
  have hz := hm.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub hu.hasFDerivAt)
  exact sub_eq_zero.mp hz

end RadiusEnvelope

namespace DiskMoments

lemma signedAverage_lipschitz {g : ℂ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {t : ℝ} (ht : 0 < t) : LipschitzWith L (fun x => signedAverage g x t) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [signedAverage_fixedDomain g x ht,signedAverage_fixedDomain g y ht,Real.dist_eq,
    ← sub_div,abs_div,abs_of_pos Real.pi_pos]
  have hxi : IntegrableOn (fun z : ℂ => g (x+t • z)) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1)
      (hg.continuous.comp (by fun_prop)).continuousOn).mono_set Metric.ball_subset_closedBall
  have hyi : IntegrableOn (fun z : ℂ => g (y+t • z)) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1)
      (hg.continuous.comp (by fun_prop)).continuousOn).mono_set Metric.ball_subset_closedBall
  rw [← integral_sub hxi hyi]
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0:ℂ) 1)) :=
    ⟨by simp⟩
  have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict (Metric.ball (0:ℂ) 1))
    (C := (L:ℝ)*dist x y) (f := fun z : ℂ => g (x+t • z)-g (y+t • z)) (by
      filter_upwards with z
      simpa only [Real.norm_eq_abs,← Real.dist_eq,dist_add_right] using hg.dist_le_mul (x+t • z) (y+t • z))
  have hv : (volume.restrict (Metric.ball (0:ℂ) 1)).real univ = Real.pi := by
    simp [measureReal_def,Complex.volume_ball]
  rw [hv,Real.norm_eq_abs] at hi
  exact (div_le_iff₀ Real.pi_pos).mpr hi

lemma signedAverage_radius_continuousOn {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => signedAverage g x t) (Icc a b) := by
  intro t ht
  exact (hasDerivAt_signedAverage hg x (ha.trans_le ht.1)).continuousAt.continuousWithinAt

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

/-- Actual signed run envelopes: locally differentiable almost everywhere, over
all radii in their compact interval. -/
theorem run_envelope_lipschitz {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L : ℝ≥0, LipschitzWith L (RadiusEnvelope.envelope (fun r x => signedAverage g x r) a b) := by
  obtain ⟨L,hL⟩ := hg.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
  exact ⟨L,RadiusEnvelope.lipschitz hab (fun x => signedAverage_radius_continuousOn hg x ha)
    (fun r hr => signedAverage_lipschitz hL (ha.trans_le hr.1))⟩

end DiskMoments

namespace DiskMoments

lemma signedAverage_eq_zero_of_outside {g : ℂ → ℝ} {R : ℝ}
    (hs : ∀ y, g y ≠ 0 → ‖y‖ ≤ R) {x : ℂ} {t : ℝ} (hx : R+t ≤ ‖x‖) :
    signedAverage g x t = 0 := by
  unfold signedAverage
  have hz : (∫ y in Metric.ball x t, g y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    by_contra hny
    have hn := hs y hny
    have hd : ‖x-y‖ < t := by simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hy
    have hh : ‖x‖ ≤ ‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
    linarith
  rw [hz,zero_div]

/-- Every radius in the run is retained, but a common compact spatial support
still exists. -/
theorem run_envelope_hasCompactSupport {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    HasCompactSupport (RadiusEnvelope.envelope (fun r x => signedAverage g x r) a b) := by
  obtain ⟨R,hR⟩ := hgc.isBounded.subset_closedBall (0:ℂ)
  have hs : ∀ y, g y ≠ 0 → ‖y‖ ≤ R := by
    intro y hy
    simpa only [Metric.mem_closedBall,dist_zero_right] using hR (subset_tsupport g hy)
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0:ℂ) (R+b)) isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  by_contra hn
  have hz : RadiusEnvelope.envelope (fun r x => signedAverage g x r) a b x = 0 := by
    apply RadiusEnvelope.zero_of_all_zero hab (signedAverage_radius_continuousOn hg x ha)
    intro r hr
    exact signedAverage_eq_zero_of_outside hs (by linarith [hr.2])
  exact hx hz

end DiskMoments

namespace DyadicHats

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

end DyadicHats

namespace DyadicHats
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
noncomputable section

namespace LipschitzWith
open scoped _root_.LipschitzWith
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ] {f g : E → ℝ} {L K : ℝ≥0}

/-- Genuine integration by parts for Lipschitz weights and compact Lipschitz
potentials. Differentiability is required only almost everywhere, and follows
from Rademacher rather than being a new premise. -/
theorem integral_fderiv_mul_eq_neg (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    (hgc : HasCompactSupport g) (v : E) :
    (∫ x, fderiv ℝ f x v * g x ∂μ) = -∫ x, fderiv ℝ g x v * f x ∂μ := by
  have h1 : (fun x => fderiv ℝ f x v*g x) =ᵐ[μ] fun x => lineDeriv ℝ f x v*g x := by
    filter_upwards [hf.ae_differentiableAt (μ := μ)] with x hx
    rw [hx.lineDeriv_eq_fderiv]
  have h2 : (fun x => lineDeriv ℝ g x (-v)*f x) =ᵐ[μ] fun x => -(fderiv ℝ g x v*f x) := by
    filter_upwards [hg.ae_differentiableAt (μ := μ)] with x hx
    rw [hx.lineDeriv_eq_fderiv,map_neg,neg_mul]
  rw [integral_congr_ae h1,hf.integral_lineDeriv_mul_eq hg hgc v,integral_congr_ae h2,integral_neg]

/-- The total gradient version obtained from Riesz and measurable fderiv is
locally integrable, including on the nondifferentiability set. -/
theorem locallyIntegrable_gradient (hf : LipschitzWith L f) :
    LocallyIntegrable (gradient f) μ := by
  have hm : AEStronglyMeasurable (gradient f) μ :=
    ((InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ f)).aestronglyMeasurable
  have hb : ∀ x, ‖gradient f x‖ ≤ (L:ℝ) := by
    intro x
    simpa only [gradient,(InnerProductSpace.toDual ℝ E).symm.norm_map] using
      (norm_fderiv_le_of_lipschitz ℝ hf : ‖fderiv ℝ f x‖ ≤ (L:ℝ))
  exact (memLp_top_of_bound hm (L:ℝ) (ae_of_all _ hb)).locallyIntegrable le_top

theorem integrable_gradient (hf : LipschitzWith L f) (hc : HasCompactSupport f) :
    Integrable (gradient f) μ := by
  have hs : HasCompactSupport (gradient f) :=
    (hc.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ E).symm)
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport (gradient f))).mp
    ((_root_.OAI.LipschitzWith.locallyIntegrable_gradient (μ := μ) hf).integrableOn_isCompact hs)

theorem integral_mul_fderiv_eq_neg (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    (hgc : HasCompactSupport g) (v : E) :
    (∫ x, f x * fderiv ℝ g x v ∂μ) = -∫ x, inner ℝ (gradient f x) v * g x ∂μ := by
  simp only [gradient,InnerProductSpace.toDual_symm_apply]
  have h := _root_.OAI.LipschitzWith.integral_fderiv_mul_eq_neg (μ := μ) hf hg hgc v
  rw [show (fun x => f x * fderiv ℝ g x v) = (fun x => fderiv ℝ g x v * f x) by
    funext x; exact mul_comm _ _]
  linarith

end LipschitzWith

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

end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.DirectionLaws
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

noncomputable section

namespace DyadicHats
open scoped BigOperators

variable {N : ℕ}

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

end DyadicHats

namespace DyadicHats
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

end DyadicHats

namespace DyadicHats
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

end DyadicHats

namespace DyadicHats
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

lemma spatialRow_distance (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hpB : ∀ z, p z ≤ B) (x y : ℂ) :
    l1dist (spatialRow old target p hp0 hp1 r x) (spatialRow old target p hp0 hp1 r y) ≤
      (Fintype.card ι:ℝ)*(16*B/r)*‖x-y‖ := by
  unfold l1dist
  calc
    _ ≤ ∑ _j : ι, (16*B/r)*‖x-y‖ := by
      apply sum_le_sum
      intro j _
      have hl := (spatialRow_component_lipschitz old target p hp0 hp1 hr hB hpB j).dist_le_mul x y
      rw [Real.dist_eq,Real.coe_toNNReal (16*B/r) (by positivity),dist_eq_norm] at hl
      exact hl
    _ = _ := by rw [sum_const,card_univ,nsmul_eq_mul,mul_assoc]

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

lemma interpolate_mono_on (r : ℝ) (x : ℂ) {f g : ℤ × ℤ → ℝ}
    (h : ∀ p, hat r p x ≠ 0 → f p ≤ g p) : interpolate r f x ≤ interpolate r g x := by
  apply Summable.tsum_le_tsum _ (summable_weighted_hat r x f) (summable_weighted_hat r x g)
  intro p
  by_cases hp : hat r p x = 0
  · simp only [hp,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (h p hp) (hat_nonneg r p x)

lemma hat_vertex_local {r : ℝ} (hr : 0 < r) {x q : ℂ}
    (hx : boxNorm (x-q) < 199*r) {p : ℤ × ℤ} (hp : hat r p x ≠ 0) :
    boxNorm (point r p-q) ≤ 200*r := by
  have hd := (hat_ne_zero_iff hr p x).mp hp
  have ht := boxNorm_add_le (point r p-x) (x-q)
  rw [sub_add_sub_cancel,boxNorm_sub_comm (point r p) x] at ht
  linarith

lemma continuous_boxNorm : Continuous boxNorm :=
  (Complex.continuous_re.abs).max (Complex.continuous_im.abs)

lemma local_neighborhood {r : ℝ} {q x : ℂ} (hx : boxNorm (x-q) < 199*r) :
    ∀ᶠ y in 𝓝 x, boxNorm (y-q) < 199*r := by
  exact ((continuous_boxNorm.comp (continuous_id.sub continuous_const)).continuousAt.eventually
    (eventually_lt_nhds hx))

end DyadicHats

namespace FiniteLabels
open DyadicHats Finset Filter
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spatialRow_truncate (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) {r : ℝ} (hr : 0 < r) {q x : ℂ}
    (hx : boxNorm (x-q) < 199*r) (j : ι) :
    spatialRow old target (truncate r q p) (truncate_nonneg r q hp0)
      (truncate_le (by norm_num) (fun z _ => hp1 z)) r x j =
    spatialRow old target p hp0 hp1 r x j := by
  rw [spatialRow_formula,spatialRow_formula]
  congr 1
  apply interpolate_congr_on
  intro z hz
  rw [truncate,ite_eq_left (hat_vertex_local hr hx hz)]

lemma spatialRow_local_distance (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    {q x y : ℂ} (hx : boxNorm (x-q) < 199*r) (hy : boxNorm (y-q) < 199*r)
    (hpB : ∀ z, boxNorm (point r z-q) ≤ 200*r → p z ≤ B) :
    l1dist (spatialRow old target p hp0 hp1 r x) (spatialRow old target p hp0 hp1 r y) ≤
      (Fintype.card ι:ℝ)*(16*B/r)*‖x-y‖ := by
  have h := spatialRow_distance old target (truncate r q p) (truncate_nonneg r q hp0)
    (truncate_le (by norm_num) (fun z _ => hp1 z)) hr hB (truncate_le hB hpB) x y
  simpa only [l1dist,spatialRow_truncate old target p hp0 hp1 hr hx,
    spatialRow_truncate old target p hp0 hp1 hr hy] using h

/-- The derivative cost is bounded by the local switched mass, with a constant
fixed by the finite palette, rather than by the number of scales or vertices. -/
lemma spatialRow_local_derivative (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    {q x : ℂ} (hx : boxNorm (x-q) < 199*r)
    (hpB : ∀ z, boxNorm (point r z-q) ≤ 200*r → p z ≤ B) :
    r*∑ j : ι, ‖gradient (fun y => spatialRow old target p hp0 hp1 r y j) x‖ ≤
      16*(Fintype.card ι:ℝ)*B := by
  have hb (j : ι) : ‖gradient (fun y => spatialRow old target p hp0 hp1 r y j) x‖ ≤ 16*B/r := by
    have he : (fun y => spatialRow old target (truncate r q p) (truncate_nonneg r q hp0)
        (truncate_le (by norm_num) (fun z _ => hp1 z)) r y j) =ᶠ[𝓝 x]
        (fun y => spatialRow old target p hp0 hp1 r y j) := by
      filter_upwards [local_neighborhood hx] with y hy
      exact spatialRow_truncate old target p hp0 hp1 hr hy j
    have hl := spatialRow_component_lipschitz old target (truncate r q p) (truncate_nonneg r q hp0)
      (truncate_le (by norm_num) (fun z _ => hp1 z)) hr hB (truncate_le hB hpB) j
    have hd := he.fderiv_eq (𝕜 := ℝ)
    have hn := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hl
    rw [hd,Real.coe_toNNReal (16*B/r) (by positivity)] at hn
    simpa only [gradient,(InnerProductSpace.toDual ℝ ℂ).symm.norm_map] using hn
  calc
    _ ≤ r*∑ _j : ι, 16*B/r := mul_le_mul_of_nonneg_left (sum_le_sum (fun j _ => hb j)) hr.le
    _ = _ := by rw [sum_const,card_univ,nsmul_eq_mul]; field_simp

end FiniteLabels

namespace FiniteLabels

lemma probability_eq_square {τ : ℝ} (hτ : 0 ≤ τ) (d : ℝ) :
    probability τ d = amplitude τ d^2 := by
  have hx : 0 ≤ τ⁻¹*max (d-τ) 0 := mul_nonneg (inv_nonneg.mpr hτ) (le_max_right _ _)
  unfold probability amplitude
  by_cases h : τ⁻¹*max (d-τ) 0 ≤ 1
  · rw [min_eq_right h,min_eq_right (by nlinarith)]
  · rw [min_eq_left (le_of_not_ge h),min_eq_left (by nlinarith)]
    norm_num

lemma amplitude_lipschitz {τ : ℝ} (hτ : 0 < τ) :
    LipschitzWith (Real.toNNReal τ⁻¹) (amplitude τ) := by
  have hid : LipschitzWith 1 (fun d : ℝ => d-τ) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [NNReal.coe_one,one_mul,Real.dist_eq,sub_sub_sub_cancel_right,le_refl]
  have hmax : LipschitzWith 1 (fun d : ℝ => max (d-τ) 0) := by
    simpa only [max_eq_left (by norm_num : (0:ℝ≥0) ≤ 1)] using hid.max (LipschitzWith.const 0)
  have hm : LipschitzWith (Real.toNNReal τ⁻¹) (fun d : ℝ => τ⁻¹*max (d-τ) 0) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro d d'
    rw [Real.dist_eq,Real.dist_eq,← mul_sub,abs_mul,
      abs_of_nonneg (inv_nonneg.mpr hτ.le),Real.coe_toNNReal _ (inv_nonneg.mpr hτ.le)]
    have hl := hmax.dist_le_mul d d'
    simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hl
    exact mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hτ.le)
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  change dist (min 1 (τ⁻¹*max (x-τ) 0)) (min 1 (τ⁻¹*max (y-τ) 0)) ≤ _
  simpa only [max_eq_right (by positivity : (0:ℝ≥0) ≤ Real.toNNReal τ⁻¹)] using
    ((LipschitzWith.const (1:ℝ)).min hm).dist_le_mul x y

lemma probability_compare {τ : ℝ} (hτ : 0 < τ) (d d' : ℝ) :
    probability τ d ≤ 2*probability τ d'+2*τ⁻¹^2*|d-d'|^2 := by
  rw [probability_eq_square hτ.le,probability_eq_square hτ.le]
  have hl := (amplitude_lipschitz hτ).dist_le_mul d d'
  rw [Real.dist_eq,Real.dist_eq,Real.coe_toNNReal _ (inv_nonneg.mpr hτ.le)] at hl
  have hdiff : (amplitude τ d-amplitude τ d')^2 ≤ (τ⁻¹*|d-d'|)^2 := by
    nlinarith [sq_abs (amplitude τ d-amplitude τ d'),abs_nonneg (amplitude τ d-amplitude τ d'),
      mul_nonneg (inv_nonneg.mpr hτ.le) (abs_nonneg (d-d'))]
  nlinarith [sq_nonneg (amplitude τ d-2*amplitude τ d')]

lemma probability_norm_compare {E : Type*} [NormedAddCommGroup E] {τ : ℝ}
    (hτ : 0 < τ) (n θ θ' : E) :
    probability τ ‖n-θ‖ ≤ 2*probability τ ‖n-θ'‖+2*τ⁻¹^2*‖θ-θ'‖^2 := by
  apply (probability_compare hτ ‖n-θ‖ ‖n-θ'‖).trans
  have hd : |‖n-θ‖-‖n-θ'‖| ≤ ‖θ-θ'‖ := by
    simpa only [sub_sub_sub_cancel_left,norm_sub_rev θ' θ] using abs_norm_sub_norm_le (n-θ) (n-θ')
  have hs : |‖n-θ‖-‖n-θ'‖|^2 ≤ ‖θ-θ'‖^2 := by
    nlinarith [abs_nonneg (‖n-θ‖-‖n-θ'‖),norm_nonneg (θ-θ')]
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*τ⁻¹^2 by positivity)
  linarith

lemma probability_eq_zero {τ d : ℝ} (hd : d ≤ τ) : probability τ d = 0 := by
  rw [probability,max_eq_right (sub_nonpos.mpr hd)]
  norm_num

end FiniteLabels

namespace FiniteLabels
open DyadicHats

lemma interpolate_const_mul (r : ℝ) (f : ℤ × ℤ → ℝ) (x : ℂ) (c : ℝ) :
    interpolate r (fun p => c*f p) x = c*interpolate r f x := by
  simp only [mul_comm c,interpolate_mul_const]

lemma norm_sub_sq_le_four {E : Type*} [NormedAddCommGroup E] (u v w : E) {A : ℝ}
    (hu : ‖u-w‖^2 ≤ A) (hv : ‖v-w‖^2 ≤ A) : ‖u-v‖^2 ≤ 4*A := by
  have ht : ‖u-v‖ ≤ ‖u-w‖+‖v-w‖ := by
    simpa only [sub_add_sub_cancel,norm_sub_rev w v] using norm_add_le (u-w) (w-v)
  nlinarith [norm_nonneg (u-v),norm_nonneg (u-w),norm_nonneg (v-w),
    sq_nonneg (‖u-w‖-‖v-w‖)]

lemma switchRate_nonneg (τ r : ℝ) (Θ : ℤ × ℤ → ℂ) (n x : ℂ) :
    0 ≤ switchRate τ r Θ n x := interpolate_nonneg r x (fun _ => probability_nonneg _ _)

/-- The row-rate comparison is produced from the literal quadratic probability
and the actual partition of unity, uniformly over all nearby grid vertices. -/
lemma probability_le_rate_energy {τ r E : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    (Θ : ℤ × ℤ → ℂ) (n θ q y : ℂ) (hy : boxNorm (y-q) < 199*r)
    (hE : ∀ z, boxNorm (point r z-q) ≤ 200*r → ‖Θ z-θ‖^2 ≤ E)
    (z : ℤ × ℤ) (hz : boxNorm (point r z-q) ≤ 200*r) :
    probability τ ‖n-Θ z‖ ≤ 2*switchRate τ r Θ n y+8*τ⁻¹^2*E := by
  have hp (z' : ℤ × ℤ) (hz' : hat r z' y ≠ 0) :
      probability τ ‖n-Θ z‖ ≤ 2*probability τ ‖n-Θ z'‖+8*τ⁻¹^2*E := by
    have he := norm_sub_sq_le_four (Θ z) (Θ z') θ (hE z hz) (hE z' (hat_vertex_local hr hy hz'))
    have hh := probability_norm_compare hτ n (Θ z) (Θ z')
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 2*τ⁻¹^2 by positivity)
    nlinarith
  calc
    _ = interpolate r (fun _ => probability τ ‖n-Θ z‖) y := (interpolate_const _ _ _).symm
    _ ≤ interpolate r (fun z' => 2*probability τ ‖n-Θ z'‖+8*τ⁻¹^2*E) y :=
      interpolate_mono_on r y hp
    _ = _ := by rw [interpolate_add,interpolate_const_mul,interpolate_const]; rfl

lemma switchRate_local_compare {τ r E : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    (Θ : ℤ × ℤ → ℂ) (n θ q x y : ℂ)
    (hx : boxNorm (x-q) < 199*r) (hy : boxNorm (y-q) < 199*r)
    (hE : ∀ z, boxNorm (point r z-q) ≤ 200*r → ‖Θ z-θ‖^2 ≤ E) :
    switchRate τ r Θ n x ≤ 2*switchRate τ r Θ n y+8*τ⁻¹^2*E := by
  change interpolate r _ x ≤ _
  calc
    _ ≤ interpolate r (fun _ => 2*switchRate τ r Θ n y+8*τ⁻¹^2*E) x := by
      apply interpolate_mono_on
      intro z hz
      exact probability_le_rate_energy hτ hr Θ n θ q y hy hE z (hat_vertex_local hr hx hz)
    _ = _ := interpolate_const _ _ _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spatialSwitchRow_local_distance {τ r E : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hE0 : 0 ≤ E)
    (label : ι → ℂ) (Θ : ℤ × ℤ → ℂ) (target : ℤ × ℤ → ι) (old : ι)
    (θ q x y : ℂ) (hx : boxNorm (x-q) < 199*r) (hy : boxNorm (y-q) < 199*r)
    (hE : ∀ z, boxNorm (point r z-q) ≤ 200*r → ‖Θ z-θ‖^2 ≤ E) :
    l1dist (spatialSwitchRow τ r label Θ target old x) (spatialSwitchRow τ r label Θ target old y) ≤
      (Fintype.card ι:ℝ)*
        (16*(2*switchRate τ r Θ (label old) y+8*τ⁻¹^2*E)/r)*‖x-y‖ := by
  apply spatialRow_local_distance old target _ _ _ hr
    (by have h := switchRate_nonneg τ r Θ (label old) y; positivity) hx hy
  intro z hz
  exact probability_le_rate_energy hτ hr Θ (label old) θ q y hy hE z hz

lemma spatialSwitchRow_local_derivative {τ r E : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hE0 : 0 ≤ E)
    (label : ι → ℂ) (Θ : ℤ × ℤ → ℂ) (target : ℤ × ℤ → ι) (old : ι)
    (θ q x y : ℂ) (hx : boxNorm (x-q) < 199*r) (hy : boxNorm (y-q) < 199*r)
    (hE : ∀ z, boxNorm (point r z-q) ≤ 200*r → ‖Θ z-θ‖^2 ≤ E) :
    r*∑ j : ι, ‖gradient (fun x => spatialSwitchRow τ r label Θ target old x j) x‖ ≤
      16*(Fintype.card ι:ℝ)*(2*switchRate τ r Θ (label old) y+8*τ⁻¹^2*E) := by
  apply spatialRow_local_derivative old target _ _ _ hr
    (by have h := switchRate_nonneg τ r Θ (label old) y; positivity) hx
  intro z hz
  exact probability_le_rate_energy hτ hr Θ (label old) θ q y hy hE z hz

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

end DyadicHats

namespace DyadicHats
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

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.DirectionEstimates
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

noncomputable section

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
lemma energy_le_four (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : energy h r q ≤ 4 := by
  have hn := norm_sub_le (Theta h r (worstVertex h r q)) (theta h r q)
  simp only [Theta,norm_theta] at hn
  change ‖theta h r (chosen h r (worstVertex h r q))-theta h r q‖^2 ≤ 4
  nlinarith [norm_nonneg (theta h r (chosen h r (worstVertex h r q))-theta h r q)]

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

end DirectionNeighbors

namespace DirectionNeighbors
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
noncomputable section
namespace ConeCoordinates

lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
lemma sqrt3_bounds : 3/2 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 := by
  have := sqrt3_sq
  have := sqrt3_pos
  constructor <;> nlinarith
lemma inner_re (n z : ℂ) : inner ℝ n z = (star n*z).re := by
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.mul_re]
  ring
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

lemma norm_le_coords {n : ℂ} (hn : ‖n‖ = 1) (z : ℂ) :
    ‖z‖ ≤ |inner ℝ n z|+|inner ℝ (Complex.I*n) z| := by
  have hnorm : ‖star n*z‖ = ‖z‖ := by simp [hn]
  rw [inner_re,inner_im,← hnorm]
  exact Complex.norm_le_abs_re_add_abs_im _

theorem cone_algebra {n : ℂ} (hn : ‖n‖ = 1) (z : ℂ) :
    ‖z‖ ≤ 12*(inner ℝ n z + max 0 (-inner ℝ (axis n 1) z) +
      max 0 (-inner ℝ (axis n (-1)) z)) := by
  let a := inner ℝ n z
  let b := inner ℝ (Complex.I*n) z
  let u := max 0 (-inner ℝ (axis n 1) z)
  let v := max 0 (-inner ℝ (axis n (-1)) z)
  have hu0 : 0 ≤ u := le_max_left _ _
  have hv0 : 0 ≤ v := le_max_left _ _
  have hu : -(Real.sqrt 3/2*a+1/2*b) ≤ u := by simpa only [u,v,a,b,inner_axis] using le_max_right 0 (-inner ℝ (axis n 1) z)
  have hv : -(Real.sqrt 3/2*a+(-1)/2*b) ≤ v := by simpa only [u,v,a,b,inner_axis] using le_max_right 0 (-inner ℝ (axis n (-1)) z)
  have hs := sqrt3_bounds
  have ha : |a| ≤ 2*(a+u+v) := by
    by_cases h : 0 ≤ a
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg (lt_of_not_ge h)]
      have hmul := mul_le_mul_of_nonpos_right hs.1 (le_of_not_ge h)
      nlinarith
  have hb : |b| ≤ 2*(u+v)+2*|a| := by
    have haa : Real.sqrt 3*a ≤ 2*|a| :=
      (mul_le_mul_of_nonneg_left (le_abs_self a) sqrt3_pos.le).trans
        (mul_le_mul_of_nonneg_right hs.2 (abs_nonneg a))
    apply abs_le.2
    constructor <;> linarith
  have hz := norm_le_coords hn z
  change ‖z‖ ≤ 12*(a+u+v)
  change ‖z‖ ≤ |a|+|b| at hz
  have := neg_le_abs a
  linarith

lemma quantize_close (z : ℂ) (hz : ‖z‖ = 1) : ‖z-(quantize z hz : ℂ)‖ < 1/2000 :=
  (Classical.choose_spec (fixedPalette.cover z hz)).2

end ConeCoordinates

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks Finset

lemma vector_tree {N : ℕ} (v : Grid N → ℂ) (k : ℕ) (b : ℝ) (p : Grid N) :
    vector (tree v k b p) = b • ∑ q : Grid N, coeff N k p q • v q := by
  induction k generalizing b p with
  | zero => simp [tree,vector,coeff]
  | succ k ih =>
    simp only [tree,vector,ih,coeff,smul_sum,sum_smul,smul_smul]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro a ha
    congr 1
    ring

lemma terminalMass_tree {N : ℕ} (v : Grid N → ℂ) (k : ℕ) {b : ℝ} (hb : 0 ≤ b) (p : Grid N) :
    terminalMass (tree v k b p) = b * ∑ q : Grid N, coeff N k p q * ‖v q‖ := by
  induction k generalizing b p with
  | zero => simp [tree,terminalMass,coeff,Real.norm_eq_abs,abs_of_nonneg hb]
  | succ k ih =>
    simp only [tree,terminalMass]
    simp_rw [ih (mul_nonneg hb (step_nonneg _ _)),coeff,mul_sum,sum_mul]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro q hq
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    ring

lemma sum_terminalMass {N : ℕ} (v : Grid N → ℂ) (k : ℕ) :
    (∑ p : Grid N, terminalMass (tree v k 1 p)) = ∑ q : Grid N, ‖v q‖ := by
  simp_rw [terminalMass_tree v k (by norm_num : (0:ℝ) ≤ 1),one_mul]
  rw [Finset.sum_comm]
  simp_rw [← sum_mul,coeff_column,one_mul]

lemma vector_actual {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (b : ℝ) (p : Grid N) :
    vector (tree (fun q : Grid N => vectorMass h r q) k b p) =
      b • vectorMass h (scale r k) p := by
  rw [vector_tree,← vectorMass_coeff hr hR hN hh hs]

end ActualMarkTrees

end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Prices
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset

lemma rho_pos : 0 < rho := Real.rpow_pos_of_pos (by norm_num) _
lemma rho_lt_one : rho < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)

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

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.SpatialLaws
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

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

end ActualLabels

namespace FiniteLabels
open DyadicHats Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma expect_nonneg (μ : Law ι) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : 0 ≤ expect μ f :=
  sum_nonneg (fun i _ => mul_nonneg (μ.nonneg i) (hf i))
lemma expect_le_one (μ : Law ι) {f : ι → ℝ} (hf : ∀ i, f i ≤ 1) : expect μ f ≤ 1 := by
  calc
    _ ≤ ∑ i, μ i*1 := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (μ.nonneg i))
    _ = _ := by simp only [mul_one,μ.total]
lemma expect_add (μ : Law ι) (f g : ι → ℝ) :
    expect μ (fun i => f i+g i) = expect μ f+expect μ g := by
  simp only [expect,mul_add,sum_add_distrib]
lemma expect_move (μ : Law ι) (P : ι → Law κ) (f : κ → ℝ) :
    expect (move μ P) f = expect μ (fun i => expect (P i) f) := by
  simp only [expect,move_apply,sum_mul,mul_sum,mul_assoc]
  rw [Finset.sum_comm]

variable [DecidableEq ι]

/-- An absorbing finite set gives exact drift equal to the off-diagonal
switch rate. Conditions concern only tents that actually meet the point. -/
lemma spatialRow_absorbing (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ)
    (b : ι → ℝ) (hb : b old = 0 ∨ b old = 1)
    (ht : ∀ z, hat r z x ≠ 0 → b (target z) = 0)
    (hz : b old = 0 → ∀ z, hat r z x ≠ 0 → p z = 0) :
    expect (spatialRow old target p hp0 hp1 r x) b+interpolate r p x = b old := by
  rw [spatialRow_expect]
  rcases hb with hb|hb
  · have he : interpolate r p x = 0 := by
      rw [interpolate_congr_on r x (hz hb),interpolate_const]
    have he' : interpolate r (fun z => p z*(b (target z)-b old)) x = 0 := by
      have hc : ∀ z, hat r z x ≠ 0 → p z*(b (target z)-b old) = 0 := by
        intro z h; rw [ht z h,hb]; ring
      rw [interpolate_congr_on r x hc,interpolate_const]
    rw [he,he']; ring
  · have hi : interpolate r (fun z => p z*(b (target z)-b old)) x =
        interpolate r (fun z => p z*(-1)) x := by
      apply interpolate_congr_on
      intro z h; rw [ht z h,hb]; ring
    rw [hi,interpolate_mul_const]; ring

end FiniteLabels

namespace ActualLabels
open FiniteLabels DyadicHats DirectionNeighbors ConeCoordinates

lemma badWeight_cases (a : ℂ) (n : Label) : badWeight a n = 0 ∨ badWeight a n = 1 := by
  unfold badWeight; split_ifs <;> simp
lemma badWeight_nonneg (a : ℂ) (n : Label) : 0 ≤ badWeight a n := by
  rcases badWeight_cases a n with h|h <;> linarith
lemma badWeight_le_one (a : ℂ) (n : Label) : badWeight a n ≤ 1 := by
  rcases badWeight_cases a n with h|h <;> linarith

lemma rate_nonneg (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : 0 ≤ rate h r x n :=
  interpolate_nonneg r x (switchChance_nonneg h r n)
lemma rate_le_one (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : rate h r x n ≤ 1 :=
  interpolate_le_const r x (switchChance_le_one h r n)

theorem row_drift {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) {anchor : ℂ}
    (ha : ‖theta h r q-anchor‖ ≤ 1/800) (old : Label) :
    expect (row h r x old) (badWeight anchor)+rate h r x old = badWeight anchor old := by
  apply spatialRow_absorbing _ _ _ _ _ _ _ _ (badWeight_cases _ _)
  · intro z hz
    have he := nearby_sample_close hr h q hx hE z hz
    have ht := target_close h r z
    have hn : ‖(target h r z:ℂ)-anchor‖ ≤
        ‖(target h r z:ℂ)-Theta h r z‖+‖Theta h r z-theta h r q‖+‖theta h r q-anchor‖ := by
      simpa only [dist_eq_norm] using dist_triangle4 (target h r z:ℂ) (Theta h r z) (theta h r q) anchor
    have ht' : ‖(target h r z:ℂ)-Theta h r z‖ < 1/2000 := by simpa only [norm_sub_rev] using ht
    exact ite_eq_left (by linarith)
  · intro hb z hz
    have hba : ‖(old:ℂ)-anchor‖ ≤ 1/200 := by
      by_contra hn
      unfold badWeight at hb
      rw [ite_eq_right hn] at hb
      norm_num at hb
    have he := nearby_sample_close hr h q hx hE z hz
    apply probability_eq_zero
    have hn : ‖(old:ℂ)-Theta h r z‖ ≤
        ‖(old:ℂ)-anchor‖+‖anchor-theta h r q‖+‖theta h r q-Theta h r z‖ := by
      simpa only [dist_eq_norm] using dist_triangle4 (old:ℂ) anchor (theta h r q) (Theta h r z)
    have he' : ‖theta h r q-Theta h r z‖ ≤ 1/1000 := by simpa only [norm_sub_rev] using he
    have ha' : ‖anchor-theta h r q‖ ≤ 1/800 := by simpa only [norm_sub_rev] using ha
    linarith

lemma law_drift {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) {anchor : ℂ}
    (ha : ‖theta h r q-anchor‖ ≤ 1/800) (μ : Law Label) :
    expect (move μ (row h r x)) (badWeight anchor)+expect μ (rate h r x) =
      expect μ (badWeight anchor) := by
  rw [expect_move,← expect_add]
  congr 1
  funext old
  exact row_drift hr h q hx hE ha old

end ActualLabels

namespace ActualLabels
open FiniteLabels DyadicHats DirectionNeighbors Finset

lemma switchCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (k : ℕ) :
    0 ≤ switchCost h r x k := by
  cases k with
  | zero => exact zero_le_one
  | succ k => exact FiniteLabels.expect_nonneg _ (rate_nonneg h (r (k+1)) x)
lemma switchCost_le_one (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (k : ℕ) :
    switchCost h r x k ≤ 1 := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact expect_le_one _ (rate_le_one h (r (k+1)) x)

/-- A telescoping estimate between arbitrary birth and death times. These are
geometric low-energy assumptions on a path, not a switch-budget premise. -/
theorem switchCost_sum (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ) (x : ℂ)
    (anchor : ℕ → ℂ) (exceptional : ℕ → Bool) {b m : ℕ} (hbm : b ≤ m)
    (hr : ∀ k ∈ Finset.Ico b m, 0 < r (k+1))
    (hx : ∀ k ∈ Finset.Ico b m, boxNorm (x-point (r (k+1)) (q (k+1))) ≤ 50*r (k+1))
    (hE : ∀ k ∈ Finset.Ico b m, exceptional (k+1) = false →
      energy h (r (k+1)) (q (k+1)) ≤ (1/1000:ℝ)^2)
    (ha : ∀ k ∈ Finset.Ico b m, exceptional (k+1) = false →
      anchor (k+1) = anchor k ∧ ‖theta h (r (k+1)) (q (k+1))-anchor k‖ ≤ 1/800) :
    (∑ k ∈ Finset.Ico b m, switchCost h r x (k+1)) ≤
      1+2*∑ k ∈ Finset.Ico b m, if exceptional (k+1) then (1:ℝ) else 0 := by
  let v : ℕ → ℝ := fun k => expect (marginal h r k x) (badWeight (anchor k))
  have hv0 (k : ℕ) : 0 ≤ v k := FiniteLabels.expect_nonneg _ (badWeight_nonneg _)
  have hv1 (k : ℕ) : v k ≤ 1 := expect_le_one _ (badWeight_le_one _)
  have hs (k : ℕ) (hk : k ∈ Finset.Ico b m) : switchCost h r x (k+1) ≤
      v k-v (k+1)+2*(if exceptional (k+1) then (1:ℝ) else 0) := by
    cases he : exceptional (k+1) with
    | false =>
      obtain ⟨heq,hclose⟩ := ha k hk he
      have hd := law_drift (hr k hk) h (q (k+1)) (hx k hk) (hE k hk he) hclose (marginal h r k x)
      have hd' : v (k+1)+switchCost h r x (k+1) = v k := by
        simpa only [v,marginal,switchCost,heq] using hd
      simp only [Bool.false_eq_true,ite_false,mul_zero,add_zero]
      linarith
    | true =>
      simp only [ite_true,mul_one]
      linarith [switchCost_le_one h r x (k+1),hv0 k,hv1 (k+1)]
  have hall := sum_le_sum hs
  rw [sum_add_distrib,← mul_sum] at hall
  have ht : (∑ k ∈ Finset.Ico b m, (v k-v (k+1))) = v b-v m := by
    have hh := Finset.sum_Ico_sub (fun k => -v k) hbm
    simpa only [neg_sub_neg] using hh
  rw [ht] at hall
  linarith [hv1 b,hv0 m]

end ActualLabels

namespace IntrinsicMarks
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

omit [Fintype ι] in
lemma activePath_valid {t : Tree ι E} {p : List ι} (h : activePath t p) : validPath t p := by
  induction p generalizing t with
  | nil => cases t <;> simp_all [activePath,validPath]
  | cons i p ih => cases t with
    | leaf v => exact h.elim
    | branch t => exact ih h

lemma rootEval_mono_active (t : Tree ι E) {F G : List ι → ℝ}
    (h : ∀ p, activePath t p → F p ≤ G p) : rootEval t F ≤ rootEval t G := by
  induction t generalizing F G with
  | leaf v =>
    by_cases hv : v = 0
    · simp [rootEval,hv]
    · exact mul_le_mul_of_nonneg_left (h [] hv) (norm_nonneg v)
  | branch t ih =>
    apply mul_le_mul_of_nonneg_left _ (survival_nonneg t)
    exact Finset.sum_le_sum fun i _ => ih i (fun p hp => h (i::p) hp)

lemma lateEval_mono_active (t : Tree ι E) {F G : List ι → ℕ → ℝ}
    (h : ∀ p b, activePath t p → b ≤ p.length → F p b ≤ G p b) : lateEval t F ≤ lateEval t G := by
  induction t generalizing F G with
  | leaf v => rfl
  | branch t ih =>
    unfold lateEval
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (survival_le_one t))
      exact Finset.sum_le_sum fun i _ => rootEval_mono_active (t i) (fun p hp => h (i::p) 1 hp (by simp))
    · exact Finset.sum_le_sum fun i _ => ih i (fun p b hp hb => h (i::p) (b+1) hp (by simpa using Nat.succ_le_succ hb))

lemma particleEval_mono_active (t : Tree ι E) {F G : List ι → ℕ → ℝ}
    (h : ∀ p b, activePath t p → b ≤ p.length → F p b ≤ G p b) : particleEval t F ≤ particleEval t G :=
  add_le_add (rootEval_mono_active t (fun p hp => h p 0 hp (Nat.zero_le _)))
    (lateEval_mono_active t h)

omit [Fintype ι] in
lemma active_append {t : Tree ι E} {p q : List ι} (h : activePath t (p++q)) :
    activePath (atPath t p) q := by
  induction p generalizing t with
  | nil => simpa only [atPath,List.nil_append] using h
  | cons i p ih =>
    cases t with
    | leaf v => exact h.elim
    | branch t => exact ih h

end IntrinsicMarks

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks

lemma pathWeight_nonneg {N : ℕ} (q : Grid N) (p : List (Grid N)) : 0 ≤ pathWeight q p := by
  induction p generalizing q with
  | nil => exact zero_le_one
  | cons s p ih => exact mul_nonneg (step_nonneg q s) (ih s)

lemma active_length {N : ℕ} (v : Grid N → ℂ) {k : ℕ} {b : ℝ} {q : Grid N}
    {p : List (Grid N)} (h : activePath (tree v k b q) p) : p.length = k := by
  induction k generalizing b q p with
  | zero => cases p with
    | nil => rfl
    | cons i p => exact h.elim
  | succ k ih => cases p with
    | nil => exact h.elim
    | cons i p => exact congrArg Nat.succ (ih h)

lemma active_ne_zero {N : ℕ} (v : Grid N → ℂ) {k : ℕ} {b : ℝ} {q : Grid N}
    {p : List (Grid N)} (h : activePath (tree v k b q) p) : b ≠ 0 := by
  induction k generalizing b q p with
  | zero => cases p with
    | nil =>
      intro hb
      simp [tree,activePath,hb] at h
    | cons i p => exact h.elim
  | succ k ih => cases p with
    | nil => exact h.elim
    | cons i p => exact (mul_ne_zero_iff.mp (ih h)).1

lemma atPath_tree {N : ℕ} (v : Grid N → ℂ) {k : ℕ} (b : ℝ) (q : Grid N)
    (p : List (Grid N)) (hp : p.length ≤ k) :
    atPath (tree v k b q) p = tree v (k-p.length) (b*pathWeight q p) (lastVertex q p) := by
  induction p generalizing k b q with
  | nil => simp [atPath,pathWeight,lastVertex]
  | cons i p ih =>
    cases k with
    | zero => simp at hp
    | succ k =>
      simp only [tree,atPath]
      rw [ih (b*step q i) i (by simpa using hp)]
      simp only [List.length_cons,Nat.succ_sub_succ_eq_sub,pathWeight,lastVertex,mul_assoc]

lemma active_hat_support {N : ℕ} (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {k : ℕ} {b : ℝ} {q : Grid N} {p : List (Grid N)}
    (h : activePath (tree v k b q) p) {x : ℂ} (hx : hat r (lastVertex q p) x ≠ 0) :
    hat (scale r k) q x ≠ 0 := by
  induction k generalizing b q p with
  | zero => cases p with
    | nil => simpa [lastVertex,scale] using hx
    | cons i p => exact h.elim
  | succ k ih => cases p with
    | nil => exact h.elim
    | cons i p =>
      have hi := ih h hx
      have hs := (mul_ne_zero_iff.mp (active_ne_zero v h)).2
      rw [scale_succ]
      exact step_support (scale_pos hr k) hs hi

lemma lastVertex_append {N : ℕ} (q : Grid N) (p s : List (Grid N)) :
    lastVertex q (p++s) = lastVertex (lastVertex q p) s := by
  induction p generalizing q with
  | nil => rfl
  | cons i p ih => exact ih i

/-- Actual spatial locality, at every prefix of every positive-mass particle
path, for every terminal position in the genuine finest hat support. -/
theorem active_prefix_locality {N : ℕ} (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {k : ℕ} {b : ℝ} {q : Grid N} {p s : List (Grid N)}
    (h : activePath (tree v k b q) (p++s)) {x : ℂ}
    (hx : hat r (lastVertex q (p++s)) x ≠ 0) :
    boxNorm (x-point (scale r (k-p.length)) (lastVertex q p)) < scale r (k-p.length) := by
  have hp : p.length ≤ k := by have := active_length v h; simp only [List.length_append] at this; omega
  have hh := active_append h
  rw [atPath_tree v b q p hp] at hh
  rw [lastVertex_append] at hx
  exact (hat_ne_zero_iff (scale_pos hr _) _ _).mp (active_hat_support v hr hh hx)

end ActualMarkTrees

namespace IntrinsicMarks
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma anchor_zero (e : E) (δ : ℝ) (t : Tree ι E) (n : E)
    (hm : markIndicator e δ t n [] = 0) :
    anchor e δ t n [] = n ∧ ‖direction e (vector t)-n‖ ≤ δ := by
  cases t with
  | leaf v =>
    have hc : ¬δ < ‖direction e v-n‖ := by
      intro hc
      simp [markIndicator,hc] at hm
    exact ⟨by simp [anchor,reset,hc],le_of_not_gt hc⟩
  | branch t =>
    have hc : ¬δ < ‖direction e (∑ i,vector (t i))-n‖ := by
      intro hc
      simp [markIndicator,hc] at hm
    exact ⟨by simp [anchor,reset,hc],le_of_not_gt hc⟩

lemma anchor_step (e : E) (δ : ℝ) (t : Tree ι E) (n : E) (p : List ι)
    (hp : validPath t p) {s : ℕ} (hs : s < p.length)
    (hm : markIndicator e δ t n (p.take (s+1)) = 0) :
    anchor e δ t n (p.take (s+1)) = anchor e δ t n (p.take s) ∧
      ‖direction e (vector (atPath t (p.take (s+1))))-anchor e δ t n (p.take s)‖ ≤ δ := by
  induction p generalizing t n s with
  | nil => simp at hs
  | cons i p ih =>
    cases t with
    | leaf v => simp [validPath] at hp
    | branch t =>
      cases s with
      | zero =>
        have hm' : markIndicator e δ (t i) (reset δ (direction e (∑ j,vector (t j))) n) [] = 0 := by
          simpa only [List.take_succ_cons,List.take_zero,markIndicator,reset] using hm
        simpa only [List.take_succ_cons,List.take_zero,anchor,atPath] using
          anchor_zero e δ (t i) (reset δ (direction e (∑ j,vector (t j))) n) hm'
      | succ s =>
        simp only [List.length_cons,Nat.succ_lt_succ_iff] at hs
        simpa only [List.take_succ_cons,anchor,atPath] using
          ih (t i) (reset δ (direction e (∑ j,vector (t j))) n) hp hs hm

lemma rootMark_cons (e : E) {δ : ℝ} (hδ : 0 ≤ δ) (t : Tree ι E) (i : ι) (p : List ι) :
    rootMarkIndicator e δ t (i::p) = markIndicator e δ t (direction e (vector t)) (i::p) := by
  cases t <;> simp [rootMarkIndicator,markIndicator,vector,not_lt_of_ge hδ]

lemma rootAnchor_step (e : E) {δ : ℝ} (hδ : 0 ≤ δ) (t : Tree ι E) (p : List ι)
    (hp : validPath t p) {s : ℕ} (hs : s < p.length)
    (hm : rootMarkIndicator e δ t (p.take (s+1)) = 0) :
    rootAnchor e δ t (p.take (s+1)) = rootAnchor e δ t (p.take s) ∧
      ‖direction e (vector (atPath t (p.take (s+1))))-rootAnchor e δ t (p.take s)‖ ≤ δ := by
  apply anchor_step e δ t (direction e (vector t)) p hp hs
  cases p with
  | nil => simp at hs
  | cons i p => simpa only [List.take_succ_cons,rootMark_cons e hδ] using hm

lemma markIndicator_cases (e : E) (δ : ℝ) (t : Tree ι E) (n : E) (p : List ι) :
    markIndicator e δ t n p = 0 ∨ markIndicator e δ t n p = 1 := by
  induction p generalizing t n with
  | nil => cases t <;> simp only [markIndicator] <;> split_ifs <;> simp
  | cons i p ih =>
    cases t with
    | leaf v => exact Or.inl rfl
    | branch t => exact ih _ _

lemma rootMarkIndicator_cases (e : E) (δ : ℝ) (t : Tree ι E) (p : List ι) :
    rootMarkIndicator e δ t p = 0 ∨ rootMarkIndicator e δ t p = 1 := by
  cases p with
  | nil => cases t <;> exact Or.inr rfl
  | cons i p => cases t with
    | leaf v => exact Or.inl rfl
    | branch t => exact markIndicator_cases e δ (t i) _ p

lemma direction_smul_pos (e v : E) {b : ℝ} (hb : 0 < b) : direction e (b • v) = direction e v := by
  by_cases hv : v = 0
  · simp [hv,direction]
  · have hb0 := hb.ne'
    simp only [direction,smul_eq_zero,hb0,hv,or_self,ite_false,norm_smul,
      Real.norm_eq_abs,abs_of_pos hb,mul_inv_rev,smul_smul]
    congr 1
    field_simp

omit [Fintype ι] [InnerProductSpace ℝ E] in
lemma pathCharge_sum (C : List ι → ℝ) (p : List ι) (b : ℕ) :
    pathCharge C p b = ∑ s ∈ Finset.Ico b (p.length+1), C (p.take s) := by
  induction p generalizing C b with
  | nil => cases b <;> simp [pathCharge]
  | cons i p ih =>
    cases b with
    | zero =>
      simp only [pathCharge,ih,List.length_cons,Nat.Ico_zero_eq_range]
      rw [Finset.sum_range_succ' (fun s => C ((i::p).take s)) (p.length+1)]
      simp only [List.take_succ_cons,List.take_zero]
      exact add_comm _ _
    | succ b =>
      simp only [pathCharge,ih,List.length_cons]
      rw [← Finset.sum_Ico_add' (fun s => C ((i::p).take s)) b (p.length+1) 1]
      simp only [List.take_succ_cons]

end IntrinsicMarks

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks

theorem direction_at_prefix {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) {k : ℕ} {b : ℝ} (hb : 0 ≤ b)
    {q : Grid N} {p s : List (Grid N)}
    (hp : activePath (tree (fun q => vectorMass h r q) k b q) (p++s)) :
    direction (1:ℂ) (vector (atPath (tree (fun q => vectorMass h r q) k b q) p)) =
      DirectionNeighbors.theta h (scale r (k-p.length)) (lastVertex q p) := by
  have hlen : p.length ≤ k := by have := active_length _ hp; simp only [List.length_append] at this; omega
  rw [atPath_tree _ b q p hlen,vector_actual hr hR hN hh hsupp]
  have hpa := active_append hp
  rw [atPath_tree _ b q p hlen] at hpa
  have hpos : 0 < b*pathWeight q p := lt_of_le_of_ne
    (mul_nonneg hb (pathWeight_nonneg q p)) (Ne.symm (active_ne_zero _ hpa))
  exact direction_smul_pos _ _ hpos

end ActualMarkTrees

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks Finset DirectionNeighbors ActualLabels

lemma mark_nonneg {ι : Type*} [Fintype ι] (t : Tree ι ℂ) (p : List ι) :
    0 ≤ rootMarkIndicator (1:ℂ) (1/800) t p := by
  rcases rootMarkIndicator_cases (1:ℂ) (1/800) t p with h | h
  · exact h.symm.le
  · exact h.symm ▸ zero_le_one

/-- The switch bound on every genuinely occupied path, using its complete
intrinsic history, even before the particle's birth. -/
theorem path_switch_bound {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N)
    {p : List (Grid N)} (hp : activePath (tree (fun q => vectorMass h r q) k 1 q) p)
    {b : ℕ} (hb : b ≤ p.length) {x : ℂ} (hx : hat r (lastVertex q p) x ≠ 0) :
    pathSwitches h r k x p b ≤ 2+
      2*pathCharge (rootMarkIndicator (1:ℂ) (1/800) (tree (fun q => vectorMass h r q) k 1 q)) p b+
      2000000*pathCharge (pathEnergy h r k q) p b := by
  classical
  let t := tree (fun q => vectorMass h r q) k 1 q
  let M := rootMarkIndicator (1:ℂ) (1/800) t
  let rs : ℕ → ℝ := fun i => scale r (k-i)
  let qs : ℕ → ℤ × ℤ := fun i => lastVertex q (p.take i)
  let E : ℕ → ℝ := fun i => energy h (rs i) (qs i)
  let A : ℕ → ℂ := fun i => rootAnchor (1:ℂ) (1/800) t (p.take i)
  let bad : ℕ → Bool := fun i => decide (M (p.take i) ≠ 0 ∨ (1/1000:ℝ)^2 < E i)
  have hlen : p.length = k := active_length _ hp
  have hpos (i : ℕ) : 0 < rs i := scale_pos hr _
  have he0 (i : ℕ) : 0 ≤ E i := energy_nonneg h _ _
  have hpref (i : ℕ) : activePath t (p.take i++p.drop i) := by
    simpa only [List.take_append_drop] using hp
  have hloc (i : ℕ) (hi : i ≤ p.length) : boxNorm (x-point (rs i) (qs i)) ≤ 50*rs i := by
    have hl := active_prefix_locality (fun q => vectorMass h r q) hr (hpref i)
      (by simpa only [List.take_append_drop] using hx)
    have hli : (p.take i).length = i := by simp only [List.length_take,min_eq_left hi]
    simp only [hli] at hl
    exact hl.le.trans (by dsimp only [rs,qs]; nlinarith [scale_pos hr (k-i)])
  have hdir (i : ℕ) (hi : i ≤ p.length) :
      direction (1:ℂ) (vector (atPath t (p.take i))) = theta h (rs i) (qs i) := by
    have hd := direction_at_prefix hr hR hN hh hsupp (by norm_num : (0:ℝ) ≤ 1) (hpref i)
    simpa only [List.length_take,min_eq_left hi] using hd
  have hbad (i : ℕ) : bad i = false → M (p.take i) = 0 ∧ E i ≤ (1/1000:ℝ)^2 := by
    simp only [bad,decide_eq_false_iff_not,not_or,not_not,not_lt]
    exact id
  have hs := switchCost_sum h rs qs x A bad (by omega : b ≤ k)
    (fun i _ => hpos (i+1))
    (fun i hi => hloc (i+1) (by simp only [Finset.mem_Ico] at hi; omega))
    (fun i _ hi => (hbad (i+1) hi).2)
    (fun i hi he => by
      have hil : i < p.length := by simp only [Finset.mem_Ico] at hi; omega
      have ha := rootAnchor_step (1:ℂ) (by norm_num : (0:ℝ) ≤ 1/800) t p
        (activePath_valid hp) hil (hbad (i+1) he).1
      rw [hdir (i+1) (by omega)] at ha
      exact ha)
  have hind (i : ℕ) : (if bad i then (1:ℝ) else 0) ≤ M (p.take i)+1000000*E i := by
    rcases rootMarkIndicator_cases (1:ℂ) (1/800) t (p.take i) with hm | hm
    · change M (p.take i) = 0 at hm
      by_cases he : (1/1000:ℝ)^2 < E i
      · simp only [bad,hm,ne_eq,not_true_eq_false,false_or,he,decide_true,ite_true]
        nlinarith
      · simp only [bad,hm,ne_eq,not_true_eq_false,false_or,he,decide_false,Bool.false_eq_true,ite_false]
        nlinarith [he0 i]
    · change M (p.take i) = 1 at hm
      have hh0 := he0 i
      by_cases he : bad i = true <;> simp [he,show M (p.take i) = 1 from hm] <;> nlinarith
  have hterm : (∑ i ∈ Ico b k, if bad (i+1) then (1:ℝ) else 0) ≤
      pathCharge M p b+1000000*pathCharge (pathEnergy h r k q) p b := by
    calc
      _ ≤ ∑ i ∈ Ico b k, (M (p.take (i+1))+1000000*E (i+1)) :=
        sum_le_sum (fun i _ => hind (i+1))
      _ = ∑ i ∈ Ico (b+1) (k+1), (M (p.take i)+1000000*E i) := by
        exact sum_Ico_add' (fun i => M (p.take i)+1000000*E i) b k 1
      _ ≤ ∑ i ∈ Ico b (p.length+1), (M (p.take i)+1000000*E i) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_Ico] at hi ⊢
          omega
        · intro i _ _
          exact add_nonneg (mark_nonneg t _) (mul_nonneg (by norm_num) (he0 i))
      _ = _ := by
        rw [pathCharge_sum,pathCharge_sum,sum_add_distrib,mul_sum]
        congr 1
        apply sum_congr rfl
        intro i hi
        congr 1
        have hil : i ≤ p.length := by have := (Finset.mem_Ico.mp hi).2; omega
        simp only [E,rs,qs,pathEnergy,List.length_take,min_eq_left hil]
  have hsum : pathSwitches h r k x p b = switchCost h rs x b+
      ∑ i ∈ Ico b k, switchCost h rs x (i+1) := by
    change (∑ i ∈ Ico b (p.length+1), switchCost h rs x i) = _
    rw [hlen,Finset.sum_eq_sum_Ico_succ_bot (by omega : b < k+1),Finset.sum_Ico_add']
  rw [hsum]
  have h1 := switchCost_le_one h rs x b
  change _ ≤ 2+2*pathCharge M p b+2000000*pathCharge (pathEnergy h r k q) p b
  linarith

end ActualMarkTrees

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Packing
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

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

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks Finset DirectionNeighbors

lemma nodeCharge_scale {N : ℕ} (v : Grid N → ℂ) (k : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (q : Grid N) (C : List (Grid N) → ℝ) :
    nodeCharge (tree v k b q) C = b*nodeCharge (tree v k 1 q) C := by
  induction k generalizing b q C with
  | zero => simp [tree,nodeCharge,Real.norm_eq_abs,abs_of_nonneg hb,mul_assoc]
  | succ k ih =>
    change ‖vector (tree v (k+1) b q)‖*C []+
      (∑ a : Grid N, nodeCharge (tree v k (b*step q a) a) (fun p => C (a::p))) =
      b*(‖vector (tree v (k+1) 1 q)‖*C []+
      (∑ a : Grid N, nodeCharge (tree v k (1*step q a) a) (fun p => C (a::p))))
    simp only [vector_tree,norm_smul,Real.norm_eq_abs,abs_of_nonneg hb,
      abs_one,one_mul]
    simp_rw [ih (mul_nonneg hb (step_nonneg _ _)),ih (step_nonneg _ _)]
    rw [mul_add,mul_sum]
    congr 1
    · ring
    · apply sum_congr rfl
      intro a ha
      ring

lemma sum_nodeCharge {N : ℕ} (v : Grid N → ℂ) (k : ℕ) (C : ℕ → Grid N → ℝ) :
    (∑ q, nodeCharge (tree v k 1 q) (spatialCharge C k q)) =
      ∑ j ∈ range (k+1), ∑ a : Grid N,
        ‖∑ z : Grid N, coeff N j a z • v z‖*C j a := by
  induction k with
  | zero =>
    have hv (a : Grid N) : (∑ z : Grid N, coeff N 0 a z • v z) = v a := by
      simpa only [tree,vector,one_smul] using (vector_tree v 0 1 a).symm
    simp only [tree,nodeCharge,one_smul,spatialCharge,List.length_nil,Nat.sub_zero,
      lastVertex,Nat.zero_add,sum_range_one,hv]
  | succ k ih =>
    have hrec (q : Grid N) : nodeCharge (tree v (k+1) 1 q) (spatialCharge C (k+1) q) =
        ‖∑ z : Grid N, coeff N (k+1) q z • v z‖*C (k+1) q+
        ∑ a : Grid N, step q a*nodeCharge (tree v k 1 a) (spatialCharge C k a) := by
      change ‖vector (tree v (k+1) 1 q)‖*spatialCharge C (k+1) q []+_ = _
      simp only [vector_tree,one_smul,spatialCharge,List.length_nil,Nat.sub_zero,lastVertex,
        one_mul,List.length_cons,Nat.add_sub_add_right]
      congr 1
      apply sum_congr rfl
      intro a ha
      exact nodeCharge_scale v k (step_nonneg q a) a _
    simp_rw [hrec]
    rw [sum_add_distrib,Finset.sum_comm (f := fun (q a : Grid N) => step q a*
      nodeCharge (tree v k 1 a) (spatialCharge C k a))]
    simp_rw [← sum_mul,grid_step_column,one_mul]
    rw [ih]
    conv_rhs => rw [sum_range_succ]
    exact add_comm _ _

lemma sum_energyCharge {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) :
    (∑ q : Grid N, nodeCharge (tree (fun q => vectorMass h r q) k 1 q)
      (pathEnergy h r k q)) =
      ∑ j ∈ range (k+1), ∑ q : Grid N, scalarMass h (scale r j) q*energy h (scale r j) q := by
  change (∑ q : Grid N, nodeCharge (tree (fun q => vectorMass h r q) k 1 q)
    (spatialCharge (fun j q => energy h (scale r j) q) k q)) = _
  rw [sum_nodeCharge]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro q hq
  rw [← vectorMass_coeff hr hR hN hh hsupp]
  rfl

theorem particle_switch_bound {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    particleEval (tree (fun q => vectorMass h r q) k 1 q) (particleSwitches h r k q) ≤
      2560004*terminalMass (tree (fun q => vectorMass h r q) k 1 q)+
      2000000*nodeCharge (tree (fun q => vectorMass h r q) k 1 q) (pathEnergy h r k q) := by
  have hp := particleEval_mono_active (tree (fun q => vectorMass h r q) k 1 q)
    (F := particleSwitches h r k q)
    (fun p b hp hb => path_switch_bound hr hR hN hh hsupp k q hp hb (x := point r (lastVertex q p)) (by
      rw [hat_at_point hr.ne']
      norm_num))
  simp only [particleEval_add,particleEval_smul,particleEval_const,particle_occupancy,
    root_marked_occupancy] at hp
  have hm := costWithRoot_le (by simp : ‖(1:ℂ)‖ = 1)
    (by norm_num : (0:ℝ) < 1/800) (tree (fun q => vectorMass h r q) k 1 q)
  norm_num at hm
  change particleEval _ (particleSwitches h r k q) ≤ _ at hp
  linarith

/-- The switch budget for the actual finite spatial forest, with every birth
population included and frozen terminal positions observed. -/
theorem forest_switch_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) :
    (∑ q : Grid N, particleEval (tree (fun q => vectorMass h r q) k 1 q)
      (particleSwitches h r k q)) ≤
      (2560004+2000000*(576*(4097:ℝ)^2))*(∫ y, ‖h y‖) := by
  have hs := sum_le_sum (fun q (_ : q ∈ (univ : Finset (Grid N))) =>
    particle_switch_bound hr hR hN hh hsupp k q)
  simp only [sum_add_distrib,← mul_sum] at hs
  rw [sum_terminalMass,sum_energyCharge hr hR hN hh hsupp] at hs
  have ht := sum_scalarMass_grid_le (N := N) hh r
  have he := neighbor_energy_budget hr hR hN hh hsupp (k+1)
  change (∑ q : Grid N, ‖vectorMass h r q‖) ≤ ∫ y, ‖h y‖ at ht
  nlinarith only [hs,ht,he]

end ActualMarkTrees

namespace FiniteLabels
variable {ι : Type*} [Fintype ι]
lemma expect_le_const (μ : Law ι) {f : ι → ℝ} {c : ℝ} (h : ∀ i, f i ≤ c) :
    expect μ f ≤ c := (expect_mono μ h).trans_eq (expect_const μ c)
lemma expect_compare (μ ν : Law ι) {f : ι → ℝ} {c : ℝ} (h : ∀ i, |f i| ≤ c) :
    expect μ f ≤ expect ν f+c*l1dist μ ν := by
  have he := expectation_difference μ ν h
  change |expect μ f-expect ν f| ≤ c*l1dist μ ν at he
  have hl := le_abs_self (expect μ f-expect ν f)
  linarith
end FiniteLabels

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats Finset

lemma comparisonConstant_ge : 1280000 ≤ comparisonConstant := by
  dsimp [comparisonConstant]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Label)]
lemma comparisonConstant_pos : 0 < comparisonConstant := lt_of_lt_of_le (by norm_num) comparisonConstant_ge
lemma comparisonConstant_one : 1 ≤ comparisonConstant := by linarith [comparisonConstant_ge]

lemma rowDerivative_nonneg (h : ℂ → ℂ) {r : ℝ} (hr : 0 ≤ r) (x : ℂ) (n : Label) :
    0 ≤ rowDerivative h r x n := mul_nonneg hr (sum_nonneg (fun _ _ => norm_nonneg _))
lemma rowDerivative_uniform (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (x : ℂ) (n : Label) :
    rowDerivative h r x n ≤ 16*(Fintype.card Label:ℝ) := by
  have hh := spatialRow_local_derivative n (target h r) (switchChance h r n)
    (switchChance_nonneg h r n) (switchChance_le_one h r n) hr (by norm_num : (0:ℝ) ≤ 1)
    (q := x) (x := x) (by simp only [sub_self,boxNorm]; norm_num; positivity)
    (fun z _ => switchChance_le_one h r n z)
  change rowDerivative h r x n ≤ 16*(Fintype.card Label:ℝ)*1 at hh
  simpa only [mul_one] using hh
lemma initial_distance (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (x y : ℂ) :
    l1dist (initial h r x) (initial h r y) ≤ comparisonConstant/r*‖x-y‖ := by
  have he := spatialRow_distance (quantize 1 (by norm_num)) (target h r) (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_rfl) hr (by norm_num : (0:ℝ) ≤ 1)
    (fun _ => le_rfl) x y
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hr.le
  dsimp [comparisonConstant]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Label)]
lemma derivativeCost_uniform (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (i : ℕ) (hr : 0 < r i) :
    derivativeCost h r x i ≤ 16*(Fintype.card Label:ℝ) := by
  cases i with
  | zero =>
    have hh := spatialRow_local_derivative (quantize 1 (by norm_num)) (target h (r 0)) (fun _ => 1)
      (fun _ => zero_le_one) (fun _ => le_rfl) hr (by norm_num : (0:ℝ) ≤ 1)
      (q := x) (x := x) (by simp only [sub_self,boxNorm]; norm_num; positivity) (fun _ _ => le_rfl)
    change derivativeCost h r x 0 ≤ 16*(Fintype.card Label:ℝ)*1 at hh
    simpa only [mul_one] using hh
  | succ i => exact expect_le_const _ (rowDerivative_uniform h hr x)

lemma rate_local (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (q : ℤ × ℤ) (x y : ℂ)
    (hx : boxNorm (x-point r q) < 199*r) (hy : boxNorm (y-point r q) < 199*r) (n : Label) :
    rate h r x n ≤ comparisonConstant*(rate h r y n+energy h r q) := by
  have he := switchRate_local_compare (by norm_num : (0:ℝ) < 1/100) hr (Theta h r)
    (n:ℂ) (theta h r q) (point r q) x y hx hy (energy_controls hr h q)
  change rate h r x n ≤ 2*rate h r y n+8*((1/100:ℝ)⁻¹)^2*energy h r q at he
  norm_num at he
  have h0 := rate_nonneg h r y n
  have h1 := energy_nonneg h r q
  have hC := comparisonConstant_ge
  nlinarith

lemma row_local_distance (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (q : ℤ × ℤ) (x y : ℂ)
    (hx : boxNorm (x-point r q) < 199*r) (hy : boxNorm (y-point r q) < 199*r) (n : Label) :
    l1dist (row h r x n) (row h r y n) ≤
      comparisonConstant*‖x-y‖/r*(rate h r y n+energy h r q) := by
  have he := spatialSwitchRow_local_distance (by norm_num : (0:ℝ) < 1/100) hr (energy_nonneg h r q)
    (fun n : Label => (n:ℂ)) (Theta h r) (target h r) n (theta h r q) (point r q) x y hx hy
    (energy_controls hr h q)
  change l1dist (row h r x n) (row h r y n) ≤
    (Fintype.card Label:ℝ)*(16*(2*rate h r y n+8*((1/100:ℝ)⁻¹)^2*energy h r q)/r)*‖x-y‖ at he
  apply he.trans
  have h0 := rate_nonneg h r y n
  have h1 := energy_nonneg h r q
  have hb : (Fintype.card Label:ℝ)*(16*(2*rate h r y n+8*((1/100:ℝ)⁻¹)^2*energy h r q)) ≤
      comparisonConstant*(rate h r y n+energy h r q) := by
    dsimp [comparisonConstant]
    norm_num
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card Label)) h0,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card Label)) h1]
  have hb' := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hr.le) (norm_nonneg (x-y))
  convert hb' using 1 <;> ring

lemma row_local_derivative (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (q : ℤ × ℤ) (x y : ℂ)
    (hx : boxNorm (x-point r q) < 199*r) (hy : boxNorm (y-point r q) < 199*r) (n : Label) :
    rowDerivative h r x n ≤ comparisonConstant*(rate h r y n+energy h r q) := by
  have he := spatialSwitchRow_local_derivative (by norm_num : (0:ℝ) < 1/100) hr (energy_nonneg h r q)
    (fun n : Label => (n:ℂ)) (Theta h r) (target h r) n (theta h r q) (point r q) x y hx hy
    (energy_controls hr h q)
  change rowDerivative h r x n ≤
    16*(Fintype.card Label:ℝ)*(2*rate h r y n+8*((1/100:ℝ)⁻¹)^2*energy h r q) at he
  apply he.trans
  have h0 := rate_nonneg h r y n
  have h1 := energy_nonneg h r q
  dsimp [comparisonConstant]
  norm_num
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card Label)) h0,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card Label)) h1]

end ActualLabels

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats Finset

lemma energyRate_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ) (y : ℂ) (i : ℕ) :
    0 ≤ energyRate h r q y i := add_nonneg (switchCost_nonneg h r y i) (energy_nonneg h (r i) (q i))
lemma energyRate_le_five (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ) (y : ℂ) (i : ℕ) :
    energyRate h r q y i ≤ 5 := by
  have h1 := switchCost_le_one h r y i
  have h2 := energy_le_four h (r i) (q i)
  dsimp [energyRate]
  linarith

/-- Spatial comparison of the actual marginal laws. No independent coupling or
pointwise uniform distribution of labels is assumed. -/
theorem marginal_spatial_distance (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ)
    (x y : ℂ) (j : ℕ) (hr : ∀ i ≤ j, 0 < r i)
    (hx : ∀ i ≤ j, boxNorm (x-point (r i) (q i)) < 199*r i)
    (hy : ∀ i ≤ j, boxNorm (y-point (r i) (q i)) < 199*r i) :
    l1dist (marginal h r j x) (marginal h r j y) ≤
      comparisonConstant*‖x-y‖*∑ i ∈ range (j+1), energyRate h r q y i/r i := by
  induction j with
  | zero =>
    have he := initial_distance h (hr 0 le_rfl) x y
    have hc : 1 ≤ energyRate h r q y 0 := by
      dsimp [energyRate,switchCost]
      linarith [energy_nonneg h (r 0) (q 0)]
    have ht := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hc (hr 0 le_rfl).le)
      (mul_nonneg comparisonConstant_pos.le (norm_nonneg (x-y)))
    simp only [Nat.zero_add,sum_range_one,marginal]
    apply he.trans
    convert ht using 1
    ring
  | succ j ih =>
    have hd := ih (fun i hi => hr i (by omega)) (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega))
    have hm := move_compare (marginal h r j x) (marginal h r j y)
      (row h (r (j+1)) x) (row h (r (j+1)) y)
    have hrow : (∑ n, marginal h r j y n*l1dist (row h (r (j+1)) x n) (row h (r (j+1)) y n)) ≤
        comparisonConstant*‖x-y‖/r (j+1)*energyRate h r q y (j+1) := by
      calc
        _ ≤ expect (marginal h r j y) (fun n => comparisonConstant*‖x-y‖/r (j+1)*
            (rate h (r (j+1)) y n+energy h (r (j+1)) (q (j+1)))) := by
          exact expect_mono _ (row_local_distance h (hr (j+1) le_rfl) (q (j+1)) x y
            (hx (j+1) le_rfl) (hy (j+1) le_rfl))
        _ = _ := by rw [FiniteLabels.expect_mul,FiniteLabels.expect_add,FiniteLabels.expect_const]; rfl
    change l1dist (marginal h r (j+1) x) (marginal h r (j+1) y) ≤ _ at hm
    rw [sum_range_succ,mul_add]
    have hterm : comparisonConstant*‖x-y‖/r (j+1)*energyRate h r q y (j+1) =
        comparisonConstant*‖x-y‖*(energyRate h r q y (j+1)/r (j+1)) := by ring
    rw [hterm] at hrow
    linarith

lemma switchCost_spatial (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℤ × ℤ) (x y : ℂ) (i : ℕ)
    (hr : 0 < r (i+1)) (hx : boxNorm (x-point (r (i+1)) q) < 199*r (i+1))
    (hy : boxNorm (y-point (r (i+1)) q) < 199*r (i+1)) :
    switchCost h r x (i+1) ≤ comparisonConstant*(switchCost h r y (i+1)+energy h (r (i+1)) q)+
      l1dist (marginal h r i x) (marginal h r i y) := by
  have he := expect_compare (marginal h r i x) (marginal h r i y)
    (fun n => by rw [abs_of_nonneg (rate_nonneg h (r (i+1)) x n)]; exact rate_le_one h (r (i+1)) x n)
  have hrw := expect_mono (marginal h r i y) (rate_local h hr q x y hx hy)
  rw [FiniteLabels.expect_mul,FiniteLabels.expect_add,FiniteLabels.expect_const] at hrw
  change expect (marginal h r i y) (rate h (r (i+1)) x) ≤
    comparisonConstant*(switchCost h r y (i+1)+energy h (r (i+1)) q) at hrw
  change expect (marginal h r i x) (rate h (r (i+1)) x) ≤ _
  linarith

lemma derivativeCost_spatial (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℤ × ℤ) (x y : ℂ) (i : ℕ)
    (hr : 0 < r (i+1)) (hx : boxNorm (x-point (r (i+1)) q) < 199*r (i+1))
    (hy : boxNorm (y-point (r (i+1)) q) < 199*r (i+1)) :
    derivativeCost h r x (i+1) ≤ comparisonConstant*(switchCost h r y (i+1)+energy h (r (i+1)) q)+
      comparisonConstant*l1dist (marginal h r i x) (marginal h r i y) := by
  have he := expect_compare (marginal h r i x) (marginal h r i y)
    (fun n => by rw [abs_of_nonneg (rowDerivative_nonneg h hr.le x n)]; exact rowDerivative_uniform h hr x n)
  have hrw := expect_mono (marginal h r i y) (row_local_derivative h hr q x y hx hy)
  rw [FiniteLabels.expect_mul,FiniteLabels.expect_add,FiniteLabels.expect_const] at hrw
  have hcoef : 16*(Fintype.card Label:ℝ) ≤ comparisonConstant := by
    dsimp [comparisonConstant]
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Label)]
  have hm := mul_le_mul_of_nonneg_right hcoef (l1dist_nonneg (marginal h r i x) (marginal h r i y))
  change derivativeCost h r x (i+1) ≤ _ at he
  change expect (marginal h r i y) (rowDerivative h (r (i+1)) x) ≤
    comparisonConstant*(switchCost h r y (i+1)+energy h (r (i+1)) q) at hrw
  linarith

end ActualLabels

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Envelopes
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace GeometricFilter
open Finset
lemma filt_nonneg {c : ℕ → ℝ} (hc : ∀ i, 0 ≤ c i) (i : ℕ) : 0 ≤ filt c i := by
  induction i with
  | zero => exact hc 0
  | succ i ih => exact add_nonneg (hc _) (div_nonneg ih (by norm_num))
lemma filt_le {c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc : ∀ i, c i ≤ A) (i : ℕ) : filt c i ≤ 2*A := by
  induction i with
  | zero => exact (hc 0).trans (by linarith)
  | succ i ih => dsimp only [filt]; linarith [hc (i+1)]
lemma filt_mono {c d : ℕ → ℝ} (h : ∀ i, c i ≤ d i) (i : ℕ) : filt c i ≤ filt d i := by
  induction i with
  | zero => exact h 0
  | succ i ih => dsimp only [filt]; linarith [h (i+1)]
lemma filt_mul (c : ℕ → ℝ) (a : ℝ) (i : ℕ) : filt (fun j => a*c j) i = a*filt c i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [filt,ih]; ring
lemma filt_sum (c : ℕ → ℝ) (i : ℕ) :
    filt c i = ∑ j ∈ range (i+1), (1/2:ℝ)^(i-j)*c j := by
  induction i with
  | zero => simp [filt]
  | succ i ih =>
    rw [filt,ih]
    conv_rhs => rw [sum_range_succ]
    simp only [Nat.sub_self,pow_zero,one_mul]
    rw [add_comm]
    congr 1
    rw [div_eq_mul_inv,sum_mul]
    apply sum_congr rfl
    intro j hj
    have hj' : j ≤ i := by have := mem_range.mp hj; omega
    rw [show i+1-j = (i-j)+1 by omega,pow_succ]
    ring

lemma filt_tail_strong {c : ℕ → ℝ} (hc0 : ∀ i, 0 ≤ c i) {b m : ℕ} (hbm : b ≤ m) :
    (∑ i ∈ Ico b (m+1), filt c i) ≤ 2*∑ i ∈ Ico b (m+1), c i+2*filt c b := by
  have hid : (∑ i ∈ Ico (b+1) (m+1), filt c i) =
      (∑ i ∈ Ico (b+1) (m+1), c i)+(∑ i ∈ Ico b m, filt c i)/2 := by
    rw [← sum_Ico_add' (fun i => filt c i) b m 1,
      ← sum_Ico_add' (fun i => c i) b m 1]
    simp only [filt,sum_add_distrib,sum_div]
  have hsplit := sum_eq_sum_Ico_succ_bot (f := filt c) (by omega : b < m+1)
  have hcsplit := sum_eq_sum_Ico_succ_bot (f := c) (by omega : b < m+1)
  have he : (∑ i ∈ Ico b m, filt c i) ≤ ∑ i ∈ Ico b (m+1), filt c i := by
    apply sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (by omega))
    intro i _ _
    exact filt_nonneg hc0 i
  rw [hsplit,hid] at he
  rw [hsplit,hid,hcsplit]
  linarith [hc0 b]

/-- The complete pre-birth history costs a fixed amount, not the birth index. -/
theorem filt_tail {c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc0 : ∀ i, 0 ≤ c i)
    (hcA : ∀ i, c i ≤ A) {b m : ℕ} (hbm : b ≤ m) :
    (∑ i ∈ Ico b (m+1), filt c i) ≤ 2*∑ i ∈ Ico b (m+1), c i+4*A := by
  have h1 := filt_tail_strong hc0 hbm
  have h2 := filt_le hA hcA b
  linarith

/-- Two geometric convolutions are summable on every occupied lifetime. -/
theorem double_tail {c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc0 : ∀ i, 0 ≤ c i)
    (hcA : ∀ i, c i ≤ A) {b m : ℕ} (hbm : b ≤ m) :
    (∑ i ∈ Ico b (m+1), filt (filt c) i) ≤ 4*∑ i ∈ Ico b (m+1), c i+16*A := by
  have h1 := filt_tail hA hc0 hcA hbm
  have h2 := filt_tail (by positivity : 0 ≤ 2*A) (filt_nonneg hc0) (filt_le hA hcA) hbm
  linarith
end GeometricFilter

namespace GeometricFilter
open Finset
lemma radius_sum {r c : ℕ → ℝ} (j : ℕ) (hr : ∀ i ≤ j, 0 < r i)
    (hstep : ∀ i < j, r i = 2*r (i+1)) :
    r j*(∑ i ∈ range (j+1), c i/r i) = filt c j := by
  induction j with
  | zero => simp only [Nat.zero_add,sum_range_one,filt]; field_simp [(hr 0 le_rfl).ne']
  | succ j ih =>
    have hs := ih (fun i hi => hr i (by omega)) (fun i hi => hstep i (by omega))
    rw [sum_range_succ,mul_add,filt]
    have he : r (j+1)*(c (j+1)/r (j+1)) = c (j+1) := by field_simp [(hr (j+1) le_rfl).ne']
    rw [he,add_comm]
    congr 1
    rw [← hs,hstep j (by omega)]
    ring
end GeometricFilter

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats Finset GeometricFilter

lemma spatialConstant_pos : 0 < spatialConstant := by
  dsimp [spatialConstant]
  have := comparisonConstant_pos
  positivity
lemma spatialConstant_ge : 2*comparisonConstant ≤ spatialConstant := by
  dsimp [spatialConstant]
  nlinarith [comparisonConstant_one]

lemma scaled_marginal_distance (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ)
    (x y : ℂ) (j : ℕ) (hr : ∀ i ≤ j, 0 < r i)
    (hstep : ∀ i < j, r i = 2*r (i+1))
    (hx : ∀ i ≤ j, boxNorm (x-point (r i) (q i)) < 199*r i)
    (hy : ∀ i ≤ j, boxNorm (y-point (r i) (q i)) < 199*r i) :
    r j*l1dist (marginal h r j x) (marginal h r j y) ≤
      comparisonConstant*‖x-y‖*filt (energyRate h r q y) j := by
  have hd := mul_le_mul_of_nonneg_left (marginal_spatial_distance h r q x y j hr hx hy) (hr j le_rfl).le
  have he := radius_sum (c := energyRate h r q y) j hr hstep
  calc
    _ ≤ r j*(comparisonConstant*‖x-y‖*∑ i ∈ range (j+1), energyRate h r q y i/r i) := hd
    _ = _ := by rw [← mul_assoc,mul_comm (r j),mul_assoc,he]

/-- Actual spatial comparison at every point of the neighborhood. The gradient
versions are pointwise bounded; differentiability is only needed later for IBP. -/
theorem filtered_spatial_cost (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ)
    (x y : ℂ) (j : ℕ) (hr : ∀ i ≤ j, 0 < r i)
    (hstep : ∀ i < j, r i = 2*r (i+1))
    (hx : ∀ i ≤ j, boxNorm (x-point (r i) (q i)) < 199*r i)
    (hy : ∀ i ≤ j, boxNorm (y-point (r i) (q i)) < 199*r i)
    (hdist : ‖x-y‖ ≤ 104*r j) :
    switchCost h r x j+derivativeCost h r x j ≤
      spatialConstant*filt (energyRate h r q y) j := by
  let c := energyRate h r q y
  have hc0 : ∀ i, 0 ≤ c i := energyRate_nonneg h r q y
  have hC := comparisonConstant_one
  have hC0 := comparisonConstant_pos.le
  cases j with
  | zero =>
    have he : 1 ≤ c 0 := by dsimp [c,energyRate,switchCost]; linarith [energy_nonneg h (r 0) (q 0)]
    have ht := derivativeCost_uniform h r x 0 (hr 0 le_rfl)
    have hbound : 1+16*(Fintype.card Label:ℝ) ≤ 2*comparisonConstant := by
      dsimp [comparisonConstant]
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Label)]
    have hh := mul_le_mul_of_nonneg_left he spatialConstant_pos.le
    dsimp only [switchCost,filt]
    change _ ≤ spatialConstant*c 0
    nlinarith [spatialConstant_ge]
  | succ j =>
    have hm := scaled_marginal_distance h r q x y j
      (fun i hi => hr i (by omega)) (fun i hi => hstep i (by omega))
      (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega))
    have hd : ‖x-y‖ ≤ 52*r j := by rw [hstep j (by omega)]; linarith
    have hmag := mul_le_mul_of_nonneg_right hd (mul_nonneg hC0 (filt_nonneg hc0 j))
    have hd' : l1dist (marginal h r j x) (marginal h r j y) ≤
        52*comparisonConstant*filt c j := by
      have hrj := hr j (by omega)
      change r j*l1dist (marginal h r j x) (marginal h r j y) ≤
        comparisonConstant*‖x-y‖*filt c j at hm
      nlinarith
    have hs := switchCost_spatial h r (q (j+1)) x y j (hr (j+1) le_rfl)
      (hx (j+1) le_rfl) (hy (j+1) le_rfl)
    have ht := derivativeCost_spatial h r (q (j+1)) x y j (hr (j+1) le_rfl)
      (hx (j+1) le_rfl) (hy (j+1) le_rfl)
    change switchCost h r x (j+1) ≤ comparisonConstant*c (j+1)+_ at hs
    change derivativeCost h r x (j+1) ≤ comparisonConstant*c (j+1)+_ at ht
    have hdC := mul_le_mul_of_nonneg_left hd' hC0
    have hcoef : (52*comparisonConstant+52*comparisonConstant^2)*filt c j ≤
        (104*comparisonConstant^2)*filt c j := by
      apply mul_le_mul_of_nonneg_right _ (filt_nonneg hc0 j)
      nlinarith
    have hcC := mul_le_mul_of_nonneg_right spatialConstant_ge (hc0 (j+1))
    change _ ≤ spatialConstant*filt c (j+1)
    rw [filt]
    dsimp [spatialConstant] at hcC ⊢
    nlinarith
end ActualLabels

namespace DyadicHats
lemma scale_mono {r : ℝ} (hr : 0 ≤ r) {i j : ℕ} (hij : i ≤ j) : scale r i ≤ scale r j := by
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij) hr
lemma descending_step (r : ℝ) {m i : ℕ} (hi : i < m) :
    scale r (m-i) = 2*scale r (m-(i+1)) := by
  rw [show m-i = (m-(i+1))+1 by omega,scale_succ]
lemma descending_compare {r : ℝ} (hr : 0 ≤ r) {m l i : ℕ} (hi : i ≤ l+1) :
    scale r (m-l) ≤ 2*scale r (m-i) := by
  rw [← scale_succ]
  exact scale_mono hr (by omega)

lemma point_mem_neighborhood {r : ℝ} (hr : 0 ≤ r) (q : ℤ × ℤ) : point r q ∈ neighborhood r q := by
  change boxNorm (point r q-point r q) ≤ _
  simp only [sub_self,boxNorm]
  simpa using (mul_nonneg (by norm_num : (0:ℝ) ≤ 25) hr)
end DyadicHats

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks

lemma terminal_path_locality {N : ℕ} (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {i : ℕ} (hi : i ≤ m) :
    boxNorm (point r (lastVertex q p)-point (scale r (m-i)) (pathVertex q p i)) < scale r (m-i) := by
  have hlen := active_length v hp
  have hp' : activePath (tree v m 1 q) (p.take i++p.drop i) := by simpa only [List.take_append_drop] using hp
  have hl := active_prefix_locality v hr hp' (x := point r (lastVertex q p)) (by
    rw [List.take_append_drop,hat_at_point hr.ne']
    norm_num)
  simpa only [List.length_take,show min i p.length = i by omega,pathVertex] using hl

/-- The neighborhoods used by assembly remain within the actual 200-neighbor
energy window at every earlier row, including the complete pre-birth history. -/
lemma path_neighborhood_geometry {N : ℕ} (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {l : ℕ} (hl : l ≤ m) {x : ℂ}
    (hx : x ∈ neighborhood (scale r (m-l)) (pathVertex q p l))
    {i : ℕ} (hi : i ≤ m) (hil : i ≤ l+1) :
    ‖x-point r (lastVertex q p)‖ ≤ 104*scale r (m-i) ∧
    boxNorm (x-point (scale r (m-i)) (pathVertex q p i)) < 199*scale r (m-i) ∧
    boxNorm (point r (lastVertex q p)-point (scale r (m-i)) (pathVertex q p i)) < 199*scale r (m-i) := by
  let y := point r (lastVertex q p)
  have hy := terminal_path_locality v hr hp hl
  have hyi := terminal_path_locality v hr hp hi
  have hxy := boxNorm_add_le (x-point (scale r (m-l)) (pathVertex q p l))
    (point (scale r (m-l)) (pathVertex q p l)-y)
  rw [sub_add_sub_cancel,boxNorm_sub_comm (point _ _)] at hxy
  change boxNorm (x-point (scale r (m-l)) (pathVertex q p l)) ≤ 25*scale r (m-l) at hx
  have hd : boxNorm (x-y) ≤ 26*scale r (m-l) := by change boxNorm (y-_) < _ at hy; linarith
  have hrel := descending_compare hr.le (m := m) hil
  have hrp := scale_pos hr (m-i)
  have hnorm := norm_le_two_boxNorm (x-y)
  have hxi := boxNorm_add_le (x-y) (y-point (scale r (m-i)) (pathVertex q p i))
  rw [sub_add_sub_cancel] at hxi
  change boxNorm (y-point (scale r (m-i)) (pathVertex q p i)) < scale r (m-i) at hyi
  exact ⟨by dsimp only [y] at hnorm hd; linarith,by linarith,by linarith⟩
end ActualMarkTrees

namespace GeometricFilter
open Finset
lemma filt_mono_on {c d : ℕ → ℝ} (j : ℕ) (h : ∀ i ≤ j, c i ≤ d i) : filt c j ≤ filt d j := by
  rw [filt_sum,filt_sum]
  exact sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (h i (by have := mem_range.mp hi; omega)) (by positivity))

lemma shifted_tail {c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc0 : ∀ i, 0 ≤ c i)
    (hcA : ∀ i, c i ≤ A) {b m : ℕ} (hbm : b ≤ m) :
    (∑ i ∈ Ico b (m+1), filt c (i+1)) ≤ 2*∑ i ∈ Ico b (m+1), c i+6*A := by
  have he := sum_Ico_sub (filt c) (by omega : b ≤ m+1)
  rw [sum_sub_distrib] at he
  have h1 := filt_tail hA hc0 hcA hbm
  linarith [filt_le hA hcA (m+1),filt_nonneg hc0 b]
end GeometricFilter

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

namespace ActualLabels
open DyadicHats GeometricFilter FiniteLabels Finset
lemma derivativeCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (i : ℕ) (hr : 0 ≤ r i) :
    0 ≤ derivativeCost h r x i := by
  cases i with
  | zero => exact mul_nonneg hr (sum_nonneg (fun _ _ => norm_nonneg _))
  | succ i => exact FiniteLabels.expect_nonneg _ (rowDerivative_nonneg h hr x)

lemma cellCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (m l : ℕ) (q : ℤ × ℤ) :
    0 ≤ cellCost h r m l q := by
  have hs (i : ℕ) : 0 ≤ localSup (fun x => switchCost h r x i) (r l) q :=
    localSup_nonneg (hr l).le q (fun x => switchCost_nonneg h r x i) (fun x _ => switchCost_le_one h r x i)
  have ht (i : ℕ) : 0 ≤ localSup (fun x => derivativeCost h r x i) (r l) q :=
    localSup_nonneg (hr l).le q (fun x => derivativeCost_nonneg h r x i (hr i).le)
      (fun x _ => derivativeCost_uniform h r x i (hr i))
  dsimp only [cellCost]
  exact add_nonneg (add_nonneg (hs _) (by split_ifs; exact zero_le_one; exact hs _)) (filt_nonneg ht l)
end ActualLabels

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks ActualLabels GeometricFilter Finset

lemma path_filtered_cost {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {l : ℕ} (hl : l ≤ m) {x : ℂ} (hx : x ∈ neighborhood (scale r (m-l)) (pathVertex q p l))
    {i : ℕ} (hi : i ≤ m) (hil : i ≤ l+1) :
    switchCost h (fun j => scale r (m-j)) x i+derivativeCost h (fun j => scale r (m-j)) x i ≤
      spatialConstant*filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))) i := by
  apply filtered_spatial_cost h _ _ x _ i (fun j _ => scale_pos hr (m-j))
    (fun j hj => descending_step r (by omega))
  · intro j hj
    exact (path_neighborhood_geometry v hr hp hl hx (by omega : j ≤ m) (by omega)).2.1
  · intro j hj
    exact (path_neighborhood_geometry v hr hp hl hx (by omega : j ≤ m) (by omega)).2.2
  · exact (path_neighborhood_geometry v hr hp hl hx hi hil).1

lemma path_cellCost {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {l : ℕ} (hl : l ≤ m) :
    cellCost h (fun j => scale r (m-j)) m l (pathVertex q p l) ≤
      spatialConstant*(filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))) l+
        filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))) (l+1)+
        filt (filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p)))) l)+
      (if l=m then 1 else 0) := by
  let rs := fun j => scale r (m-j)
  let c := energyRate h rs (pathVertex q p) (point r (lastVertex q p))
  have hs (i : ℕ) (hi : i ≤ m) (hil : i ≤ l+1) :
      localSup (fun x => switchCost h rs x i) (rs l) (pathVertex q p l) ≤ spatialConstant*filt c i := by
    apply localSup_le (scale_pos hr _).le
    intro x hx
    have hh := path_filtered_cost h v hr hp hl hx hi hil
    change switchCost h rs x i+derivativeCost h rs x i ≤ spatialConstant*filt c i at hh
    linarith [derivativeCost_nonneg h rs x i (scale_pos hr _).le]
  have ht (i : ℕ) (hi : i ≤ l) :
      localSup (fun x => derivativeCost h rs x i) (rs l) (pathVertex q p l) ≤ spatialConstant*filt c i := by
    apply localSup_le (scale_pos hr _).le
    intro x hx
    have hh := path_filtered_cost h v hr hp hl hx (show i ≤ m by omega) (show i ≤ l+1 by omega)
    change switchCost h rs x i+derivativeCost h rs x i ≤ spatialConstant*filt c i at hh
    linarith [switchCost_nonneg h rs x i]
  have hT := filt_mono_on l ht
  rw [filt_mul] at hT
  have hnext : (if l=m then 1 else localSup (fun x => switchCost h rs x (l+1)) (rs l) (pathVertex q p l)) ≤
      spatialConstant*filt c (l+1)+(if l=m then 1 else 0) := by
    split_ifs with he
    · have hh := mul_nonneg spatialConstant_pos.le (filt_nonneg (energyRate_nonneg h rs (pathVertex q p) (point r (lastVertex q p))) (l+1))
      linarith
    · simpa only [add_zero] using hs (l+1) (by omega) le_rfl
  have hcur := hs l hl (by omega)
  change cellCost h rs m l (pathVertex q p l) ≤ _
  dsimp only [cellCost]
  change _ ≤ spatialConstant*(filt c l+filt c (l+1)+filt (filt c) l)+(if l=m then 1 else 0)
  linarith

lemma path_cellCost_sum {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {b : ℕ} (hb : b ≤ m) :
    (∑ l ∈ Ico b (m+1), cellCost h (fun j => scale r (m-j)) m l (pathVertex q p l)) ≤
      spatialConstant*(8*∑ i ∈ Ico b (m+1),
        energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p)) i+130)+1 := by
  let c := energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))
  have hc0 := energyRate_nonneg h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))
  have hcA := energyRate_le_five h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))
  have h1 := filt_tail (by norm_num : (0:ℝ) ≤ 5) hc0 hcA hb
  have h2 := shifted_tail (by norm_num : (0:ℝ) ≤ 5) hc0 hcA hb
  have h3 := double_tail (by norm_num : (0:ℝ) ≤ 5) hc0 hcA hb
  have hs := sum_le_sum (fun l (hl : l ∈ Finset.Ico b (m+1)) => path_cellCost h v hr hp (show l ≤ m by have := Finset.mem_Ico.mp hl; omega))
  change _ ≤ ∑ l ∈ Ico b (m+1), (spatialConstant*(filt c l+filt c (l+1)+filt (filt c) l)+(if l=m then 1 else 0)) at hs
  simp only [sum_add_distrib,← mul_sum] at hs
  have he : (∑ l ∈ Ico b (m+1), if l=m then (1:ℝ) else 0) = 1 := by simp [hb]
  rw [he] at hs
  change _ ≤ spatialConstant*(8*∑ i ∈ Ico b (m+1), c i+130)+1
  have hh : (∑ i ∈ Ico b (m+1), filt c i)+(∑ i ∈ Ico b (m+1), filt c (i+1))+
      (∑ i ∈ Ico b (m+1), filt (filt c) i) ≤ 8*∑ i ∈ Ico b (m+1), c i+130 := by linarith
  exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_left hh spatialConstant_pos.le])
end ActualMarkTrees

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks ActualLabels GeometricFilter DirectionNeighbors Finset

lemma packingCharge_path {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {b : ℕ} (hb : b ≤ p.length) :
    pathCharge (packingCharge h r m q) p b ≤
      8*spatialConstant*particleSwitches h r m q p b+
      8*spatialConstant*pathCharge (pathEnergy h r m q) p b+(130*spatialConstant+1) := by
  have hlen := active_length v hp
  have hs := path_cellCost_sum h v hr hp (show b ≤ m by omega)
  have hC : pathCharge (packingCharge h r m q) p b =
      ∑ i ∈ Ico b (m+1), cellCost h (fun j => scale r (m-j)) m i (pathVertex q p i) := by
    rw [pathCharge_sum,hlen]
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ m := by have := Finset.mem_Ico.mp hi; omega
    simp only [packingCharge,spatialCharge,List.length_take,hlen,min_eq_left hi',
      Nat.sub_sub_self hi',pathVertex]
  have hE : (∑ i ∈ Ico b (m+1), energyRate h (fun j => scale r (m-j)) (pathVertex q p)
      (point r (lastVertex q p)) i) =
      particleSwitches h r m q p b+pathCharge (pathEnergy h r m q) p b := by
    rw [pathCharge_sum]
    simp only [particleSwitches,pathSwitches,hlen,energyRate,sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ m := by have := Finset.mem_Ico.mp hi; omega
    simp only [pathEnergy,List.length_take,hlen,min_eq_left hi',pathVertex]
  rw [hC]
  rw [hE] at hs
  linarith

lemma tree_packing_bound {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (q : Grid N) :
    nodeCharge (tree v m 1 q) (packingCharge h r m q) ≤
      8*spatialConstant*particleEval (tree v m 1 q) (particleSwitches h r m q)+
      8*spatialConstant*nodeCharge (tree v m 1 q) (pathEnergy h r m q)+
      (130*spatialConstant+1)*terminalMass (tree v m 1 q) := by
  have hs := particleEval_mono_active (tree v m 1 q)
    (F := pathCharge (packingCharge h r m q))
    (fun p b hp hb => packingCharge_path h v hr hp hb)
  simp only [particleEval_add,particleEval_smul,particleEval_const,particle_occupancy] at hs
  nlinarith only [hs]

lemma packingConstant_pos : 0 < packingConstant := by
  dsimp [packingConstant]
  have := spatialConstant_pos
  positivity

theorem spatial_packing {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) :
    (∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale r j) q*
      cellCost h (fun i => scale r (m-i)) m (m-j) q) ≤
      packingConstant*(∫ y, ‖h y‖) := by
  have hs := sum_le_sum (fun q (_ : q ∈ (univ : Finset (Grid N))) =>
    tree_packing_bound h (fun q => vectorMass h r q) hr m q)
  simp only [sum_add_distrib,← mul_sum] at hs
  have hleft : (∑ q : Grid N, nodeCharge (tree (fun q => vectorMass h r q) m 1 q)
      (packingCharge h r m q)) =
      ∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale r j) q*
        cellCost h (fun i => scale r (m-i)) m (m-j) q := by
    unfold packingCharge
    rw [sum_nodeCharge]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro q hq
    rw [← vectorMass_coeff hr hR hN hh hsupp]
    rfl
  rw [hleft,sum_energyCharge hr hR hN hh hsupp,sum_terminalMass] at hs
  have hS := forest_switch_budget hr hR hN hh hsupp m
  have hE := neighbor_energy_budget hr hR hN hh hsupp (m+1)
  have hM := sum_scalarMass_grid_le (N := N) hh r
  change (∑ q : Grid N, ‖vectorMass h r q‖) ≤ ∫ y, ‖h y‖ at hM
  have hcoef : 0 ≤ 8*spatialConstant := by have := spatialConstant_pos; positivity
  have hcoef' : 0 ≤ 130*spatialConstant+1 := by have := spatialConstant_pos; positivity
  dsimp only [packingConstant]
  nlinarith only [hs,mul_le_mul_of_nonneg_left hS hcoef,
    mul_le_mul_of_nonneg_left hE hcoef,mul_le_mul_of_nonneg_left hM hcoef']
end ActualMarkTrees

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces

lemma rootMass_nonneg {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) :
    0 ≤ rootMass h r k S := sum_nonneg (fun _ _ => norm_nonneg _)

end CommonPrices

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Potentials
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace PhysicalCells
open MeasureTheory Set

lemma unitCell_measurable : MeasurableSet unitCell :=
  (Complex.measurable_re measurableSet_Ico).inter (Complex.measurable_im measurableSet_Ico)
lemma toUnit_continuous (p : ℂ) (r : ℝ) : Continuous (toUnit p r) := by unfold toUnit; fun_prop
lemma cell_measurable (p : ℂ) (r : ℝ) : MeasurableSet (cell p r) :=
  (toUnit_continuous p r).measurable unitCell_measurable
end PhysicalCells

namespace DiskMoments
lemma signedAverage_abs_le {g : ℂ → ℝ} {M : ℝ} (hM : ∀ y, |g y| ≤ M)
    (x : ℂ) {t : ℝ} (ht : 0 < t) : |signedAverage g x t| ≤ M := by
  rw [signedAverage_fixedDomain g x ht,abs_div,abs_of_pos Real.pi_pos]
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0:ℂ) 1)) := ⟨by simp⟩
  have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict (Metric.ball (0:ℂ) 1))
    (C := M) (f := fun z : ℂ => g (x+t • z)) (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hM (x+t • z)))
  have hv : (volume.restrict (Metric.ball (0:ℂ) 1)).real univ = Real.pi := by
    simp [measureReal_def,Complex.volume_ball]
  rw [hv,Real.norm_eq_abs] at hi
  exact (div_le_iff₀ Real.pi_pos).mpr hi

end DiskMoments

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Runs
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace SignedRuns
open DiskMoments RadiusEnvelope ActualLabels Finset

variable (g : ℂ → ℝ) (r : ℕ → ℝ)

lemma radius_antitone (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k) : Antitone r := by
  apply antitone_nat_of_succ_le
  intro k
  have := hr (k+1)
  linarith [hstep k]

lemma runEnvelope_attains (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) {i j : ℕ} (hij : i ≤ j) (x : ℂ) :
    ∃ t ∈ Icc (r j) (2*r i), runEnvelope g r i j x = signedAverage g x t ∧
      ∀ s ∈ Icc (r j) (2*r i), signedAverage g x s ≤ signedAverage g x t := by
  apply attains _ x (signedAverage_radius_continuousOn hg x (hr j))
  have := radius_antitone r hr hstep hij
  linarith [hr i]

lemma runEnvelope_le_next (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) {i j : ℕ} (hij : i ≤ j) (x : ℂ) :
    runEnvelope g r i j x ≤ runEnvelope g r i (j+1) x := by
  obtain ⟨t,ht,he,_⟩ := runEnvelope_attains g r hg hr hstep hij x
  rw [he]
  apply le_envelope ⟨(radius_antitone r hr hstep (Nat.le_succ j)).trans ht.1,ht.2⟩ x
    (signedAverage_radius_continuousOn hg x (hr (j+1)))

lemma runEnvelope_extension_bound (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) {i j : ℕ} (hij : i ≤ j) (x : ℂ) {V : ℝ}
    (hV : ∀ t t', 0 < t → t ≤ 4*r (j+1) → 0 < t' → t' ≤ 4*r (j+1) →
      |signedAverage g x t-signedAverage g x t'| ≤ V) :
    |runEnvelope g r i (j+1) x-runEnvelope g r i j x| ≤ V := by
  have hV0 : 0 ≤ V := by
    have hh := hr (j+1)
    simpa using hV (r (j+1)) (r (j+1)) hh (by linarith) hh (by linarith)
  have h0 := runEnvelope_le_next g r hg hr hstep hij x
  rw [abs_of_nonneg (sub_nonneg.mpr h0)]
  obtain ⟨t,ht,he,_⟩ := runEnvelope_attains g r hg hr hstep (hij.trans (Nat.le_succ j)) x
  rw [he]
  by_cases htj : r j ≤ t
  · have hh := le_envelope (u := fun t y => signedAverage g y t) ⟨htj,ht.2⟩ x
      (signedAverage_radius_continuousOn hg x (hr j))
    change signedAverage g x t ≤ runEnvelope g r i j x at hh
    linarith
  · have hb : signedAverage g x (r j) ≤ runEnvelope g r i j x := by
      change signedAverage g x (r j) ≤ envelope (fun t y => signedAverage g y t) (r j) (2*r i) x
      apply le_envelope (u := fun t y => signedAverage g y t) (a := r j) (b := 2*r i) (r := r j) ⟨le_rfl,?_⟩ x (signedAverage_radius_continuousOn hg x (hr j))
      have := radius_antitone r hr hstep hij
      linarith [hr i]
    have hh := hV t (r j) ((hr (j+1)).trans_le ht.1)
      (by linarith [hstep j,hr (j+1)]) (hr j) (by linarith [hstep j,hr (j+1)])
    linarith [le_abs_self (signedAverage g x t-signedAverage g x (r j))]

lemma runEnvelope_new_bound (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (j : ℕ) (x : ℂ) {V : ℝ}
    (hV : ∀ t t', 0 < t → t ≤ 4*r j → 0 < t' → t' ≤ 4*r j →
      |signedAverage g x t-signedAverage g x t'| ≤ V) :
    |runEnvelope g r j j x-signedAverage g x (r j)| ≤ V := by
  obtain ⟨t,ht,he,_⟩ := runEnvelope_attains g r hg hr hstep le_rfl x
  rw [he]
  exact hV t (r j) ((hr j).trans_le ht.1) (by linarith [hr j,ht.2]) (hr j) (by linarith [hr j])

lemma activeStart_le (n : Label) (p : List Label) : activeStart (n::p) ≤ p.length := by
  induction p generalizing n with
  | nil => simp [activeStart]
  | cons old p ih =>
    dsimp only [activeStart]
    split_ifs
    · exact (ih old).trans (by simp)
    · rfl

lemma potential_increment (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (x : ℂ) (v : ℕ → ℝ)
    (hv : ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |signedAverage g x t-signedAverage g x t'| ≤ v k)
    (n : Label) (p : List Label) : ‖potential g r x (n::p)-potential g r x p‖ ≤ v p.length := by
  cases p with
  | nil =>
    simp only [potential,List.length_nil,sub_zero,norm_smul,Real.norm_eq_abs,label_unit,mul_one]
    exact runEnvelope_new_bound g r hg hr hstep 0 x (hv 0)
  | cons old p =>
    simp only [potential,add_sub_cancel_left,List.length_cons]
    split_ifs
    · simp only [norm_smul,Real.norm_eq_abs,label_unit,mul_one]
      exact runEnvelope_extension_bound g r hg hr hstep (activeStart_le old p) x (hv (p.length+1))
    · simp only [norm_smul,Real.norm_eq_abs,label_unit,mul_one]
      exact runEnvelope_new_bound g r hg hr hstep (p.length+1) x (hv (p.length+1))

theorem potential_continuation_bound (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (x : ℂ) (v : ℕ → ℝ)
    (hv : ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |signedAverage g x t-signedAverage g x t'| ≤ v k)
    (p q : List Label) : ‖potential g r x (q++p)-potential g r x p‖ ≤
      ∑ k ∈ Ico p.length (p.length+q.length), v k := by
  induction q with
  | nil => simp
  | cons n q ih =>
    have htri : ‖potential g r x ((n::q)++p)-potential g r x p‖ ≤
        ‖potential g r x (n::(q++p))-potential g r x (q++p)‖+
        ‖potential g r x (q++p)-potential g r x p‖ := by
      simpa only [sub_add_sub_cancel,List.cons_append] using norm_add_le
        (potential g r x (n::(q++p))-potential g r x (q++p))
        (potential g r x (q++p)-potential g r x p)
    have hi := potential_increment g r hg hr hstep x v hv n (q++p)
    apply htri.trans
    rw [List.length_cons,Nat.add_succ,sum_Ico_succ_top (by omega : p.length ≤ p.length+q.length)]
    simpa only [List.length_append,Nat.add_comm,add_comm] using add_le_add hi ih
end SignedRuns

namespace SignedRuns
open SignedAssembly FiniteLabels ActualLabels Finset

variable (g : ℂ → ℝ) (r : ℕ → ℝ) (x : ℂ)
variable (J : ℕ → Label → RowJet Label ℂ) (v : ℕ → ℝ)

lemma jet_terminalBound (d : ℕ) (p : List Label) (old : Label) (c : ℂ) (B : ℝ)
    (h : ∀ q : List Label, q.length = d → ‖potential g r x (q++p)-c‖ ≤ B) :
    TerminalBound (jet g r x J v d p old) c B := by
  induction d generalizing p old with
  | zero => simpa only [jet,TerminalBound,List.nil_append] using h [] rfl
  | succ d ih =>
    intro n
    apply ih
    intro q hq
    have hh := h (q++[n]) (by simp only [List.length_append,List.length_singleton,hq])
    simpa only [List.append_assoc,List.singleton_append] using hh

lemma jet_controlled (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k)
    (hv : ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |DiskMoments.signedAverage g x t-DiskMoments.signedAverage g x t'| ≤ v k)
    (d : ℕ) (p : List Label) (old : Label) : Controlled (jet g r x J v d p old) := by
  induction d generalizing p old with
  | zero => trivial
  | succ d ih =>
    constructor
    · intro n
      apply jet_terminalBound
      intro q hq
      have hh := potential_continuation_bound g r hg hr hstep x v hv p (q++[n])
      simpa only [List.append_assoc,List.singleton_append,List.length_append,List.length_singleton,hq,Nat.add_assoc] using hh
    · intro n
      exact ih (n::p) n

lemma jet_cost (d : ℕ) (p : List Label) (old : Label) (m : ℕ) (hm : p.length+d = m) :
    cost (jet g r x J v d p old) = rewardCost J
      (fun k n => (∑ a, ‖(J k n).grad a‖)*(∑ l ∈ Ico k m, v l)) p.length d old := by
  induction d generalizing p old with
  | zero => rfl
  | succ d ih =>
    simp only [jet,cost,rewardCost]
    have htop : p.length+d+1 = m := by omega
    rw [htop]
    congr 1
    apply sum_congr rfl
    intro a _
    rw [ih (a::p) a (by simp only [List.length_cons]; omega)]
    rfl

lemma expect_rewardCost (reward : ℕ → Label → ℝ) (μ : ℕ → Law Label)
    (hμ : ∀ k, μ (k+1) = move (μ k) (fun n => (J k n).law)) (d k : ℕ) :
    expect (μ k) (rewardCost J reward k d) =
      ∑ i ∈ Ico k (k+d), expect (μ i) (reward i) := by
  induction d generalizing k with
  | zero => simp [rewardCost,FiniteLabels.expect]
  | succ d ih =>
    change expect (μ k) (fun n => reward k n+expect (J k n).law (fun a => rewardCost J reward (k+1) d a)) = _
    rw [expect_add,← expect_move,← hμ k,ih]
    rw [sum_Ico_eq_sum_range,sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left,Nat.add_assoc,Nat.add_sub_cancel_left]
    rw [sum_range_succ']
    simp only [Nat.add_zero,Nat.add_left_comm,add_comm,Nat.add_sub_cancel_right]

/-- Signed finite-history flux with the actual run potential and the exact
forward stochastic marginal law. No old large-radius envelope is priced. -/
theorem run_signed_flux_bound (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k)
    (hv : ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |DiskMoments.signedAverage g x t-DiskMoments.signedAverage g x t'| ≤ v k)
    (m : ℕ) (old : Label) (μ : ℕ → Law Label) (hμ0 : μ 0 = delta old)
    (hμ : ∀ k, μ (k+1) = move (μ k) (fun n => (J k n).law)) :
    |pathFlux (jet g r x J v m [] old) 1 0| ≤
      ∑ k ∈ range m, expect (μ k) (fun n => ∑ a, ‖(J k n).grad a‖)*
        (∑ l ∈ Ico k m, v l) := by
  have hh := signed_flux_bound _ (jet_controlled g r x J v hg hr hstep hv m [] old)
  rw [jet_cost g r x J v m [] old m (by simp)] at hh
  have he := expect_rewardCost J
    (fun k n => (∑ a, ‖(J k n).grad a‖)*(∑ l ∈ Ico k m, v l)) μ hμ m 0
  rw [hμ0,expect_delta] at he
  simp only [Nat.zero_add,Nat.Ico_zero_eq_range] at he
  simp only [List.length_nil] at hh
  rw [he] at hh
  simpa only [FiniteLabels.expect,← mul_assoc,← sum_mul] using hh
end SignedRuns

namespace SignedRuns
open DiskMoments RadiusEnvelope ActualLabels ConeCoordinates

lemma closedRuns_bounds (n : Label) (p : List Label) :
    ∀ a ∈ closedRuns (n::p), a.first ≤ a.last ∧ a.last < p.length := by
  induction p generalizing n with
  | nil => simp [closedRuns]
  | cons old p ih =>
    simp only [closedRuns]
    split_ifs with h
    · intro a ha
      exact ⟨(ih old a ha).1,(ih old a ha).2.trans (by simp)⟩
    · intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · subst a
        exact ⟨activeStart_le old p,by simp⟩
      · exact ⟨(ih old a ha).1,(ih old a ha).2.trans (by simp)⟩

lemma runs_bounds (n : Label) (p : List Label) :
    ∀ a ∈ runs (n::p), a.first ≤ a.last ∧ a.last ≤ p.length := by
  intro a ha
  rcases List.mem_cons.mp ha with ha | ha
  · subst a
    exact ⟨activeStart_le n p,le_rfl⟩
  · exact ⟨(closedRuns_bounds n p a ha).1,(closedRuns_bounds n p a ha).2.le⟩

lemma runs_cover (n : Label) (p : List Label) (k : ℕ) (hk : k ≤ p.length) :
    ∃ a ∈ runs (n::p), a.first ≤ k ∧ k ≤ a.last := by
  induction p generalizing n k with
  | nil =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    exact ⟨⟨n,0,0⟩,by simp [runs,activeStart],le_rfl,le_rfl⟩
  | cons old p ih =>
    by_cases h : n = old
    · subst n
      by_cases hs : activeStart (old::p) ≤ k
      · refine ⟨⟨old,activeStart (old::p),p.length+1⟩,?_,hs,?_⟩
        · simp [runs,activeStart]
        · simpa using hk
      · have hk' : k ≤ p.length := (le_of_not_ge hs).trans (activeStart_le old p)
        obtain ⟨a,ha,hak,hka⟩ := ih old k hk'
        have hac : a ∈ closedRuns (old::p) := by
          rcases List.mem_cons.mp ha with ha | ha
          · subst a
            exact False.elim (hs hak)
          · exact ha
        exact ⟨a,by simp [runs,closedRuns,hac],hak,hka⟩
    · by_cases hk' : k ≤ p.length
      · obtain ⟨a,ha,hak,hka⟩ := ih old k hk'
        exact ⟨a,by simpa only [runs,closedRuns,h,ite_false,List.mem_cons] using Or.inr ha,hak,hka⟩
      · have he : k = p.length+1 := by simp only [List.length_cons] at hk; omega
        subst k
        exact ⟨⟨n,p.length+1,p.length+1⟩,by simp [runs,activeStart,h],le_rfl,le_rfl⟩

lemma potential_eq_runs (g : ℂ → ℝ) (r : ℕ → ℝ) (x : ℂ) (n : Label) (p : List Label) :
    potential g r x (n::p) = ((runs (n::p)).map fun a =>
      (runEnvelope g r a.first a.last x-signedAverage g x (r a.first)) • (a.dir:ℂ)).sum := by
  induction p generalizing n with
  | nil => simp [potential,runs,closedRuns,activeStart]
  | cons old p ih =>
    rw [potential,ih]
    by_cases h : n = old
    · subst n
      simp only [runs,closedRuns,activeStart,ite_true,List.length_cons,List.map_cons,List.sum_cons]
      module
    · simp only [runs,closedRuns,activeStart,h,ite_false,List.length_cons,List.map_cons,List.sum_cons]
      abel

lemma radius_in_bin (r : ℕ → ℝ)
    (hstep : ∀ k, 2*r (k+1) = r k) (j : ℕ) {t : ℝ} (ht : t ∈ Icc (r j) (2*r 0)) :
    ∃ k ≤ j, t ∈ Icc (r k) (2*r k) := by
  induction j with
  | zero => exact ⟨0,le_rfl,ht⟩
  | succ j ih =>
    by_cases h : r j ≤ t
    · obtain ⟨k,hk,hkt⟩ := ih ⟨h,ht.2⟩
      exact ⟨k,hk.trans (Nat.le_succ j),hkt⟩
    · exact ⟨j+1,le_rfl,ht.1,by linarith [hstep j]⟩

lemma runs_cover_radius (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (n : Label) (p : List Label) {t : ℝ}
    (ht : t ∈ Icc (r p.length) (2*r 0)) :
    ∃ a ∈ runs (n::p), t ∈ Icc (r a.last) (2*r a.first) := by
  obtain ⟨k,hk,hkt⟩ := radius_in_bin r hstep p.length ht
  obtain ⟨a,ha,hi,hj⟩ := runs_cover n p k hk
  refine ⟨a,ha,?_,?_⟩
  · exact (radius_antitone r hr hstep hj).trans hkt.1
  · have hh := radius_antitone r hr hstep hi
    linarith [hkt.2]

/-- Every history has an actually attaining winning run. No radius selection
is differentiated. -/
lemma winning_run (g : ℂ → ℝ) (r : ℕ → ℝ) (hg : ContDiff ℝ 1 g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (n : Label) (p : List Label) (x : ℂ) :
    ∃ a ∈ runs (n::p), ∃ t ∈ Icc (r a.last) (2*r a.first),
      runEnvelope g r 0 p.length x = signedAverage g x t ∧
      runEnvelope g r a.first a.last x = signedAverage g x t := by
  obtain ⟨t,ht,he,hmax⟩ := runEnvelope_attains g r hg hr hstep (Nat.zero_le _) x
  obtain ⟨a,ha,hat⟩ := runs_cover_radius r hr hstep n p ht
  refine ⟨a,ha,t,hat,he,le_antisymm ?_ ?_⟩
  · obtain ⟨s,hs,hsval,_⟩ := runEnvelope_attains g r hg hr hstep (runs_bounds n p a ha).1 x
    rw [hsval]
    apply hmax
    constructor
    · exact (radius_antitone r hr hstep (runs_bounds n p a ha).2).trans hs.1
    · have hh := radius_antitone r hr hstep (Nat.zero_le a.first)
      linarith [hs.2]
  · exact le_envelope (u := fun t y => signedAverage g y t) hat x (signedAverage_radius_continuousOn hg x (hr a.last))

end SignedRuns

namespace FiniteLabels
lemma Law.ext_mass {ι : Type*} [Fintype ι] {μ ν : Law ι} (h : μ.mass = ν.mass) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl
end FiniteLabels

namespace ActualLabels
open FiniteLabels SignedAssembly Finset ConeCoordinates

lemma before_move (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) (k : ℕ) :
    before h r old x (k+1) = move (before h r old x k) (observation h r k x) := by
  cases k with
  | zero =>
    apply Law.ext_mass
    funext j
    change initial h (r 0) x j = ∑ n, delta old n*initial h (r 0) x j
    rw [← sum_mul,(delta old).total,one_mul]
  | succ k => rfl

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

lemma observation_ae_diff (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) :
    ∀ᵐ x, ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x := by
  simp only [ae_all_iff]
  intro k n j
  exact (observation_lipschitz h r k (hr k) n j).ae_differentiableAt

/-- The jet's expected absolute row derivative is exactly T_k/r_k from the
physical spatial packing theorem. -/
lemma observationJet_cost (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (k : ℕ) (hr : 0 < r k) :
    expect (before h r old x k) (fun n => ∑ j, ‖(observationJet h r x hd k n).grad j‖) =
      derivativeCost h r x k/r k := by
  cases k with
  | zero =>
    change expect (delta old) (fun _ => ∑ j, ‖gradient (fun y => initial h (r 0) y j) x‖) = _
    rw [FiniteLabels.expect_const,derivativeCost,mul_div_cancel_left₀ _ hr.ne']
  | succ k =>
    simp only [observationJet,RowJet.ofLawAt,observation,before,derivativeCost,rowDerivative,FiniteLabels.expect]
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro n _
    field_simp
end ActualLabels

namespace SignedRuns
open ActualLabels FiniteLabels SignedAssembly Finset

lemma weight_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) (p : List Label) :
    0 ≤ weight h r old x p := by
  induction p with
  | nil => exact zero_le_one
  | cons n p ih => exact mul_nonneg ih ((observation h r p.length x (p.headD old)).nonneg n)

lemma weight_le_one (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) (p : List Label) :
    weight h r old x p ≤ 1 := by
  induction p with
  | nil => exact le_rfl
  | cons n p ih =>
    apply (mul_le_mul ih (law_le_one (observation h r p.length x (p.headD old)) n)
      ((observation h r p.length x (p.headD old)).nonneg n) zero_le_one).trans_eq
    exact one_mul 1

lemma lipschitz_bounded_mul {f g : ℂ → ℝ} {K L : ℝ≥0} (hf : LipschitzWith K f)
    (hg : LipschitzWith L g) (hfb : ∀ x, ‖f x‖ ≤ 1) (hgb : ∀ x, ‖g x‖ ≤ 1) :
    LipschitzWith (K+L) (fun x => f x*g x) := by
  rw [lipschitzWith_iff_norm_sub_le] at hf hg ⊢
  intro x y
  calc
    ‖f x*g x-f y*g y‖ = ‖f x*(g x-g y)+g y*(f x-f y)‖ := by congr 1; ring
    _ ≤ ‖f x*(g x-g y)‖+‖g y*(f x-f y)‖ := norm_add_le _ _
    _ = ‖f x‖*‖g x-g y‖+‖g y‖*‖f x-f y‖ := by rw [norm_mul,norm_mul]
    _ ≤ 1*((L:ℝ)*‖x-y‖)+1*((K:ℝ)*‖x-y‖) := by
      gcongr
      · exact hfb x
      · exact hg x y
      · exact hgb y
      · exact hf x y
    _ = ((K+L:ℝ≥0):ℝ)*‖x-y‖ := by push_cast; ring

lemma weight_lipschitz (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (old : Label) (p : List Label) : ∃ K, LipschitzWith K (fun x => weight h r old x p) := by
  induction p with
  | nil => exact ⟨0,LipschitzWith.const 1⟩
  | cons n p ih =>
    obtain ⟨K,hK⟩ := ih
    refine ⟨_,lipschitz_bounded_mul hK (observation_lipschitz h r p.length (hr _) _ n) ?_ ?_⟩
    · intro x
      rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg h r old x p)]
      exact weight_le_one h r old x p
    · intro x
      rw [Real.norm_eq_abs,abs_of_nonneg ((observation h r p.length x (p.headD old)).nonneg n)]
      exact law_le_one (observation h r p.length x (p.headD old)) n

lemma weight_diff (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (p : List Label) : DifferentiableAt ℝ (fun y => weight h r old y p) x := by
  induction p with
  | nil => exact differentiableAt_const 1
  | cons n p ih => exact ih.mul (hd p.length (p.headD old) n)

lemma gradient_weight_cons (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (n : Label) (p : List Label) :
    gradient (fun y => weight h r old y (n::p)) x =
      weight h r old x p • (observationJet h r x hd p.length (p.headD old)).grad n+
      observation h r p.length x (p.headD old) n • gradient (fun y => weight h r old y p) x := by
  simp only [weight,observationJet,RowJet.ofLawAt,gradient]
  rw [fderiv_fun_mul (weight_diff h r old x hd p) (hd p.length (p.headD old) n)]
  simp only [map_add,map_smul]

lemma flux_eq_weightedLeaves (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label)
    (x : ℂ) (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (v : ℕ → ℝ) (d : ℕ) (p : List Label) :
    pathFlux (jet g r x (observationJet h r x hd) v d p (p.headD old))
      (weight h r old x p) (gradient (fun y => weight h r old y p) x) =
        leafSum (fun q => inner ℝ (gradient (fun y => weight h r old y q) x) (potential g r x q)) d p := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
    simp only [jet,pathFlux,leafSum]
    apply sum_congr rfl
    intro n _
    change pathFlux _ (weight h r old x (n::p))
      (weight h r old x p • (observationJet h r x hd p.length (p.headD old)).grad n+
        observation h r p.length x (p.headD old) n • gradient (fun y => weight h r old y p) x) = _
    rw [← gradient_weight_cons h r old x hd n p]
    exact ih (n::p)

/-- The signed flux bound for derivatives of the actual spatial history
weights, with the true initial row and forward marginal derivatives. -/
theorem actual_signed_flux_bound (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ)
    (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (old : Label) (x : ℂ)
    (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (v : ℕ → ℝ)
    (hv : ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |DiskMoments.signedAverage g x t-DiskMoments.signedAverage g x t'| ≤ v k)
    (m : ℕ) :
    |leafSum (fun q => inner ℝ (gradient (fun y => weight h r old y q) x) (potential g r x q)) m []| ≤
      ∑ k ∈ range m, (derivativeCost h r x k/r k)*(∑ l ∈ Ico k m, v l) := by
  have hh := run_signed_flux_bound g r x (observationJet h r x hd) v hg hr hstep hv m old
    (before h r old x) rfl (before_move h r old x)
  have he := flux_eq_weightedLeaves g h r old x hd v m []
  simp only [List.headD_nil,weight] at he
  rw [show gradient (fun _ : ℂ => (1:ℝ)) x = 0 from gradient_const x 1] at he
  rw [he] at hh
  simpa only [observationJet_cost h r old x hd _ (hr _)] using hh
end SignedRuns

namespace SignedRuns
open DiskMoments RadiusEnvelope ActualLabels ConeCoordinates

lemma run_gradient_touching {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) {i j : ℕ} {x : ℂ}
    (hd : DifferentiableAt ℝ (runEnvelope g r i j) x) {t : ℝ}
    (ht : t ∈ Icc (r j) (2*r i)) (he : runEnvelope g r i j x = signedAverage g x t) :
    gradient (runEnvelope g r i j) x = gradient (fun y => signedAverage g y t) x := by
  obtain ⟨K,hK⟩ := hg.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
  have hu := hasFDerivAt_signedAverage hg (fun y => norm_fderiv_le_of_lipschitz ℝ hK) x
    ((hr j).trans_le ht.1)
  unfold gradient runEnvelope
  rw [RadiusEnvelope.fderiv_touching ht (fun y => signedAverage_radius_continuousOn hg y (hr j)) he hd hu.differentiableAt]

lemma runs_ae_diff {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k) :
    ∀ᵐ x, ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x := by
  simp only [ae_all_iff]
  intro i j hij
  have hab : r j ≤ 2*r i := by
    have := radius_antitone r hr hstep hij
    linarith [hr i]
  obtain ⟨L,hL⟩ := run_envelope_lipschitz hg hgc (hr j) hab
  exact hL.ae_differentiableAt

lemma coneContribution_nonneg (n : Label) (z : ℂ) : 0 ≤ coneContribution n z := by
  have hc := cone_algebra (label_unit n) z
  change ‖z‖ ≤ 12*coneContribution n z at hc
  linarith [norm_nonneg z]

theorem run_master {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (n : Label) (p : List Label) (x : ℂ)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x) :
    ‖gradient (runEnvelope g r 0 p.length) x‖ ≤
      12*((runs (n::p)).map fun a => coneContribution a.dir
        (gradient (runEnvelope g r a.first a.last) x)).sum := by
  obtain ⟨a,ha,t,ht,hgval,haval⟩ := winning_run g r hg hr hstep n p x
  have hab := runs_bounds n p a ha
  have htg : t ∈ Icc (r p.length) (2*r 0) := by
    constructor
    · exact (radius_antitone r hr hstep hab.2).trans ht.1
    · have hh := radius_antitone r hr hstep (Nat.zero_le a.first)
      linarith [ht.2]
  have he : gradient (runEnvelope g r 0 p.length) x = gradient (runEnvelope g r a.first a.last) x :=
    (run_gradient_touching hg hgc hr (hd 0 p.length (Nat.zero_le _)) htg hgval).trans
      (run_gradient_touching hg hgc hr (hd a.first a.last hab.1) ht haval).symm
  rw [he]
  apply (cone_algebra (label_unit a.dir) _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 12)
  apply List.single_le_sum
  · intro z hz
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hz
    exact coneContribution_nonneg b.dir _
  · exact List.mem_map.mpr ⟨a,ha,rfl⟩
end SignedRuns

namespace DiskMoments
lemma signedAverage_hasCompactSupport {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (fun x => signedAverage g x t) := by
  have he : RadiusEnvelope.envelope (fun s x => signedAverage g x s) t t =
      fun x => signedAverage g x t := by
    funext x
    obtain ⟨s,hs,he,_⟩ := RadiusEnvelope.attains (u := fun s x => signedAverage g x s) (a := t) (b := t) le_rfl x (signedAverage_radius_continuousOn hg x ht)
    have hst : s = t := le_antisymm hs.2 hs.1
    simpa only [hst] using he
  rw [← he]
  exact run_envelope_hasCompactSupport hg hc ht le_rfl
end DiskMoments

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.RunCancellation
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace SignedRuns
open DiskMoments ActualLabels

lemma regular_zero : Regular (fun _ : ℂ => (0:ℂ)) :=
  ⟨HasCompactSupport.zero,0,LipschitzWith.const 0⟩

lemma regular_add {f g : ℂ → ℂ} (hf : Regular f) (hg : Regular g) :
    Regular (fun x => f x+g x) := by
  obtain ⟨hfC,L,hfL⟩ := hf
  obtain ⟨hgC,K,hgL⟩ := hg
  exact ⟨hfC.add hgC,L+K,hfL.add hgL⟩

lemma regular_scalar {f : ℂ → ℝ} (hc : HasCompactSupport f) {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : Label) : Regular (fun x => f x • (n:ℂ)) := by
  refine ⟨hc.smul_right,L,?_⟩
  rw [lipschitzWith_iff_norm_sub_le] at hf ⊢
  intro x y
  simpa only [← sub_smul,norm_smul,label_unit,mul_one] using hf x y

lemma regular_listSum {α : Type*} (l : List α) (f : α → ℂ → ℂ)
    (hf : ∀ a ∈ l, Regular (f a)) : Regular (fun x => (l.map fun a => f a x).sum) := by
  induction l with
  | nil => exact regular_zero
  | cons a l ih =>
    exact regular_add (hf a (by simp)) (ih (fun b hb => hf b (by simp [hb])))

lemma runTerm_regular {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (a : Run) (ha : a.first ≤ a.last) :
    Regular (fun x => (runEnvelope g r a.first a.last x-signedAverage g x (r a.first)) • (a.dir:ℂ)) := by
  have hab : r a.last ≤ 2*r a.first := by
    have := radius_antitone r hr hstep ha
    linarith [hr a.first]
  obtain ⟨L,hL⟩ := run_envelope_lipschitz hg hgc (hr a.last) hab
  obtain ⟨K,hK⟩ := hg.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
  apply regular_scalar
    ((run_envelope_hasCompactSupport hg hgc (hr a.last) hab).sub (signedAverage_hasCompactSupport hg hgc (hr a.first)))
    (hL.sub (signedAverage_lipschitz hK (hr a.first)))

/-- Every exact history potential is compactly supported and Lipschitz, as
needed for signed weighted integration by parts. -/
theorem potential_regular {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (p : List Label) : Regular (fun x => potential g r x p) := by
  cases p with
  | nil => exact regular_zero
  | cons n p =>
    simp_rw [potential_eq_runs]
    exact regular_listSum (runs (n::p)) _ (fun a ha =>
      runTerm_regular hg hgc hr hstep a (runs_bounds n p a ha).1)
end SignedRuns

namespace SignedRuns
open Complex

lemma inner_coordinates (z w : ℂ) :
    inner ℝ z w = inner ℝ z (1:ℂ)*w.re+inner ℝ z I*w.im := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [inner_add_right]
  have hre : (w.re:ℂ) = w.re • (1:ℂ) := by simp
  have him : (w.im:ℂ)*I = w.im • I := by rw [Complex.real_smul]
  rw [hre,him,real_inner_smul_right,real_inner_smul_right]
  ring

lemma gradient_aestronglyMeasurable (f : ℂ → ℝ) : AEStronglyMeasurable (gradient f) :=
  ((InnerProductSpace.toDual ℝ ℂ).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)).aestronglyMeasurable

lemma gradient_norm_le {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : ℂ) :
    ‖gradient f x‖ ≤ (L:ℝ) := by
  simpa only [gradient,(InnerProductSpace.toDual ℝ ℂ).symm.norm_map] using
    (norm_fderiv_le_of_lipschitz ℝ hf : ‖fderiv ℝ f x‖ ≤ (L:ℝ))

lemma integrable_fderiv_apply {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hc : HasCompactSupport f) (v : ℂ) : Integrable (fun x => fderiv ℝ f x v) := by
  have hi := (innerSL ℝ v).integrable_comp (_root_.OAI.LipschitzWith.integrable_gradient (μ := volume) hf hc)
  apply hi.congr
  filter_upwards with x
  change inner ℝ v (gradient f x) = _
  rw [real_inner_comm,gradient,InnerProductSpace.toDual_symm_apply]

lemma integrable_gradient_mul {f g : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hg : Integrable g) (v : ℂ) : Integrable (fun x => inner ℝ (gradient f x) v*g x) := by
  apply hg.bdd_mul ((gradient_aestronglyMeasurable f).inner aestronglyMeasurable_const)
  filter_upwards with x
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (gradient_norm_le hf x) (norm_nonneg v))

lemma regular_integrable (V : ℂ → ℂ) (hV : Regular V) : Integrable V := by
  obtain ⟨hc,L,hL⟩ := hV
  exact hL.continuous.integrable_of_hasCompactSupport hc

lemma weighted_divergence_integrable {w : ℂ → ℝ} {K : ℝ≥0} (hw : LipschitzWith K w)
    (hb : ∀ x, ‖w x‖ ≤ 1) {V : ℂ → ℂ} (hV : Regular V) :
    Integrable (fun x => w x*divergence V x) := by
  obtain ⟨hc,L,hL⟩ := hV
  have hr := integrable_fderiv_apply (Complex.reCLM.lipschitz.comp hL)
    (hc.comp_left (map_zero Complex.reCLM)) (1:ℂ)
  have hi := integrable_fderiv_apply (Complex.imCLM.lipschitz.comp hL)
    (hc.comp_left (map_zero Complex.imCLM)) I
  exact (hr.add hi).bdd_mul hw.continuous.aestronglyMeasurable (ae_of_all _ hb)

lemma potential_flux_integrable {w : ℂ → ℝ} {K : ℝ≥0} (hw : LipschitzWith K w)
    {V : ℂ → ℂ} (hV : Regular V) :
    Integrable (fun x => inner ℝ (gradient w x) (V x)) := by
  have hi := regular_integrable V hV
  apply (hi.norm.const_mul (K:ℝ)).mono'
    ((gradient_aestronglyMeasurable w).inner hi.aestronglyMeasurable)
  filter_upwards with x
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (gradient_norm_le hw x) (norm_nonneg _))

/-- Weighted vector integration by parts for the actual class of compact
Lipschitz path potentials and bounded Lipschitz spatial history weights. -/
theorem vector_weighted_ibp {w : ℂ → ℝ} {K : ℝ≥0} (hw : LipschitzWith K w)
    (hb : ∀ x, ‖w x‖ ≤ 1) {V : ℂ → ℂ} (hV : Regular V) :
    (∫ x, w x*divergence V x) = -∫ x, inner ℝ (gradient w x) (V x) := by
  obtain ⟨hc,L,hL⟩ := hV
  have hrL := Complex.reCLM.lipschitz.comp hL
  have hiL := Complex.imCLM.lipschitz.comp hL
  have hrC := hc.comp_left (map_zero Complex.reCLM)
  have hiC := hc.comp_left (map_zero Complex.imCLM)
  have hr := (integrable_fderiv_apply hrL hrC (1:ℂ)).bdd_mul
    hw.continuous.aestronglyMeasurable (ae_of_all _ hb)
  have hi := (integrable_fderiv_apply hiL hiC I).bdd_mul
    hw.continuous.aestronglyMeasurable (ae_of_all _ hb)
  have hrr := integrable_gradient_mul hw (hrL.continuous.integrable_of_hasCompactSupport hrC) (1:ℂ)
  have hir := integrable_gradient_mul hw (hiL.continuous.integrable_of_hasCompactSupport hiC) I
  change (∫ x, w x*(fderiv ℝ (Complex.reCLM ∘ V) x 1+fderiv ℝ (Complex.imCLM ∘ V) x I)) = _
  simp only [mul_add]
  rw [integral_add hr hi,_root_.OAI.LipschitzWith.integral_mul_fderiv_eq_neg (μ := volume) hw hrL hrC (1:ℂ),
    _root_.OAI.LipschitzWith.integral_mul_fderiv_eq_neg (μ := volume) hw hiL hiC I,← neg_add,← integral_add hrr hir]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  exact (inner_coordinates _ _).symm
end SignedRuns

namespace SignedRuns
open ActualLabels FiniteLabels SignedAssembly Finset DiskMoments

lemma leafSum_add (f g : List Label → ℝ) (d : ℕ) (p : List Label) :
    leafSum (fun q => f q+g q) d p = leafSum f d p+leafSum g d p := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih => simp only [leafSum,ih,sum_add_distrib]

lemma leafSum_mul_const (f : List Label → ℝ) (c : ℝ) (d : ℕ) (p : List Label) :
    leafSum (fun q => f q*c) d p = leafSum f d p*c := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih => simp only [leafSum,ih,sum_mul]

lemma leafSum_const_mul (f : List Label → ℝ) (c : ℝ) (d : ℕ) (p : List Label) :
    leafSum (fun q => c*f q) d p = c*leafSum f d p := by
  simpa only [mul_comm] using leafSum_mul_const f c d p

lemma leafSum_neg (f : List Label → ℝ) (d : ℕ) (p : List Label) :
    leafSum (fun q => -(f q)) d p = -leafSum f d p := by
  simpa only [neg_one_mul] using leafSum_const_mul f (-1) d p

lemma leafSum_mono (f g : List Label → ℝ) (d : ℕ) (p : List Label)
    (hle : ∀ q, q.length = p.length+d → f q ≤ g q) : leafSum f d p ≤ leafSum g d p := by
  induction d generalizing p with
  | zero => exact hle p (by simp)
  | succ d ih =>
    apply sum_le_sum
    intro n _
    apply ih
    intro q hq
    apply hle q
    simp only [List.length_cons] at hq
    omega

lemma leafSum_congr (f g : List Label → ℝ) (d : ℕ) (p : List Label)
    (he : ∀ q, q.length = p.length+d → f q = g q) : leafSum f d p = leafSum g d p :=
  le_antisymm (leafSum_mono f g d p (fun q hq => (he q hq).le))
    (leafSum_mono g f d p (fun q hq => (he q hq).ge))

lemma leafSum_weight (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) (d : ℕ) (p : List Label) :
    leafSum (weight h r old x) d p = weight h r old x p := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
    simp only [leafSum,ih,weight,← mul_sum,(observation h r p.length x (p.headD old)).total,mul_one]

lemma leafSum_integrable (f : List Label → ℂ → ℝ) (hf : ∀ q, Integrable (f q))
    (d : ℕ) (p : List Label) : Integrable (fun x => leafSum (fun q => f q x) d p) := by
  induction d generalizing p with
  | zero => exact hf p
  | succ d ih => exact integrable_finsetSum _ (fun n _ => ih (n::p))

lemma integral_leafSum (f : List Label → ℂ → ℝ) (hf : ∀ q, Integrable (f q))
    (d : ℕ) (p : List Label) :
    (∫ x, leafSum (fun q => f q x) d p) = leafSum (fun q => ∫ x, f q x) d p := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
    simp only [leafSum]
    rw [integral_finsetSum _ (fun n _ => leafSum_integrable f hf d (n::p))]
    exact sum_congr rfl (fun n _ => ih (n::p))

theorem history_weighted_ibp (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (old : Label) (m : ℕ) :
    (∫ x, leafSum (fun q => weight h r old x q*divergence (fun y => potential g r y q) x) m []) =
      -∫ x, leafSum (fun q => inner ℝ (gradient (fun y => weight h r old y q) x) (potential g r x q)) m [] := by
  have hreg (q : List Label) := potential_regular hg hc hr hstep q
  have hint (q : List Label) : Integrable (fun x => weight h r old x q*divergence (fun y => potential g r y q) x) := by
    obtain ⟨K,hK⟩ := weight_lipschitz h r hr old q
    apply weighted_divergence_integrable hK _ (hreg q)
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg h r old x q)]
    exact weight_le_one h r old x q
  have hflux (q : List Label) : Integrable (fun x => inner ℝ (gradient (fun y => weight h r old y q) x) (potential g r x q)) := by
    obtain ⟨K,hK⟩ := weight_lipschitz h r hr old q
    exact potential_flux_integrable hK (hreg q)
  rw [integral_leafSum _ hint,integral_leafSum _ hflux,← leafSum_neg]
  apply leafSum_congr
  intro q _
  obtain ⟨K,hK⟩ := weight_lipschitz h r hr old q
  apply vector_weighted_ibp hK _ (hreg q)
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg h r old x q)]
  exact weight_le_one h r old x q

/-- Averaging preserves the complete signed run-master inequality; finite
history weights sum to one at every observation point. -/
theorem expected_run_master (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (old : Label) (m : ℕ) (x : ℂ)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x) :
    ‖gradient (runEnvelope g r 0 m) x‖ ≤
      12*leafSum (fun q => weight h r old x q*((runs q).map fun a => coneContribution a.dir
        (gradient (runEnvelope g r a.first a.last) x)).sum) (m+1) [] := by
  have hh := leafSum_mono
    (fun q => weight h r old x q*‖gradient (runEnvelope g r 0 m) x‖)
    (fun q => weight h r old x q*(12*((runs q).map fun a => coneContribution a.dir
        (gradient (runEnvelope g r a.first a.last) x)).sum)) (m+1) [] (by
      intro q hq
      cases q with
      | nil => simp at hq
      | cons n p =>
        have hp : p.length = m := by simpa using hq
        apply mul_le_mul_of_nonneg_left _ (weight_nonneg h r old x (n::p))
        simpa only [hp] using run_master hg hc hr hstep n p x hd)
  rw [leafSum_mul_const,leafSum_weight,weight,one_mul] at hh
  have he : (fun q => weight h r old x q*(12*((runs q).map fun a => coneContribution a.dir
        (gradient (runEnvelope g r a.first a.last) x)).sum)) =
      (fun q => 12*(weight h r old x q*((runs q).map fun a => coneContribution a.dir
        (gradient (runEnvelope g r a.first a.last) x)).sum)) := by funext q; ring
  rw [he,leafSum_const_mul] at hh
  exact hh
end SignedRuns

namespace SignedRuns
open DiskMoments ActualLabels Complex

lemma divergence_add {U V : ℂ → ℂ} {x : ℂ}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) :
    divergence (fun y => U y+V y) x = divergence U x+divergence V x := by
  have hUr : DifferentiableAt ℝ (fun y => (U y).re) x := Complex.reCLM.differentiableAt.comp x hU
  have hVr : DifferentiableAt ℝ (fun y => (V y).re) x := Complex.reCLM.differentiableAt.comp x hV
  have hUi : DifferentiableAt ℝ (fun y => (U y).im) x := Complex.imCLM.differentiableAt.comp x hU
  have hVi : DifferentiableAt ℝ (fun y => (V y).im) x := Complex.imCLM.differentiableAt.comp x hV
  simp only [divergence,Complex.add_re,Complex.add_im]
  rw [fderiv_fun_add hUr hVr,fderiv_fun_add hUi hVi]
  simp only [_root_.add_apply]
  ring

lemma divergence_scalar {f : ℂ → ℝ} {x : ℂ} (hf : DifferentiableAt ℝ f x) (n : ℂ) :
    divergence (fun y => f y • n) x = inner ℝ n (gradient f x) := by
  simp only [divergence,Complex.real_smul,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  rw [fderiv_mul_const hf n.re,fderiv_mul_const hf n.im]
  simp only [_root_.smul_apply,smul_eq_mul]
  rw [real_inner_comm,inner_coordinates]
  simp only [gradient,InnerProductSpace.toDual_symm_apply]
  ring

lemma listSum_diff {α : Type*} (l : List α) (V : α → ℂ → ℂ) {x : ℂ}
    (hd : ∀ a ∈ l, DifferentiableAt ℝ (V a) x) :
    DifferentiableAt ℝ (fun y => (l.map fun a => V a y).sum) x := by
  induction l with
  | nil => exact differentiableAt_const 0
  | cons a l ih =>
    exact (hd a (by simp)).add (ih (fun a ha => hd a (by simp [ha])))

lemma divergence_listSum {α : Type*} (l : List α) (V : α → ℂ → ℂ) {x : ℂ}
    (hd : ∀ a ∈ l, DifferentiableAt ℝ (V a) x) :
    divergence (fun y => (l.map fun a => V a y).sum) x = (l.map fun a => divergence (V a) x).sum := by
  induction l with
  | nil => simp [divergence]
  | cons a l ih =>
    have hs := listSum_diff l V (fun b hb => hd b (by simp [hb]))
    simp only [List.map_cons,List.sum_cons]
    rw [divergence_add (hd a (by simp)) hs,ih (fun b hb => hd b (by simp [hb]))]

lemma average_diff {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (x : ℂ) {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ (fun y => signedAverage g y t) x := by
  obtain ⟨K,hK⟩ := hg.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  exact (hasFDerivAt_signedAverage hg (fun y => norm_fderiv_le_of_lipschitz ℝ hK) x ht).differentiableAt

/-- The divergence of the exact path potential is the complete signed sum
of run gradients, with precisely the starting-baseline gradients removed. -/
lemma potential_divergence {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) (p : List Label) (x : ℂ)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x) :
    divergence (fun y => potential g r y p) x =
      ((runs p).map fun a => inner ℝ (a.dir:ℂ)
        (gradient (runEnvelope g r a.first a.last) x-gradient (fun y => signedAverage g y (r a.first)) x)).sum := by
  cases p with
  | nil => simp [potential,runs,divergence]
  | cons n p =>
    simp_rw [potential_eq_runs]
    have hd' (a : Run) (ha : a ∈ runs (n::p)) :
        DifferentiableAt ℝ (fun y => runEnvelope g r a.first a.last y-signedAverage g y (r a.first)) x :=
      (hd a.first a.last (runs_bounds n p a ha).1).sub (average_diff hg hgc x (hr a.first))
    rw [divergence_listSum _ _ (fun a ha => (hd' a ha).smul_const (a.dir:ℂ))]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    rw [divergence_scalar (hd' a ha)]
    congr 1
    simp only [gradient]
    rw [fderiv_fun_sub (hd a.first a.last (runs_bounds n p a ha).1) (average_diff hg hgc x (hr a.first)),map_sub]
end SignedRuns

namespace SignedRuns
open DiskMoments ActualLabels Finset ConeCoordinates

lemma radius_in_run_bin (r : ℕ → ℝ) (hstep : ∀ k, 2*r (k+1) = r k)
    {i j : ℕ} (hij : i ≤ j) {t : ℝ} (ht : t ∈ Icc (r j) (2*r i)) :
    ∃ k ∈ Set.Icc i j, t ∈ Icc (r k) (2*r k) := by
  obtain ⟨l,hl,htl⟩ := radius_in_bin (fun k => r (i+k))
    (fun k => by simpa [Nat.add_assoc] using hstep (i+k)) (j-i)
    (by simpa only [Nat.add_sub_of_le hij,Nat.add_zero] using ht)
  exact ⟨i+l,⟨by omega,by omega⟩,htl⟩

lemma attaining_endpoint {g : ℂ → ℝ} {r : ℕ → ℝ}
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    {i j k : ℕ} (hik : i ≤ k) (hkj : k ≤ j) {x : ℂ} {t : ℝ}
    (ht : t ∈ Icc (r k) (2*r k))
    (hmax : ∀ s ∈ Icc (r j) (2*r i), signedAverage g x s ≤ signedAverage g x t) :
    PhysicalEndpointRadius g (r k) x t := by
  refine ⟨ht,Or.inr (Or.inr ?_)⟩
  intro s hs
  apply hmax
  constructor
  · exact (radius_antitone r hr hstep hkj).trans hs.1
  · have := radius_antitone r hr hstep hik
    linarith [hs.2]

lemma attaining_interior {g : ℂ → ℝ} {r : ℕ → ℝ}
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    {i j k : ℕ} (hik : i < k) (hkj : k < j) {x : ℂ} {t : ℝ}
    (ht : t ∈ Icc (r k) (2*r k))
    (hmax : ∀ s ∈ Icc (r j) (2*r i), signedAverage g x s ≤ signedAverage g x t) :
    PhysicalNeighborhoodRadius g (r k) x t := by
  refine ⟨ht,?_⟩
  intro s _ hs
  apply hmax
  have hs' := abs_le.mp hs
  have hlow := radius_antitone r hr hstep (show k+1 ≤ j by omega)
  have hhigh := radius_antitone r hr hstep (show i+1 ≤ k by omega)
  constructor <;> linarith [hstep k,hstep i,hr k,ht.1,ht.2]

lemma unfavorable_le_norm (n : Label) (z : ℂ) : unfavorable n z ≤ 2*‖z‖ := by
  have h (s : ℝ) (hs : s^2 = 1) : max 0 (-inner ℝ (axis n s) z) ≤ ‖z‖ := by
    apply max_le (norm_nonneg _)
    have hh := abs_real_inner_le_norm (axis (n:ℂ) s) z
    rw [axis_norm (label_unit n) hs,one_mul] at hh
    exact (neg_le_abs _).trans hh
  have hp := h 1 (by norm_num)
  have hm := h (-1) (by norm_num)
  unfold unfavorable
  linarith

/-- The exact unfavorable run term is charged either to one interior bin or
one of its two end bins; padding by nonnegative costs permits summing runs. -/
lemma run_unfavorable_bound {g : ℂ → ℝ} {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (H : ℕ → Label → ℝ) (J : ℕ → ℝ) (hH : ∀ k n, 0 ≤ H k n) (hJ : ∀ k, 0 ≤ J k)
    (x : ℂ) (n : Label) {i j : ℕ} (hij : i ≤ j)
    (hd : DifferentiableAt ℝ (runEnvelope g r i j) x)
    (hinterior : ∀ k t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H k n)
    (hend : ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J k) :
    unfavorable n (gradient (runEnvelope g r i j) x) ≤
      (∑ k ∈ Icc i j, H k n)+2*(J i+J j) := by
  obtain ⟨t,ht,he,hm⟩ := runEnvelope_attains g r hg hr hstep hij x
  rw [run_gradient_touching hg hc hr hd ht he]
  obtain ⟨k,hk,hkt⟩ := radius_in_run_bin r hstep hij ht
  have hs : 0 ≤ ∑ k ∈ Icc i j, H k n := sum_nonneg (fun _ _ => hH _ _)
  by_cases hki : k = i
  · subst k
    have hb := (unfavorable_le_norm n _).trans (mul_le_mul_of_nonneg_left
      (hend i t (attaining_endpoint hr hstep le_rfl hij hkt hm)) (by norm_num : (0:ℝ) ≤ 2))
    linarith [hJ j]
  by_cases hkj : k = j
  · subst k
    have hb := (unfavorable_le_norm n _).trans (mul_le_mul_of_nonneg_left
      (hend j t (attaining_endpoint hr hstep hij le_rfl hkt hm)) (by norm_num : (0:ℝ) ≤ 2))
    linarith [hJ i]
  have hik := hk.1
  have hkj' := hk.2
  have hb := hinterior k t (attaining_interior hr hstep (by omega) (by omega) hkt hm)
  have hsum : H k n ≤ ∑ l ∈ Icc i j, H l n := single_le_sum (fun l _ => hH l n) (Finset.mem_Icc.mpr hk)
  linarith [hJ i,hJ j]
end SignedRuns

namespace SignedRuns
open ActualLabels FiniteLabels Finset

lemma leafSum_succ_last {E : Type*} [AddCommMonoid E] (f : List Label → E)
    (m : ℕ) (p : List Label) :
    leafSum f (m+1) p = leafSum (fun q => ∑ n, f (n::q)) m p := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    change (∑ n, leafSum f (m+1) (n::p)) =
      ∑ n, leafSum (fun q => ∑ j, f (j::q)) m (n::p)
    simp_rw [ih]

/-- The exact head law obtained from the genuine finite-history products. -/
lemma leafSum_headLaw (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (m : ℕ) (F : Label → ℝ) :
    leafSum (fun q => weight h r old x q*F (q.headD old)) m [] =
      expect (before h r old x m) F := by
  induction m generalizing F with
  | zero => simp only [leafSum,weight,List.headD_nil,one_mul,before,expect_delta]
  | succ m ih =>
    rw [leafSum_succ_last,before_move,expect_move]
    have he (q : List Label) :
        (∑ n, weight h r old x (n::q)*F ((n::q).headD old)) =
          weight h r old x q*expect (observation h r q.length x (q.headD old)) F := by
      simp only [weight,List.headD_cons,FiniteLabels.expect,mul_assoc,mul_sum]
    simp_rw [he]
    have hc := leafSum_congr
      (fun q => weight h r old x q*expect (observation h r q.length x (q.headD old)) F)
      (fun q => weight h r old x q*expect (observation h r m x (q.headD old)) F) m []
      (by
        intro q hq
        have hqm : q.length = m := by simpa using hq
        rw [hqm])
    rw [hc]
    exact ih (fun n => FiniteLabels.expect (observation h r m x n) F)

lemma leafSum_pathReward (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (A : ℕ → Label → Label → ℝ) (m : ℕ) :
    leafSum (fun q => weight h r old x q*pathReward old A q) m [] =
      ∑ k ∈ range m, expect (before h r old x k)
        (fun n => expect (observation h r k x n) (A k n)) := by
  induction m with
  | zero => simp [leafSum,pathReward]
  | succ m ih =>
    rw [leafSum_succ_last,sum_range_succ]
    have he (q : List Label) :
        (∑ n, weight h r old x (n::q)*pathReward old A (n::q)) =
          weight h r old x q*pathReward old A q+
            weight h r old x q*expect (observation h r q.length x (q.headD old)) (A q.length (q.headD old)) := by
      simp only [weight,pathReward,mul_add,sum_add_distrib,← sum_mul,← mul_sum,FiniteLabels.expect,mul_assoc]
      rw [(observation h r q.length x (q.headD old)).total,one_mul]
    simp_rw [he]
    rw [leafSum_add,ih]
    congr 1
    have hc := leafSum_congr
      (fun q => weight h r old x q*expect (observation h r q.length x (q.headD old)) (A q.length (q.headD old)))
      (fun q => weight h r old x q*expect (observation h r m x (q.headD old)) (A m (q.headD old))) m []
      (by
        intro q hq
        have hqm : q.length = m := by simpa using hq
        rw [hqm])
    rw [hc]
    exact leafSum_headLaw h r old x m (fun n => FiniteLabels.expect (observation h r m x n) (A m n))

end SignedRuns

namespace SignedRuns
open ActualLabels FiniteLabels Finset

lemma run_span_sum (H : ℕ → Label → ℝ) (old : Label) (p : List Label) :
    ((runs p).map fun a => ∑ k ∈ Icc a.first a.last, H k a.dir).sum =
      pathReward old (fun k _ n => H k n) p := by
  cases p with
  | nil => rfl
  | cons n p =>
    induction p generalizing n with
    | nil => simp [runs,closedRuns,activeStart,pathReward]
    | cons n' p ih =>
      by_cases hn : n = n'
      · subst n
        have hsum : (∑ k ∈ Icc (activeStart (n'::p)) (p.length+1), H k n') =
            (∑ k ∈ Icc (activeStart (n'::p)) p.length, H k n')+H (p.length+1) n' := by
          exact sum_Icc_succ_top ((activeStart_le n' p).trans (Nat.le_succ _)) _
        have hh := ih n'
        simp only [runs,List.map_cons,List.sum_cons] at hh
        simp only [runs,closedRuns,activeStart,ite_true,List.length_cons,List.map_cons,List.sum_cons,pathReward]
        rw [hsum]
        simp only [pathReward] at hh
        linarith
      · have hh := ih n'
        simp only [runs,List.map_cons,List.sum_cons] at hh
        simp only [runs,closedRuns,activeStart,hn,ite_false,List.length_cons,List.map_cons,List.sum_cons,pathReward,
          Finset.Icc_self,sum_singleton]
        simp only [pathReward] at hh
        linarith

lemma run_start_sum (J : ℕ → ℝ) (old : Label) (p : List Label) :
    ((runs p).map fun a => J a.first).sum = pathReward old (startReward J) p := by
  cases p with
  | nil => rfl
  | cons n p =>
    induction p generalizing n with
    | nil => simp [runs,activeStart,closedRuns,pathReward,startReward]
    | cons n' p ih =>
      have hh := ih n'
      simp only [runs,List.map_cons,List.sum_cons] at hh
      simp only [pathReward,startReward] at hh
      by_cases hn : n = n'
      · subst n
        simpa only [runs,closedRuns,activeStart,ite_true,List.length_cons,List.map_cons,List.sum_cons,
          pathReward,startReward,List.headD_cons,add_zero] using hh
      · simp only [runs,closedRuns,activeStart,hn,ite_false,List.length_cons,List.map_cons,List.sum_cons,
          pathReward,startReward,List.headD_cons]
        linarith

lemma run_boundary_sum (J : ℕ → ℝ) (old n : Label) (p : List Label) :
    ((runs (n::p)).map fun a => J a.first+J a.last).sum =
      pathReward old (boundaryReward J) (n::p)+J p.length := by
  induction p generalizing n with
  | nil => simp [runs,activeStart,closedRuns,pathReward,boundaryReward]
  | cons n' p ih =>
    have hh := ih n'
    simp only [runs,List.map_cons,List.sum_cons,pathReward,boundaryReward] at hh
    by_cases hn : n = n'
    · subst n
      simp only [runs,closedRuns,activeStart,ite_true,List.length_cons,List.map_cons,List.sum_cons,
        pathReward,boundaryReward,List.headD_cons]
      linarith
    · simp only [runs,closedRuns,activeStart,hn,ite_false,List.length_cons,List.map_cons,List.sum_cons,
        pathReward,boundaryReward,List.headD_cons]
      linarith

end SignedRuns

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.SpatialBudgets
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace ActualLabels
open FiniteLabels DyadicHats Finset

lemma observation_startReward_le (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (J : ℕ → ℝ) (hJ : ∀ k, 0 ≤ J k) (k : ℕ) :
    expect (before h r old x k)
      (fun n => expect (observation h r k x n) (SignedRuns.startReward J k n)) ≤
      switchCost h r x k*J k := by
  cases k with
  | zero =>
    change (expect (delta old) fun _ => expect (initial h (r 0) x) (fun _ => J 0)) ≤ 1*J 0
    rw [FiniteLabels.expect_const,FiniteLabels.expect_const,one_mul]
  | succ k =>
    change expect (marginal h r k x) (fun n => expect (row h (r (k+1)) x n)
      (fun j => if j = n then 0 else J (k+1))) ≤ _
    have he (n : Label) : (fun j : Label => if j = n then (0:ℝ) else J (k+1)) =
        fun j => J (k+1)*(if j = n then 0 else 1) := by funext j; split_ifs <;> simp
    simp_rw [he,FiniteLabels.expect_mul]
    rw [switchCost,mul_comm _ (J (k+1))]
    apply mul_le_mul_of_nonneg_left _ (hJ _)
    exact expect_mono _ (fun n => row_change_le_rate h (r (k+1)) x n)

end ActualLabels

namespace ActualLabels
open FiniteLabels Finset

lemma boundaryCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (m k : ℕ) :
    0 ≤ boundaryCost h r x m k := by
  unfold boundaryCost
  apply add_nonneg (switchCost_nonneg h r x k)
  split_ifs
  · exact zero_le_one
  · exact switchCost_nonneg h r x (k+1)

lemma boundary_reward_sum (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (J : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ range (m+1), (match k with | 0 => J 0 | l+1 => switchCost h r x (l+1)*(J l+J (l+1))))+J m =
      ∑ k ∈ range (m+1), boundaryCost h r x m k*J k := by
  induction m with
  | zero => simp [boundaryCost,switchCost]; ring
  | succ m ih =>
    conv_lhs => rw [sum_range_succ]
    conv_rhs => rw [sum_range_succ]
    have he : (∑ k ∈ range (m+1), boundaryCost h r x (m+1) k*J k) =
        (∑ k ∈ range (m+1), boundaryCost h r x m k*J k)+
          (switchCost h r x (m+1)-1)*J m := by
      conv_lhs => rw [sum_range_succ]
      conv_rhs => rw [sum_range_succ]
      have hh : (∑ k ∈ range m, boundaryCost h r x (m+1) k*J k) =
          ∑ k ∈ range m, boundaryCost h r x m k*J k := by
        apply sum_congr rfl
        intro k hk
        have hk' := mem_range.mp hk
        simp only [boundaryCost,ite_eq_right (by omega : k ≠ m+1),ite_eq_right (by omega : k ≠ m)]
      rw [hh]
      simp only [boundaryCost,ite_eq_right (by omega : m ≠ m+1),ite_true]
      ring
    rw [he,← ih]
    simp only [boundaryCost,ite_true]
    ring
end ActualLabels

namespace SignedRuns
open ActualLabels FiniteLabels Finset

lemma expected_start_sum_bound (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (J : ℕ → ℝ) (hJ : ∀ k, 0 ≤ J k) (m : ℕ) :
    leafSum (fun q => weight h r old x q*((runs q).map fun a => J a.first).sum) (m+1) [] ≤
      ∑ k ∈ range (m+1), switchCost h r x k*J k := by
  simp_rw [run_start_sum J old]
  rw [leafSum_pathReward]
  exact sum_le_sum (fun k _ => observation_startReward_le h r old x J hJ k)

lemma expected_boundary_sum_bound (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (J : ℕ → ℝ) (hJ : ∀ k, 0 ≤ J k) (m : ℕ) :
    leafSum (fun q => weight h r old x q*((runs q).map fun a => J a.first+J a.last).sum) (m+1) [] ≤
      ∑ k ∈ range (m+1), boundaryCost h r x m k*J k := by
  have he := leafSum_congr
    (fun q => weight h r old x q*((runs q).map fun a => J a.first+J a.last).sum)
    (fun q => weight h r old x q*pathReward old (boundaryReward J) q+weight h r old x q*J m)
    (m+1) [] (by
      intro q hq
      cases q with
      | nil => simp at hq
      | cons n p =>
        have hp : p.length = m := by simpa using hq
        rw [run_boundary_sum J old, hp,mul_add])
  rw [he,leafSum_add,leafSum_pathReward,leafSum_mul_const,leafSum_weight,weight,one_mul]
  rw [← boundary_reward_sum]
  exact add_le_add (sum_le_sum (fun k _ => observation_boundaryReward_le h r old x J hJ k)) le_rfl

lemma expected_span_sum (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (H : ℕ → Label → ℝ) (m : ℕ) :
    leafSum (fun q => weight h r old x q*((runs q).map fun a => ∑ k ∈ Icc a.first a.last, H k a.dir).sum) (m+1) [] =
      ∑ k ∈ range (m+1), expect (marginal h r k x) (H k) := by
  simp_rw [run_span_sum H old]
  rw [leafSum_pathReward]
  apply sum_congr rfl
  intro k _
  rw [← expect_move,← before_move]
  rfl

end SignedRuns

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

lemma cell_subset_root_neighborhood {N : ℕ} {r : ℝ} (hr : 0 < r)
    (p : ℤ × ℤ) (q : Grid N) (hq : q ∈ cellRoots N p) :
    cell (point r p) r ⊆ neighborhood r q := by
  intro y hy
  have hqp : boxNorm (point r p-point r q) ≤ 20*r := by
    rw [boxNorm_sub_comm]
    exact (mem_window_iff hr 20 p q).mp (mem_filter.mp hq).2
  have hb := boxNorm_add_le (y-point r p) (point r p-point r q)
  rw [sub_add_sub_cancel] at hb
  have hc := mem_cell_box hr hy
  change boxNorm (y-point r q) ≤ 25*r
  linarith

lemma tsum_ofReal_le {ι : Type*} (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (A : ℝ)
    (hbudget : ∀ s : Finset ι, ∑ i ∈ s, B i ≤ A) :
    (∑' i, ENNReal.ofReal (B i)) ≤ ENNReal.ofReal A := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hB i)]
  exact ENNReal.ofReal_le_ofReal (hbudget s)

end PhysicalCells

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

end CommonPrices

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
proved. This is the common production rule for all three spatial budgets. -/
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
lemma geometricRadii_step (base : ℝ) (m k : ℕ) :
    2*geometricRadii base m (k+1) = geometricRadii base m k := by
  unfold geometricRadii
  rw [pow_succ]
  field_simp
lemma geometricRadii_eq (base : ℝ) {m k : ℕ} (hk : k ≤ m) :
    geometricRadii base m k = scale base (m-k) := by
  unfold geometricRadii scale
  rw [show m = (m-k)+k by omega,pow_add]
  field_simp
  rw [show m-k+k-k = m-k by omega]
  ring

lemma marginal_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (k : ℕ)
    (hrs : ∀ i, i ≤ k → r i = s i) (x : ℂ) : marginal h r k x = marginal h s k x := by
  induction k with
  | zero => simp only [marginal,hrs 0 le_rfl]
  | succ k ih =>
    simp only [marginal,hrs (k+1) le_rfl,ih (fun i hi => hrs i (by omega))]

lemma switchCost_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (k : ℕ)
    (hrs : ∀ i, i ≤ k → r i = s i) (x : ℂ) : switchCost h r x k = switchCost h s x k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [switchCost,hrs (k+1) le_rfl,marginal_congr h r s k (fun i hi => hrs i (by omega)) x]

lemma derivativeCost_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (k : ℕ)
    (hrs : ∀ i, i ≤ k → r i = s i) (x : ℂ) : derivativeCost h r x k = derivativeCost h s x k := by
  cases k with
  | zero => simp only [derivativeCost,hrs 0 le_rfl]
  | succ k =>
    simp only [derivativeCost,hrs (k+1) le_rfl,marginal_congr h r s k (fun i hi => hrs i (by omega)) x]

lemma cellCost_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (m l : ℕ) (hl : l ≤ m)
    (hrs : ∀ i, i ≤ m → r i = s i) (q : ℤ × ℤ) : cellCost h r m l q = cellCost h s m l q := by
  have hsw (i : ℕ) (hi : i ≤ m) : (fun x => switchCost h r x i) = fun x => switchCost h s x i := by
    funext x
    exact switchCost_congr h r s i (fun j hj => hrs j (by omega)) x
  have hdc (i : ℕ) (hi : i ≤ m) : (fun x => derivativeCost h r x i) = fun x => derivativeCost h s x i := by
    funext x
    exact derivativeCost_congr h r s i (fun j hj => hrs j (by omega)) x
  unfold cellCost
  rw [hrs l hl,hsw l hl]
  congr 1
  · split_ifs with he
    · rfl
    · rw [hsw (l+1) (by omega)]
  · rw [filt_sum,filt_sum]
    apply sum_congr rfl
    intro i hi
    rw [hdc i (by have := mem_range.mp hi; omega)]
end ActualLabels

namespace SignedRuns
open ActualLabels FiniteLabels Finset DiskMoments PhysicalCells SignedAssembly

lemma run_cone_bound {g : ℂ → ℝ} {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (H : ℕ → Label → ℝ) (J : ℕ → ℝ) (hH : ∀ k n, 0 ≤ H k n) (hJ : ∀ k, 0 ≤ J k)
    (x : ℂ) (n : Label) (p : List Label)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x)
    (hinterior : ∀ k n t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H k n)
    (hend : ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J k) :
    ((runs (n::p)).map fun a => coneContribution a.dir (gradient (runEnvelope g r a.first a.last) x)).sum ≤
      divergence (fun y => potential g r y (n::p)) x+
      ((runs (n::p)).map fun a => J a.first).sum+
      ((runs (n::p)).map fun a => ∑ k ∈ Icc a.first a.last, H k a.dir).sum+
      2*((runs (n::p)).map fun a => J a.first+J a.last).sum := by
  rw [potential_divergence hg hc hr (n::p) x hd]
  rw [← List.sum_map_mul_left,← List.sum_map_add,← List.sum_map_add,← List.sum_map_add]
  apply List.sum_le_sum
  intro a ha
  have hab := runs_bounds n p a ha
  have hu := run_unfavorable_bound hg hc hr hstep H J hH hJ x a.dir hab.1
    (hd _ _ hab.1) (hinterior · a.dir ·) hend
  have hb := hend a.first (r a.first) ⟨⟨le_rfl,by linarith [hr a.first]⟩,Or.inl rfl⟩
  have hi := real_inner_le_norm (a.dir:ℂ) (gradient (fun y => signedAverage g y (r a.first)) x)
  rw [label_unit,one_mul] at hi
  simp only [inner_sub_right]
  unfold coneContribution unfavorable at *
  linarith

/-- Complete pointwise signed assembly, still retaining the divergence term.
The remaining terms are exactly the direct directional and boundary costs. -/
theorem pointwise_signed_master {g : ℂ → ℝ} (h : ℂ → ℂ) {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (H : ℕ → Label → ℝ) (J : ℕ → ℝ) (hH : ∀ k n, 0 ≤ H k n) (hJ : ∀ k, 0 ≤ J k)
    (old : Label) (m : ℕ) (x : ℂ)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x)
    (hinterior : ∀ k n t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H k n)
    (hend : ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J k) :
    ‖gradient (runEnvelope g r 0 m) x‖ ≤ 12*(
      leafSum (fun q => weight h r old x q*divergence (fun y => potential g r y q) x) (m+1) []+
      (∑ k ∈ range (m+1), expect (marginal h r k x) (H k))+
      3*(∑ k ∈ range (m+1), boundaryCost h r x m k*J k)) := by
  have hh := leafSum_mono
    (fun q => weight h r old x q*((runs q).map fun a => coneContribution a.dir
      (gradient (runEnvelope g r a.first a.last) x)).sum)
    (fun q => weight h r old x q*divergence (fun y => potential g r y q) x+
      weight h r old x q*((runs q).map fun a => J a.first).sum+
      weight h r old x q*((runs q).map fun a => ∑ k ∈ Icc a.first a.last, H k a.dir).sum+
      2*(weight h r old x q*((runs q).map fun a => J a.first+J a.last).sum)) (m+1) [] (by
        intro q hq
        cases q with
        | nil => simp at hq
        | cons n p =>
          have hh := mul_le_mul_of_nonneg_left
            (run_cone_bound hg hc hr hstep H J hH hJ x n p hd hinterior hend)
            (weight_nonneg h r old x (n::p))
          nlinarith only [hh])
  rw [leafSum_add,leafSum_add,leafSum_add,leafSum_const_mul,expected_span_sum] at hh
  have hb := expected_boundary_sum_bound h r old x J hJ m
  have hs := expected_start_sum_bound h r old x J hJ m
  have hsb : (∑ k ∈ range (m+1), switchCost h r x k*J k) ≤
      ∑ k ∈ range (m+1), boundaryCost h r x m k*J k := by
    apply sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_right _ (hJ k)
    unfold boundaryCost
    have hn : 0 ≤ if k=m then (1:ℝ) else switchCost h r x (k+1) := by
      split_ifs
      · exact zero_le_one
      · exact switchCost_nonneg h r x (k+1)
    linarith
  have hm := expected_run_master g h r hg hc hr hstep old m x hd
  linarith
end SignedRuns

namespace PhysicalCells
open DyadicHats
lemma center_mem_cell (p : ℂ) (r : ℝ) : p ∈ cell p r := by
  simp [cell,toUnit,unitCell]
lemma cellSup_le {f : ℂ → ℝ} {r A : ℝ} (p : ℤ × ℤ)
    (h : ∀ x ∈ cell (point r p) r, f x ≤ A) : cellSup f r p ≤ A := by
  apply csSup_le (Set.Nonempty.image f ⟨point r p,center_mem_cell _ _⟩)
  rintro z ⟨x,hx,rfl⟩
  exact h x hx
lemma le_cellSup {f : ℂ → ℝ} {r A : ℝ} (p : ℤ × ℤ)
    (h : ∀ x ∈ cell (point r p) r, f x ≤ A) {x : ℂ} (hx : x ∈ cell (point r p) r) :
    f x ≤ cellSup f r p := le_csSup ⟨A,by rintro z ⟨y,hy,rfl⟩; exact h y hy⟩ ⟨x,hx,rfl⟩
lemma cellSup_nonneg {f : ℂ → ℝ} {r A : ℝ} (p : ℤ × ℤ)
    (h0 : ∀ x, 0 ≤ f x) (h : ∀ x ∈ cell (point r p) r, f x ≤ A) : 0 ≤ cellSup f r p :=
  (h0 (point r p)).trans (le_cellSup p h (center_mem_cell _ _))
end PhysicalCells

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells CommonPrices DirectionNeighbors FiniteLabels Finset

lemma costLimit_pos : 0 < costLimit := by dsimp [costLimit]; positivity
lemma pointCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (x : ℂ) (m k : ℕ) :
    0 ≤ pointCost h r x m k := add_nonneg (boundaryCost_nonneg h r x m k)
      (filt_nonneg (fun i => derivativeCost_nonneg h r x i (hr i).le) k)
lemma pointCost_le (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (x : ℂ) (m k : ℕ) :
    pointCost h r x m k ≤ costLimit := by
  have hs0 := switchCost_le_one h r x k
  have hs1 := switchCost_le_one h r x (k+1)
  have ht := filt_le (by positivity : (0:ℝ) ≤ 16*(Fintype.card Label:ℝ))
    (fun i => derivativeCost_uniform h r x i (hr i)) k
  dsimp [pointCost,boundaryCost,costLimit]
  split_ifs <;> linarith

lemma pointCost_le_cellCost (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (m k : ℕ) (q : ℤ × ℤ) (x : ℂ) (hx : x ∈ neighborhood (r k) q) :
    pointCost h r x m k ≤ cellCost h r m k q := by
  have hs (i : ℕ) : switchCost h r x i ≤ localSup (fun y => switchCost h r y i) (r k) q :=
    le_localSup q (fun y _ => switchCost_le_one h r y i) hx
  have ht (i : ℕ) : derivativeCost h r x i ≤ localSup (fun y => derivativeCost h r y i) (r k) q :=
    le_localSup q (fun y _ => derivativeCost_uniform h r y i (hr i)) hx
  have hf := filt_mono ht k
  dsimp [pointCost,boundaryCost,cellCost]
  split_ifs <;> linarith [hs k,hs (k+1)]

lemma cellSup_pointCost_le {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (m k : ℕ) (p : ℤ × ℤ) (q : Grid N) (hq : q ∈ cellRoots N p) :
    cellSup (fun x => pointCost h r x m k) (r k) p ≤ cellCost h r m k q := by
  apply cellSup_le p
  intro x hx
  exact pointCost_le_cellCost h r hr m k q x (cell_subset_root_neighborhood (hr k) p q hq hx)

lemma cellSup_pointCost_uniform (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (m k : ℕ) (p : ℤ × ℤ) : cellSup (fun x => pointCost h r x m k) (r k) p ≤ costLimit :=
  cellSup_le p (fun x _ => pointCost_le h r hr x m k)

lemma pointCost_cell_budget {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (base : ℝ) (m k j : ℕ) (hrj : r k = scale base j) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, cellSup (fun x => pointCost h r x m k) (r k) p*
      rootMass h base j (cellRoots N p)) ≤
        1681*∑ q : Grid N, scalarMass h (r k) q*cellCost h r m k q := by
  calc
    _ ≤ ∑ p ∈ P, ∑ q ∈ cellRoots N p, scalarMass h (r k) q*cellCost h r m k q := by
      apply sum_le_sum
      intro p _
      unfold rootMass
      rw [mul_sum]
      apply sum_le_sum
      intro q hq
      rw [← hrj,mul_comm]
      exact mul_le_mul_of_nonneg_left (cellSup_pointCost_le h r hr m k p q hq) (norm_nonneg _)
    _ ≤ _ := cellRoots_budget _ (fun q => mul_nonneg (norm_nonneg _) (cellCost_nonneg h r hr m k q)) P
end ActualLabels

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

lemma pointCost_mass_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      cellSup (fun x => pointCost h (geometricRadii base m) x m (m-j)) (scale base j) p*
        rootMass h base j (cellRoots N p)) ≤ 1681*packingConstant*(∫ y, ‖h y‖) := by
  have he : (∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (geometricRadii base m) m (m-j) q) =
      ∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (fun i => scale base (m-i)) m (m-j) q := by
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro q _
    rw [cellCost_congr h _ _ m (m-j) (Nat.sub_le m j)
      (fun i hi => geometricRadii_eq base hi)]
  calc
    _ ≤ ∑ j ∈ range (m+1), 1681*∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (geometricRadii base m) m (m-j) q := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      have ht := pointCost_cell_budget (N := N) h (geometricRadii base m) (geometricRadii_pos hb m)
        base m (m-j) j (geometricRadii_reverse base hjm) (P j)
      simpa only [geometricRadii_reverse base hjm] using ht
    _ = 1681*(∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (geometricRadii base m) m (m-j) q) := by rw [mul_sum]
    _ ≤ _ := by
      rw [he,mul_assoc]
      exact mul_le_mul_of_nonneg_left (spatial_packing hb hR hN hh hsupp m) (by norm_num)

lemma pointCost_price_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      cellSup (fun x => pointCost h (geometricRadii base m) x m (m-j)) (scale base j) p*
        cellPrice N base h j (cellRoots N p)) ≤ costLimit*priceConstant*(∫ y, ‖h y‖) := by
  calc
    _ ≤ ∑ j ∈ range (m+1), ∑ p ∈ P j, costLimit*cellPrice N base h j (cellRoots N p) := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      apply sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_right _ (cellPrice_nonneg hb hR hN hh hsupp j _)
      rw [← geometricRadii_reverse base hjm]
      exact cellSup_pointCost_uniform h _ (geometricRadii_pos hb m) m (m-j) p
    _ = costLimit*(∑ j ∈ range (m+1), ∑ p ∈ P j, cellPrice N base h j (cellRoots N p)) := by
      simp only [mul_sum]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (cellPrice_budget hb hR hN hh hsupp m P) costLimit_pos.le

end ActualLabels

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.BandBounds
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace ActualLabels
open DyadicHats PhysicalCells CommonPrices ActualMarkTrees Finset FiniteLabels

lemma spatialPriceConstant_pos : 0 < spatialPriceConstant := by
  unfold spatialPriceConstant
  have := packingConstant_pos
  have := costLimit_pos
  have := priceConstant_nonneg
  positivity

lemma pointCost_total_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      cellSup (fun x => pointCost h (geometricRadii base m) x m (m-j)) (scale base j) p*
        (rootMass h base j (cellRoots N p)+cellPrice N base h j (cellRoots N p))) ≤
      spatialPriceConstant*(∫ y, ‖h y‖) := by
  simp only [mul_add,sum_add_distrib]
  have h1 := pointCost_mass_budget hb hR hN hh hsupp m P
  have h2 := pointCost_price_budget hb hR hN hh hsupp m P
  unfold spatialPriceConstant
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
lemma gradient_measurable (f : ℂ → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

lemma marginal_continuous (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (k : ℕ) (n : Label) :
    Continuous (fun x => marginal h r k x n) := by
  induction k generalizing n with
  | zero => exact (observation_lipschitz h r 0 (hr 0) n n).continuous
  | succ k ih =>
    change Continuous (fun x => ∑ j : Label, marginal h r k x j*row h (r (k+1)) x j n)
    apply continuous_finsetSum
    intro j _
    exact (ih j).mul (observation_lipschitz h r (k+1) (hr (k+1)) j n).continuous

lemma rate_continuous (h : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (n : Label) :
    Continuous (fun x => rate h r x n) := by
  exact (interpolate_lipschitz hr (by norm_num : (0:ℝ) ≤ 1) (fun p => by
    rw [abs_of_nonneg (switchChance_nonneg h r n p)]
    exact switchChance_le_one h r n p)).continuous

lemma switchCost_continuous (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (k : ℕ) :
    Continuous (fun x => switchCost h r x k) := by
  cases k with
  | zero => exact continuous_const
  | succ k =>
    change Continuous (fun x => ∑ j : Label, marginal h r k x j*rate h (r (k+1)) x j)
    exact continuous_finsetSum _ (fun j _ => (marginal_continuous h r hr k j).mul (rate_continuous h (hr (k+1)) j))

lemma derivativeCost_measurable (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (k : ℕ) :
    Measurable (fun x => derivativeCost h r x k) := by
  cases k with
  | zero =>
    change Measurable (fun x => r 0*∑ j : Label, ‖gradient (fun y => initial h (r 0) y j) x‖)
    exact measurable_const.mul (Finset.measurable_fun_sum _ (fun j _ => (gradient_measurable _).norm))
  | succ k =>
    change Measurable (fun x => ∑ n : Label, marginal h r k x n*(r (k+1)*
      ∑ j : Label, ‖gradient (fun y => row h (r (k+1)) y n j) x‖))
    apply Finset.measurable_fun_sum
    intro n _
    exact (marginal_continuous h r hr k n).measurable.mul
      (measurable_const.mul (Finset.measurable_fun_sum _ (fun j _ => (gradient_measurable _).norm)))

lemma filt_measurable {f : ℂ → ℕ → ℝ} (hf : ∀ i, Measurable (fun x => f x i)) (k : ℕ) :
    Measurable (fun x => filt (f x) k) := by
  induction k with
  | zero => exact hf 0
  | succ k ih => exact (hf (k+1)).add (ih.div_const 2)

lemma pointCost_measurable (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (m k : ℕ) :
    Measurable (fun x => pointCost h r x m k) := by
  unfold pointCost boundaryCost
  apply Measurable.add
  · apply Measurable.add (switchCost_continuous h r hr k).measurable
    split_ifs
    · exact measurable_const
    · exact (switchCost_continuous h r hr (k+1)).measurable
  · exact filt_measurable (derivativeCost_measurable h r hr) k
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

namespace GeometricFilter
open Finset
lemma radius_convolution {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (c J : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ range m, c k/r k*(∑ l ∈ Ico k m, r l*J l)) =
      ∑ l ∈ range m, filt c l*J l := by
  simp only [mul_sum]
  rw [← Nat.Ico_zero_eq_range,Finset.sum_Ico_Ico_comm]
  simp only [Nat.Ico_zero_eq_range]
  apply sum_congr rfl
  intro l _
  rw [← sum_mul]
  have he := radius_sum (r := r) (c := c) l (fun i _ => hr i) (fun i _ => (hstep i).symm)
  rw [← he]
  ring
end GeometricFilter

namespace SignedRuns
open ActualLabels FiniteLabels Finset DiskMoments PhysicalCells SignedAssembly GeometricFilter

lemma total_divergence_integrable (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (old : Label) (m : ℕ) :
    Integrable (fun x => leafSum (fun q => weight h r old x q*divergence (fun y => potential g r y q) x) m []) := by
  apply leafSum_integrable
  intro q
  obtain ⟨K,hK⟩ := weight_lipschitz h r hr old q
  apply weighted_divergence_integrable hK _ (potential_regular hg hc hr hstep q)
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg h r old x q)]
  exact weight_le_one h r old x q

lemma total_flux_integrable (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (old : Label) (m : ℕ) :
    Integrable (fun x => leafSum (fun q => inner ℝ (gradient (fun y => weight h r old y q) x)
      (potential g r x q)) m []) := by
  apply leafSum_integrable
  intro q
  obtain ⟨K,hK⟩ := weight_lipschitz h r hr old q
  exact potential_flux_integrable hK (potential_regular hg hc hr hstep q)

lemma band_gradient_integrable {g : ℂ → ℝ} {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (m : ℕ) : Integrable (gradient (runEnvelope g r 0 m)) := by
  have hab : r m ≤ 2*r 0 := by
    have hh := radius_antitone r hr hstep (Nat.zero_le m)
    linarith [hr 0]
  obtain ⟨L,hL⟩ := run_envelope_lipschitz hg hc (hr m) hab
  exact _root_.OAI.LipschitzWith.integrable_gradient hL (run_envelope_hasCompactSupport hg hc (hr m) hab)

/-- Integration of the signed master, with its actual history law. The only
remaining inputs here are actual analytic majorants and their integrals; no
unsigned sum of run gradients is introduced. -/
theorem integrated_signed_master {g : ℂ → ℝ} (h : ℂ → ℂ) {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (H : ℕ → Label → ℂ → ℝ) (J : ℕ → ℂ → ℝ)
    (hH : ∀ k n x, 0 ≤ H k n x) (hJ : ∀ k x, 0 ≤ J k x)
    (old : Label) (m : ℕ)
    (hinterior : ∀ᵐ x, ∀ k n t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H k n x)
    (hend : ∀ᵐ x, ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J k x)
    (hvalue : ∀ᵐ x, ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |signedAverage g x t-signedAverage g x t'| ≤ r k*J k x)
    (hHi : ∀ k, k ≤ m → ∀ n, Integrable (H k n))
    (hJi : ∀ k, k ≤ m → Integrable (J k)) :
    (∫ x, ‖gradient (runEnvelope g r 0 m) x‖) ≤
      12*((∑ k ∈ range (m+1), ∫ x, expect (marginal h r k x) (fun n => H k n x))+
        4*(∑ k ∈ range (m+1), ∫ x, pointCost h r x m k*J k x)) := by
  have hdi (k : ℕ) (hk : k ≤ m) :
      Integrable (fun x => expect (marginal h r k x) (fun n => H k n x)) := by
    apply integrable_finsetSum
    intro n _
    apply (hHi k hk n).bdd_mul (marginal_continuous h r hr k n).measurable.aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg ((marginal h r k x).nonneg n)]
      exact law_le_one _ _)
  have hbi (k : ℕ) (hk : k ≤ m) : Integrable (fun x => pointCost h r x m k*J k x) := by
    apply (hJi k hk).bdd_mul (pointCost_measurable h r hr m k).aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pointCost_nonneg h r hr x m k)]
      exact pointCost_le h r hr x m k)
  let D := fun x => ∑ k ∈ range (m+1), expect (marginal h r k x) (fun n => H k n x)
  let B := fun x => ∑ k ∈ range (m+1), pointCost h r x m k*J k x
  have hDi : Integrable D := integrable_finsetSum _ (fun k hk => hdi k (by have := mem_range.mp hk; omega))
  have hBi : Integrable B := integrable_finsetSum _ (fun k hk => hbi k (by have := mem_range.mp hk; omega))
  let div := fun x => leafSum (fun q => weight h r old x q*divergence (fun y => potential g r y q) x) (m+1) []
  let flux := fun x => leafSum (fun q => inner ℝ (gradient (fun y => weight h r old y q) x) (potential g r x q)) (m+1) []
  have hdivi : Integrable div := total_divergence_integrable g h r hg hc hr hstep old (m+1)
  have hfluxi : Integrable flux := total_flux_integrable g h r hg hc hr hstep old (m+1)
  have hb (x : ℂ) : (∑ k ∈ range (m+1), boundaryCost h r x m k*J k x) ≤ B x := by
    apply sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_right _ (hJ k x)
    dsimp [pointCost]
    linarith [filt_nonneg (fun i => derivativeCost_nonneg h r x i (hr i).le) k]
  have hmaster : ∀ᵐ x, ‖gradient (runEnvelope g r 0 m) x‖ ≤ 12*(div x+D x+3*B x) := by
    filter_upwards [runs_ae_diff hg hc hr hstep,hinterior,hend] with x hd hi he
    have hh := pointwise_signed_master h hg hc hr hstep (fun k n => H k n x) (fun k => J k x)
      (fun k n => hH k n x) (fun k => hJ k x) old m x hd hi he
    change ‖gradient (runEnvelope g r 0 m) x‖ ≤ 12*(div x+D x+3*_) at hh
    linarith [hb x]
  have hf : ∀ᵐ x, -flux x ≤ B x := by
    filter_upwards [observation_ae_diff h r hr,hvalue] with x hd hv
    have ht := actual_signed_flux_bound g h r hg hr hstep old x hd (fun k => r k*J k x) hv (m+1)
    rw [radius_convolution hr hstep] at ht
    have hle : (∑ k ∈ range (m+1), filt (fun i => derivativeCost h r x i) k*J k x) ≤ B x := by
      apply sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_right _ (hJ k x)
      dsimp [pointCost]
      linarith [boundaryCost_nonneg h r x m k]
    exact (neg_le_abs (flux x)).trans (ht.trans hle)
  have hi := integral_mono_ae (band_gradient_integrable hg hc hr hstep m).norm
    ((hdivi.add hDi).add (hBi.const_mul 3) |>.const_mul 12) hmaster
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (f := fun x => div x+D x) (g := fun x => 3*B x) (hdivi.add hDi) (hBi.const_mul 3),integral_add hdivi hDi,
    integral_const_mul] at hi
  have hip : (∫ x, div x) = -∫ x, flux x := history_weighted_ibp g h r hg hc hr hstep old (m+1)
  have hfi := integral_mono_ae hfluxi.neg hBi hf
  simp only [Pi.neg_apply,integral_neg] at hfi
  have hDint : (∫ x, D x) = ∑ k ∈ range (m+1), ∫ x, expect (marginal h r k x) (fun n => H k n x) :=
    integral_finsetSum _ (fun k hk => hdi k (by have := mem_range.mp hk; omega))
  have hBint : (∫ x, B x) = ∑ k ∈ range (m+1), ∫ x, pointCost h r x m k*J k x :=
    integral_finsetSum _ (fun k hk => hbi k (by have := mem_range.mp hk; omega))
  rw [hip] at hi
  rw [← hDint,← hBint]
  linarith
end SignedRuns

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

/-- Actual endpoint/value weights charged simultaneously at every level. -/
theorem patched_joint : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R) (hN : R/base+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) →
    ∃ J : ℕ → ℂ → ℝ,
      (∀ j x, 0 ≤ J j x) ∧ (∀ j, Integrable (J j)) ∧
      (∀ᵐ x, ∀ j t, PhysicalEndpointRadius g (scale base j) x t →
        ‖gradient (fun y => signedAverage g y t) x‖ ≤ J j x) ∧
      (∀ᵐ x, ∀ j t t', 0 < t → t ≤ 4*scale base j → 0 < t' → t' ≤ 4*scale base j →
        |signedAverage g x t-signedAverage g x t'| ≤ scale base j*J j x) ∧
      (∀ m, (∑ j ∈ range (m+1), ∫ x, pointCost (gradient g) (geometricRadii base m) x m (m-j)*J j x) ≤
        C*(∫ y, ‖gradient g y‖)) := by
  obtain ⟨c,hc,hp⟩ := physical_joint_price
  refine ⟨c*spatialPriceConstant,mul_pos hc spatialPriceConstant_pos,?_⟩
  intro N base R hb hR hN g hg hh hs hd
  let n : Label := target (gradient g) base (0,0)
  choose F hFm hFi hFb hFv using fun j p => hp hb hR hN hg hh hs hd j p n
  let B := fun j p => rootMass (gradient g) base j (cellRoots N p)+cellPrice N base (gradient g) j (cellRoots N p)
  have hB (j p) : 0 ≤ B j p := add_nonneg (rootMass_nonneg _ _ _ _) (cellPrice_nonneg hb hR hN hh hs j _)
  have hpi (j) : (∫⁻ x, patch (scale base j) (F j) x) ≤
      ENNReal.ofReal (c*((1681+priceConstant)*(∫ y, ‖gradient g y‖))) := by
    apply lintegral_patch_budget _ _ (hFm j) (fun p => c*B j p) (fun p => mul_nonneg hc.le (hB j p)) _ (hFi j)
    intro P
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (total_level_budget hb hR hN hh hs j P) hc.le
  let J := fun j x => (patch (scale base j) (F j) x).toReal
  have hJi (j) : Integrable (J j) := patch_integrable _ _ (hFm j) (hpi j)
  have hfin : ∀ᵐ x, ∀ j, patch (scale base j) (F j) x ≠ ⊤ :=
    (ae_all_iff).mpr (fun j => patch_finite _ _ (hFm j) (hpi j))
  refine ⟨J,fun _ _ => ENNReal.toReal_nonneg,hJi,?_,?_,?_⟩
  · filter_upwards [hfin] with x hx
    intro j t ht
    exact real_le_patch (F j) (gridIndex (scale base j) x) (mem_index_cell (scale_pos hb j) x) (hx j)
      (hFb j _ x (mem_index_cell (scale_pos hb j) x) t ht)
  · filter_upwards [hfin] with x hx
    intro j t t' ht hb' ht' hb''
    have ht := real_le_patch (F j) (gridIndex (scale base j) x) (mem_index_cell (scale_pos hb j) x) (hx j)
      (hFv j _ x (mem_index_cell (scale_pos hb j) x) t t' ht hb' ht' hb'')
    exact (div_le_iff₀ (scale_pos hb j)).mp ht |>.trans_eq (mul_comm _ _)
  · intro m
    let W := fun j x => pointCost (gradient g) (geometricRadii base m) x m (m-j)
    let A := fun j p => cellSup (W j) (scale base j) p
    have hwm (j) : Measurable (W j) := pointCost_measurable _ _ (geometricRadii_pos hb m) m (m-j)
    have hw0 (j x) : 0 ≤ W j x := pointCost_nonneg _ _ (geometricRadii_pos hb m) x m (m-j)
    have hwM (j x) : W j x ≤ costLimit := pointCost_le _ _ (geometricRadii_pos hb m) x m (m-j)
    have hA (j p) : 0 ≤ A j p := cellSup_nonneg p (hw0 j) (fun x _ => hwM j x)
    have hWB (j p x) (hx : x ∈ cell (point (scale base j) p) (scale base j)) :
        ENNReal.ofReal (W j x) ≤ ENNReal.ofReal (A j p) :=
      ENNReal.ofReal_le_ofReal (le_cellSup p (fun y _ => hwM j y) hx)
    have hwt := integrated_weighted_patches (range (m+1)) (scale base) F
      (fun j _ => hFm j) (fun j x => ENNReal.ofReal (W j x)) (fun j _ => (hwm j).ennreal_ofReal)
      A (fun j p => c*B j p) (fun j _ => hA j) (fun j _ p => mul_nonneg hc.le (hB j p))
      (fun j _ => hFi j) (fun j _ => hWB j) (c*spatialPriceConstant*(∫ y, ‖gradient g y‖)) (by
        intro P
        have hbgt := mul_le_mul_of_nonneg_left (pointCost_total_budget hb hR hN hh hs m (fun _ => P)) hc.le
        simpa only [A,W,B,mul_sum,mul_assoc,mul_left_comm] using hbgt)
    exact real_weighted_patches (range (m+1)) (scale base) F (fun j _ => hJi j)
      W (fun j _ => hwm j) (fun j _ => hw0 j) costLimit (fun j _ => hwM j)
      (mul_nonneg (mul_nonneg hc.le spatialPriceConstant_pos.le) (integral_nonneg (fun y => norm_nonneg _))) hwt
end CommonPrices

namespace SignedRuns
open ActualLabels FiniteLabels Finset DiskMoments PhysicalCells SignedAssembly GeometricFilter CommonPrices DyadicHats

/-- Reverse the spatial scale index and fill unused indices with genuine global
Lipschitz bounds. Only the physical prices at indices at most m are integrated. -/
lemma master_from_patches {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {base : ℝ} (hb : 0 < base) (m : ℕ)
    (H : ℕ → Label → ℂ → ℝ) (J : ℕ → ℂ → ℝ)
    (hH : ∀ j n x, 0 ≤ H j n x) (hJ : ∀ j x, 0 ≤ J j x)
    (hHi : ∀ j n, Integrable (H j n)) (hJi : ∀ j, Integrable (J j))
    (hinterior : ∀ᵐ x, ∀ j n t, PhysicalNeighborhoodRadius g (scale base j) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H j n x)
    (hend : ∀ᵐ x, ∀ j t, PhysicalEndpointRadius g (scale base j) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J j x)
    (hvalue : ∀ᵐ x, ∀ j t t', 0 < t → t ≤ 4*scale base j → 0 < t' → t' ≤ 4*scale base j →
      |signedAverage g x t-signedAverage g x t'| ≤ scale base j*J j x) :
    (∫ x, ‖gradient (runEnvelope g (geometricRadii base m) 0 m) x‖) ≤
      12*((∑ j ∈ range (m+1), ∫ x, expect (marginal (gradient g) (geometricRadii base m) (m-j) x) (fun n => H j n x))+
        4*(∑ j ∈ range (m+1), ∫ x, pointCost (gradient g) (geometricRadii base m) x m (m-j)*J j x)) := by
  classical
  let r := geometricRadii base m
  have hr := geometricRadii_pos hb m
  obtain ⟨L,hL⟩ := hg.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hg.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have hMa (y) : |g y| ≤ M := by simpa only [Real.norm_eq_abs] using hM y
  let H' := fun k n x => if k ≤ m then H (m-k) n x else 2*(L:ℝ)
  let J' := fun k x => if k ≤ m then J (m-k) x else (L:ℝ)+2*M/r k
  have hH' (k n x) : 0 ≤ H' k n x := by dsimp [H']; split_ifs; exact hH _ _ _; positivity
  have hJ' (k x) : 0 ≤ J' k x := by
    dsimp [J']; split_ifs
    · exact hJ _ _
    · exact add_nonneg L.coe_nonneg (div_nonneg (mul_nonneg (by norm_num) hM0) (hr k).le)
  have hHi' (k) (hk : k ≤ m) (n) : Integrable (H' k n) := by simpa only [H',ite_eq_left hk] using hHi (m-k) n
  have hJi' (k) (hk : k ≤ m) : Integrable (J' k) := by simpa only [J',ite_eq_left hk] using hJi (m-k)
  have hint' : ∀ᵐ x, ∀ k n t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H' k n x := by
    filter_upwards [hinterior] with x hx
    intro k n t ht
    dsimp [H']
    split_ifs with hk
    · apply hx
      simpa only [r,geometricRadii_eq base hk] using ht
    · exact (unfavorable_le_norm n _).trans (mul_le_mul_of_nonneg_left
        (gradient_norm_le (signedAverage_lipschitz hL ((hr k).trans_le ht.1.1)) x) (by norm_num))
  have hend' : ∀ᵐ x, ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J' k x := by
    filter_upwards [hend] with x hx
    intro k t ht
    dsimp [J']
    split_ifs with hk
    · apply hx
      simpa only [r,geometricRadii_eq base hk] using ht
    · have he := gradient_norm_le (signedAverage_lipschitz hL ((hr k).trans_le ht.1.1)) x
      have hpos : 0 ≤ 2*M/r k := div_nonneg (mul_nonneg (by norm_num) hM0) (hr k).le
      linarith
  have hval' : ∀ᵐ x, ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |signedAverage g x t-signedAverage g x t'| ≤ r k*J' k x := by
    filter_upwards [hvalue] with x hx
    intro k t t' ht hbt ht' hbt'
    dsimp [J']
    split_ifs with hk
    · simpa only [r,geometricRadii_eq base hk] using hx (m-k) t t' ht
        (by simpa only [r,geometricRadii_eq base hk] using hbt) ht'
        (by simpa only [r,geometricRadii_eq base hk] using hbt')
    · have he := abs_sub (signedAverage g x t) (signedAverage g x t')
      have he1 := signedAverage_abs_le hMa x ht
      have he2 := signedAverage_abs_le hMa x ht'
      rw [mul_add,mul_div_cancel₀ _ (hr k).ne']
      have hp : 0 ≤ r k*(L:ℝ) := mul_nonneg (hr k).le L.coe_nonneg
      linarith
  have hi := integrated_signed_master (gradient g) hg hc hr (geometricRadii_step base m)
    H' J' hH' hJ' (target (gradient g) base (0,0)) m hint' hend' hval' hHi' hJi'
  have hd : (∑ k ∈ range (m+1), ∫ x, expect (marginal (gradient g) r k x) (fun n => H' k n x)) =
      ∑ j ∈ range (m+1), ∫ x, expect (marginal (gradient g) r (m-j) x) (fun n => H j n x) := by
    rw [← sum_range_reflect (fun k => ∫ x, expect (marginal (gradient g) r k x) (fun n => H' k n x)) (m+1)]
    apply sum_congr rfl
    intro j hj
    have hjm : j ≤ m := by have := mem_range.mp hj; omega
    simp only [Nat.add_sub_cancel,H',ite_eq_left (Nat.sub_le m j),Nat.sub_sub_self hjm]
  have he : (∑ k ∈ range (m+1), ∫ x, pointCost (gradient g) r x m k*J' k x) =
      ∑ j ∈ range (m+1), ∫ x, pointCost (gradient g) r x m (m-j)*J j x := by
    rw [← sum_range_reflect (fun k => ∫ x, pointCost (gradient g) r x m k*J' k x) (m+1)]
    apply sum_congr rfl
    intro j hj
    have hjm : j ≤ m := by have := mem_range.mp hj; omega
    simp only [Nat.add_sub_cancel,J',ite_eq_left (Nat.sub_le m j),Nat.sub_sub_self hjm]
  rw [hd,he] at hi
  exact hi

/-- The genuine smooth signed dyadic finite-band estimate. No probability,
common-price, local analytic estimate, or total variation bound is assumed. -/
theorem smooth_compact_dyadic_band : ∃ C : ℝ, 0 < C ∧
    ∀ {g : ℂ → ℝ}, ContDiff ℝ 1 g → HasCompactSupport g →
    ∀ {base : ℝ}, 0 < base → ∀ m : ℕ,
    (∫ x, ‖gradient (runEnvelope g (geometricRadii base m) 0 m) x‖) ≤ C*(∫ x, ‖gradient g x‖) := by
  obtain ⟨Cd,hCd,hpd⟩ := patched_unfavorable
  obtain ⟨Cj,hCj,hpj⟩ := patched_joint
  refine ⟨12*((Fintype.card Label:ℝ)*Cd+4*Cj),by positivity,?_⟩
  intro g hg hc base hb m
  have hh : Integrable (gradient g) := (continuous_gradient hg).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)
  obtain ⟨R0,hR0⟩ := (gradient_hasCompactSupport hc).isBounded.subset_closedBall (0:ℂ)
  let R := max 0 R0
  have hR : 0 ≤ R := le_max_left _ _
  have hs : ∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R := by
    intro y hy
    have he : ‖y‖ ≤ R0 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hR0 (subset_tsupport (gradient g) hy)
    exact he.trans (le_max_right _ _)
  obtain ⟨N,hN⟩ := exists_nat_ge (R/base+1)
  obtain ⟨L,hL⟩ := hg.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  have hd : ∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D := ⟨L,fun _ => norm_fderiv_le_of_lipschitz ℝ hL⟩
  obtain ⟨H,hH,hHi,hHd,hHb⟩ := hpd hb hR hN hg hh hs hd
  obtain ⟨J,hJ,hJi,hJe,hJv,hJb⟩ := hpj hb hR hN hg hh hs hd
  have hi := master_from_patches hg hc hb m H J hH hJ hHi hJi hHd hJe hJv
  have hdi (j : ℕ) (n : Label) : Integrable (fun x => marginal (gradient g) (geometricRadii base m) (m-j) x n*H j n x) := by
    apply (hHi j n).bdd_mul (marginal_continuous _ _ (geometricRadii_pos hb m) (m-j) n).measurable.aestronglyMeasurable
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg ((marginal _ _ _ x).nonneg n)]; exact law_le_one _ _)
  have hD : (∑ j ∈ range (m+1), ∫ x, expect (marginal (gradient g) (geometricRadii base m) (m-j) x) (fun n => H j n x)) ≤
      (Fintype.card Label:ℝ)*Cd*(∫ y, ‖gradient g y‖) := by
    simp only [FiniteLabels.expect]
    simp_rw [integral_finsetSum univ (fun n _ => hdi _ n)]
    rw [Finset.sum_comm]
    have he := sum_le_sum (s := univ) (fun n _ => hHb m n)
    simpa only [sum_const,card_univ,nsmul_eq_mul,mul_assoc] using he
  have hB := hJb m
  nlinarith only [hi,hD,hB]
end SignedRuns

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.WeakLimits
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
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace SobolevBand
open DiskMoments RadiusEnvelope SignedRuns GeometricFilter DyadicHats ActualLabels

lemma geometric_band_eq (f : ℂ → ℝ) (a : ℝ) (m : ℕ) :
    runEnvelope f (geometricRadii a m) 0 m = band f a (2*((2:ℝ)^m*a)) := by
  unfold runEnvelope band
  rw [geometricRadii_eq a (le_refl m),geometricRadii_eq a (Nat.zero_le m)]
  simp only [Nat.sub_self,Nat.sub_zero,scale,pow_zero,one_mul]

lemma smooth_dyadic_bound_oai : ∃ C : ℝ, 0<C ∧ ∀ {f : ℂ → ℝ}, ContDiff ℝ 1 f →
    HasCompactSupport f → ∀ {a : ℝ}, 0<a → ∀ m : ℕ,
    (∫ x,‖gradient (band f a (2*((2:ℝ)^m*a))) x‖) ≤ C*(∫ x,‖gradient f x‖) := by
  obtain ⟨C,hC,he⟩ := smooth_compact_dyadic_band
  refine ⟨C,hC,?_⟩
  intro f hf hc a ha m
  simpa only [geometric_band_eq] using he hf hc ha m

end SobolevBand

end

end OAI
end

theorem solution : type_of% @OAI.SobolevBand.smooth_dyadic_bound_oai := @OAI.SobolevBand.smooth_dyadic_bound_oai

-- Prove2me | solution 1 for OAI.SignedDisk.CenteredDiskEndpoint.main_signed_finite_band
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:32:35.418021+00:00
-- url     : https://prove2.me/submissions/50591b93-025d-43f0-bc66-9cb34ca9e0e7

import Mathlib
import Definitions.Def_SignedFiniteBand
import Definitions.Def_OAIW2SD000
import Theorems.Thm_OAI_SignedDisk_CommonPrices_patched_joint
import Theorems.Thm_OAI_SignedDisk_CommonPrices_patched_unfavorable

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskKernels1
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

noncomputable section

namespace SignedDisk

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

namespace DiskMoments
open DiskKernels

lemma gradient_hasCompactSupport {g : ℂ → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (gradient g) := (hc.fderiv ℝ).comp_left (map_zero _)

end DiskMoments

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
-- module Solutions.OAIW2_SignedDisk.SignedDisk_IntrinsicMarks1
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

noncomputable section

namespace SignedDisk

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

end DyadicHats

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff

namespace LipschitzWith
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
    ((SignedDisk.LipschitzWith.locallyIntegrable_gradient hf).integrableOn_isCompact hs)

theorem integral_mul_fderiv_eq_neg (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    (hgc : HasCompactSupport g) (v : E) :
    (∫ x, f x * fderiv ℝ g x v ∂μ) = -∫ x, inner ℝ (gradient f x) v * g x ∂μ := by
  simp only [gradient,InnerProductSpace.toDual_symm_apply]
  have h := SignedDisk.LipschitzWith.integral_fderiv_mul_eq_neg (μ := μ) hf hg hgc v
  rw [show (fun x => f x * fderiv ℝ g x v) = (fun x => fderiv ℝ g x v * f x) by
    funext x; exact mul_comm _ _]
  linarith

end LipschitzWith

open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

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

open Finset

open Finset

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

lemma continuous_boxNorm : Continuous boxNorm :=
  (Complex.continuous_re.abs).max (Complex.continuous_im.abs)

lemma local_neighborhood {r : ℝ} {q x : ℂ} (hx : boxNorm (x-q) < 199*r) :
    ∀ᶠ y in 𝓝 x, boxNorm (y-q) < 199*r := by
  exact ((continuous_boxNorm.comp (continuous_id.sub continuous_const)).continuousAt.eventually
    (eventually_lt_nhds hx))

end DyadicHats

namespace FiniteLabels

section
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

end

open DyadicHats

end FiniteLabels

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

end ConeCoordinates

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

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats

lemma label_unit (n : Label) : ‖(n:ℂ)‖ = 1 := fixedPalette.unit n n.property

end ActualLabels

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_FiniteLabels2
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

end FiniteLabels

namespace ActualLabels
open FiniteLabels DyadicHats DirectionNeighbors ConeCoordinates

lemma rate_nonneg (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : 0 ≤ rate h r x n :=
  interpolate_nonneg r x (switchChance_nonneg h r n)
lemma rate_le_one (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : rate h r x n ≤ 1 :=
  interpolate_le_const r x (switchChance_le_one h r n)

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

end ActualLabels

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

namespace FiniteLabels
variable {ι : Type*} [Fintype ι]
lemma expect_le_const (μ : Law ι) {f : ι → ℝ} {c : ℝ} (h : ∀ i, f i ≤ c) :
    expect μ f ≤ c := (expect_mono μ h).trans_eq (expect_const μ c)
end FiniteLabels

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats Finset

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

end ActualLabels

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
open DyadicHats GeometricFilter FiniteLabels Finset
lemma derivativeCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (i : ℕ) (hr : 0 ≤ r i) :
    0 ≤ derivativeCost h r x i := by
  cases i with
  | zero => exact mul_nonneg hr (sum_nonneg (fun _ _ => norm_nonneg _))
  | succ i => exact FiniteLabels.expect_nonneg _ (rowDerivative_nonneg h hr x)

end ActualLabels

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

namespace DiskMoments

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

namespace SignedRuns

section
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
end

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

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskMoments1
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
  have hi := (innerSL ℝ v).integrable_comp (SignedDisk.LipschitzWith.integrable_gradient (μ := volume) hf hc)
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
  rw [integral_add hr hi,SignedDisk.LipschitzWith.integral_mul_fderiv_eq_neg hw hrL hrC (1:ℂ),
    SignedDisk.LipschitzWith.integral_mul_fderiv_eq_neg hw hiL hiC I,← neg_add,← integral_add hrr hir]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  exact (inner_coordinates _ _).symm

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

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells CommonPrices DirectionNeighbors FiniteLabels Finset

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
  exact SignedDisk.LipschitzWith.integrable_gradient hL (run_envelope_hasCompactSupport hg hc (hr m) hab)

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

/- Directional weak gradients and coordinate isometries on the plane. -/
namespace WeakSobolev
open ContinuousLinearMap
open scoped Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma norm_convolution_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : E → ℝ} {g : E → F}
    (hK : Integrable K μ) (hg : Integrable g μ) :
    (∫ x, ‖(K ⋆[lsmul ℝ ℝ,μ] g) x‖ ∂μ) ≤ (∫ x, |K x| ∂μ)*(∫ x, ‖g x‖ ∂μ) := by
  have hi := hK.norm.integrable_convolution (lsmul ℝ ℝ) hg.norm
  calc
    _ ≤ ∫ x, ( (fun y => ‖K y‖) ⋆[lsmul ℝ ℝ,μ] (fun y => ‖g y‖)) x ∂μ := by
      apply integral_mono_ae (hK.integrable_convolution (lsmul ℝ ℝ) hg).norm hi
      filter_upwards [hK.norm.ae_convolution_exists (lsmul ℝ ℝ) hg.norm] with x hx
      simp only [convolution_def,lsmul_apply,smul_eq_mul] at hx ⊢
      exact norm_integral_le_of_norm_le hx (ae_of_all _ (fun y => by rw [norm_smul]))
    _ = _ := by rw [integral_convolution _ hK.norm hg.norm]; simp only [lsmul_apply,smul_eq_mul,Real.norm_eq_abs]

lemma lipschitz_hasGradient {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasGradient (μ := μ) f (gradient f) := by
  intro φ hφ hc v
  obtain ⟨K,hK⟩ := hφ.lipschitzWith_of_hasCompactSupport hc (by simp)
  exact SignedDisk.LipschitzWith.integral_mul_fderiv_eq_neg hf hK hc v
end WeakSobolev

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_Main
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

namespace SobolevBand
open DiskMoments RadiusEnvelope

lemma smooth_average_lipschitz {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a t : ℝ} (ha : 0<a) (hat : a≤t) :
    LipschitzWith (⟨(∫ y, ‖gradient f y‖)/(Real.pi*a^2),by positivity⟩ : ℝ≥0) (fun x => signedAverage f x t) := by
  obtain ⟨L,hL⟩ := hf.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  have hD := fun y => norm_fderiv_le_of_lipschitz ℝ hL (x₀ := y)
  have hi : Integrable (gradient f) := (continuous_gradient hf).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)
  have ht := ha.trans_le hat
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hasFDerivAt_signedAverage hf hD x ht).differentiableAt)
  intro x
  change ‖fderiv ℝ (fun x => signedAverage f x t) x‖ ≤ _
  rw [← (InnerProductSpace.toDual ℝ ℂ).symm.norm_map]
  change ‖gradient (fun x => signedAverage f x t) x‖ ≤ _
  rw [gradient_signedAverage hf hD x ht,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(Real.pi*t^2)⁻¹)]
  have he : ‖∫ y in Metric.ball x t, gradient f y‖ ≤ ∫ y, ‖gradient f y‖ :=
    (norm_integral_le_integral_norm _).trans (setIntegral_le_integral hi.norm (ae_of_all _ (fun y => norm_nonneg _)))
  rw [← div_eq_inv_mul]
  exact (div_le_div_of_nonneg_right he (by positivity)).trans
    (div_le_div_of_nonneg_left (integral_nonneg (fun y => norm_nonneg _)) (by positivity)
      (mul_le_mul_of_nonneg_left (sq_le_sq₀ ha.le ht.le |>.mpr hat) Real.pi_pos.le))

lemma smooth_band_lipschitz {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    LipschitzWith (⟨(∫ y, ‖gradient f y‖)/(Real.pi*a^2),by positivity⟩ : ℝ≥0) (band f a b) :=
  RadiusEnvelope.lipschitz hab (fun x => signedAverage_radius_continuousOn hf x ha)
    (fun _ hr => smooth_average_lipschitz hf hc ha hr.1)

open DiskMoments RadiusEnvelope SignedRuns GeometricFilter DyadicHats ActualLabels

lemma geometric_band_eq (f : ℂ → ℝ) (a : ℝ) (m : ℕ) :
    runEnvelope f (geometricRadii a m) 0 m = band f a (2*((2:ℝ)^m*a)) := by
  unfold runEnvelope band
  rw [geometricRadii_eq a (le_refl m),geometricRadii_eq a (Nat.zero_le m)]
  simp only [Nat.sub_self,Nat.sub_zero,scale,pow_zero,one_mul]

lemma smooth_band_integrable_gradient {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    Integrable (gradient (band f a b)) :=
  SignedDisk.LipschitzWith.integrable_gradient (smooth_band_lipschitz hf hc ha hab)
    (run_envelope_hasCompactSupport hf hc ha hab)

lemma smooth_dyadic_bound : ∃ C : ℝ, 0<C ∧ ∀ {f : ℂ → ℝ}, ContDiff ℝ 1 f →
    HasCompactSupport f → ∀ {a : ℝ}, 0<a → ∀ m : ℕ,
    (∫ x,‖gradient (band f a (2*((2:ℝ)^m*a))) x‖) ≤ C*(∫ x,‖gradient f x‖) := by
  obtain ⟨C,hC,he⟩ := smooth_compact_dyadic_band
  refine ⟨C,hC,?_⟩
  intro f hf hc a ha m
  simpa only [geometric_band_eq] using he hf hc ha m

end SobolevBand

namespace WeakSobolev
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

lemma HasGradient.comp_isometry {f : F → ℝ} {g : F → F}
    (hw : HasGradient (μ := volume) f g) (e : E ≃ₗᵢ[ℝ] F) :
    HasGradient (μ := volume) (fun x => f (e x)) (fun x => e.symm (g (e x))) := by
  intro φ hφ hc v
  let ψ := φ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp e.symm.contDiff
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e.symm.toHomeomorph
  have hd x : fderiv ℝ ψ (e x) (e v)=fderiv ℝ φ x v := by
    rw [fderiv_comp (e x) (hφ.differentiable (by simp) _) (e.symm.differentiableAt),e.symm.fderiv]
    change fderiv ℝ φ (e.symm (e x)) (e.symm (e v))=fderiv ℝ φ x v
    simp only [e.symm_apply_apply]
  have hi x : ⟪e.symm (g (e x)),v⟫=⟪g (e x),e v⟫ := by
    simpa only [e.apply_symm_apply] using (e.inner_map_map (e.symm (g (e x))) v).symm
  have h := hw ψ hψ hψc (e v)
  rw [← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun y => f y*fderiv ℝ ψ y (e v)),
    ← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun y => ⟪g y,e v⟫*ψ y)] at h
  simpa only [hd,← hi,ψ,Function.comp_apply,e.symm_apply_apply] using h
end WeakSobolev

namespace CenteredDiskEndpoint
open WeakSobolev

lemma hasGradient_iff_hasWeakGradient {f : Plane → ℝ} {g : Plane → Plane}
    (hf : LocallyIntegrable f) (hg : Integrable g) :
    HasGradient (μ := volume) f g ↔ HasWeakGradient f g := by
  constructor
  · intro hw φ hφ hc i
    simpa only [testPartial,EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul]
      using hw φ hφ hc (EuclideanSpace.single i 1)
  · intro hw φ hφ hc v
    have hv : v=∑ i : Fin 2,v i • EuclideanSpace.single i 1 := by
      simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
        ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v).symm
    have hleft i : Integrable (fun x => f x*testPartial φ i x) :=
      hf.integrable_smul_right_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ _)
    have hright i : Integrable (fun x => g x i*φ x) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hg).locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
    have hd x : f x*fderiv ℝ φ x v=∑ i : Fin 2,v i*(f x*testPartial φ i x) := by
      conv_lhs => rw [hv]
      simp only [_root_.map_sum,map_smul,smul_eq_mul,Finset.mul_sum,testPartial]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hi x : ⟪g x,v⟫*φ x=∑ i : Fin 2,v i*(g x i*φ x) := by
      conv_lhs => rw [hv]
      simp only [inner_sum,real_inner_smul_right,EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hd,hi]
    rw [integral_finsetSum _ (fun i _ => (hleft i).const_mul _),
      integral_finsetSum _ (fun i _ => (hright i).const_mul _)]
    simp only [integral_const_mul,hw φ hφ hc,Finset.sum_neg_distrib,mul_neg]

lemma integrable_comp_complexPlane_symm {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} :
    Integrable (fun x => f (complexPlane.symm x)) ↔ Integrable f :=
  complexPlane.symm.measurePreserving.integrable_comp_emb complexPlane.symm.toMeasurableEquiv.measurableEmbedding

lemma locallyIntegrable_comp_complexPlane {f : Plane → ℝ} :
    LocallyIntegrable (fun z => f (complexPlane z)) ↔ LocallyIntegrable f := by
  have h := locallyIntegrable_map_homeomorph complexPlane.toHomeomorph (f := f) (μ := volume)
  change LocallyIntegrable f (Measure.map complexPlane volume) ↔ LocallyIntegrable (fun z => f (complexPlane z)) at h
  rw [complexPlane.measurePreserving.map_eq] at h
  exact h.symm

lemma gradientNorm_comp_complexPlane (g : Plane → Plane) :
    (∫ z,‖complexPlane.symm (g (complexPlane z))‖)=gradientNorm g := by
  simp only [LinearIsometryEquiv.norm_map,gradientNorm]
  exact complexPlane.measurePreserving.integral_comp complexPlane.toMeasurableEquiv.measurableEmbedding (fun x => ‖g x‖)

lemma gradientNorm_comp_complexPlane_symm (G : ℂ → ℂ) :
    gradientNorm (fun x => complexPlane (G (complexPlane.symm x)))=∫ z,‖G z‖ := by
  simp only [LinearIsometryEquiv.norm_map,gradientNorm]
  exact complexPlane.symm.measurePreserving.integral_comp complexPlane.symm.toMeasurableEquiv.measurableEmbedding (fun z => ‖G z‖)
end CenteredDiskEndpoint

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff Convolution

namespace SobolevBand
open DiskMoments RadiusEnvelope ContinuousLinearMap

lemma band_self (f : ℂ → ℝ) (a : ℝ) :
    band f a a = fun x => signedAverage f x a := by
  funext x
  simp [band, envelope, Set.Icc_self]

lemma diskKernel_nonneg (a : ℝ) (x : ℂ) : 0 ≤ diskKernel a x := by
  apply Set.indicator_nonneg
  intro y hy
  positivity

lemma diskKernel_integrable (a : ℝ) : Integrable (diskKernel a) := by
  exact (integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball

lemma diskKernel_integral_abs {a : ℝ} (ha : 0 < a) :
    (∫ x, |diskKernel a x|) = 1 := by
  simp_rw [abs_of_nonneg (diskKernel_nonneg a _)]
  rw [diskKernel, integral_indicator measurableSet_ball, setIntegral_const,
    measureReal_def, Complex.volume_ball]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le,
    smul_eq_mul]
  change a^2 * Real.pi * (Real.pi*a^2)⁻¹ = 1
  field_simp

lemma diskKernel_convolution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : ℂ → F) (a : ℝ) (x : ℂ) :
    (diskKernel a ⋆[lsmul ℝ ℝ, volume] g) x =
      (Real.pi*a^2)⁻¹ • ∫ y in Metric.ball x a, g y := by
  rw [convolution_eq_swap, ← integral_smul, ← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  have hm : x-y ∈ Metric.ball (0 : ℂ) a ↔ y ∈ Metric.ball x a := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
  by_cases hy : y ∈ Metric.ball x a
  · simp only [diskKernel, Set.indicator_of_mem (hm.mpr hy), Set.indicator_of_mem hy,
      lsmul_apply]
  · simp only [diskKernel, Set.indicator_of_notMem (mt hm.mp hy),
      Set.indicator_of_notMem hy, lsmul_apply, zero_smul]

lemma smooth_band_self_bound {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {a : ℝ} (ha : 0 < a) :
    (∫ x, ‖gradient (band f a a) x‖) ≤ ∫ x, ‖gradient f x‖ := by
  have hgi : Integrable (gradient f) :=
    (continuous_gradient hf).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)
  obtain ⟨L, hL⟩ := hf.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  have he : gradient (band f a a) = diskKernel a ⋆[lsmul ℝ ℝ, volume] gradient f := by
    funext x
    rw [band_self, gradient_signedAverage hf
      (fun y => norm_fderiv_le_of_lipschitz ℝ hL (x₀ := y)) x ha,
      diskKernel_convolution]
  rw [he]
  have h := WeakSobolev.norm_convolution_le (diskKernel_integrable a) hgi
  simpa only [diskKernel_integral_abs ha, one_mul] using h

/-- The natural index includes zero, with one absolute constant for both cases. -/
theorem smooth_dyadic_bound_including_zero : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {f : ℂ → ℝ}, ContDiff ℝ 1 f → HasCompactSupport f →
    ∀ {a : ℝ}, 0 < a → ∀ m : ℕ,
      (∫ x, ‖gradient (band f a ((2 : ℝ)^m*a)) x‖) ≤ C*(∫ x, ‖gradient f x‖) := by
  obtain ⟨C, hC, hbound⟩ := smooth_dyadic_bound
  refine ⟨max C 1, (le_max_right C 1).trans' zero_le_one, ?_⟩
  intro f hf hc a ha m
  have hv : 0 ≤ ∫ x, ‖gradient f x‖ := integral_nonneg (fun x => norm_nonneg _)
  cases m with
  | zero =>
      simpa only [pow_zero, one_mul] using
        (smooth_band_self_bound hf hc ha).trans
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_right C 1) hv)
  | succ n =>
      have he : (2 : ℝ)^(n+1)*a = 2*((2 : ℝ)^n*a) := by rw [pow_succ]; ring
      rw [he]
      exact (hbound hf hc ha n).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 1) hv)

end SobolevBand

namespace CenteredDiskEndpoint
open DiskMoments SobolevBand WeakSobolev

lemma signedAverage_comp_complexPlane (f : Plane → ℝ) (z : ℂ) (r : ℝ) :
    signedAverage (fun w => f (complexPlane w)) z r = diskAverage f (complexPlane z) r := by
  unfold signedAverage diskAverage
  congr 1
  have h := complexPlane.measurePreserving.setIntegral_image_emb
    complexPlane.toMeasurableEquiv.measurableEmbedding f (Metric.ball z r)
  rw [complexPlane.image_ball] at h
  exact h.symm

lemma signedBand_comp_complexPlane (f : Plane → ℝ) (a b : ℝ) :
    band (fun w => f (complexPlane w)) a b = fun z => signedBand f a b (complexPlane z) := by
  funext z
  simp only [band, RadiusEnvelope.envelope, signedBand, signedAverage_comp_complexPlane]

lemma gradient_comp_complexPlane {f : Plane → ℝ} (hf : Differentiable ℝ f) (z : ℂ) :
    gradient (fun w => f (complexPlane w)) z = complexPlane.symm (gradient f (complexPlane z)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  change fderiv ℝ (f ∘ complexPlane) z v = _
  rw [fderiv_comp z (hf _) complexPlane.differentiableAt, complexPlane.fderiv]
  change fderiv ℝ f (complexPlane z) (complexPlane v) = _
  rw [← inner_gradient_left]
  simpa only [complexPlane.apply_symm_apply] using
    complexPlane.inner_map_map (complexPlane.symm (gradient f (complexPlane z))) v

theorem main_signed_finite_band_oai : SignedFiniteBandStatement := by
  obtain ⟨C, hC, hbound⟩ := smooth_dyadic_bound_including_zero
  refine ⟨C, hC, ?_⟩
  intro f hf hc a ha m
  let f' : ℂ → ℝ := fun z => f (complexPlane z)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hf' : ContDiff ℝ 1 f' := hf1.comp complexPlane.contDiff
  have hc' : HasCompactSupport f' := hc.comp_homeomorph complexPlane.toHomeomorph
  have hab : a ≤ (2 : ℝ)^m*a := by
    have hp : (1 : ℝ) ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp ha.le
  have hL := smooth_band_lipschitz hf' hc' ha hab
  have hFi' := hL.continuous.locallyIntegrable (μ := volume)
  have hGi' := smooth_band_integrable_gradient hf' hc' ha hab
  have he : band f' a ((2 : ℝ)^m*a) =
      fun z => signedBand f a ((2 : ℝ)^m*a) (complexPlane z) :=
    signedBand_comp_complexPlane f a _
  have hFi : LocallyIntegrable (signedBand f a ((2 : ℝ)^m*a)) := by
    apply locallyIntegrable_comp_complexPlane.mp
    simpa only [he] using hFi'
  let G' := gradient (band f' a ((2 : ℝ)^m*a))
  let G := fun x => complexPlane (G' (complexPlane.symm x))
  have hG0 : Integrable (fun x => G' (complexPlane.symm x)) :=
    integrable_comp_complexPlane_symm.mpr hGi'
  have hGi : Integrable G :=
    complexPlane.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hG0
  have hw' : HasGradient (μ := volume) (band f' a ((2 : ℝ)^m*a)) G' :=
    lipschitz_hasGradient hL
  have hw0 := hw'.comp_isometry complexPlane.symm
  have hw : HasWeakGradient (signedBand f a ((2 : ℝ)^m*a)) G := by
    apply (hasGradient_iff_hasWeakGradient hFi hGi).mp
    simpa only [he, complexPlane.apply_symm_apply, LinearIsometryEquiv.symm_symm] using hw0
  refine ⟨hFi, G, hGi, hw, ?_⟩
  have hnorm : (∫ z, ‖gradient f' z‖) = gradientNorm (gradient f) := by
    calc
      _ = ∫ z, ‖complexPlane.symm (gradient f (complexPlane z))‖ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => congrArg norm
          (gradient_comp_complexPlane (hf1.differentiable one_ne_zero) z))
      _ = _ := gradientNorm_comp_complexPlane (gradient f)
  rw [show gradientNorm G = ∫ z, ‖G' z‖ from gradientNorm_comp_complexPlane_symm G']
  exact (hbound hf' hc' ha m).trans_eq (congrArg (fun v => C*v) hnorm)

end CenteredDiskEndpoint

end SignedDisk

end

end OAI
end

theorem solution : type_of% @OAI.SignedDisk.CenteredDiskEndpoint.main_signed_finite_band_oai := @OAI.SignedDisk.CenteredDiskEndpoint.main_signed_finite_band_oai

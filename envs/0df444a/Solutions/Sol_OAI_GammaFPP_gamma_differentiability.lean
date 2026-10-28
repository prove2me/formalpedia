-- Prove2me | solution 1 for OAI.GammaFPP.gamma_differentiability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:01:33.151904+00:00
-- url     : https://prove2.me/submissions/b30c9312-67c7-45c5-9634-67b8d942b58a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_GammaPassage
import Definitions.Def_OAIW2GF000
import Theorems.Thm_OAI_GammaFPP_CrossingBridge_gamma_direction_nat_limit
import Theorems.Thm_OAI_GammaFPP_CrossingBridge_gamma_spatial_witness_BK_scales
import Theorems.Thm_OAI_GammaFPP_GammaEnvironment_isTimeConstant

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_ExtremeSlopes
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem extreme_slopes_ordered (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    leftSlope φ ≤ rightSlope φ :=
  hφ.leftDeriv_le_rightDeriv_of_mem_interior (by simp)

theorem extreme_slopes_contact (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    HasDerivWithinAt φ (leftSlope φ) (Iio 0) 0 ∧
    HasDerivWithinAt φ (rightSlope φ) (Ioi 0) 0 := by
  exact ⟨hφ.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp),
    hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)⟩

theorem convex_transverse_profile {E : Type*} [AddCommGroup E] [Module ℝ E]
    (μ : E → ℝ) (u e : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z) :
    ConvexOn ℝ univ (fun t : ℝ => μ (u + t • e)) := by
  refine ⟨convex_univ, ?_⟩
  intro v _ w _ a b ha hb hab
  simp only [smul_eq_mul]
  have heq : u + (a * v + b * w) • e = a • (u + v • e) + b • (u + w • e) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm,
      ← add_smul, hab, one_smul, ← add_smul]
  rw [heq]
  exact (hadd _ _).trans_eq (by rw [hhom a ha, hhom b hb])

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_LocalDifferentiability
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter
open scoped Topology

theorem profile_hasDerivAt_of_equal_slopes (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ)
    (heq : leftSlope φ = rightSlope φ) : HasDerivAt φ (leftSlope φ) 0 := by
  obtain ⟨hl, hr⟩ := extreme_slopes_contact φ hφ
  rw [← heq] at hr
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  exact ⟨(hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hl,
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hr⟩

theorem differentiableAt_of_transverse_profile
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : E → ℝ) (x r : E →L[ℝ] ℝ) (u e : E)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e)
    (hprofile : DifferentiableAt ℝ (fun t : ℝ => μ (u + t • e)) 0) :
    DifferentiableAt ℝ μ u := by
  let φ : ℝ → ℝ := fun t => μ (u + t • e)
  have hinv : DifferentiableAt ℝ (fun z : E => (x z)⁻¹) u :=
    (hasDerivAt_inv (x := x u) (by rw [hxu]; norm_num)).differentiableAt.comp u x.differentiableAt
  have hquot : DifferentiableAt ℝ (fun z : E => r z / x z) u := by
    convert! r.differentiableAt.mul hinv using 1
  have hcomp : DifferentiableAt ℝ (fun z : E => φ (r z / x z)) u := by
    have hφat : DifferentiableAt ℝ φ (r u / x u) := by
      simpa only [hru, hxu, zero_div] using hprofile
    exact DifferentiableAt.comp (f := fun z : E => r z / x z) (g := φ) u hφat hquot
  have hprod : DifferentiableAt ℝ (fun z : E => x z * φ (r z / x z)) u :=
    x.differentiableAt.mul hcomp
  have hpos : ∀ᶠ z in 𝓝 u, 0 < x z :=
    x.continuous.continuousAt (lt_mem_nhds (show 0 < x u by rw [hxu]; norm_num))
  have heq : μ =ᶠ[𝓝 u] (fun z : E => x z * φ (r z / x z)) := by
    filter_upwards [hpos] with z hz
    have hrepr : z = x z • (u + (r z / x z) • e) := by
      rw [smul_add, smul_smul]
      have hc : x z * (r z / x z) = r z := by field_simp [ne_of_gt hz]
      rw [hc]
      exact hcoords z
    change μ z = x z * μ (u + (r z / x z) • e)
    conv_lhs => rw [hrepr]
    exact hhom _ (le_of_lt hz) _
  exact hprod.congr_of_eventuallyEq heq

theorem differentiableAt_of_equal_extreme_slopes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : E → ℝ) (x r : E →L[ℝ] ℝ) (u e : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e)
    (heq : leftSlope (fun t : ℝ => μ (u + t • e)) =
      rightSlope (fun t : ℝ => μ (u + t • e))) :
    ∃ ℓ : E →L[ℝ] ℝ, HasFDerivAt μ ℓ u := by
  exact differentiableAt_of_transverse_profile μ x r u e hhom hxu hru hcoords
    (profile_hasDerivAt_of_equal_slopes _ (convex_transverse_profile μ u e hadd hhom)
      heq).differentiableAt

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_Paths
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem defect_append (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds es : List Step) :
    defect τ b m a p (ds ++ es) =
      defect τ b m a p ds + defect τ b m a (p + displacement ds) es := by
  simp [defect, pathCost_append]; ring

theorem minimum_defect (τ : Edge → ℝ) (b m am ap : ℝ) (ha : am ≤ ap)
    (p : Vertex) (ds : List Step) :
    min (defect τ b m ap p ds) (defect τ b m am p ds) =
      defect τ b m ((am + ap) / 2) p ds -
        ((ap - am) / 2) * |transverse b (displacement ds)| := by
  unfold defect support
  by_cases hr : 0 ≤ transverse b (displacement ds)
  · rw [abs_of_nonneg hr, min_eq_left]
    · ring
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha) hr]
  · have hr' : transverse b (displacement ds) ≤ 0 := le_of_not_ge hr
    rw [abs_of_nonpos hr', min_eq_right]
    · ring
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha) hr']

theorem transverse_chunk_witness (τ : Edge → ℝ) (b m am ap η s : ℝ)
    (ha : am ≤ ap) (hs : 0 < s) (hη : 0 < η)
    (hgap : 4 * η ≤ (ap - am) / 2) (p : Vertex) (ds : List Step)
    (hfull : s ≤ |transverse b (displacement ds)|)
    (hcheap : defect τ b m ((am + ap) / 2) p ds < η * s) :
    defect τ b m ap p ds < -η * s ∨ defect τ b m am p ds < -η * s := by
  have hm := minimum_defect τ b m am ap ha p ds
  have hg : 0 ≤ (ap - am) / 2 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hfull hg
  have hprod' := mul_le_mul_of_nonneg_right hgap (le_of_lt hs)
  have : min (defect τ b m ap p ds) (defect τ b m am p ds) < -η * s := by
    nlinarith [mul_pos hη hs]
  exact min_lt_iff.mp this

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_WitnessDecomposition
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

variable {α : Type*}

theorem first_drop (d : α → ℝ) (η : ℝ) (xs : List α)
    (hstep : ∀ x ∈ xs, -η ≤ d x) (a : ℝ) (ha : -η ≤ a)
    (hdrop : a + total d xs < -η) :
    ∃ pre rest, xs = pre ++ rest ∧ pre ≠ [] ∧
      -2 * η ≤ a + total d pre ∧ a + total d pre < -η := by
  induction xs generalizing a with
  | nil => simp at hdrop; linarith
  | cons x xs ih =>
    have hx := hstep x (by simp)
    have ht : ∀ y ∈ xs, -η ≤ d y := fun y hy => hstep y (by simp [hy])
    by_cases h : a + d x < -η
    · refine ⟨[x], xs, rfl, by simp, ?_, ?_⟩ <;> simp <;> linarith
    · obtain ⟨pre, rest, heq, hne, hlo, hhi⟩ :=
        ih ht (a + d x) (le_of_not_gt h) (by simpa [add_assoc] using hdrop)
      refine ⟨x :: pre, rest, by simp [heq], by simp, ?_, ?_⟩
      · simpa [add_assoc] using hlo
      · simpa [add_assoc] using hhi

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_PathWitnesses
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem trace_total_defect (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds : List Step) :
    total (stepDefect τ b m a) (trace p ds) = defect τ b m a p ds := by
  induction ds generalizing p with
  | nil => simp [trace, defect, pathCost]
  | cons d ds ih =>
    simp [trace, ih, defect, pathCost, stepDefect, traversalEdge]
    ring

theorem support_step_bound (b m a : ℝ) (d : Step) :
    support b m a d.delta ≤ max |m - a * b| |a| := by
  cases d with
  | east =>
    have he : support b m a Step.east.delta = m - a * b := by
      simp [Step.delta, support, transverse]; ring
    rw [he]
    exact (le_abs_self _).trans (le_max_left _ _)
  | west =>
    have he : support b m a Step.west.delta = -(m - a * b) := by
      simp [Step.delta, support, transverse]; ring
    rw [he]
    exact (neg_le_abs _).trans (le_max_left _ _)
  | north =>
    simpa [Step.delta, support, transverse] using (le_abs_self a).trans (le_max_right |m-a*b| |a|)
  | south =>
    simpa [Step.delta, support, transverse] using (neg_le_abs a).trans (le_max_right |m-a*b| |a|)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_PlaneGeometry
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem plane_reconstruction (b : ℝ) (z : Plane) :
    z = xCoord z • direction b + rCoord b z • transverseUnit := by
  ext i
  fin_cases i <;> simp [direction, transverseUnit, PiLp.add_apply, PiLp.smul_apply]
  ring

theorem norm_positive_homogeneous (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z := by
  intro t ht z
  rw [hμ.homogeneous, abs_of_nonneg ht]

theorem planar_differentiability_of_no_corner (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (b : ℝ)
    (heq : leftSlope (fun t : ℝ => μ (direction b + t • transverseUnit)) =
      rightSlope (fun t : ℝ => μ (direction b + t • transverseUnit))) :
    ∃ ℓ : Plane →L[ℝ] ℝ, HasFDerivAt μ ℓ (direction b) := by
  exact differentiableAt_of_equal_extreme_slopes μ xCoord (rCoord b) (direction b)
    transverseUnit hμ.triangle (norm_positive_homogeneous μ hμ)
    (xCoord_direction b) (rCoord_direction b) (plane_reconstruction b) heq

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MGF
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- Exponential weighting changes the Gamma rate from `rate` to `rate - theta`. -/
lemma gamma_weighted_density {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) (x : ℝ) :
    gammaPDF shape rate x * ENNReal.ofReal (exp (theta * x)) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) *
        gammaPDF shape (rate - theta) x := by
  have hs : 0 < rate - theta := sub_pos.mpr htheta
  have hc : 0 ≤ (rate / (rate - theta)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hrate hs) shape).le
  by_cases hx : 0 ≤ x
  · rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc]
    congr 1
    have hexp : exp (-(rate * x)) * exp (theta * x) =
        exp (-((rate - theta) * x)) := by
      rw [← exp_add]
      congr 1
      ring
    calc
      rate ^ shape / Gamma shape * x ^ (shape - 1) * exp (-(rate * x)) *
          exp (theta * x) =
          rate ^ shape / Gamma shape * x ^ (shape - 1) *
            (exp (-(rate * x)) * exp (theta * x)) := by ring
      _ = rate ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x)) := by rw [hexp]
      _ = (rate / (rate - theta)) ^ shape *
          ((rate - theta) ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x))) := by
        rw [Real.div_rpow hrate.le hs.le]
        have hpow : (rate - theta) ^ shape ≠ 0 :=
          (Real.rpow_pos_of_pos hs shape).ne'
        have hgamma : Gamma shape ≠ 0 := (Real.Gamma_pos_of_pos hshape).ne'
        field_simp [hpow, hgamma]
  · rw [gammaPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

/-- The nonnegative exponential moment from the normalized density with shifted rate. -/
theorem gamma_lintegral_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x)) ∂gammaMeasure shape rate) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
  change (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x))
    ∂volume.withDensity (gammaPDF shape rate)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold gammaPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, gamma_weighted_density hshape hrate htheta]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one hshape (sub_pos.mpr htheta), mul_one]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}

lemma IidEnvironment.measurable_edgeSum (h : IidEnvironment ν P τ)
    (S : Finset PlanarFPP.Edge) : Measurable (edgeSum S τ) :=
  Finset.measurable_sum S (fun e _ => h.measurable e)

variable {shape rate theta : ℝ}

/-- The nonnegative exponential moment of a finite iid Gamma edge sum. -/
theorem GammaEnvironment.lintegral_exp_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) =
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card := by
  classical
  let X : PlanarFPP.Edge → Ω → ℝ≥0∞ :=
    fun e ω => ENNReal.ofReal (Real.exp (theta * τ e ω))
  have hX : ∀ e, Measurable (X e) := by
    intro e
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable e)))
  have hXi : iIndepFun X P := h.independent.comp
    (fun _ (x : ℝ) => ENNReal.ofReal (Real.exp (theta * x))) (fun _ => by fun_prop)
  have hpoint (ω : Ω) : ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) =
      ∏ e ∈ S, X e ω := by
    rw [edgeSum, Finset.mul_sum, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg (fun e _ => (Real.exp_pos _).le)
  have hm (e : PlanarFPP.Edge) :
      (∫⁻ ω, X e ω ∂P) = ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
    change (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * τ e ω)) ∂P) = _
    rw [← lintegral_map (f := fun x : ℝ => ENNReal.ofReal (Real.exp (theta * x)))
      (by fun_prop) (h.measurable e), h.marginal e]
    exact gamma_lintegral_exp hshape hrate htheta
  simp_rw [hpoint]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun S X hXi hX]
  simp only [hm, Finset.prod_const]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}
variable {shape rate theta : ℝ}

/-- Exponential Markov bound for a real parameter `theta` and an arbitrary real threshold. -/
theorem GammaEnvironment.exponential_markov_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  have hm : Measurable (fun ω => ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable_edgeSum S)))
  calc
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
        P {ω | ENNReal.ofReal (Real.exp (theta * a)) ≤
          ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))} := by
      apply measure_mono
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hω)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) /
        ENNReal.ofReal (Real.exp (theta * a)) :=
      meas_ge_le_lintegral_div hm.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
    _ = _ := by rw [h.lintegral_exp_edgeSum hshape hrate htheta S]

/-- Gamma Chernoff lower-tail estimate for `theta < 0`. -/
theorem GammaEnvironment.lower_tail_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_neg : theta < 0) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | edgeSum S τ ω ≤ a} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  apply le_trans (measure_mono ?_)
    (h.exponential_markov_edgeSum hshape hrate (htheta_neg.trans hrate) S a)
  intro ω hω
  exact mul_le_mul_of_nonpos_left hω htheta_neg.le

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPath
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

lemma trace_edge_length (p : Vertex) (ds : List Step) :
    ((trace p ds).map traversalEdge).length = ds.length := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simpa only [trace, List.map_cons, List.length_cons] using
      (congrArg Nat.succ (ih (p + d.delta)))

lemma pathCost_trace_edge_sum (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost w p ds = (((trace p ds).map traversalEdge).map w).sum := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp only [pathCost, trace, List.map_cons, List.sum_cons,
      traversalEdge, ih]

/-- Only a trail's traversal sum can be replaced by its distinct-edge set sum. -/
lemma pathCost_eq_distinct_edgeSum (w : Edge → ℝ) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) :
    pathCost w p ds = ∑ e ∈ ((trace p ds).map traversalEdge).toFinset, w e := by
  classical
  rw [pathCost_trace_edge_sum]
  exact (List.sum_toFinset w hn).symm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Genuine Gamma lower tail for any fixed trail, with arbitrary real threshold.
The positive parameter s uses the native MGF at theta=-s. -/
theorem GammaEnvironment.cheap_path_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) (t : ℝ) :
    P {ω | pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ ds.length /
        ENNReal.ofReal (Real.exp (-s * t)) := by
  classical
  have hc : ((trace p ds).map traversalEdge).toFinset.card = ds.length := by
    rw [List.toFinset_card_of_nodup hn, trace_edge_length]
  have he (ω : Ω) : edgeSum ((trace p ds).map traversalEdge).toFinset τ ω =
      pathCost (fun e => τ e ω) p ds := by
    exact (pathCost_eq_distinct_edgeSum (fun e => τ e ω) p ds hn).symm
  have hb := h.lower_tail_edgeSum hs hr (neg_neg_of_pos hsp)
    ((trace p ds).map traversalEdge).toFinset t
  simpa only [he, hc, sub_neg_eq_add] using hb

/-- The probability that a finite family contains a cheap trail is bounded by
its cardinality times the single-trail estimate. -/
theorem GammaEnvironment.cheap_path_family_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (F : Finset (List Step)) (n : ℕ)
    (hF : ∀ ds ∈ F, ((trace p ds).map traversalEdge).Nodup ∧ ds.length = n)
    (t : ℝ) :
    P {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (F.card : ℝ≥0∞) * ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
  classical
  have he : {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} =
      ⋃ ds ∈ F, {ω | pathCost (fun e => τ e ω) p ds ≤ t} := by
    ext ω
    simp
  rw [he]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _ds ∈ F, ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
      apply Finset.sum_le_sum
      intro ds hds
      simpa only [(hF ds hds).2] using
        h.cheap_path_probability hs hr s hsp p ds (hF ds hds).1 t
    _ = _ := by simp

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathCounting
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

attribute [local instance] OAI.GammaFPP.cheapStepFintype
private lemma cheapStep_card : Fintype.card Step = 4 := by decide

lemma card_fixedStepLists_le (n : ℕ) : (fixedStepLists n).card ≤ 4 ^ n := by
  classical
  calc
    (fixedStepLists n).card ≤ (Finset.univ : Finset (Fin n → Step)).card :=
      Finset.card_image_le
    _ = 4 ^ n := by rw [Finset.card_univ, Fintype.card_fun, cheapStep_card, Fintype.card_fin]

lemma card_fixedTrailLists_le (p : Vertex) (n : ℕ) :
    (fixedTrailLists p n).card ≤ 4 ^ n := by
  classical
  exact (Finset.card_filter_le _ _).trans (card_fixedStepLists_le n)

/-- Exact event equality; there is no hidden restriction to a selected optimizer. -/
lemma fixedTrail_event_eq {Ω : Type*} (τ : Edge → Ω → ℝ)
    (p : Vertex) (n : ℕ) (t : ℝ) :
    {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} =
    {ω | ∃ ds ∈ fixedTrailLists p n, pathCost (fun e => τ e ω) p ds ≤ t} := by
  ext ω
  simp only [Set.mem_ofPred_eq, mem_fixedTrailLists]
  constructor
  · rintro ⟨ds, hl, hn, hc⟩
    exact ⟨ds, ⟨hl, hn⟩, hc⟩
  · rintro ⟨ds, ⟨hl, hn⟩, hc⟩
    exact ⟨ds, hl, hn, hc⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual fixed-length trails, with a proved four-way exponential count. -/
theorem GammaEnvironment.cheap_fixed_length_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (n : ℕ) (t : ℝ) :
    P {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} ≤
      ((4 ^ n : ℕ) : ℝ≥0∞) *
        ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
          ENNReal.ofReal (Real.exp (-s * t))) := by
  rw [fixedTrail_event_eq]
  have hb := h.cheap_path_family_probability hs hr s hsp p (fixedTrailLists p n) n
    (fun ds hds => ((mem_fixedTrailLists p n ds).mp hds).symm) t
  refine hb.trans (mul_le_mul_left ?_ _)
  exact_mod_cast card_fixedTrailLists_le p n

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathDecay
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP
open scoped ENNReal

lemma cheapChernoff_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapChernoff shape rate := by
  have hl : 0 < Real.log (16 : ℝ) := Real.log_pos (by norm_num)
  exact mul_pos hr (sub_pos.mpr (Real.one_lt_exp_iff.mpr (div_pos hl hs)))

lemma cheapSlope_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapSlope shape rate :=
  div_pos (Real.log_pos (by norm_num)) (cheapChernoff_pos hs hr)

/-- The exact native Gamma Laplace factor is 1/16 at the chosen parameter. -/
lemma cheapChernoff_factor {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    (rate / (rate + cheapChernoff shape rate)) ^ shape = (1 / 16 : ℝ) := by
  have hd : rate + cheapChernoff shape rate =
      rate * Real.exp (Real.log 16 / shape) := by
    unfold cheapChernoff
    ring
  have hratio : rate / (rate + cheapChernoff shape rate) =
      Real.exp (-(Real.log 16 / shape)) := by
    rw [hd, Real.exp_neg]
    field_simp [hr.ne', Real.exp_ne_zero]
  rw [hratio, ← Real.exp_mul]
  have he : -(Real.log 16 / shape) * shape = -Real.log 16 := by
    field_simp [hs.ne']
  rw [he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
  norm_num

lemma cheapChernoff_mul_slope {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    cheapChernoff shape rate * cheapSlope shape rate = Real.log 2 := by
  unfold cheapSlope
  field_simp [(cheapChernoff_pos hs hr).ne']

/-- Exact cancellation of counting, Laplace factor and linear threshold. -/
lemma cheap_count_bound_eq {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) (n : ℕ) :
    (4 : ℝ)^n * (((rate / (rate + cheapChernoff shape rate)) ^ shape)^n /
      Real.exp (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) =
        (1 / 2 : ℝ)^n := by
  rw [cheapChernoff_factor hs hr]
  have he : -cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)) =
      (n : ℝ) * (-Real.log 2) := by
    have hc := cheapChernoff_mul_slope hs hr
    calc
      _ = -(cheapChernoff shape rate * cheapSlope shape rate) * (n : ℝ) := by ring
      _ = _ := by rw [hc]; ring
  rw [he, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← div_pow, ← mul_pow]
  norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual trails of n steps from p are exponentially unlikely to cost at
most c*n. This includes n=0, where the empty path has probability one. -/
theorem GammaEnvironment.cheap_fixed_length_decay_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (n : ℕ) :
    P.real {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧
        pathCost (fun e => τ e ω) p ds ≤ cheapSlope shape rate * (n : ℝ)} ≤
      (1 / 2 : ℝ)^n := by
  have hsp := cheapChernoff_pos hs hr
  have hbase : 0 ≤ (rate / (rate + cheapChernoff shape rate)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hr (add_pos hr hsp)) shape).le
  have hden : ENNReal.ofReal (Real.exp
      (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hfin : ((4 ^ n : ℕ) : ℝ≥0∞) *
      ((ENNReal.ofReal ((rate / (rate + cheapChernoff shape rate)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp
          (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ))))) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp)
      (ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden)
  have hb := ENNReal.toReal_mono hfin
    (h.cheap_fixed_length_probability hs hr (cheapChernoff shape rate) hsp p n
      (cheapSlope shape rate * (n : ℝ)))
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hbase,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Nat.cast_pow, Nat.cast_ofNat] at hb
  change P.real _ ≤ _ at hb
  rw [cheap_count_bound_eq hs hr n] at hb
  exact hb

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapLongTrails
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Exponential decay is summable, including the nonempty bad event at n=0. -/
theorem GammaEnvironment.summable_cheapTrailEvent_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) : Summable (fun n => P.real (cheapTrailEvent shape rate τ p n)) := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  exact hg.of_nonneg_of_le (fun _ => measureReal_nonneg)
    (fun n => h.cheap_fixed_length_decay_real hs hr p n)

/-- At each fixed start, almost surely all sufficiently long trails have
strictly positive linear cost. No independence across lengths is used. -/
theorem GammaEnvironment.ae_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  let := h.probability
  have hsum : (∑' n, P (cheapTrailEvent shape rate τ p n)) ≠ ⊤ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      (h.summable_cheapTrailEvent_real hs hr p).tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨N, ?_⟩
  intro ds hlen htrail
  by_contra hc
  exact hN ds.length hlen ⟨ds, rfl, htrail, le_of_not_gt hc⟩

/-- Countably many lattice starts may share one event; the length cutoff can
depend on both the environment and the start. -/
theorem GammaEnvironment.ae_all_starts_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  rw [ae_all_iff]
  intro p
  exact h.ae_long_trails_cost hs hr p

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LoopErasure
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.LoopErase
open PlanarFPP

/-- Near-optimal paths with simple physical-edge traces, at every pair of
lattice endpoints and every positive approximation error. -/
theorem exists_near_optimal_simple_path (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (ε : ℝ) (hε : 0 < ε) :
    ∃ ds : List Step, p+displacement ds=q ∧
      ((trace p ds).map traversalEdge).Nodup ∧
      passageTime w p q ≤ pathCost w p ds ∧ pathCost w p ds < passageTime w p q+ε := by
  obtain ⟨ds,hend,hcost⟩ := exists_near_optimal_path w p q ε hε
  obtain ⟨es,he,hs,hc⟩ := erase_path_loops w hw p ds
  have he' : p+displacement es=q := by rw [he,hend]
  exact ⟨es,he',hs,passageTime_le_cost w hw p q es he',hc.trans_lt hcost⟩

end GammaFPP.LoopErase

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PassageLowerBound
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP Filter

/-- Each original nearest-neighbor step contributes at most one L1 unit. -/
lemma displacement_natAbs_sum_le_length (ds : List Step) :
    (displacement ds).1.natAbs + (displacement ds).2.natAbs ≤ ds.length := by
  induction ds with
  | nil => simp [displacement]
  | cons d ds ih =>
      have h₁ := Int.natAbs_add_le d.delta.1 (displacement ds).1
      have h₂ := Int.natAbs_add_le d.delta.2 (displacement ds).2
      have hd : d.delta.1.natAbs + d.delta.2.natAbs = 1 := by
        cases d <;> norm_num [Step.delta]
      simp only [displacement_cons, List.length_cons]
      change (d.delta.1 + (displacement ds).1).natAbs +
        (d.delta.2 + (displacement ds).2).natAbs ≤ ds.length + 1
      omega

/-- Literal latticeDistance, not the product max norm. -/
lemma latticeDistance_endpoint_le_length (p : Vertex) (ds : List Step) :
    latticeDistance p (p + displacement ds) ≤ ds.length := by
  simpa only [latticeDistance, Prod.fst_add, Prod.snd_add, add_sub_cancel_left] using
    displacement_natAbs_sum_le_length ds

/-- Erasure preserves the endpoint, so every sufficiently distant arbitrary
path inherits the long-trail lower bound, even if it repeats edges. -/
lemma pathCost_lower_of_long_trails (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (p : Vertex) (N : ℕ)
    (hN : ∀ es : List Step, N ≤ es.length →
      ((trace p es).map traversalEdge).Nodup → c * (es.length : ℝ) < pathCost w p es)
    (q : Vertex) (hq : N ≤ latticeDistance p q) (ds : List Step)
    (hend : p + displacement ds = q) :
    c * (latticeDistance p q : ℝ) < pathCost w p ds := by
  obtain ⟨es, he, hn, hcost⟩ := LoopErase.erase_path_loops w hw p ds
  have hend' : p + displacement es = q := by rw [he, hend]
  have hdist : latticeDistance p q ≤ es.length := by
    simpa only [hend'] using latticeDistance_endpoint_le_length p es
  have hdistR : (latticeDistance p q : ℝ) ≤ (es.length : ℝ) := by
    exact_mod_cast hdist
  exact (mul_le_mul_of_nonneg_left hdistR hc).trans_lt
    ((hN es (hq.trans hdist) hn).trans_le hcost)

/-- Taking the infimum of path costs preserves the non-strict lower bound,
without requiring the existence of a minimizing path. -/
lemma passageTime_lower_of_long_trails (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (p : Vertex) (N : ℕ)
    (hN : ∀ es : List Step, N ≤ es.length →
      ((trace p es).map traversalEdge).Nodup → c * (es.length : ℝ) < pathCost w p es)
    (q : Vertex) (hq : N ≤ latticeDistance p q) :
    c * (latticeDistance p q : ℝ) ≤ passageTime w p q := by
  apply le_csInf (path_costs_nonempty w p q)
  rintro t ⟨ds, hend, rfl⟩
  exact (pathCost_lower_of_long_trails w hw c hc p N hN q hq ds hend).le

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- On one probability-one event, every lattice start has an eventual metric
lower bound for all distant endpoints. The cutoff may depend on start/sample. -/
theorem GammaEnvironment.ae_all_starts_passageTime_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∃ N : ℕ, ∀ q : Vertex,
      N ≤ latticeDistance p q →
        cheapSlope shape rate * (latticeDistance p q : ℝ) ≤
          passageTime (fun e => τ e ω) p q := by
  filter_upwards [h.ae_positive, h.ae_all_starts_long_trails_cost hs hr] with ω hpos hlong
  intro p
  obtain ⟨N, hN⟩ := hlong p
  refine ⟨N, ?_⟩
  intro q hq
  exact passageTime_lower_of_long_trails (fun e => τ e ω) (fun e => (hpos e).le)
    (cheapSlope shape rate) (cheapSlope_pos hs hr).le p N hN q hq

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanPositive
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped Topology ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Fatou needs only eventual lower bounds, not samplewise convergence. -/
lemma lower_le_limit_integral_of_ae_eventually [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (a m : ℝ)
    (hX : ∀ n, Measurable (X n)) (hI : ∀ n, Integrable (X n) P)
    (hpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ X n ω)
    (hlower : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, a ≤ X n ω)
    (hlimit : Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 m)) (hm : 0 ≤ m) :
    a ≤ m := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (X n ω)
  have hmeas : ∀ n, Measurable (F n) := fun n => (hX n).ennreal_ofReal
  have hpoint : ∀ᵐ ω ∂P, ENNReal.ofReal a ≤ liminf (fun n => F n ω) atTop := by
    filter_upwards [hlower] with ω hω
    exact le_liminf_of_le (h := hω.mono fun n hn => ENNReal.ofReal_le_ofReal hn)
  have hlow : ENNReal.ofReal a ≤ ∫⁻ ω, liminf (fun n => F n ω) atTop ∂P := by
    simpa only [lintegral_const, measure_univ, mul_one] using lintegral_mono_ae hpoint
  have hfatou := lintegral_liminf_le (μ := P) (u := atTop) hmeas
  have hint (n : ℕ) : (∫⁻ ω, F n ω ∂P) = ENNReal.ofReal (∫ ω, X n ω ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal (hI n) (hpos n)).symm
  have ht : Tendsto (fun n => ∫⁻ ω, F n ω ∂P) atTop (𝓝 (ENNReal.ofReal m)) := by
    simpa only [hint] using ENNReal.tendsto_ofReal hlimit
  have hb : ENNReal.ofReal a ≤ ENNReal.ofReal m := by
    simpa only [ht.liminf_eq] using hlow.trans hfatou
  exact (ENNReal.ofReal_le_ofReal_iff hm).mp hb

/-- Literal lattice L1 distance scales under natural multiplication. -/
lemma latticeDistance_zero_nsmul (z : Vertex) (n : ℕ) :
    latticeDistance 0 (n • z) = n * latticeDistance 0 z := by
  simp [latticeDistance, nsmul_eq_mul, Int.natAbs_mul, Nat.mul_add]

variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The actual Fekete mean limit has the same positive linear lower bound as
the eventual path metric. The zero direction is treated before division. -/
theorem GammaEnvironment.directionalMeanConstant_linear_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤ directionalMeanConstant h hs hr z := by
  by_cases hz : z = 0
  · subst z
    simp [latticeDistance, h.directionalMeanConstant_zero hs hr]
  let : IsProbabilityMeasure P := h.probability
  have hd : 0 < latticeDistance 0 z := by
    by_contra hn
    have hd0 : latticeDistance 0 z = 0 := Nat.eq_zero_of_not_pos hn
    have hxy : z.1 = 0 ∧ z.2 = 0 := by simpa [latticeDistance] using hd0
    exact hz (Prod.ext hxy.1 hxy.2)
  let X : ℕ → Ω → ℝ := fun n ω => passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ)
  have hX : ∀ n, Measurable (X n) := fun n =>
    (h.measurable_passageTime 0 (n • z)).div_const (n : ℝ)
  have hI : ∀ n, Integrable (X n) P := fun n =>
    (h.integrable_passageTime hs hr 0 (n • z)).div_const (n : ℝ)
  have hpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ X n ω := by
    intro n
    filter_upwards [h.ae_positive] with ω hω
    exact div_nonneg (passageTime_nonneg _ (fun e => (hω e).le) 0 (n • z))
      (Nat.cast_nonneg n)
  have hlower : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤ X n ω := by
    filter_upwards [h.ae_all_starts_passageTime_lower hs hr] with ω hω
    obtain ⟨N, hN⟩ := hω 0
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
    have hnd : N ≤ latticeDistance 0 (n • z) := by
      rw [latticeDistance_zero_nsmul]
      nlinarith
    have hb := hN (n • z) hnd
    rw [latticeDistance_zero_nsmul, Nat.cast_mul] at hb
    change cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤
      passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ)
    apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  have hlimit : Tendsto (fun n => ∫ ω, X n ω ∂P) atTop
      (𝓝 (directionalMeanConstant h hs hr z)) := by
    simpa only [X, integral_div, meanPassageSequence] using h.meanPassageSequence_tendsto hs hr z
  exact lower_le_limit_integral_of_ae_eventually X _ _ hX hI hpos hlower hlimit
    (h.directionalMeanConstant_nonneg hs hr z)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanNorm
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP Topology

/-- Positive denominators transport a lattice coercivity bound to rationals. -/
lemma rationalMean_lower (m : Vertex → ℝ) (c : ℝ)
    (hm : ∀ x, c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|) ≤ m x)
    (q : ℚ × ℚ) :
    c * (|(q.1 : ℝ)| + |(q.2 : ℝ)|) ≤ rationalMean m q := by
  let x := rationalNumerator q
  let n := rationalDenominator q
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (rationalDenominator_pos q)
  have he := rationalLatticePoint_numerator_denominator q
  have h₁ : (x.1 : ℝ) / (n : ℝ) = (q.1 : ℝ) := by
    have hq : (x.1 : ℚ) / (n : ℚ) = q.1 := by
      simpa only [rationalLatticePoint] using congrArg Prod.fst he
    exact_mod_cast hq
  have h₂ : (x.2 : ℝ) / (n : ℝ) = (q.2 : ℝ) := by
    have hq : (x.2 : ℚ) / (n : ℚ) = q.2 := by
      simpa only [rationalLatticePoint] using congrArg Prod.snd he
    exact_mod_cast hq
  change _ ≤ m x / (n : ℝ)
  rw [← h₁, ← h₂, abs_div, abs_div, abs_of_pos hn]
  simpa only [← add_div, ← mul_div_assoc] using
    div_le_div_of_nonneg_right (hm x) hn.le

/-- A closed inequality on the rational image holds on its real closure. -/
lemma realMeanExtension_lower {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (c : ℝ) (hl : ∀ q, c * (|(q.1 : ℝ)| + |(q.2 : ℝ)|) ≤ f q)
    (v : ℝ × ℝ) : c * (|v.1| + |v.2|) ≤ realMeanExtension f v := by
  apply isClosed_property rationalPairCast_dense
    (p := fun v => c * (|v.1| + |v.2|) ≤ realMeanExtension f v) ?_ ?_ v
  · exact isClosed_le
      (continuous_const.mul (continuous_fst.abs.add continuous_snd.abs))
      (realMeanExtension_uniformContinuous hf).continuous
  · intro q
    rw [realMeanExtension_on_rat hf]
    exact hl q

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma gammaMeanPairSeminorm_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : ℝ × ℝ) :
    cheapSlope shape rate * (|v.1| + |v.2|) ≤ gammaMeanPairSeminorm h hs hr v := by
  change _ ≤ realMeanExtension (rationalMean (directionalMeanConstant h hs hr)) v
  have hlip := rationalMean_l1 (directionalMeanConstant h hs hr)
    (fun k z => h.directionalMeanConstant_nsmul hs hr z k)
    (shape/rate) (h.directionalMeanConstant_l1_lipschitz hs hr)
  apply realMeanExtension_lower
    (rational_l1_lipschitz _ ⟨shape/rate, (div_pos hs hr).le⟩ hlip).uniformContinuous
  intro q
  apply rationalMean_lower
  intro z
  simpa [latticeDistance] using h.directionalMeanConstant_linear_lower hs hr z

lemma gammaMeanNorm_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : Plane) : cheapSlope shape rate * (|v 0| + |v 1|) ≤ gammaMeanNorm h hs hr v :=
  gammaMeanPairSeminorm_lower h hs hr (v 0, v 1)

/-- The real extension of the Gamma directional mean constants is a norm. -/
theorem gammaMeanNorm_laws
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    TimeConstantNorm (gammaMeanNorm h hs hr) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    exact apply_nonneg (gammaMeanPairSeminorm h hs hr) (v 0, v 1)
  · intro v
    constructor
    · intro hv
      have hb := gammaMeanNorm_lower h hs hr v
      have hc := cheapSlope_pos hs hr
      rw [hv] at hb
      have h₀ : v 0 = 0 := abs_eq_zero.mp (by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)])
      have h₁ : v 1 = 0 := abs_eq_zero.mp (by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)])
      ext i
      fin_cases i
      · exact h₀
      · exact h₁
    · rintro rfl
      change gammaMeanPairSeminorm h hs hr 0 = 0
      exact map_zero _
  · intro v w
    change gammaMeanPairSeminorm h hs hr ((v 0, v 1) + (w 0, w 1)) ≤ _
    exact map_add_le_add (gammaMeanPairSeminorm h hs hr) _ _
  · intro a v
    change gammaMeanPairSeminorm h hs hr (a • (v 0, v 1)) = _
    simpa only [Real.norm_eq_abs, gammaMeanNorm] using map_smul_eq_mul (gammaMeanPairSeminorm h hs hr) a (v 0, v 1)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_AnalyticCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Analytic
open PlanarFPP Set Filter MeasureTheory
open scoped Topology

theorem plane_coordinate_le_norm (v : Plane) (i : Fin 2) : |v i| ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

theorem timeConstantNorm_lipschitz_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v w, |μ v - μ w| ≤ B * ‖v-w‖ := by
  let e0 : Plane := PiLp.single 2 0 1
  let e1 : Plane := PiLp.single 2 1 1
  let B := μ e0 + μ e1 + 1
  have hB : 0 < B := by dsimp [B]; linarith [hμ.nonneg e0, hμ.nonneg e1]
  have hu (v : Plane) : μ v ≤ B * ‖v‖ := by
    have he : v = v 0 • e0 + v 1 • e1 := by
      ext i; fin_cases i <;> simp [e0, e1]
    have ht := hμ.triangle (v 0 • e0) (v 1 • e1)
    rw [← he, hμ.homogeneous, hμ.homogeneous] at ht
    have h0 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 0) (hμ.nonneg e0)
    have h1 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 1) (hμ.nonneg e1)
    dsimp [B]
    nlinarith [norm_nonneg v]
  refine ⟨B, hB, ?_⟩
  intro v w
  apply abs_le.mpr
  have h1 := hμ.triangle (v-w) w
  have h2 := hμ.triangle (w-v) v
  simp only [sub_add_cancel] at h1 h2
  have hu1 := hu (v-w)
  have hu2 := hu (w-v)
  rw [norm_sub_rev] at hu2
  constructor <;> linarith

theorem timeConstantNorm_continuous (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    Continuous μ := by
  obtain ⟨B, hB, hb⟩ := timeConstantNorm_lipschitz_bound μ hμ
  apply Metric.continuous_iff.mpr
  intro v ε hε
  refine ⟨ε/B, div_pos hε hB, ?_⟩
  intro w hw
  have hd : ‖w-v‖ < ε/B := hw
  have he := (lt_div_iff₀ hB).mp hd
  have hl := hb w v
  change |μ w-μ v| < ε
  nlinarith

theorem norm_direction_pos (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    0 < μ (direction b) := by
  have hn : direction b ≠ 0 := by
    intro hh
    have := congrArg xCoord hh
    norm_num [direction] at this
  exact lt_of_le_of_ne (hμ.nonneg _) (Ne.symm ((hμ.zero_iff _).not.mpr hn))

lemma norm_differentiable_smul (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (u : Plane) (t : ℝ) (ht : t ≠ 0) (hu : DifferentiableAt ℝ μ u) :
    DifferentiableAt ℝ μ (t • u) := by
  have hi : DifferentiableAt ℝ μ (t⁻¹ • (t • u)) := by simpa [smul_smul,ht] using hu
  have hc := hi.comp (t • u) (differentiableAt_id.const_smul t⁻¹)
  have hd := hc.const_mul |t|
  have he : (fun z : Plane => |t| *μ (t⁻¹ • z))=μ := by
    funext z
    rw [hμ.homogeneous,abs_inv,← mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr ht),one_mul]
  simpa only [Function.comp_def,he] using hd

lemma convex_continuous_deriv (φ : ℝ → ℝ) (hc : ConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) : Continuous (deriv φ) := by
  let g := fun x => deriv φ x+x
  have hm : Monotone g := fun x y h => add_le_add
    (hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ x) (mem_univ y) h) h
  have hg (x : ℝ) : HasDerivAt (fun t => φ t+t^2/2) (g x) x := by
    have hq : HasDerivAt (fun t : ℝ => t^2/2) x x := by
      simpa using ((hasDerivAt_id x).pow 2).div_const 2
    exact (hd x).hasDerivAt.add hq
  have hsurj : Function.Surjective g := by
    intro y
    let a := min 0 (y-deriv φ 0-1)
    let b := max 0 (y-deriv φ 0+1)
    have ha : a ≤ 0 := min_le_left ..
    have hb : 0 ≤ b := le_max_left ..
    have hda := hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ a) (mem_univ 0) ha
    have hdb := hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ 0) (mem_univ b) hb
    have hay : a ≤ y-deriv φ 0-1 := min_le_right ..
    have hby : y-deriv φ 0+1 ≤ b := le_max_right ..
    have hga : g a < y := by dsimp [g]; linarith
    have hgb : y < g b := by dsimp [g]; linarith
    obtain ⟨x,_hx,hx⟩ := exists_hasDerivWithinAt_eq_of_gt_of_lt (ha.trans hb)
      (fun x _ => (hg x).hasDerivWithinAt) hga hgb
    exact ⟨x,hx⟩
  have hcont := hm.continuous_of_surjective hsurj
  convert hcont.sub continuous_id using 1
  funext x
  dsimp [g]
  ring

lemma convex_contDiff_one (φ : ℝ → ℝ) (hc : ConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) : ContDiff ℝ 1 φ :=
  contDiff_one_iff_deriv.mpr ⟨hd,convex_continuous_deriv φ hc hd⟩

lemma plane_direction_representation (v : Plane) (hx : v 0 ≠ 0) :
    v 0 • direction (v 1/v 0)=v := by
  ext i
  fin_cases i <;> simp [direction,PiLp.smul_apply]
  field_simp

lemma contDiff_direction : ContDiff ℝ 1 direction := by
  have hh : ContDiff ℝ 1 (fun t : ℝ => direction 0+t • transverseUnit) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have he : (fun t : ℝ => direction 0+t • transverseUnit)=direction := by
    funext t; ext i; fin_cases i <;> simp [direction,transverseUnit,PiLp.add_apply,PiLp.smul_apply]
  rwa [he] at hh

lemma sphereChart_coordinates (μ : Plane → ℝ) (c t : ℝ) :
    sphereChart μ c t 0=c/μ (direction t) ∧ sphereChart μ c t 1=(c/μ (direction t))*t := by
  simp [sphereChart,direction,PiLp.smul_apply]

lemma sphereChart_ratio (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    directionRatio (sphereChart μ c t)=t := by
  obtain ⟨h0,h1⟩ := sphereChart_coordinates μ c t
  unfold directionRatio
  rw [h0,h1]
  have hp := norm_direction_pos μ hμ t
  field_simp

lemma sphereChart_mem (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (c : ℝ) (hc : |c|=1) (t : ℝ) :
    μ (sphereChart μ c t)=1 ∧ 0 < c*sphereChart μ c t 0 := by
  have hp := norm_direction_pos μ hμ t
  have hc0 : c ≠ 0 := by intro he; simp [he] at hc
  constructor
  · rw [sphereChart,hμ.homogeneous,abs_div,hc,abs_of_pos hp]
    field_simp
  · rw [(sphereChart_coordinates μ c t).1]
    have hcs : 0 < c*c := mul_self_pos.mpr hc0
    exact (div_pos hcs hp).trans_eq (by ring)

lemma sphereChart_reconstruct (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (c : ℝ) (hc : |c|=1) (v : Plane) (hv : μ v=1) (hsign : 0 < c*v 0) :
    sphereChart μ c (directionRatio v)=v := by
  have hx : v 0 ≠ 0 := by intro he; rw [he,mul_zero] at hsign; exact lt_irrefl _ hsign
  have hrep := plane_direction_representation v hx
  change v 0 • direction (directionRatio v)=v at hrep
  have hnorm : |v 0| *μ (direction (directionRatio v))=1 := by
    rw [← hμ.homogeneous,hrep,hv]
  have hcx : c*|v 0|=v 0 := by
    rcases eq_or_eq_neg_of_abs_eq hc with hc | hc
    · rw [hc] at hsign ⊢
      simp only [one_mul] at hsign ⊢
      exact abs_of_pos hsign
    · rw [hc] at hsign ⊢
      have hvneg : v 0 < 0 := by linarith
      rw [abs_of_neg hvneg]
      ring
  have he : c/μ (direction (directionRatio v))=v 0 := by
    apply (div_eq_iff (ne_of_gt (norm_direction_pos μ hμ _))).mpr
    rw [← hcx,mul_assoc,hnorm,mul_one]
  rw [sphereChart,he]
  exact hrep

lemma sphereChart_contDiff (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) :
    ContDiff ℝ 1 (sphereChart μ c) :=
  (contDiff_const.div hφ (fun t => ne_of_gt (norm_direction_pos μ hμ t))).smul contDiff_direction

lemma sphereChart_regular (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    ∃ d : Plane, HasDerivAt (sphereChart μ c) d t ∧ d ≠ 0 := by
  have hg := ((sphereChart_contDiff μ hμ hφ c).differentiable (by norm_num) t).hasDerivAt
  let y : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have hx : sphereChart μ c t 0 ≠ 0 := by
    rw [(sphereChart_coordinates μ c t).1]
    exact div_ne_zero hc (ne_of_gt (norm_direction_pos μ hμ t))
  have hyc : ContDiffAt ℝ 1 (fun z : Plane => z 1) (sphereChart μ c t) := y.contDiff.contDiffAt
  have hxc : ContDiffAt ℝ 1 (fun z : Plane => z 0) (sphereChart μ c t) := xCoord.contDiff.contDiffAt
  have hr : DifferentiableAt ℝ directionRatio (sphereChart μ c t) :=
    (hyc.div hxc hx).differentiableAt (by norm_num)
  have hchain := hr.hasFDerivAt.comp_hasDerivAt t hg
  have he : (directionRatio ∘ sphereChart μ c)=id := funext (sphereChart_ratio μ hμ c hc)
  rw [he] at hchain
  have hid := hchain.unique (hasDerivAt_id t)
  refine ⟨_,hg,?_⟩
  intro hz
  rw [hz,map_zero] at hid
  norm_num at hid

lemma sphere_horizontal_chart (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) (hc : |c|=1)
    (v : Plane) (hv : μ v=1) (hsign : 0 < c*v 0) : HasC1CurveChart {z | μ z=1} v := by
  let U : Set Plane := {z | 0 < c*z 0}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_const.mul xCoord.continuous)
  have hc0 : c ≠ 0 := by intro he; simp [he] at hc
  let y : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have hθ : ContinuousOn directionRatio U := y.continuous.continuousOn.div xCoord.continuous.continuousOn
    (fun z hz => by intro he; change 0<c*z 0 at hz; rw [he,mul_zero] at hz; exact lt_irrefl _ hz)
  exact ⟨U,hU,hsign,hv,sphereChart μ c,directionRatio,sphereChart_contDiff μ hμ hφ c,hθ,
    sphereChart_mem μ hμ c hc,sphereChart_ratio μ hμ c hc0,
    fun z hz => sphereChart_reconstruct μ hμ c hc z hz.1 hz.2,sphereChart_regular μ hμ hφ c hc0⟩

theorem norm_ball_frontier (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    frontier {v | μ v ≤ 1}={v | μ v=1} := by
  apply Subset.antisymm (frontier_le_subset_eq (timeConstantNorm_continuous μ hμ) continuous_const)
  intro v hv
  change μ v=1 at hv
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure (show μ v ≤ 1 by exact hv.le),?_⟩
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝[>] (1 : ℝ)) (𝓝 v) := by
    have hh : ContinuousAt (fun t : ℝ => t • v) 1 := continuous_id.smul continuous_const |>.continuousAt
    simpa only [one_smul] using hh.mono_left (show 𝓝[>] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 1<t at ht
  change ¬μ (t • v) ≤ 1
  rw [hμ.homogeneous,hv,abs_of_pos (show 0<t by linarith)]
  linarith

lemma chart_preimage_isometry (S : Set Plane) (v : Plane)
    (e : Plane ≃ₗᵢ[ℝ] Plane) (h : HasC1CurveChart S (e v)) :
    HasC1CurveChart (e ⁻¹' S) v := by
  obtain ⟨U,hU,hv,hvS,γ,θ,hγ,hθ,hmem,hleft,hright,hreg⟩ := h
  refine ⟨e ⁻¹' U,hU.preimage e.continuous,hv,hvS,e.symm ∘ γ,θ ∘ e,?_,?_,?_,?_,?_,?_⟩
  · exact e.symm.toContinuousLinearEquiv.contDiff.comp hγ
  · exact hθ.comp e.continuous.continuousOn (fun _ hz => hz)
  · intro t
    simpa only [Function.comp_apply,mem_inter_iff,mem_preimage,e.apply_symm_apply] using hmem t
  · intro t
    simpa only [Function.comp_apply,e.apply_symm_apply] using hleft t
  · intro z hz
    change e.symm (γ (θ (e z)))=z
    rw [hright (e z) hz,e.symm_apply_apply]
  · intro t
    obtain ⟨d,hd,hne⟩ := hreg t
    refine ⟨e.symm d,e.symm.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t hd,?_⟩
    intro hz
    exact hne (e.symm.injective (by simpa using hz))

end GammaFPP.Analytic

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_AnalyticEndgame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Analytic
open PlanarFPP Set Filter
open scoped Topology

lemma norm_comp_swap (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    TimeConstantNorm (fun v => μ (swapPlane v)) := by
  refine ⟨fun v => hμ.nonneg _, ?_, ?_, ?_⟩
  · intro v
    rw [hμ.zero_iff]
    exact ⟨fun hv => swapPlane.injective (by simpa using hv), fun hv => by simp [hv]⟩
  · intro v w
    simpa only [map_add] using hμ.triangle (swapPlane v) (swapPlane w)
  · intro a v
    simpa only [map_smul] using hμ.homogeneous a (swapPlane v)

lemma norm_profile_contDiff (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hd : DifferentiableAwayFromOrigin μ) :
    ContDiff ℝ 1 (fun t => μ (direction t)) := by
  have he (t : ℝ) : direction 0+t • transverseUnit=direction t := by
    ext i; fin_cases i <;> simp [direction,transverseUnit,PiLp.add_apply,PiLp.smul_apply]
  have hc := convex_transverse_profile μ (direction 0) transverseUnit
    hμ.triangle (norm_positive_homogeneous μ hμ)
  have hder : Differentiable ℝ (fun t : ℝ => μ (direction 0+t • transverseUnit)) := by
    intro t
    have hne : direction t ≠ 0 := by
      intro hz
      have hh := congrArg xCoord hz
      change (1 : ℝ)=0 at hh
      norm_num at hh
    obtain ⟨ℓ,hℓ⟩ := hd (direction t) hne
    have hh : DifferentiableAt ℝ μ (direction 0+t • transverseUnit) := by
      rw [he]
      exact hℓ.differentiableAt
    have hm : DifferentiableAt ℝ (fun s : ℝ => direction 0+s • transverseUnit) t :=
      (((hasDerivAt_id t).smul_const transverseUnit).const_add (direction 0)).differentiableAt
    exact DifferentiableAt.comp (g := μ) (f := fun s : ℝ => direction 0+s • transverseUnit) t hh hm
  simpa only [he] using convex_contDiff_one _ hc hder

lemma differentiable_away_comp_swap (μ : Plane → ℝ)
    (hd : DifferentiableAwayFromOrigin μ) :
    DifferentiableAwayFromOrigin (fun v => μ (swapPlane v)) := by
  intro v hv
  have hne : swapPlane v ≠ 0 := by
    intro hz
    exact hv (swapPlane.injective (by simpa using hz))
  obtain ⟨ℓ,hℓ⟩ := hd (swapPlane v) hne
  exact ⟨ℓ.comp swapPlane.toContinuousLinearEquiv.toContinuousLinearMap,
    hℓ.comp v swapPlane.toContinuousLinearEquiv.hasFDerivAt⟩

/-- The unit sphere of a differentiable planar norm has regular `C¹` curve
charts with continuous local inverses. -/
theorem norm_sphere_curve_chart (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hd : DifferentiableAwayFromOrigin μ) (v : Plane) (hv : μ v=1) :
    GammaFPP.HasC1CurveChart {z | μ z=1} v := by
  have horizontal (ν : Plane → ℝ) (hν : TimeConstantNorm ν)
      (hder : DifferentiableAwayFromOrigin ν) (z : Plane) (hz : ν z=1)
      (hx : z 0 ≠ 0) : GammaFPP.HasC1CurveChart {w | ν w=1} z := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · exact sphere_horizontal_chart ν hν (norm_profile_contDiff ν hν hder) (-1)
        (by norm_num) z hz (by linarith)
    · exact sphere_horizontal_chart ν hν (norm_profile_contDiff ν hν hder) 1
        (by norm_num) z hz (by simpa using hpos)
  by_cases hx : v 0 ≠ 0
  · exact horizontal μ hμ hd v hv hx
  · have hvne : v ≠ 0 := by
      intro he
      have hz := (hμ.zero_iff v).mpr he
      linarith
    have hy : v 1 ≠ 0 := by
      intro hy
      apply hvne
      ext i
      fin_cases i <;> simp_all
    have hs := horizontal (fun z => μ (swapPlane z)) (norm_comp_swap μ hμ)
      (differentiable_away_comp_swap μ hd) (swapPlane v) (by simpa using hv)
      (by simpa using hy)
    have hh := chart_preimage_isometry {z | μ (swapPlane z)=1} v swapPlane hs
    have he : swapPlane ⁻¹' {z | μ (swapPlane z)=1} = {z | μ z=1} := by
      ext z
      simp only [mem_preimage, mem_ofPred_eq, swapPlane_swap]
    rwa [he] at hh

/-- The topological frontier of the norm unit ball has regular `C¹` curve charts. -/
theorem norm_boundary_curve_chart (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hd : DifferentiableAwayFromOrigin μ) (v : Plane)
    (hv : v ∈ frontier {z | μ z ≤ 1}) :
    GammaFPP.HasC1CurveChart (frontier {z | μ z ≤ 1}) v := by
  rw [norm_ball_frontier μ hμ] at hv ⊢
  exact norm_sphere_curve_chart μ hμ hd v hv

end GammaFPP.Analytic

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanSwap
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Filter Topology PlanarFPP

namespace SwapGeometry

lemma swapEdge_injective : Function.Injective swapEdge := Function.LeftInverse.injective swapEdge_swap

lemma swapStep_edge (p : Vertex) (d : Step) : (swapStep d).edge p.swap=swapEdge (d.edge p) := by
  cases d <;> rfl

lemma displacement_swap (ds : List Step) : displacement (ds.map swapStep)=(displacement ds).swap := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [ih,Prod.swap_add]

lemma pathCost_swap (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost w p.swap (ds.map swapStep)=pathCost (fun e => w (swapEdge e)) p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [pathCost,swapStep_edge,← Prod.swap_add,ih]

lemma passageTime_swap (w : Edge → ℝ) (p q : Vertex) :
    passageTime w p.swap q.swap=passageTime (fun e => w (swapEdge e)) p q := by
  unfold passageTime
  congr 1
  ext t
  constructor
  · rintro ⟨ds,hend,hc⟩
    refine ⟨ds.map swapStep,?_,?_⟩
    · rw [displacement_swap]
      have hh := congrArg Prod.swap hend
      simpa only [Prod.swap_add,Prod.swap_swap] using hh
    · have hh := pathCost_swap (fun e => w (swapEdge e)) p.swap ds
      simpa only [Prod.swap_swap,swapEdge_swap,hc] using hh
  · rintro ⟨ds,hend,hc⟩
    exact ⟨ds.map swapStep,by rw [displacement_swap,← Prod.swap_add,hend],by rw [pathCost_swap,hc]⟩

end SwapGeometry

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {ν : Measure ℝ}

theorem IidEnvironment.coordinateSwap (h : IidEnvironment ν P τ) :
    IidEnvironment ν P (fun e => τ (SwapGeometry.swapEdge e)) where
  probability := h.probability
  measurable := fun e => h.measurable (SwapGeometry.swapEdge e)
  independent := h.independent.precomp SwapGeometry.swapEdge_injective
  marginal := fun e => h.marginal (SwapGeometry.swapEdge e)

/-- Coordinate swap preserves the integral of each passage time; the integral
identity also holds for the totalized integral without an integrability assumption. -/
theorem IidEnvironment.integral_passageTime_coordinateSwap
    (h : IidEnvironment ν P τ) (p q : Vertex) :
    (∫ ω, passageTime (fun e => τ e ω) p.swap q.swap ∂P) =
      ∫ ω, passageTime (fun e => τ e ω) p q ∂P := by
  have hm : Measurable (fun w : Edge → ℝ => passageTime w p q) :=
    PlanarFPP.measurable_passageTime (fun e => measurable_pi_apply e) p q
  have hs := h.coordinateSwap.integral_configuration
    (fun w : Edge → ℝ => passageTime w p q) hm
  have ho := h.integral_configuration
    (fun w : Edge → ℝ => passageTime w p q) hm
  have he : (∫ ω, passageTime (fun e => τ e ω) p.swap q.swap ∂P) =
      ∫ ω, passageTime (fun e => τ (SwapGeometry.swapEdge e) ω) p q ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      SwapGeometry.passageTime_swap (fun e => τ e ω) p q)
  exact he.trans (hs.trans ho.symm)

variable {shape rate : ℝ}

/-- The equality holds for every index including zero, and swaps the two
coordinates rather than applying central symmetry. -/
theorem GammaEnvironment.meanPassageSequence_coordinateSwap
    (h : GammaEnvironment shape rate P τ) (z : Vertex) (n : ℕ) :
    meanPassageSequence P τ z.swap n = meanPassageSequence P τ z n := by
  have he : (n • z).swap = n • z.swap := rfl
  have hz : (0 : Vertex).swap = 0 := rfl
  simpa only [meanPassageSequence, he, hz] using
    h.integral_passageTime_coordinateSwap 0 (n • z)

/-- Actual deterministic mean-limit invariance, with no norm or time-constant
existence premise. It also includes the zero direction. -/
theorem GammaEnvironment.directionalMeanConstant_coordinateSwap
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    directionalMeanConstant h hs hr z.swap = directionalMeanConstant h hs hr z := by
  have ht := h.meanPassageSequence_tendsto hs hr z.swap
  simp only [h.meanPassageSequence_coordinateSwap] at ht
  exact tendsto_nhds_unique ht (h.meanPassageSequence_tendsto hs hr z)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanNormSwap
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP

lemma rationalMean_swap (m : Vertex → ℝ) (hm : ∀ z, m z.swap=m z)
    (q : ℚ × ℚ) : rationalMean m q.swap = rationalMean m q := by
  have hn : rationalNumerator q.swap = (rationalNumerator q).swap := rfl
  have hd : rationalDenominator q.swap = rationalDenominator q := by
    simp only [rationalDenominator, Prod.fst_swap, Prod.snd_swap, Nat.mul_comm]
  simp only [rationalMean, hn, hd, hm]

lemma realMeanExtension_swap {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (hs : ∀ q, f q.swap=f q) (v : ℝ × ℝ) :
    realMeanExtension f v.swap = realMeanExtension f v := by
  have hc := (realMeanExtension_uniformContinuous hf).continuous
  apply isClosed_property rationalPairCast_dense
    (p := fun v : ℝ × ℝ => realMeanExtension f v.swap=realMeanExtension f v) ?_ ?_ v
  · exact isClosed_eq (hc.comp (continuous_snd.prodMk continuous_fst)) hc
  · intro q
    have he : (rationalPairCast q).swap = rationalPairCast q.swap := rfl
    rw [he, realMeanExtension_on_rat hf, realMeanExtension_on_rat hf]
    exact hs q

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma gammaMeanPairSeminorm_swap (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (v : ℝ × ℝ) :
    gammaMeanPairSeminorm h hs hr v.swap = gammaMeanPairSeminorm h hs hr v := by
  change realMeanExtension (rationalMean (directionalMeanConstant h hs hr)) v.swap =
    realMeanExtension (rationalMean (directionalMeanConstant h hs hr)) v
  have hlip := rationalMean_l1 (directionalMeanConstant h hs hr)
    (fun k z => h.directionalMeanConstant_nsmul hs hr z k)
    (shape/rate) (h.directionalMeanConstant_l1_lipschitz hs hr)
  apply realMeanExtension_swap
    (rational_l1_lipschitz _ ⟨shape/rate, (div_pos hs hr).le⟩ hlip).uniformContinuous
  intro q
  exact rationalMean_swap _ (h.directionalMeanConstant_coordinateSwap hs hr) q

/-- Derived from actual expectation-limit symmetry through rational density. -/
theorem gammaMeanNorm_swap (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (v : Plane) :
    gammaMeanNorm h hs hr (Analytic.swapPlane v) = gammaMeanNorm h hs hr v := by
  change gammaMeanPairSeminorm h hs hr
    ((Analytic.swapPlane v) 0, (Analytic.swapPlane v) 1) =
      gammaMeanPairSeminorm h hs hr (v 0,v 1)
  rw [Analytic.swapPlane_zero, Analytic.swapPlane_one]
  exact gammaMeanPairSeminorm_swap h hs hr (v 0,v 1)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_AnalyticSpecialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Analytic
open PlanarFPP Set MeasureTheory

/-- Coordinate-swap symmetry and norm homogeneity extend absence of corners
on the slope wedge to differentiability at every nonzero vector. -/
theorem differentiable_away_of_noCornerWedge (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (hswap : ∀ v, μ (swapPlane v)=μ v)
    (hnc : NoCornerWedge μ) : DifferentiableAwayFromOrigin μ := by
  have horizontal (v : Plane) (hv : v ≠ 0) (hdom : |v 1| ≤ |v 0|) :
      DifferentiableAt ℝ μ v := by
    have hx : v 0 ≠ 0 := by
      intro hx
      have hy : v 1=0 := by simpa [hx] using hdom
      apply hv
      ext i
      fin_cases i <;> simp [hx,hy]
    have hb : |v 1/v 0| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr hx)).mpr hdom
    obtain ⟨ℓ,hℓ⟩ := planar_differentiability_of_no_corner μ hμ (v 1/v 0) (hnc _ hb)
    have hh := norm_differentiable_smul μ hμ (direction (v 1/v 0)) (v 0) hx hℓ.differentiableAt
    rwa [plane_direction_representation v hx] at hh
  intro v hv
  have hd : DifferentiableAt ℝ μ v := by
    by_cases hh : |v 1| ≤ |v 0|
    · exact horizontal v hv hh
    · have hsv : swapPlane v ≠ 0 := by
        intro hz
        exact hv (swapPlane.injective (by simpa using hz))
      have hdom : |swapPlane v 1| ≤ |swapPlane v 0| := by
        simpa using (le_of_not_ge hh)
      have hs := horizontal (swapPlane v) hsv hdom
      have hc := hs.comp v swapPlane.toContinuousLinearEquiv.differentiableAt
      have he : (fun z => μ (swapPlane z))=μ := funext hswap
      simpa only [Function.comp_def,he] using hc
  exact ⟨fderiv ℝ μ v,hd.hasFDerivAt⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Absence of corners on the slope wedge gives differentiability and regular
boundary charts for the Gamma mean norm. -/
theorem gammaMeanNorm_analytic_of_noCorner
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (hnc : NoCornerWedge (gammaMeanNorm h hs hr)) :
    DifferentiableAwayFromOrigin (gammaMeanNorm h hs hr) ∧
      ∀ v ∈ frontier {z | gammaMeanNorm h hs hr z ≤ 1},
        GammaFPP.HasC1CurveChart (frontier {z | gammaMeanNorm h hs hr z ≤ 1}) v := by
  have hn := gammaMeanNorm_laws h hs hr
  have hd := differentiable_away_of_noCornerWedge _ hn (gammaMeanNorm_swap h hs hr) hnc
  exact ⟨hd, norm_boundary_curve_chart _ hn hd⟩

/-- A time-constant property and absence of corners on the slope wedge identify
the Gamma mean norm as a differentiable limit norm with regular boundary charts. -/
theorem gammaMeanNorm_target_conjunction_of_inputs
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (ht : IsTimeConstant P τ (gammaMeanNorm h hs hr))
    (hnc : NoCornerWedge (gammaMeanNorm h hs hr)) :
    ∃ μ : Plane → ℝ, TimeConstantNorm μ ∧ IsTimeConstant P τ μ ∧
      DifferentiableAwayFromOrigin μ ∧
      ∀ v ∈ frontier {z | μ z ≤ 1},
        GammaFPP.HasC1CurveChart (frontier {z | μ z ≤ 1}) v := by
  obtain ⟨hd,hcharts⟩ := gammaMeanNorm_analytic_of_noCorner h hs hr hnc
  exact ⟨gammaMeanNorm h hs hr,gammaMeanNorm_laws h hs hr,ht,hd,hcharts⟩

end GammaFPP.Analytic

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CrossingLocalized
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

theorem mem_internalEdges (e : Edge) (V : Finset Vertex) :
    e ∈ internalEdges V ↔ e.1 ∈ V ∧ edgeEnd e ∈ V := by
  simp [internalEdges]

theorem step_mem_internalEdges (V : Finset Vertex) (p : Vertex) (d : Step)
    (hp : p ∈ V) (hq : p+d.delta ∈ V) : d.edge p ∈ internalEdges V := by
  rw [mem_internalEdges]
  cases d <;> simp_all [Step.edge,Step.delta,edgeEnd,add_assoc]
  all_goals change p+0 ∈ V; simpa using hp

theorem pathIn_cons_iff (p : Vertex) (d : Step) (ds : List Step) (S : Set Vertex) :
    PathIn p (d::ds) S ↔ p ∈ S ∧ PathIn (p+d.delta) ds S := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp),?_⟩
    intro i hi
    have hh := h (i+1) (by simpa using hi)
    simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh
  · rintro ⟨hp,ht⟩ i hi
    cases i with
    | zero => simpa using hp
    | succ i =>
      have hh := ht i (by simpa using hi)
      simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh

theorem pathIn_endpoint (p : Vertex) (ds : List Step) (S : Set Vertex)
    (h : PathIn p ds S) : p+displacement ds ∈ S := by
  simpa using h ds.length le_rfl

theorem pathEdges_subset_internalEdges (V : Finset Vertex) (p : Vertex) (ds : List Step)
    (h : PathIn p ds (V : Set Vertex)) : pathEdges p ds ⊆ internalEdges V := by
  induction ds generalizing p with
  | nil => simp [pathEdges]
  | cons d ds ih =>
    obtain ⟨hp,ht⟩ := (pathIn_cons_iff p d ds _).mp h
    have hq : p+d.delta ∈ V := by simpa using ht 0 (by omega)
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · rw [he]
      exact step_mem_internalEdges V p d hp hq
    · exact ih (p+d.delta) ht he

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SourceTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem norm_direction_pos (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    0 < μ (direction b) := by
  have hn : direction b ≠ 0 := by
    intro hh
    have := congrArg xCoord hh
    norm_num [direction] at this
  exact lt_of_le_of_ne (hμ.nonneg _) (Ne.symm ((hμ.zero_iff _).not.mpr hn))

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer endpoint subdivision for Lemma `gr:variable-endpoints`.
Floors use Euclidean division by a positive mesh, including at negative columns. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge

lemma meshFloor_bounds (x d : ℤ) (hd : 0 < d) :
    meshFloor x d ≤ x ∧ x < meshFloor x d+d := by
  have h0 := Int.emod_nonneg x (ne_of_gt hd)
  have h1 := Int.emod_lt_of_pos x hd
  have he := Int.emod_add_ediv_mul x d
  dsimp [meshFloor]
  omega

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridVerticalPaths
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Grid Set Finset MeasureTheory ProbabilityTheory

theorem pathIn_append (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (hd : PathIn p ds S) (he : PathIn (p+displacement ds) es S) :
    PathIn p (ds++es) S := by
  intro i hi
  by_cases hid : i ≤ ds.length
  · simpa only [List.take_append, Nat.sub_eq_zero_of_le hid, List.take_zero,
      List.append_nil] using hd i hid
  · have hle : ds.length ≤ i := by omega
    have hie : i-ds.length ≤ es.length := by simp only [List.length_append] at hi; omega
    have hh := he (i-ds.length) hie
    simpa only [List.take_append, List.take_of_length_le hle, displacement_append,
      add_assoc] using hh

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

lemma spatialWitness_edges (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ)
    (p : GammaFPP.BK.StrictPathWitness) (hp : p ∈ spatialWitnessFamily b m₀ am ap K η k m ih) :
    p.edges ⊆ spatialWitnessSupport b k m ih := by
  apply pathEdges_subset_internalEdges
  rcases hp with ⟨hin,_⟩ | ⟨_,_,hin,_⟩
  · intro i hi
    apply Finset.mem_union.mpr
    exact Or.inl ((translatedEndpointBox_finite ..).mem_toFinset.mpr (hin i hi))
  · intro i hi
    exact Finset.mem_union.mpr (Or.inr ((mem_rareFastVertices ..).mpr (hin i hi)))

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PathSubpaths
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

lemma pathIn_append_left (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (h : PathIn p (ds++es) S) : PathIn p ds S := by
  intro i hi
  have hh := h i (by simp only [List.length_append]; omega)
  simpa only [List.take_append,Nat.sub_eq_zero_of_le hi,List.take_zero,List.append_nil] using hh

lemma pathIn_append_right (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (h : PathIn p (ds++es) S) : PathIn (p+displacement ds) es S := by
  intro i hi
  have hh := h (ds.length+i) (by simp only [List.length_append]; omega)
  simpa only [List.take_append,List.take_of_length_le (show ds.length ≤ ds.length+i by omega),
    Nat.add_sub_cancel_left,displacement_append,add_assoc] using hh

lemma pathIn_reverseSteps (p : Vertex) (ds : List Step) (S : Set Vertex)
    (h : PathIn p ds S) : PathIn (p+displacement ds) (reverseSteps ds) S := by
  induction ds generalizing p with
  | nil => simpa [reverseSteps] using h
  | cons d ds ih =>
    obtain ⟨hp,ht⟩ := (pathIn_cons_iff p d ds S).mp h
    have hi := ih (p+d.delta) ht
    have hend : p+displacement (d::ds)+displacement (reverseSteps ds)=p+d.delta := by
      rw [displacement_cons,displacement_reverseSteps]
      abel
    have hs : PathIn (p+d.delta) [d.reverse] S := by
      apply (pathIn_cons_iff _ _ _ _).mpr
      refine ⟨?_,?_⟩
      · simpa using ht 0 (by omega)
      · intro i _
        simpa using hp
    have he : reverseSteps (d::ds)=reverseSteps ds++[d.reverse] := by simp [reverseSteps]
    rw [he]
    apply pathIn_append _ _ _ _ (by simpa [displacement_cons,add_assoc] using hi)
    simpa only [hend] using hs

/-- First visit to a column from its left, with the prefix staying to the left. -/
lemma path_first_column_up (p : Vertex) (ds : List Step) (X : ℤ)
    (hp : p.1 ≤ X) (hend : X ≤ (p+displacement ds).1) :
    ∃ pre rest : List Step, ds=pre++rest ∧ (p+displacement pre).1=X ∧
      PathIn p pre {z | z.1 ≤ X} := by
  induction ds generalizing p with
  | nil =>
    refine ⟨[],[],rfl,by simpa using le_antisymm hp (by simpa using hend),?_⟩
    intro i _
    simpa using hp
  | cons d ds ih =>
    by_cases he : p.1=X
    · refine ⟨[],d::ds,rfl,by simpa using he,?_⟩
      intro i _
      simpa using hp
    · have hp' : (p+d.delta).1 ≤ X := by
        cases d <;> simp only [Step.delta,Prod.fst_add] <;> omega
      have hend' : X ≤ (p+d.delta+displacement ds).1 := by
        simpa only [displacement_cons,add_assoc] using hend
      obtain ⟨pre,rest,heq,hcol,hin⟩ := ih (p+d.delta) hp' hend'
      refine ⟨d::pre,rest,by simp [heq],by simpa [displacement_cons,add_assoc] using hcol,?_⟩
      exact (pathIn_cons_iff ..).mpr ⟨hp,hin⟩

/-- First visit to a column from its right, with the prefix staying to the right. -/
lemma path_first_column_down (p : Vertex) (ds : List Step) (X : ℤ)
    (hp : X ≤ p.1) (hend : (p+displacement ds).1 ≤ X) :
    ∃ pre rest : List Step, ds=pre++rest ∧ (p+displacement pre).1=X ∧
      PathIn p pre {z | X ≤ z.1} := by
  induction ds generalizing p with
  | nil =>
    refine ⟨[],[],rfl,by simpa using le_antisymm (by simpa using hend) hp,?_⟩
    intro i _
    simpa using hp
  | cons d ds ih =>
    by_cases he : p.1=X
    · refine ⟨[],d::ds,rfl,by simpa using he,?_⟩
      intro i _
      simpa using hp
    · have hp' : X ≤ (p+d.delta).1 := by
        cases d <;> simp only [Step.delta,Prod.fst_add] <;> omega
      have hend' : (p+d.delta+displacement ds).1 ≤ X := by
        simpa only [displacement_cons,add_assoc] using hend
      obtain ⟨pre,rest,heq,hcol,hin⟩ := ih (p+d.delta) hp' hend'
      refine ⟨d::pre,rest,by simp [heq],by simpa [displacement_cons,add_assoc] using hcol,?_⟩
      exact (pathIn_cons_iff ..).mpr ⟨hp,hin⟩

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PathColumnCrossing
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

/-- Last-left/first-right subcrossing from an actual finite path. The middle
path stays between the two columns; both outside pieces are retained. -/
theorem path_column_subcrossing (p : Vertex) (ds : List Step) (A B : ℤ)
    (hp : p.1 ≤ A) (hAB : A ≤ B) (hend : B ≤ (p+displacement ds).1) :
    ∃ pre mid post : List Step, ds=pre++mid++post ∧
      (p+displacement pre).1=A ∧
      (p+displacement pre+displacement mid).1=B ∧
      PathIn (p+displacement pre) mid {z | A ≤ z.1 ∧ z.1 ≤ B} := by
  obtain ⟨front,post,he,hB,hinB⟩ := path_first_column_up p ds B (hp.trans hAB) hend
  let zB := p+displacement front
  have hrev : zB+displacement (reverseSteps front)=p := by simp [zB]
  obtain ⟨revMid,revPre,heR,hA,hinA⟩ := path_first_column_down zB (reverseSteps front) A
    (by change A ≤ (p+displacement front).1; omega) (by rw [hrev]; exact hp)
  have hfront : front=reverseSteps revPre++reverseSteps revMid := by
    have hh := congrArg reverseSteps heR
    simpa only [reverseSteps_reverse,reverseSteps_append] using hh
  have hfull : zB+displacement revMid+displacement revPre=p := by
    rw [heR,displacement_append,← add_assoc] at hrev
    exact hrev
  have hstart : p+displacement (reverseSteps revPre)=zB+displacement revMid := by
    rw [displacement_reverseSteps,← hfull]
    abel
  have hmid : p+displacement (reverseSteps revPre)+displacement (reverseSteps revMid)=zB := by
    rw [hstart,displacement_reverseSteps]
    abel
  refine ⟨reverseSteps revPre,reverseSteps revMid,post,by rw [he,hfront],?_,?_,?_⟩
  · rw [hstart]
    exact hA
  · rw [hmid]
    exact hB
  · have hl := pathIn_reverseSteps zB revMid {z | A ≤ z.1} hinA
    have hu := pathIn_append_right p (reverseSteps revPre) (reverseSteps revMid) {z | z.1 ≤ B}
      (by rw [← hfront]; exact hinB)
    rw [← hstart] at hl
    intro i hi
    exact ⟨hl i hi,hu i hi⟩

/-- Any middle part of a path inherits the original vertex localization. -/
lemma pathIn_middle (p : Vertex) (pre mid post : List Step) (S : Set Vertex)
    (h : PathIn p (pre++mid++post) S) : PathIn (p+displacement pre) mid S :=
  pathIn_append_right p pre mid S (pathIn_append_left p (pre++mid) post S h)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialChunkGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

lemma spatialTranslate_center (b : ℝ) (k m : ℕ) (ih : ℤ×ℤ) :
    transverse b (spatialTranslate b k m ih) =
      (⌊b*(ih.1*(2 : ℤ)^m)⌋ : ℝ)-b*(ih.1*(2 : ℤ)^m)+(ih.2 : ℝ)*(2 : ℝ)^k := by
  simp [spatialTranslate,transverse]
  ring

lemma spatialChunkIndex_horizontal (b : ℝ) (k m : ℕ) (p : Vertex) :
    0 ≤ p.1-(spatialTranslate b k m (spatialChunkIndex b k m p)).1 ∧
      p.1-(spatialTranslate b k m (spatialChunkIndex b k m p)).1 < (2 : ℤ)^m := by
  have h := meshFloor_bounds p.1 ((2 : ℤ)^m) (by positivity)
  dsimp [spatialChunkIndex,spatialTranslate,meshFloor] at *
  omega

lemma spatialChunkIndex_transverse (b : ℝ) (k m : ℕ) (p : Vertex) :
    0 ≤ transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p)) ∧
      transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p)) < (2 : ℝ)^k+1 := by
  have hs : (0 : ℝ) < 2^k := by positivity
  have hl := (le_div_iff₀ hs).mp (Int.floor_le (transverse b p/(2 : ℝ)^k))
  have hu := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (transverse b p/(2 : ℝ)^k))
  have hf := Int.floor_le (b*((spatialChunkIndex b k m p).1*(2 : ℤ)^m))
  have hf' := Int.lt_floor_add_one (b*((spatialChunkIndex b k m p).1*(2 : ℤ)^m))
  rw [spatialTranslate_center]
  simp only [spatialChunkIndex,Int.cast_ofNat] at hf hf' ⊢
  constructor <;> nlinarith [hf,hf']

/-- Source chunk localization, including the possible one-unit transverse
overshoot at the first exit. -/
lemma spatial_chunk_vertex_in_box (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p z : Vertex)
    (hx : |z.1-p.1| ≤ 2*(2 : ℤ)^m)
    (hr : |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1) :
    z-spatialTranslate b k m (spatialChunkIndex b k m p) ∈ endpointBox b 4 4 k m := by
  have hpx := spatialChunkIndex_horizontal b k m p
  have hpr := spatialChunkIndex_transverse b k m p
  have hpxR : 0 ≤ (p.1 : ℝ)-((spatialTranslate b k m (spatialChunkIndex b k m p)).1 : ℝ) ∧
      (p.1 : ℝ)-((spatialTranslate b k m (spatialChunkIndex b k m p)).1 : ℝ) < (2 : ℝ)^m := by
    exact_mod_cast hpx
  have hxR : |(z.1 : ℝ)-(p.1 : ℝ)| ≤ 2*(2 : ℝ)^m := by exact_mod_cast hx
  have hzx := abs_le.mp hxR
  have hzr := abs_le.mp hr
  have htrans : transverse b (z-spatialTranslate b k m (spatialChunkIndex b k m p)) =
      transverse b z-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p)) := by
    simp [transverse]; ring
  constructor
  · simp only [Prod.fst_sub,Int.cast_sub]
    apply abs_le.mpr
    constructor <;> linarith [hpxR.1,hpxR.2,pow_pos (by norm_num : (0 : ℝ) < 2) m]
  · rw [htrans]
    apply abs_le.mpr
    constructor <;> linarith [hpr.1,hpr.2]

lemma spatial_chunk_in_box (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p : Vertex) (ds : List Step)
    (hchunk : ∀ i ≤ ds.length, |(displacement (ds.take i)).1| ≤ 2*(2 : ℤ)^m ∧
      |transverse b (displacement (ds.take i))| ≤ (2 : ℝ)^k+1) :
    PathIn p ds {z | z-spatialTranslate b k m (spatialChunkIndex b k m p) ∈ endpointBox b 4 4 k m} := by
  intro i hi
  apply spatial_chunk_vertex_in_box b k m hs p
  · simpa only [Prod.fst_add,add_sub_cancel_left] using (hchunk i hi).1
  · simpa only [transverse_add,add_sub_cancel_left] using (hchunk i hi).2

lemma spatialChunkIndex_origin (b : ℝ) (k m : ℕ) : spatialChunkIndex b k m 0=0 := by
  simp [spatialChunkIndex,transverse]

/-- Consecutive source chunk indices have coordinate increments at most 3,
so a length-N itinerary has at most 49 choices at each step. -/
lemma spatialChunkIndex_increment (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p z : Vertex)
    (hx : |z.1-p.1| ≤ 2*(2 : ℤ)^m)
    (hr : |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1) :
    |(spatialChunkIndex b k m z).1-(spatialChunkIndex b k m p).1| ≤ 3 ∧
      |(spatialChunkIndex b k m z).2-(spatialChunkIndex b k m p).2| ≤ 3 := by
  have hL : (0 : ℤ) < 2^m := by positivity
  have hp := meshFloor_bounds p.1 ((2 : ℤ)^m) hL
  have hz := meshFloor_bounds z.1 ((2 : ℤ)^m) hL
  have hx' := abs_le.mp hx
  constructor
  · change |z.1/(2 : ℤ)^m-p.1/(2 : ℤ)^m| ≤ 3
    dsimp [meshFloor] at hp hz
    apply abs_le.mpr
    constructor <;> nlinarith [hp.1,hp.2,hz.1,hz.2]
  · have hs0 : (0 : ℝ) < 2^k := by positivity
    have hp0 := (le_div_iff₀ hs0).mp (Int.floor_le (transverse b p/(2 : ℝ)^k))
    have hp1 := (div_lt_iff₀ hs0).mp (Int.lt_floor_add_one (transverse b p/(2 : ℝ)^k))
    have hz0 := (le_div_iff₀ hs0).mp (Int.floor_le (transverse b z/(2 : ℝ)^k))
    have hz1 := (div_lt_iff₀ hs0).mp (Int.lt_floor_add_one (transverse b z/(2 : ℝ)^k))
    have hr' := abs_le.mp hr
    have hh : |(⌊transverse b z/(2 : ℝ)^k⌋ : ℝ)-(⌊transverse b p/(2 : ℝ)^k⌋ : ℝ)| ≤ 3 := by
      apply abs_le.mpr
      constructor <;> nlinarith [hr'.1,hr'.2]
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [spatialChunkIndex,Int.cast_abs,Int.cast_sub,Int.cast_ofNat] using hh

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialFirstExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

lemma chunkInterior_zero (b : ℝ) (k m : ℕ) : chunkInterior b k m 0 := by
  constructor
  · change (0 : ℤ) < 2*(2 : ℤ)^m
    positivity
  · simp [transverse]

/-- The first exit is selected from the actual finite path. No chunk or
subpath existence is assumed. -/
theorem first_full_spatial_chunk (b : ℝ) (k m : ℕ) (ds : List Step) :
    (∀ i ≤ ds.length, chunkInterior b k m (displacement (ds.take i))) ∨
    ∃ pre rest : List Step, ds=pre++rest ∧ pre ≠ [] ∧ FullSpatialChunk b k m pre := by
  classical
  by_cases h : ∃ i : ℕ, i ≤ ds.length ∧ ¬chunkInterior b k m (displacement (ds.take i))
  · let n := Nat.find h
    have hn := Nat.find_spec h
    have hn0 : 0 < n := by
      by_contra hh
      have he : n=0 := by omega
      have hn' : ¬chunkInterior b k m (displacement (ds.take n)) := hn.2
      simp only [he,List.take_zero,displacement_nil] at hn'
      exact hn' (chunkInterior_zero b k m)
    have hlen : (ds.take n).length=n := List.length_take_of_le hn.1
    refine Or.inr ⟨ds.take n,ds.drop n,(List.take_append_drop n ds).symm,?_,?_,?_⟩
    · intro he
      rw [he] at hlen
      simp only [List.length_nil] at hlen
      omega
    · intro i hi
      rw [hlen] at hi
      have hnot := Nat.find_min h hi
      have hip : i ≤ ds.length := by omega
      have hv : chunkInterior b k m (displacement (ds.take i)) := by tauto
      simpa only [List.take_take,Nat.min_eq_left hi.le] using hv
    · exact hn.2
  · exact Or.inl (fun i hi => by by_contra hn; exact h ⟨i,hi,hn⟩)

lemma step_transverse_abs_le (b : ℝ) (hb : |b| ≤ 1) (d : Step) : |transverse b d.delta| ≤ 1 := by
  cases d with
  | east => simpa [Step.delta,transverse] using hb
  | west => simpa [Step.delta,transverse] using hb
  | north => norm_num [Step.delta,transverse]
  | south => norm_num [Step.delta,transverse]

/-- A step out of the open chunk rectangle overshoots transversely by at
most one and cannot overshoot the integer longitudinal boundary. -/
lemma chunk_step_localization (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (v : Vertex)
    (hv : chunkInterior b k m v) (d : Step) :
    |(v+d.delta).1| ≤ 2*(2 : ℤ)^m ∧ |transverse b (v+d.delta)| ≤ (2 : ℝ)^k+1 := by
  have hx := abs_lt.mp hv.1
  constructor
  · cases d <;> simp only [Step.delta,Prod.fst_add] <;> apply abs_le.mpr <;> omega
  · rw [transverse_add]
    exact (abs_add_le _ _).trans (by linarith [hv.2,step_transverse_abs_le b hb d])

lemma proper_chunk_endpoint_localization (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (ds : List Step)
    (hproper : ∀ i < ds.length, chunkInterior b k m (displacement (ds.take i))) :
    |(displacement ds).1| ≤ 2*(2 : ℤ)^m ∧ |transverse b (displacement ds)| ≤ (2 : ℝ)^k+1 := by
  induction ds using List.reverseRecOn with
  | nil =>
    constructor
    · change (0 : ℤ) ≤ 2*(2 : ℤ)^m
      positivity
    · simpa [transverse] using (show (0 : ℝ) ≤ (2 : ℝ)^k+1 by positivity)
  | append_singleton ds d _ih =>
    have h := hproper ds.length (by simp)
    have ht : (ds++[d]).take ds.length=ds := by simp
    rw [ht] at h
    simpa [displacement_append,displacement] using chunk_step_localization b hb k m (displacement ds) h d

lemma proper_chunk_localization (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (ds : List Step)
    (hproper : ∀ i < ds.length, chunkInterior b k m (displacement (ds.take i))) :
    ∀ i ≤ ds.length, |(displacement (ds.take i)).1| ≤ 2*(2 : ℤ)^m ∧
      |transverse b (displacement (ds.take i))| ≤ (2 : ℝ)^k+1 := by
  intro i hi
  rcases lt_or_eq_of_le hi with hi | rfl
  · exact ⟨(hproper i hi).1.le,by linarith [(hproper i hi).2]⟩
  · simpa using proper_chunk_endpoint_localization b hb k m ds hproper

/-- Every full first-exit chunk supplies the precise spatial box needed by
the actual witness family, including its terminal vertex. -/
lemma fullSpatialChunk_in_box (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (h : FullSpatialChunk b k m ds) :
    PathIn p ds {z | z-spatialTranslate b k m (spatialChunkIndex b k m p) ∈ endpointBox b 4 4 k m} :=
  spatial_chunk_in_box b k m hs p ds (proper_chunk_localization b hb k m ds h.1)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialChunks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

/-- The source first-exit decomposition of every actual finite path. Empty
remainders are retained; every full chunk is nonempty. -/
theorem spatial_chunk_decomposition (b : ℝ) (k m : ℕ) (ds : List Step) :
    ∃ blocks : List (List Step), ∃ rest : List Step,
      ds=blocks.flatten++rest ∧ (∀ q ∈ blocks, FullSpatialChunk b k m q) ∧
      (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) := by
  induction hn : ds.length using Nat.strong_induction_on generalizing ds with
  | h n ih =>
    rcases first_full_spatial_chunk b k m ds with hrest | ⟨pre,rest,heq,hpre,hfull⟩
    · exact ⟨[],ds,by simp,by simp,hrest⟩
    · have hlen : rest.length < n := by
        rw [heq,List.length_append] at hn
        have hp := List.length_pos_iff.mpr hpre
        omega
      obtain ⟨bs,tail,hbs,hbf,hbt⟩ := ih rest.length hlen rest rfl
      refine ⟨pre::bs,tail,?_,?_,hbt⟩
      · simp [heq,hbs,List.append_assoc]
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hfull
        · exact hbf q hq

/-- Each full chunk and the remainder change the longitudinal coordinate by
at most `2L`, giving the cut-number bound from the manuscript. -/
lemma spatial_chunk_displacement_bound (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ)
    (blocks : List (List Step)) (rest : List Step)
    (hfull : ∀ q ∈ blocks, FullSpatialChunk b k m q)
    (hrest : ∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) :
    |(displacement (blocks.flatten++rest)).1| ≤ 2*(2 : ℤ)^m*((blocks.length : ℤ)+1) := by
  induction blocks with
  | nil =>
    have hh := (hrest rest.length le_rfl).1.le
    simpa using hh
  | cons q qs ih =>
    have hq := proper_chunk_endpoint_localization b hb k m q (hfull q (by simp)).1
    have htail := ih (fun v hv => hfull v (by simp [hv]))
    simp only [List.flatten_cons,List.append_assoc,displacement_append,Prod.fst_add,List.length_cons,Nat.cast_add,Nat.cast_one]
    have ht := abs_add_le (displacement q).1 (displacement (qs.flatten++rest)).1
    simp only [displacement_append,Prod.fst_add] at ht htail
    nlinarith [hq.1]

lemma chunkIndexTail_length (b : ℝ) (k m : ℕ) (p : Vertex) (blocks : List (List Step)) :
    (chunkIndexTail b k m p blocks).length=blocks.length := by
  induction blocks generalizing p with
  | nil => rfl
  | cons q qs ih => simp [chunkIndexTail,ih]

/-- Every actual full-chunk itinerary obeys the bounded increment rule.
The indices may repeat. -/
lemma chunkIndexTail_bounded (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (p : Vertex) (blocks : List (List Step))
    (hfull : ∀ q ∈ blocks, FullSpatialChunk b k m q) :
    BoundedIndexSteps (spatialChunkIndex b k m p) (chunkIndexTail b k m p blocks) := by
  induction blocks generalizing p with
  | nil => trivial
  | cons q qs ih =>
    have hq := proper_chunk_endpoint_localization b hb k m q (hfull q (by simp)).1
    have hinc := spatialChunkIndex_increment b k m hs p (p+displacement q)
      (by simpa only [Prod.fst_add,add_sub_cancel_left] using hq.1)
      (by simpa only [transverse_add,add_sub_cancel_left] using hq.2)
    exact ⟨hinc.1,hinc.2,ih _ (fun v hv => hfull v (by simp [hv]))⟩

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialChunkWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

/-- A negative midpoint defect in the actual chunk box is already a
labelled witness for one of the extreme support events. -/
lemma negative_midpoint_spatial_witness (w : Edge → ℝ) (b m₀ am ap K η : ℝ)
    (ha : am ≤ ap) (k m : ℕ) (ih : ℤ×ℤ) (p : Vertex) (ds : List Step)
    (hin : PathIn p ds {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m})
    (hc : defect w b m₀ ((am+ap)/2) p ds < -η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m ih,
      q.start=p ∧ q.steps=ds ∧ q.Good w := by
  have hid := minimum_defect w b m₀ am ap ha p ds
  have hn : 0 ≤ ((ap-am)/2)*|transverse b (displacement ds)| := mul_nonneg (by linarith) (abs_nonneg _)
  have hmin : min (defect w b m₀ ap p ds) (defect w b m₀ am p ds) < -η*(2 : ℝ)^k := by linarith
  rcases min_lt_iff.mp hmin with hp | hm
  · refine ⟨⟨p,ds,support b m₀ ap (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inr rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hp
    linarith
  · refine ⟨⟨p,ds,support b m₀ am (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inl rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hm
    linarith

/-- The transverse-exit case of wi:chunk-witness. The witnessing path is
the whole original chunk, so its physical edge set is unchanged. -/
theorem full_chunk_transverse_witness (w : Edge → ℝ) (b m₀ am ap K η : ℝ)
    (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η) (hgap : 4*η ≤ (ap-am)/2)
    (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p : Vertex) (ds : List Step)
    (hfull : FullSpatialChunk b k m ds)
    (htrans : (2 : ℝ)^k ≤ |transverse b (displacement ds)|)
    (hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p),
      q.start=p ∧ q.steps=ds ∧ q.Good w := by
  have hin := fullSpatialChunk_in_box b hb k m hs p ds hfull
  have hc := transverse_chunk_witness w b m₀ am ap η ((2 : ℝ)^k) ha (by positivity) hη hgap p ds htrans hcheap
  rcases hc with hp | hm
  · refine ⟨⟨p,ds,support b m₀ ap (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inr rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hp
    linarith
  · refine ⟨⟨p,ds,support b m₀ am (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inl rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hm
    linarith

/-- Nonnegative weights exclude a cheap chunk exiting through the negative
longitudinal boundary, at the exact deterministic source scale. -/
lemma negative_longitudinal_chunk_not_cheap (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ a η : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (p : Vertex) (ds : List Step)
    (hfull : FullSpatialChunk b k m ds)
    (hx : (displacement ds).1= -2*(2 : ℤ)^m)
    (hscale : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|a| *((2 : ℝ)^k+1)) :
    η*(2 : ℝ)^k < defect w b m₀ a p ds := by
  have hr := (proper_chunk_endpoint_localization b hb k m ds hfull.1).2
  have hc := pathCost_nonneg hw p ds
  have hmul := mul_le_mul_of_nonneg_left hr (abs_nonneg a)
  have hab := le_abs_self (a*transverse b (displacement ds))
  rw [abs_mul] at hab
  unfold defect support
  rw [hx]
  push_cast
  nlinarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialCrossingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

lemma spatialChunkIndex_transverse_column (b : ℝ) (k m : ℕ) (p : Vertex) (i : ℤ) :
    0 ≤ transverse b p-transverse b (spatialTranslate b k m (i,(spatialChunkIndex b k m p).2)) ∧
      transverse b p-transverse b (spatialTranslate b k m (i,(spatialChunkIndex b k m p).2)) < (2 : ℝ)^k+1 := by
  have hs : (0 : ℝ) < 2^k := by positivity
  have hl := (le_div_iff₀ hs).mp (Int.floor_le (transverse b p/(2 : ℝ)^k))
  have hu := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (transverse b p/(2 : ℝ)^k))
  have hf := Int.floor_le (b*(i*(2 : ℤ)^m))
  have hf' := Int.lt_floor_add_one (b*(i*(2 : ℤ)^m))
  rw [spatialTranslate_center]
  simp only [spatialChunkIndex,Int.cast_ofNat] at hf hf' ⊢
  constructor <;> nlinarith [hf,hf']

lemma chunk_subcrossing_region (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (p z : Vertex)
    (hx : ((spatialChunkIndex b k m p).1+1)*(2 : ℤ)^m ≤ z.1 ∧
      z.1 ≤ ((spatialChunkIndex b k m p).1+2)*(2 : ℤ)^m)
    (hr : |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1) :
    z ∈ rareFastRegion b 1 8 ((2 : ℝ)^k) ((2 : ℤ)^m)
      (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) := by
  have hcenter := spatialChunkIndex_transverse_column b k m p ((spatialChunkIndex b k m p).1+1)
  have ht : transverse b (z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) =
      transverse b z-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) := by
    simp [transverse]; ring
  have hx' : 0 ≤ (z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 ∧
      (z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 ≤ (2 : ℤ)^m := by
    simp only [spatialTranslate,Prod.fst_add,Prod.fst_sub]
    constructor <;> nlinarith [hx.1,hx.2]
  have hxR : 0 ≤ ((z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 : ℝ) ∧
      ((z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 : ℝ) ≤ (2 : ℝ)^m := by exact_mod_cast hx'
  refine ⟨by simpa using (show -(2 : ℝ)^m ≤ ((z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 : ℝ) by linarith [pow_pos (by norm_num : (0 : ℝ)<2) m]),?_,?_⟩
  · push_cast
    nlinarith [hxR.2,pow_pos (by norm_num : (0 : ℝ)<2) m]
  · rw [ht]
    have hcenter' : 0 ≤ transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) ∧
        transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) < (2 : ℝ)^k+1 := by
      have he : spatialChunkIndex b k m p+(1,0)=((spatialChunkIndex b k m p).1+1,(spatialChunkIndex b k m p).2) := by ext <;> simp
      rw [he]
      exact hcenter
    have hz := abs_le.mp hr
    apply abs_le.mpr
    constructor <;> nlinarith [hcenter'.1,hcenter'.2]

lemma pathEdges_append (p : Vertex) (ds es : List Step) :
    pathEdges p (ds++es)=pathEdges p ds ∪ pathEdges (p+displacement ds) es := by
  induction ds generalizing p with
  | nil => simp [pathEdges]
  | cons d ds ih => simp [pathEdges,ih,displacement_cons,add_assoc,Finset.insert_union]

lemma pathEdges_middle_subset (p : Vertex) (pre mid post : List Step) :
    pathEdges (p+displacement pre) mid ⊆ pathEdges p (pre++mid++post) := by
  rw [pathEdges_append,pathEdges_append]
  exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialPositiveChunk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

/-- Positive-longitudinal case of wi:chunk-witness. The outer pieces are
checked first; otherwise the actual middle subcrossing witnesses E(s,L). -/
theorem positive_longitudinal_chunk_witness (w : Edge → ℝ) (b m₀ am ap K η : ℝ)
    (hb : |b| ≤ 1) (ha : am ≤ ap) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hscale : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (hfull : FullSpatialChunk b k m ds)
    (hx : (displacement ds).1=2*(2 : ℤ)^m)
    (hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p),
      q.Good w ∧ q.edges ⊆ pathEdges p ds := by
  let ih := spatialChunkIndex b k m p
  let L : ℤ := (2 : ℤ)^m
  let A := (ih.1+1)*L
  let B := (ih.1+2)*L
  have hL : 0 < L := by dsimp [L]; positivity
  have hi := meshFloor_bounds p.1 L hL
  have hidx : ih.1=p.1/L := rfl
  have hpA : p.1 ≤ A := by dsimp [A]; rw [hidx]; dsimp [meshFloor] at hi; nlinarith [hi.2]
  have hAB : A ≤ B := by dsimp [A,B]; nlinarith
  have hend : B ≤ (p+displacement ds).1 := by
    dsimp [B]
    rw [hidx]
    simp only [hx]
    dsimp [meshFloor] at hi
    change p.1/L*L ≤ p.1 ∧ _ at hi
    dsimp [L] at *
    nlinarith [hi.1]
  obtain ⟨pre,mid,post,heq,hpre,hmid,hincols⟩ := path_column_subcrossing p ds A B hpA hAB hend
  let box : Set Vertex := {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m}
  have hin : PathIn p (pre++mid++post) box := by
    rw [← heq]
    exact fullSpatialChunk_in_box b hb k m hs p ds hfull
  have hprebox : PathIn p pre box :=
    pathIn_append_left p pre mid box (pathIn_append_left p (pre++mid) post box hin)
  have hpostbox := pathIn_append_right p (pre++mid) post box hin
  by_cases hnegPre : defect w b m₀ ((am+ap)/2) p pre < -η*(2 : ℝ)^k
  · obtain ⟨q,hq,hqs,hqd,hgood⟩ := negative_midpoint_spatial_witness w b m₀ am ap K η ha k m ih p pre hprebox hnegPre
    refine ⟨q,hq,hgood,?_⟩
    change pathEdges q.start q.steps ⊆ pathEdges p ds
    rw [hqs,hqd,heq,pathEdges_append,pathEdges_append]
    exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  · by_cases hnegPost : defect w b m₀ ((am+ap)/2) (p+displacement (pre++mid)) post < -η*(2 : ℝ)^k
    · obtain ⟨q,hq,hqs,hqd,hgood⟩ := negative_midpoint_spatial_witness w b m₀ am ap K η ha k m ih
        (p+displacement (pre++mid)) post hpostbox hnegPost
      refine ⟨q,hq,hgood,?_⟩
      change pathEdges q.start q.steps ⊆ pathEdges p ds
      rw [hqs,hqd,heq,pathEdges_append]
      exact Finset.subset_union_right
    · have hprelo := le_of_not_gt hnegPre
      have hpostlo := le_of_not_gt hnegPost
      have hsum := hcheap
      rw [heq,defect_append,defect_append] at hsum
      have hmidcheap : defect w b m₀ ((am+ap)/2) (p+displacement pre) mid < 3*η*(2 : ℝ)^k := by linarith
      have hrloc : PathIn p (pre++mid++post) {z | |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1} := by
        rw [← heq]
        intro i hi'
        simpa only [mem_ofPred_eq,transverse_add,add_sub_cancel_left] using
          (proper_chunk_localization b hb k m ds hfull.1 i hi').2
      have hrmid := pathIn_middle p pre mid post _ hrloc
      have hrstart : |transverse b (p+displacement pre)-transverse b p| ≤ (2 : ℝ)^k+1 := by
        simpa using hrmid 0 (by omega)
      have hrend := pathIn_endpoint _ _ _ hrmid
      change |transverse b (p+displacement pre+displacement mid)-transverse b p| ≤ (2 : ℝ)^k+1 at hrend
      have hrd : |transverse b (displacement mid)| ≤ 2*((2 : ℝ)^k+1) := by
        have hh := abs_sub (transverse b (p+displacement pre+displacement mid)-transverse b p)
          (transverse b (p+displacement pre)-transverse b p)
        simp only [transverse_add] at hh hrend
        have he : transverse b p+transverse b (displacement pre)+transverse b (displacement mid)-transverse b p-
            (transverse b p+transverse b (displacement pre)-transverse b p)=transverse b (displacement mid) := by ring
        rw [he] at hh
        simp only [transverse_add] at hrstart
        linarith
      have hdx : (displacement mid).1=L := by
        simp only [Prod.fst_add] at hmid
        dsimp [A,B] at hpre hmid
        nlinarith
      have hac := mul_le_mul_of_nonneg_left hrd (abs_nonneg ((am+ap)/2))
      have haa := le_abs_self (((am+ap)/2)*transverse b (displacement mid))
      rw [abs_mul] at haa
      have hcost : pathCost w (p+displacement pre) mid < m₀*(L : ℝ)+K*(2 : ℝ)^k := by
        unfold defect support at hmidcheap
        rw [hdx] at hmidcheap
        nlinarith
      let q : GammaFPP.BK.StrictPathWitness := ⟨p+displacement pre,mid,m₀*(L : ℝ)+K*(2 : ℝ)^k⟩
      refine ⟨q,Or.inr ⟨?_,?_,?_,?_⟩,hcost,?_⟩
      · change (p+displacement pre).1=(spatialTranslate b k m (ih+(1,0))).1
        simpa [A,spatialTranslate,L] using hpre
      · change (p+displacement pre+displacement mid).1=(spatialTranslate b k m (ih+(1,0))).1+(2 : ℤ)^m
        rw [hmid]
        dsimp [B,spatialTranslate,L]
        ring
      · intro i hi'
        exact chunk_subcrossing_region b k m hs p _ (hincols i hi') (hrmid i hi')
      · change m₀*(L : ℝ)+K*(2 : ℝ)^k=m₀*(2 : ℤ)^m+K*(2 : ℝ)^k
        simp [L]
      · change pathEdges (p+displacement pre) mid ⊆ pathEdges p ds
        rw [heq]
        exact pathEdges_middle_subset p pre mid post

/-- Complete source wi:chunk-witness for actual full chunks. -/
theorem cheap_full_spatial_chunk_witness (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (hfull : FullSpatialChunk b k m ds)
    (hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p),
      q.Good w ∧ q.edges ⊆ pathEdges p ds := by
  by_cases hr : (2 : ℝ)^k ≤ |transverse b (displacement ds)|
  · obtain ⟨q,hq,hs',hd',hg⟩ := full_chunk_transverse_witness w b m₀ am ap K η hb ha hη hgap k m hs p ds hfull hr hcheap
    refine ⟨q,hq,hg,?_⟩
    change pathEdges q.start q.steps ⊆ pathEdges p ds
    rw [hs',hd']
  · have hl := (proper_chunk_endpoint_localization b hb k m ds hfull.1).1
    have hx : 2*(2 : ℤ)^m ≤ |(displacement ds).1| := by
      by_contra hh
      exact hfull.2 ⟨lt_of_not_ge hh,lt_of_not_ge hr⟩
    have heq : |(displacement ds).1|=2*(2 : ℤ)^m := le_antisymm hl hx
    rcases eq_or_eq_neg_of_abs_eq heq with hx | hx
    · exact positive_longitudinal_chunk_witness w b m₀ am ap K η hb ha k m hs hscale₂ p ds hfull hx hcheap
    · have hh := negative_longitudinal_chunk_not_cheap w hw b m₀ ((am+ap)/2) η hb k m p ds hfull
        (by simpa using hx) hscale₁
      linarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ContiguousWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

lemma trace_append (p : Vertex) (ds es : List Step) :
    trace p (ds++es)=trace p ds++trace (p+displacement ds) es := by
  induction ds generalizing p with
  | nil => simp [trace]
  | cons d ds ih => simp [trace,ih,add_assoc]

/-- A contiguous split of actual traversals is a split into actual paths. -/
lemma trace_split (p : Vertex) (ds : List Step) (xs ys : List Traversal)
    (h : trace p ds=xs++ys) :
    ∃ pre rest : List Step, ds=pre++rest ∧ trace p pre=xs ∧
      trace (p+displacement pre) rest=ys := by
  induction xs generalizing p ds with
  | nil => exact ⟨[],ds,rfl,rfl,by simpa using h⟩
  | cons x xs ih =>
    cases ds with
    | nil => simp [trace] at h
    | cons d ds =>
      obtain ⟨hx,ht⟩ := List.cons.inj h
      obtain ⟨pre,rest,he,hpre,hrest⟩ := ih (p+d.delta) ds ht
      refine ⟨d::pre,rest,by simp [he],?_,?_⟩
      · simp only [trace,hpre,hx]
      · simpa only [displacement_cons,add_assoc] using hrest

lemma trace_edges (p : Vertex) (ds : List Step) :
    ((trace p ds).map traversalEdge).toFinset=pathEdges p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [trace,traversalEdge,pathEdges,ih]

lemma simple_append_edges (p : Vertex) (ds es : List Step)
    (h : ((trace p (ds++es)).map traversalEdge).Nodup) :
    ((trace p ds).map traversalEdge).Nodup ∧
    ((trace (p+displacement ds) es).map traversalEdge).Nodup ∧
    Disjoint (pathEdges p ds) (pathEdges (p+displacement ds) es) := by
  rw [trace_append,List.map_append,List.nodup_append] at h
  refine ⟨h.1,h.2.1,?_⟩
  rw [← trace_edges,← trace_edges]
  exact Finset.disjoint_left.mpr (fun e he hf =>
    h.2.2 e (List.mem_toFinset.mp he) e (List.mem_toFinset.mp hf) rfl)

/-- Source wi:chunk-defect. Construct actual labelled negative-prefix witnesses
inside the original box, with disjoint physical edges and the basic bound. -/
theorem spatial_negative_prefix_witnesses (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (ha : am ≤ ap) (hη : 0 ≤ η)
    (k m : ℕ) (ih : ℤ×ℤ)
    (hscale : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step)
    (hin : PathIn p ds {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m})
    (hsimple : ((trace p ds).map traversalEdge).Nodup) :
    ∃ ws : List GammaFPP.BK.StrictPathWitness,
      ws.Pairwise (fun q r => Disjoint q.edges r.edges) ∧
      (∀ q ∈ ws, q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧
        q.Good w ∧ q.edges ⊆ pathEdges p ds) ∧
      -η*(2 : ℝ)^k-2*η*(2 : ℝ)^k*ws.length ≤ defect w b m₀ ((am+ap)/2) p ds := by
  have hηs : 0 ≤ η*(2 : ℝ)^k := mul_nonneg hη (by positivity)
  induction hn : ds.length using Nat.strong_induction_on generalizing p ds with
  | h n rec =>
    by_cases hlo : -η*(2 : ℝ)^k ≤ defect w b m₀ ((am+ap)/2) p ds
    · exact ⟨[],by simp,by simp,by simpa using hlo⟩
    · have hstep : ∀ t ∈ trace p ds, -(η*(2 : ℝ)^k) ≤ stepDefect w b m₀ ((am+ap)/2) t := by
        intro t _
        have ht := hw (traversalEdge t)
        have hs := (support_step_bound b m₀ ((am+ap)/2) t.2).trans hscale
        unfold stepDefect
        linarith
      obtain ⟨xs,ys,he,hne,hxslo,hxshi⟩ := first_drop (stepDefect w b m₀ ((am+ap)/2))
        (η*(2 : ℝ)^k) (trace p ds) hstep 0 (by linarith)
        (by rw [trace_total_defect]; linarith)
      obtain ⟨pre,rest,heq,hpre,hrest⟩ := trace_split p ds xs ys he
      have hpreNe : pre ≠ [] := by intro hz; subst pre; simp [trace] at hpre; exact hne hpre
      have hlen : rest.length < n := by
        have hh := List.length_pos_iff.mpr hpreNe
        rw [heq,List.length_append] at hn
        omega
      have hsimp := simple_append_edges p pre rest (by rw [← heq]; exact hsimple)
      have hin' : PathIn p (pre++rest) {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m} := by rw [← heq]; exact hin
      have hprelo : -2*(η*(2 : ℝ)^k) ≤ defect w b m₀ ((am+ap)/2) p pre := by
        rw [← trace_total_defect,hpre]; simpa using hxslo
      have hprehi : defect w b m₀ ((am+ap)/2) p pre < -η*(2 : ℝ)^k := by
        rw [← trace_total_defect,hpre]; simpa [neg_mul] using hxshi
      obtain ⟨q,hq,hqs,hqd,hqg⟩ := negative_midpoint_spatial_witness w b m₀ am ap K η ha k m ih p pre
        (pathIn_append_left p pre rest _ hin') hprehi
      have hqe : q.edges=pathEdges p pre := by change pathEdges q.start q.steps=_; rw [hqs,hqd]
      obtain ⟨ws,hpair,hws,hbound⟩ := rec rest.length hlen (p+displacement pre) rest
        (pathIn_append_right p pre rest _ hin') hsimp.2.1 rfl
      refine ⟨q::ws,List.pairwise_cons.mpr ⟨?_,hpair⟩,?_,?_⟩
      · intro r hr
        rw [hqe]
        exact hsimp.2.2.mono_right (hws r hr).2.2
      · intro r hr
        rw [heq,pathEdges_append]
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨hq,hqg,by rw [hqe]; exact Finset.subset_union_left⟩
        · exact ⟨(hws r hr).1,(hws r hr).2.1,(hws r hr).2.2.trans Finset.subset_union_right⟩
      · rw [heq,defect_append]
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        nlinarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialWitnessCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP
open Set

/-- A constructive form of wi:full-defect. If the greedy family is empty,
a cheap full chunk supplies a single witness. No maximum is assumed. -/
theorem spatial_full_chunk_witnesses (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (hfull : FullSpatialChunk b k m ds)
    (hsimple : ((trace p ds).map traversalEdge).Nodup) :
    ∃ ws : List GammaFPP.BK.StrictPathWitness,
      ws.Pairwise (fun q r => Disjoint q.edges r.edges) ∧
      (∀ q ∈ ws, q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p) ∧
        q.Good w ∧ q.edges ⊆ pathEdges p ds) ∧
      η*(2 : ℝ)^k-4*η*(2 : ℝ)^k*ws.length ≤ defect w b m₀ ((am+ap)/2) p ds := by
  have hηs : 0 ≤ η*(2 : ℝ)^k := by positivity
  obtain ⟨ws,hpair,hws,hbasic⟩ := spatial_negative_prefix_witnesses w hw b m₀ am ap K η ha hη.le k m
    (spatialChunkIndex b k m p) hstep p ds (fullSpatialChunk_in_box b hb k m hs p ds hfull) hsimple
  by_cases hempty : ws=[]
  · subst ws
    simp only [List.length_nil,Nat.cast_zero,mul_zero,sub_zero] at hbasic
    by_cases hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k
    · obtain ⟨q,hq,hg,he⟩ := cheap_full_spatial_chunk_witness w hw b m₀ am ap K η hb ha hη hgap
        k m hs hscale₁ hscale₂ p ds hfull hcheap
      refine ⟨[q],by simp,?_,?_⟩
      · intro r hr
        have heq : r=q := List.mem_singleton.mp hr
        subst r
        exact ⟨hq,hg,he⟩
      · simp only [List.length_singleton,Nat.cast_one,mul_one]
        linarith
    · exact ⟨[],by simp,by simp,by simpa using le_of_not_gt hcheap⟩
  · have hlen : (1 : ℝ) ≤ ws.length := by exact_mod_cast List.length_pos_iff.mpr hempty
    refine ⟨ws,hpair,hws,?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hlen hηs]

/-- Source wi:total-defect, including all physical-edge disjointness and the
actual ordered chunk indices. Witness families are constructed, not supplied. -/
theorem spatial_total_witnesses (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (blocks : List (List Step)) (rest : List Step)
    (hfull : ∀ q ∈ blocks, FullSpatialChunk b k m q)
    (hrest : ∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i)))
    (hsimple : ((trace p (blocks.flatten++rest)).map traversalEdge).Nodup) :
    ∃ packs : List (List GammaFPP.BK.StrictPathWitness),
      packs.length=blocks.length+1 ∧
      List.Forall₂ (fun ws ih => ∀ q ∈ ws,
        q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w)
        packs (spatialChunkIndex b k m p :: chunkIndexTail b k m p blocks) ∧
      packs.flatten.Pairwise (fun q r => Disjoint q.edges r.edges) ∧
      (∀ q ∈ packs.flatten, q.edges ⊆ pathEdges p (blocks.flatten++rest)) ∧
      ((blocks.length : ℝ)-1)*η*(2 : ℝ)^k-4*η*(2 : ℝ)^k*packs.flatten.length ≤
        defect w b m₀ ((am+ap)/2) p (blocks.flatten++rest) := by
  have hηs : 0 ≤ η*(2 : ℝ)^k := by positivity
  induction blocks generalizing p with
  | nil =>
    have hin := spatial_chunk_in_box b k m hs p rest
      (proper_chunk_localization b hb k m rest (fun i hi => hrest i hi.le))
    obtain ⟨ws,hpair,hws,hbound⟩ := spatial_negative_prefix_witnesses w hw b m₀ am ap K η ha hη.le k m
      (spatialChunkIndex b k m p) hstep p rest hin (by simpa using hsimple)
    refine ⟨[ws],rfl,?_,by simpa using hpair,?_,?_⟩
    · exact List.Forall₂.cons (fun q hq => ⟨(hws q hq).1,(hws q hq).2.1⟩) List.Forall₂.nil
    · simpa using (fun q hq => (hws q hq).2.2)
    · simp only [List.length_nil,Nat.cast_zero,zero_sub,neg_mul,one_mul,List.flatten_singleton,List.flatten_nil,List.nil_append]
      nlinarith [mul_nonneg hηs (show (0 : ℝ) ≤ ws.length by positivity)]
  | cons ds blocks rec =>
    have hsim : ((trace p (ds++(blocks.flatten++rest))).map traversalEdge).Nodup := by
      simpa only [List.flatten_cons,List.append_assoc] using hsimple
    have hsplit := simple_append_edges p ds (blocks.flatten++rest) hsim
    obtain ⟨ws,hpair,hws,hbound⟩ := spatial_full_chunk_witnesses w hw b m₀ am ap K η hb ha hη hgap k m hs
      hstep hscale₁ hscale₂ p ds (hfull ds (by simp)) hsplit.1
    obtain ⟨packs,hlen,hassign,hdisj,hedges,htotal⟩ := rec (p+displacement ds)
      (fun q hq => hfull q (by simp [hq])) hsplit.2.1
    refine ⟨ws::packs,by simp [hlen],List.Forall₂.cons ?_ hassign,?_,?_,?_⟩
    · exact fun q hq => ⟨(hws q hq).1,(hws q hq).2.1⟩
    · simp only [List.flatten_cons,List.pairwise_append]
      refine ⟨hpair,hdisj,?_⟩
      intro q hq r hr
      exact hsplit.2.2.mono (hws q hq).2.2 (hedges r hr)
    · intro q hq
      simp only [List.flatten_cons,List.mem_append] at hq
      simp only [List.flatten_cons,List.append_assoc]
      rw [pathEdges_append]
      rcases hq with hq | hq
      · exact (hws q hq).2.2.trans Finset.subset_union_left
      · exact (hedges q hq).trans Finset.subset_union_right
    · simp only [List.flatten_cons,List.append_assoc,List.length_cons,List.length_append,
        Nat.cast_add,Nat.cast_one]
      rw [defect_append]
      linarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_WitnessSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP
open Set

lemma takeWitnessPacks_length {α : Type*} (t : ℕ) (packs : List (List α)) :
    (takeWitnessPacks t packs).length=packs.length := by
  induction packs generalizing t with
  | nil => rfl
  | cons ws packs ih => simp [takeWitnessPacks,ih]

lemma takeWitnessPacks_flatten {α : Type*} (t : ℕ) (packs : List (List α)) :
    (takeWitnessPacks t packs).flatten=packs.flatten.take t := by
  induction packs generalizing t with
  | nil => simp [takeWitnessPacks]
  | cons ws packs ih => simp [takeWitnessPacks,ih,List.take_append]

lemma takeWitnessPacks_assign {α β : Type*} (R : α → β → Prop) (t : ℕ)
    (packs : List (List α)) (is : List β)
    (h : List.Forall₂ (fun ws i => ∀ q ∈ ws, R q i) packs is) :
    List.Forall₂ (fun ws i => ∀ q ∈ ws, R q i) (takeWitnessPacks t packs) is := by
  induction h generalizing t with
  | nil => exact List.Forall₂.nil
  | @cons ws i packs is hws htail ih =>
    exact List.Forall₂.cons (fun q hq => hws q (List.mem_of_mem_take hq)) (ih _)

/-- The exact source selection threshold, with a convenient sufficient N≥4. -/
lemma long_path_witness_count (H a : ℝ) (ha : 0 < a) (N M : ℕ) (hN : 4 ≤ N)
    (hlower : ((N : ℝ)-1)*a-4*a*M ≤ H) (hcheap : H < N*a/2) :
    N/16 ≤ M := by
  have hM : (N : ℝ)/8-1/4 < M := by nlinarith
  have hdiv : ((N/16 : ℕ) : ℝ)*16 ≤ N := by exact_mod_cast Nat.div_mul_le_self N 16
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : ((N/16 : ℕ) : ℝ) ≤ M := by linarith
  exact_mod_cast hh

lemma witnessLabels_length (ns : List ℕ) (is : List (ℤ×ℤ)) (h : ns.length=is.length) :
    (witnessLabels ns is).length=ns.sum := by
  induction ns generalizing is with
  | nil => simp [witnessLabels]
  | cons n ns ih =>
    cases is with
    | nil => simp at h
    | cons i is => simp [witnessLabels,ih is (by simpa using h)]

theorem witnessPacks_strictDisjoint (w : Edge → ℝ) (b m₀ am ap K η : ℝ) (k m : ℕ)
    (packs : List (List GammaFPP.BK.StrictPathWitness)) (is : List (ℤ×ℤ))
    (hassign : List.Forall₂ (fun ws ih => ∀ q ∈ ws,
      q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w) packs is)
    (hpair : packs.flatten.Pairwise (fun q r => Disjoint q.edges r.edges)) :
    GammaFPP.BK.StrictDisjointPaths (spatialListSupport b k m (witnessLabels (packs.map List.length) is))
      ((witnessLabels (packs.map List.length) is).map (spatialWitnessFamily b m₀ am ap K η k m)) w := by
  let labels := witnessLabels (packs.map List.length) is
  have hlabels : List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w)
      packs.flatten labels := by
    clear hpair
    induction hassign with
    | nil => exact List.Forall₂.nil
    | @cons ws i packs is hws htail ih =>
      change List.Forall₂ _ (ws++packs.flatten) ((List.replicate ws.length i)++_)
      induction ws with
      | nil => exact ih
      | cons q qs ih =>
        exact List.Forall₂.cons (hws q (by simp)) (ih (fun r hr => hws r (by simp [hr])))
  refine ⟨packs.flatten,?_,hpair⟩
  have hsupp (ih : ℤ×ℤ) (hi : ih ∈ labels) : spatialWitnessSupport b k m ih ⊆ spatialListSupport b k m labels := by
    intro e he
    exact Finset.mem_biUnion.mpr ⟨ih,List.mem_toFinset.mpr hi,he⟩
  have hall : List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧
      q.edges ⊆ spatialListSupport b k m labels ∧ q.Good w) packs.flatten labels := by
    have enrich (ps : List GammaFPP.BK.StrictPathWitness) (js : List (ℤ×ℤ))
        (hh : List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w) ps js)
        (hsub : ∀ i ∈ js, i ∈ labels) :
        List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧
          q.edges ⊆ spatialListSupport b k m labels ∧ q.Good w) ps js := by
      induction hh with
      | nil => exact List.Forall₂.nil
      | @cons q i ps js hq ht rec =>
        exact List.Forall₂.cons
          ⟨hq.1,(spatialWitness_edges b m₀ am ap K η k m i q hq.1).trans (hsupp i (hsub i (by simp))),hq.2⟩
          (rec (fun j hj => hsub j (by simp [hj])))
    exact enrich _ _ hlabels (fun _ hi => hi)
  exact List.forall₂_map_right_iff.mpr hall

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_WitnessEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP
open Finset

lemma spatialNeighbors_card (i : ℤ×ℤ) : (spatialNeighbors i).card ≤ 49 := by
  apply (card_image_le).trans
  norm_num [card_product,Int.card_Icc,Int.toNat]

lemma mem_spatialNeighbors (i j : ℤ×ℤ) (h₁ : |j.1-i.1| ≤ 3) (h₂ : |j.2-i.2| ≤ 3) :
    j ∈ spatialNeighbors i := by
  apply mem_image.mpr
  refine ⟨j-i,?_,by abel⟩
  exact mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp h₁),mem_Icc.mpr (abs_le.mp h₂)⟩

lemma spatialItineraries_card (i : ℤ×ℤ) (n : ℕ) : (spatialItineraries i n).card ≤ 49^n := by
  induction n generalizing i with
  | zero => simp [spatialItineraries]
  | succ n ih =>
    calc
      _ ≤ ∑ j ∈ spatialNeighbors i, ((spatialItineraries j n).image (List.cons j)).card := card_biUnion_le
      _ ≤ ∑ _j ∈ spatialNeighbors i, 49^n := sum_le_sum (fun j _ => card_image_le.trans (ih j))
      _ = (spatialNeighbors i).card * 49^n := by simp
      _ ≤ 49*49^n := Nat.mul_le_mul_right _ (spatialNeighbors_card i)
      _ = _ := by rw [pow_succ]; omega

lemma mem_spatialItineraries (i : ℤ×ℤ) (is : List (ℤ×ℤ)) (h : BoundedIndexSteps i is) :
    is ∈ spatialItineraries i is.length := by
  induction is generalizing i with
  | nil => simp [spatialItineraries]
  | cons j js ih =>
    change j::js ∈ (spatialNeighbors i).biUnion (fun j => (spatialItineraries j js.length).image (List.cons j))
    change |j.1-i.1| ≤ 3 ∧ |j.2-i.2| ≤ 3 ∧ BoundedIndexSteps j js at h
    have hj : j ∈ spatialNeighbors i := mem_spatialNeighbors i j h.1 h.2.1
    have ht : js ∈ spatialItineraries j js.length := ih j h.2.2
    simp only [mem_biUnion,mem_image]
    exact ⟨j,hj,js,ht,rfl⟩

lemma compositionCandidates_card (n t : ℕ) : (compositionCandidates n t).card ≤ 2^(n+t) := by
  induction n generalizing t with
  | zero => simp only [compositionCandidates,card_singleton,Nat.zero_add]; exact Nat.one_le_pow _ _ (by omega)
  | succ n ih =>
    induction t with
    | zero => simp only [compositionCandidates,card_singleton,Nat.add_zero]; exact Nat.one_le_pow _ _ (by omega)
    | succ t ht =>
      rw [compositionCandidates]
      calc
        _ ≤ ((compositionCandidates n (t+1)).image (List.cons 0)).card+
            ((compositionCandidates (n+1) t).image increaseFirst).card := card_union_le ..
        _ ≤ 2^(n+(t+1))+2^(n+1+t) := Nat.add_le_add (card_image_le.trans (ih _)) (card_image_le.trans ht)
        _ = 2^(n+1+(t+1)) := by rw [show n+(t+1)=n+1+t by omega,show n+1+(t+1)=(n+1+t)+1 by omega,pow_succ]; omega

lemma mem_compositionCandidates (n t : ℕ) (ns : List ℕ) (hlen : ns.length=n+1) (hsum : ns.sum=t) :
    ns ∈ compositionCandidates n t := by
  induction n generalizing t ns with
  | zero =>
    cases ns with
    | nil => simp at hlen
    | cons a ns =>
      have he : ns=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst ns
      have ha : a=t := by simpa using hsum
      simp [compositionCandidates,ha]
  | succ n ih =>
    induction t generalizing ns with
    | zero =>
      have hz : ns=List.replicate (n+2) 0 := by
        have zeros (ls : List ℕ) (hh : ls.sum=0) : ls=List.replicate ls.length 0 := by
          induction ls with
          | nil => rfl
          | cons a ls rec =>
            simp only [List.sum_cons] at hh
            have ha : a=0 := by omega
            have ht : ls.sum=0 := by omega
            simp only [List.length_cons,List.replicate_succ]
            exact congrArg₂ List.cons ha (rec ht)
        have he := zeros ns hsum
        simpa [hlen] using he
      simp [compositionCandidates,hz]
    | succ t ht =>
      cases ns with
      | nil => simp at hlen
      | cons a ns =>
        have hlen' : ns.length=n+1 := by simpa using hlen
        cases a with
        | zero =>
          rw [compositionCandidates]
          apply mem_union_left
          exact mem_image.mpr ⟨ns,ih (t+1) ns hlen' (by simpa using hsum),rfl⟩
        | succ a =>
          rw [compositionCandidates]
          apply mem_union_right
          exact mem_image.mpr ⟨a::ns,ht (a::ns) (by simpa using hlen) (by simp only [List.sum_cons] at hsum ⊢; omega),rfl⟩

lemma mem_compositionCover (n t : ℕ) (ns : List ℕ) :
    ns ∈ compositionCover n t ↔ ns.length=n+1 ∧ ns.sum=t := by
  simp only [compositionCover,mem_filter]
  exact ⟨fun h => h.2,fun h => ⟨mem_compositionCandidates n t ns h.1 h.2,h⟩⟩

/-- The source 4^N bound, without counting any witnessing paths. -/
lemma compositionCover_card (n t : ℕ) (ht : t ≤ n) : (compositionCover n t).card ≤ 4^n := by
  calc
    _ ≤ 2^(n+t) := (card_filter_le ..).trans (compositionCandidates_card n t)
    _ ≤ 2^(n+n) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 4^n := by rw [pow_add,← mul_pow]; norm_num

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialBadPathCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP
open Set Finset

/-- Every bad actual path is covered by one itinerary and one weak composition.
No choice of individual witnessing paths is included in the finite count. -/
theorem spatial_bad_path_cover (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (N : ℕ) (hN : 4 ≤ N) (hbad : SpatialBadPath w b m₀ ((am+ap)/2) η k m N) :
    ∃ is ∈ spatialItineraries 0 N, ∃ ns ∈ compositionCover N (N/16),
      (0::is).length=ns.length ∧
      GammaFPP.BK.StrictDisjointPaths (spatialListSupport b k m (witnessLabels ns (0::is)))
        ((witnessLabels ns (0::is)).map (spatialWitnessFamily b m₀ am ap K η k m)) w := by
  obtain ⟨blocks,rest,hlen,hfull,hrest,hsimple,hcheap⟩ := hbad
  obtain ⟨packs,hplen,hassign,hpair,hedges,hlower⟩ := spatial_total_witnesses w hw b m₀ am ap K η hb ha hη
    hgap k m hs hstep hscale₁ hscale₂ 0 blocks rest hfull hrest hsimple
  have hcount : N/16 ≤ packs.flatten.length :=
    long_path_witness_count (defect w b m₀ ((am+ap)/2) 0 (blocks.flatten++rest)) (η*(2 : ℝ)^k) (by positivity) N _ hN
      (by rw [hlen] at hlower; nlinarith [hlower]) (by nlinarith [hcheap])
  let selected := takeWitnessPacks (N/16) packs
  let ns := selected.map List.length
  let is := chunkIndexTail b k m 0 blocks
  have hilen : is.length=N := by dsimp [is]; rw [chunkIndexTail_length,hlen]
  have his : is ∈ spatialItineraries 0 N := by
    have hh := mem_spatialItineraries (spatialChunkIndex b k m 0) is (chunkIndexTail_bounded b hb k m hs 0 blocks hfull)
    simpa only [spatialChunkIndex_origin,hilen] using hh
  have hnlen : ns.length=N+1 := by simp [ns,selected,takeWitnessPacks_length,hplen,hlen]
  have hnflat : selected.flatten=packs.flatten.take (N/16) := takeWitnessPacks_flatten ..
  have hnsum : ns.sum=N/16 := by
    change (selected.map List.length).sum=_
    rw [← List.length_flatten,hnflat,List.length_take,Nat.min_eq_left hcount]
  have hselected := takeWitnessPacks_assign
    (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w) (N/16) packs _ hassign
  have hselectedPair : selected.flatten.Pairwise (fun q r => Disjoint q.edges r.edges) := by
    rw [hnflat]
    exact hpair.sublist (List.take_sublist ..)
  refine ⟨is,his,ns,(mem_compositionCover ..).mpr ⟨hnlen,hnsum⟩,by simp [hilen,hnlen],?_⟩
  have hc := witnessPacks_strictDisjoint w b m₀ am ap K η k m selected
    (spatialChunkIndex b k m 0::is) hselected hselectedPair
  simpa only [spatialChunkIndex_origin] using hc

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialEntropyProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK
open Set Finset MeasureTheory Filter
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Source wi:entropy-bound for actual bad paths, using the proved geometric
cover and a same-scale actual spatial BK bound. -/
theorem spatial_bad_path_probability (henv : GammaEnvironment shape rate P τ)
    (_hshape : 0 < shape) (_hrate : 0 < rate)
    (b m₀ am ap K η p₀ : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η) (hp₀ : 0 ≤ p₀)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (hBK : ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
      (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ p₀^is.length)
    (N : ℕ) (hN : 4 ≤ N) :
    P.real {ω | SpatialBadPath (fun e => τ e ω) b m₀ ((am+ap)/2) η k m N} ≤
      (196 : ℝ)^N*p₀^(N/16) := by
  let _ := henv.probability
  let codes := spatialItineraries 0 N ×ˢ compositionCover N (N/16)
  let E (code : List (ℤ×ℤ) × List ℕ) : Set Ω := {ω |
    (0::code.1).length=code.2.length ∧
    StrictDisjointPaths (spatialListSupport b k m (witnessLabels code.2 (0::code.1)))
      ((witnessLabels code.2 (0::code.1)).map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)}
  have hsub : {ω | SpatialBadPath (fun e => τ e ω) b m₀ ((am+ap)/2) η k m N} ≤ᵐ[P]
      ⋃ code ∈ codes,E code := by
    filter_upwards [henv.ae_positive] with ω hp hbad
    obtain ⟨is,his,ns,hns,hlen,hD⟩ := spatial_bad_path_cover (fun e => τ e ω) (fun e => (hp e).le)
      b m₀ am ap K η hb ha hη hgap k m hs hstep hscale₁ hscale₂ N hN hbad
    exact mem_iUnion₂.mpr ⟨(is,ns),mem_product.mpr ⟨his,hns⟩,hlen,hD⟩
  have hE (code : List (ℤ×ℤ) × List ℕ) (hc : code ∈ codes) : P.real (E code) ≤ p₀^(N/16) := by
    have hcomp := (mem_compositionCover ..).mp (mem_product.mp hc).2
    by_cases hlen : (0::code.1).length=code.2.length
    · have hl := witnessLabels_length code.2 (0::code.1) hlen.symm
      rw [hcomp.2] at hl
      have hh := hBK (witnessLabels code.2 (0::code.1))
      rw [hl] at hh
      have hEC : E code ⊆ {ω | StrictDisjointPaths
          (spatialListSupport b k m (witnessLabels code.2 (0::code.1)))
          ((witnessLabels code.2 (0::code.1)).map (spatialWitnessFamily b m₀ am ap K η k m))
          (fun e => τ e ω)} := by
        intro ω hω
        exact hω.2
      exact (measureReal_mono (μ := P) hEC).trans hh
    · have he : E code=∅ := by
        ext ω
        exact ⟨fun h => (hlen h.1).elim,False.elim⟩
      rw [he,measureReal_empty]
      positivity
  have hcard : (codes.card : ℝ) ≤ (196 : ℝ)^N := by
    have hc : codes.card ≤ 196^N := by
      calc
        _ = (spatialItineraries 0 N).card*(compositionCover N (N/16)).card := card_product ..
        _ ≤ 49^N*4^N := Nat.mul_le_mul (spatialItineraries_card 0 N)
          (compositionCover_card N (N/16) (Nat.div_le_self ..))
        _ = 196^N := by rw [← mul_pow]; norm_num
    exact_mod_cast hc
  calc
    _ ≤ P.real (⋃ code ∈ codes,E code) := ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
    _ ≤ ∑ code ∈ codes,P.real (E code) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _code ∈ codes,p₀^(N/16) := sum_le_sum hE
    _ = (codes.card : ℝ)*p₀^(N/16) := by simp
    _ ≤ (196 : ℝ)^N*p₀^(N/16) := mul_le_mul_of_nonneg_right hcard (by positivity)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_WitnessBorelCantelli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK
open Set Finset MeasureTheory Filter

/-- Group the floor exponent by its remainder modulo 16. -/
lemma entropy_geometric_bound (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) (hr1 : r ≤ 1) (N : ℕ) :
    a^N*(r^16)^(N/16) ≤ (r^15)⁻¹*(a*r)^N := by
  have hrem : N%16 ≤ 15 := by have hh := Nat.mod_lt N (by omega : 0<16); omega
  have hp : r^15 ≤ r^(N%16) := pow_le_pow_of_le_one hr.le hr1 hrem
  have hid : (r^16)^(N/16)*r^(N%16)=r^N := by
    rw [← pow_mul,← pow_add]
    congr 1
    have hh := Nat.mod_add_div N 16
    omega
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ a^N*(r^16)^(N/16) by positivity)
  simp only [mul_assoc] at hh
  rw [hid,← mul_pow] at hh
  calc
    _ ≤ (a*r)^N/r^15 := (le_div_iff₀ (pow_pos hr 15)).mpr (by simpa only [mul_assoc] using hh)
    _ = _ := by ring

/-- The exact entropy bound is summable whenever p=r^16 and 196r<1. -/
theorem summable_witness_entropy (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 196*r < 1) :
    Summable (fun N : ℕ => (196 : ℝ)^N*(r^16)^(N/16)) := by
  have hs := (summable_geometric_of_lt_one (show 0 ≤ 196*r by positivity) hsmall).mul_left ((r^15)⁻¹)
  exact hs.of_nonneg_of_le (fun _ => by positivity) (entropy_geometric_bound 196 r (by norm_num) hr hr1)

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Source wi:long-paths at a fixed scale. The same almost-sure event controls
all finite simple paths, rather than a single path chosen in advance. -/
theorem ae_eventually_spatial_long_paths (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b m₀ am ap K η r : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 196*r < 1)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (hBK : ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
      (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ (r^16)^is.length) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      ∀ blocks : List (List Step), ∀ rest : List Step,
      blocks.length=N → (∀ q ∈ blocks, FullSpatialChunk b k m q) →
      (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) →
      ((trace 0 (blocks.flatten++rest)).map traversalEdge).Nodup →
      N*η*(2 : ℝ)^k/2 ≤ defect (fun e => τ e ω) b m₀ ((am+ap)/2) 0 (blocks.flatten++rest) := by
  let _ := henv.probability
  let B (N : ℕ) : Set Ω := {ω | SpatialBadPath (fun e => τ e ω) b m₀ ((am+ap)/2) η k m N}
  have hbound (N : ℕ) (hN : 4 ≤ N) : P.real (B N) ≤ (196 : ℝ)^N*(r^16)^(N/16) :=
    spatial_bad_path_probability henv hshape hrate b m₀ am ap K η (r^16) hb ha hη (by positivity)
      hgap k m hs hstep hscale₁ hscale₂ hBK N hN
  have hsum : Summable (fun N => P.real (B N)) := by
    rw [← summable_nat_add_iff 4]
    have hh := (summable_nat_add_iff 4).mpr (summable_witness_entropy r hr hr1 hsmall)
    exact hh.of_nonneg_of_le (fun _ => measureReal_nonneg) (fun n => hbound (n+4) (by omega))
  have ht : (∑' N, P (B N)) ≠ ⊤ := by
    simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hsum.tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem ht] with ω hω
  filter_upwards [hω] with N hN
  intro blocks rest hlen hfull hrest hsimple
  by_contra hc
  exact hN ⟨blocks,rest,hlen,hfull,hrest,hsimple,lt_of_not_ge hc⟩

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ActualWitnessScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK
open MeasureTheory Filter

/-- All three source deterministic inequalities follow from explicit scale
cutoffs. The crossing constant is the manuscript's 100(1+|a-|+|a+|). -/
lemma witness_scale_inequalities (b m₀ am ap η s L : ℝ) (hm : 0 < m₀)
    (hη : 0 < η) (hη1 : η ≤ 1) (hs : 2 ≤ s)
    (hS : max |m₀-((am+ap)/2)*b| |(am+ap)/2| / η ≤ s)
    (hD : ((η+2*|(am+ap)/2|+1)/m₀)*s ≤ L) :
    max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*s ∧
    η*s < 2*m₀*L-|(am+ap)/2| *(s+1) ∧
    3*η*s+2*|(am+ap)/2| *(s+1) < 100*(1+|am|+|ap|)*s := by
  have hstep := (div_le_iff₀ hη).mp hS
  have hD' := mul_le_mul_of_nonneg_left hD hm.le
  have he : m₀*((η+2*|(am+ap)/2|+1)/m₀*s)=(η+2*|(am+ap)/2|+1)*s := by field_simp
  rw [he] at hD'
  have hA : 2*|(am+ap)/2| ≤ |am|+|ap| := by
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    linarith [abs_add_le am ap]
  have hAs := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ s+1)
  have hηs := mul_le_mul_of_nonneg_right hη1 (by linarith : 0 ≤ s)
  have haS := mul_nonneg (abs_nonneg am) (by linarith : 0 ≤ s-1)
  have hapS := mul_nonneg (abs_nonneg ap) (by linarith : 0 ≤ s-1)
  have hmidS := mul_nonneg (abs_nonneg ((am+ap)/2)) (by linarith : 0 ≤ s-1)
  refine ⟨by nlinarith,?_,?_⟩ <;> nlinarith [abs_nonneg am,abs_nonneg ap,abs_nonneg ((am+ap)/2),mul_pos hη (by linarith : 0<s)]

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Construct one genuine characteristic scale satisfying both the deterministic
source constraints and actual spatial BK with an explicit entropy parameter. -/
theorem gamma_witness_scale (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (b η : ℝ)
    (hb : |b| ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ k m : ℕ, 2 ≤ (2 : ℝ)^k ∧
      max |(gammaMeanNorm henv hshape hrate) (direction b)-
        ((extremeSlope (gammaMeanNorm henv hshape hrate) b false+extremeSlope (gammaMeanNorm henv hshape hrate) b true)/2)*b|
        |(extremeSlope (gammaMeanNorm henv hshape hrate) b false+extremeSlope (gammaMeanNorm henv hshape hrate) b true)/2| ≤ η*(2 : ℝ)^k ∧
      η*(2 : ℝ)^k < 2*(gammaMeanNorm henv hshape hrate) (direction b)*(2 : ℝ)^m-
        |(extremeSlope (gammaMeanNorm henv hshape hrate) b false+extremeSlope (gammaMeanNorm henv hshape hrate) b true)/2| *((2 : ℝ)^k+1) ∧
      3*η*(2 : ℝ)^k+2*|(extremeSlope (gammaMeanNorm henv hshape hrate) b false+extremeSlope (gammaMeanNorm henv hshape hrate) b true)/2| *((2 : ℝ)^k+1)
        < sourceCrossingK shape rate (gammaMeanNorm henv hshape hrate) b*(2 : ℝ)^k ∧
      ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
        (is.map (spatialWitnessFamily b ((gammaMeanNorm henv hshape hrate) (direction b))
          (extremeSlope (gammaMeanNorm henv hshape hrate) b false) (extremeSlope (gammaMeanNorm henv hshape hrate) b true)
          (sourceCrossingK shape rate (gammaMeanNorm henv hshape hrate) b) η k m)) (fun e => τ e ω)} ≤
        (((1 : ℝ)/1024)^16)^is.length := by
  let μ := (gammaMeanNorm henv hshape hrate)
  let am := extremeSlope μ b false
  let ap := extremeSlope μ b true
  let a := (am+ap)/2
  let m₀ := μ (direction b)
  let q₀ : ℝ := ((1/1024)^16)/2
  have hq : 0 < q₀ := by dsimp [q₀]; positivity
  have hq1 : q₀ < 1 := by dsimp [q₀]; norm_num
  let S := max 2 (max |m₀-a*b| |a| / η)
  let D := (η+2*|a|+1)/m₀
  obtain ⟨k,hk,hs,hd,hBK⟩ := gamma_spatial_witness_BK_scales henv hshape hrate b q₀ η hb hq hq1 hη 0 S D
  let m := characteristicExponent P τ shape rate μ b q₀ k
  have hpow : (characteristicLength P τ shape rate μ b q₀ k : ℝ)=(2 : ℝ)^m := by
    simp [characteristicLength,m]
  rw [hpow] at hd
  have hs2 : 2 ≤ (2 : ℝ)^k := (le_max_left _ _).trans hs
  have hsC : max |m₀-a*b| |a| / η ≤ (2 : ℝ)^k := (le_max_right _ _).trans hs
  obtain ⟨hstep,hscale₁,hscale₂⟩ := witness_scale_inequalities b m₀ am ap η ((2 : ℝ)^k) ((2 : ℝ)^m)
    (norm_direction_pos μ (gammaMeanNorm_laws henv hshape hrate) b) hη hη1 hs2 hsC hd
  have hK : 100*(1+|am|+|ap|) ≤ sourceCrossingK shape rate μ b := by
    dsimp [am,ap]
    unfold sourceCrossingK
    nlinarith [abs_nonneg (coordinateAllowance shape rate)]
  have hscale₂Gamma := hscale₂.trans_le
    (mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ 2^k))
  refine ⟨k,m,hs2,hstep,hscale₁,hscale₂Gamma,?_⟩
  intro is
  have hh := hBK is
  have he : 2*q₀=((1 : ℝ)/1024)^16 := by dsimp [q₀]; ring
  rw [he] at hh
  exact hh

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_NoCornerContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK
open Set Filter MeasureTheory
open scoped Topology

/-- The source no-corner contradiction, using actual near-optimal simple paths
and the cut-number bound. No geodesic existence or selected-path limit is assumed. -/
theorem long_paths_contradict_directional_limit (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ a η : ℝ) (hb : |b| ≤ 1) (hη : 0 < η) (k m : ℕ)
    (hlim : Tendsto (fun n : ℕ => passageTime w 0 ((n : ℤ),⌊b*(n : ℝ)⌋)/(n : ℝ)) atTop (𝓝 m₀))
    (hlong : ∀ᶠ N : ℕ in atTop, ∀ blocks : List (List Step), ∀ rest : List Step,
      blocks.length=N → (∀ q ∈ blocks, FullSpatialChunk b k m q) →
      (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) →
      ((trace 0 (blocks.flatten++rest)).map traversalEdge).Nodup →
      N*η*(2 : ℝ)^k/2 ≤ defect w b m₀ a 0 (blocks.flatten++rest)) : False := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hlong
  let A := η*(2 : ℝ)^k
  let L := (2 : ℝ)^m
  let δ := A/(8*L)
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : 8*L*δ=A := by dsimp [δ]; field_simp
  have hup := hlim.eventually (gt_mem_nhds (show m₀ < m₀+δ by linarith))
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hnlarge := hnat.eventually (eventually_gt_atTop (((N₀ : ℝ)+1)*2*L))
  have hnC := hnat.eventually (eventually_gt_atTop ((A/2+|a|+1)/δ))
  have hnpos := hnat.eventually (eventually_gt_atTop (0 : ℝ))
  obtain ⟨n,hnup,hnlarge,hnC,hnpos⟩ := (hup.and (hnlarge.and (hnC.and hnpos))).exists
  obtain ⟨ds,hend,hsimple,_hmin,hcost⟩ := GammaFPP.LoopErase.exists_near_optimal_simple_path w hw 0 ((n : ℤ),⌊b*(n : ℝ)⌋) 1 (by norm_num)
  have hdisp : displacement ds=((n : ℤ),⌊b*(n : ℝ)⌋) := by simpa using hend
  obtain ⟨blocks,rest,heq,hfull,hrest⟩ := spatial_chunk_decomposition b k m ds
  have hcut := spatial_chunk_displacement_bound b hb k m blocks rest hfull hrest
  rw [← heq,hdisp] at hcut
  have hcutR : (n : ℝ) ≤ 2*L*((blocks.length : ℝ)+1) := by
    have hh : (n : ℤ) ≤ 2*(2 : ℤ)^m*((blocks.length : ℤ)+1) := by simpa using hcut
    dsimp [L]
    exact_mod_cast hh
  have hN : N₀ ≤ blocks.length := by
    by_contra hh
    have hl : ((blocks.length : ℝ)+1) ≤ N₀ := by exact_mod_cast (show blocks.length+1 ≤ N₀ by omega)
    have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*L by positivity)
    nlinarith
  have hlow := hN₀ blocks.length hN blocks rest rfl hfull hrest (by rw [← heq]; exact hsimple)
  have hloA : (blocks.length : ℝ)*A/2 ≤ defect w b m₀ a 0 ds := by
    rw [← heq] at hlow
    simpa only [A,mul_assoc] using hlow
  have hr : |(⌊b*(n : ℝ)⌋ : ℝ)-b*n| ≤ 1 := by
    apply abs_le.mpr
    have hl := Int.floor_le (b*(n : ℝ))
    have hu := Int.lt_floor_add_one (b*(n : ℝ))
    constructor <;> linarith
  have hab : |a*((⌊b*(n : ℝ)⌋ : ℝ)-b*n)| ≤ |a| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left hr (abs_nonneg a)
  have hsupport : m₀*n-|a| ≤ support b m₀ a (displacement ds) := by
    rw [hdisp]
    simp only [support,transverse,Int.cast_natCast]
    linarith [(abs_le.mp hab).1]
  have hpass : passageTime w 0 ((n : ℤ),⌊b*(n : ℝ)⌋) < (m₀+δ)*n := (div_lt_iff₀ hnpos).mp hnup
  have hupper : defect w b m₀ a 0 ds < δ*n+|a|+1 := by
    unfold defect
    nlinarith
  have hcutδ := mul_le_mul_of_nonneg_left hcutR hδ.le
  have hδN := congrArg (fun x : ℝ => x*((blocks.length : ℝ)+1)) hδeq
  have hC : A/2+|a|+1 < δ*n := by
    have hh := (div_lt_iff₀ hδ).mp hnC
    nlinarith
  nlinarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ActualNoCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK
open MeasureTheory Filter
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem gamma_no_corner (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (b : ℝ) (hb : |b| ≤ 1) :
    extremeSlope (gammaMeanNorm henv hshape hrate) b false=extremeSlope (gammaMeanNorm henv hshape hrate) b true := by
  let _ := henv.probability
  let μ := (gammaMeanNorm henv hshape hrate)
  let am := extremeSlope μ b false
  let ap := extremeSlope μ b true
  have horder : am ≤ ap := by
    exact extreme_slopes_ordered _ (convex_transverse_profile μ (direction b) transverseUnit
      (gammaMeanNorm_laws henv hshape hrate).triangle (norm_positive_homogeneous μ (gammaMeanNorm_laws henv hshape hrate)))
  change am=ap
  by_contra hneq
  have hgap0 : 0 < (ap-am)/8 := by have hh := lt_of_le_of_ne horder hneq; linarith
  let η := min 1 ((ap-am)/8)
  have hη : 0 < η := lt_min (by norm_num) hgap0
  have hη1 : η ≤ 1 := min_le_left ..
  have hgap : 4*η ≤ (ap-am)/2 := by have hh := min_le_right (1 : ℝ) ((ap-am)/8); nlinarith
  obtain ⟨k,m,hs,hstep,hscale₁,hscale₂,hBK⟩ := gamma_witness_scale henv hshape hrate b η hb hη hη1
  have hlong := ae_eventually_spatial_long_paths henv hshape hrate b (μ (direction b)) am ap (sourceCrossingK shape rate μ b) η
    ((1 : ℝ)/1024) hb horder hη (by norm_num) (by norm_num) (by norm_num)
    hgap k m hs hstep hscale₁ hscale₂ hBK
  obtain ⟨ω,hp,hl,hh⟩ := (henv.ae_positive.and ((gamma_direction_nat_limit henv hshape hrate b).and hlong)).exists
  exact long_paths_contradict_directional_limit (fun e => τ e ω) (fun e => (hp e).le)
    b (μ (direction b)) ((am+ap)/2) η hb hη k m hl hh

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Differentiability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Differentiability for Gamma weights

Theorem `thm:gamma-differentiability` of
*Strict convexity and differentiability of the planar exponential first-passage limit shape*.
The almost-sure passage-time limit is asserted for each fixed real direction.
-/

namespace GammaFPP
open PlanarFPP MeasureTheory

/-- Differentiability and regular C¹ boundary charts for planar Gamma first-passage percolation. -/
theorem gamma_differentiability_oai : GammaDifferentiabilityTarget := by
  intro shape rate hs hr Ω _ P τ h
  have hnc : Analytic.NoCornerWedge (gammaMeanNorm h hs hr) := by
    intro b hb
    simpa [PlanarFPP.extremeSlope] using
      CrossingBridge.gamma_no_corner h hs hr b hb
  exact Analytic.gammaMeanNorm_target_conjunction_of_inputs h hs hr
    (h.isTimeConstant hs hr) hnc

end GammaFPP

end OAI
end

theorem solution : type_of% @OAI.GammaFPP.gamma_differentiability_oai := @OAI.GammaFPP.gamma_differentiability_oai

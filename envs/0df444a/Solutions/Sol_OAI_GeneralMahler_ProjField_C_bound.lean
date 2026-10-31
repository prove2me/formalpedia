-- Prove2me | solution 1 for OAI.GeneralMahler.ProjField.C_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:41:28.990199+00:00
-- url     : https://prove2.me/submissions/c910b22b-5eb0-4c3f-85b4-e69a33d70577

import Mathlib
import Definitions.Def_GeneralMahler
import Definitions.Def_OAIQ026G002
import Theorems.Thm_OAI_GeneralMahler_ProjField_budget

section
-- module Solutions.OAIQ026_GM.Compat
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Cone
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive dual cones and their Laplace integrals (paper Piece 2, §01)

The measure is ordinary Lebesgue (statements proved for any compatible
Lebesgue normalization where useful). "ProperCone" here is Mathlib's
closed cone containing zero; the extra paper hypotheses (solid and
contains no line) are imposed as needed. In the main application both
C and its positive dual have specified interior points.
-/

noncomputable section

open Filter Set MeasureTheory MeasureTheory.Measure Metric Real
open scoped ENNReal NNReal Topology Pointwise RealInnerProductSpace

namespace GeneralMahler

section Cone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]

theorem chi_pos {C : ProperCone ℝ E} (hs : (interior (C:Set E)).Nonempty)
    {V : E} (hV : V ∈ interior (posDual C : Set E)) :
    0 < chi C V := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?hn (chi_integrable hV)).mpr
  case hn => exact ae_of_all _ fun x => (Real.exp_pos _).le
  apply lt_of_lt_of_le (isOpen_interior.measure_pos volume hs)
  apply measure_mono
  exact fun x hx => ⟨(Real.exp_pos _).ne', interior_subset hx⟩

end Cone
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Growth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Elementary bounds used throughout the Gaussian and layer integrations.
We keep pointwise growth and measurability hypotheses separate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Real
open scoped Topology ENNReal RealInnerProductSpace NNReal
namespace GeneralMahler
section
variable {X Y E F : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

namespace PolyBound

variable {f g : X → E}
theorem prodMk {h : X → F} (hf : PolyBound f) (hh : PolyBound h) :
    PolyBound fun x => (f x,h x) := by
  obtain ⟨C,n,hc,hb⟩ := common hf hh
  exact ⟨C,n,hc,fun x => max_le (hb x).1 (hb x).2⟩
end PolyBound
end

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_IBP
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Integration-by-parts formula for the normal measure.
Derived by differentiating translations; includes Lipschitz projections. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Filter Topology Set Real WithLp
open scoped RealInnerProductSpace ENNReal NNReal
namespace GeneralMahler
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem smoothG_derivative_lipschitz {f : Rn n → F} {K : ℝ≥0} (h : LipschitzWith K f)
    (a : Rn n) :
    Integrable (fun x => fderiv ℝ f (x+a)) (normal n) ∧
      HasFDerivAt (smoothG f) (∫ x, fderiv ℝ f (x+a) ∂normal n) a := by
  have H : ∀ᵐ x ∂volume, DifferentiableAt ℝ f x := h.ae_differentiableAt
  have hh : ∀ᵐ x ∂normal n, DifferentiableAt ℝ f (x+a) :=
    normal_ac.ae_le ((measurePreserving_add_right volume a).quasiMeasurePreserving.tendsto_ae.eventually H)
  refine smoothG_translate_derivative (PolyBound.lipschitz h) h.continuous a
    (hh.mono fun x hx => hx.hasFDerivAt) (g := fun x => K) (integrable_const _) ?_
  intro x b _
  simpa only [← dist_eq_norm, dist_add_left] using h.dist_le_mul (x+b) (x+a)

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Rapid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Polynomial growth and rapid layer decay with polynomial loss in
the Gaussian variables. Fubini and moment estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real ProbabilityTheory
open scoped ENNReal NNReal Topology Pointwise
namespace GeneralMahler
section
variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

section Integrals
variable [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsAddHaarMeasure μ]

variable [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  {ν : Measure Y} [IsGaussian ν]

lemma mixed_integrable {f : X → Y → E}
    (h : mixed f) (hf : AEStronglyMeasurable f.uncurry (μ.prod ν)) :
    Integrable f.uncurry (μ.prod ν) := by
  let p := Module.finrank ℝ X+1
  let g := fun x:X => ((1+‖x‖)^p)⁻¹
  obtain ⟨C,l,hc,H⟩ := h p
  have hg : Integrable g μ := envelope_inv_int
  have hi := (hg.mul_prod ((integrable_envelope l (μ := ν)).const_mul C))
  apply hi.mono' hf (ae_of_all _ ?_)
  rintro ⟨x,y⟩
  change ‖f x y‖ ≤ g x * (C*(1+‖y‖)^l)
  dsimp only [g]; rw [ mul_comm, ← div_eq_mul_inv,le_div_iff₀ (by positivity)]
  apply H
end Integrals
end
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_pRapid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar tail estimates near §02. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped ENNReal NNReal Topology
namespace GeneralMahler

namespace Layers

-- ratio p/a used in μ tail moment proof
lemma ratio_bound : PolyBound (fun x => p x / a x) := by
  obtain ⟨C,hc,h⟩ := p_small
  have h₀ := a_pos 0
  let k := C*exp 4+(a 0)⁻¹
  refine ⟨k,2,by dsimp [k]; positivity,?_⟩
  intro x
  have he : 0 < a x := a_pos x
  rw [Real.norm_of_nonneg (div_nonneg (p_pos _).le he.le)]
  rcases le_total x 0 with hx|hx
  · have h1 := a_low (-x) (by linarith)
    have h2 := h (-x) (by linarith)
    simp only [neg_neg,neg_phi] at h1 h2
    have hp : 0 < 1 + -x := by linarith
    apply le_trans _ (show C*exp 4*(1+ -x)^2 ≤ k*(1+‖x‖)^2 by
      rw [Real.norm_eq_abs,abs_of_nonpos hx]; unfold k; gcongr; simp [h₀.le])
    rw [div_le_iff₀ he]
    have he' : phi x ≤ ((1+ -x)^2*exp 4)*a x := by
      rw [Real.exp_neg (4:ℝ)] at h1
      have hv := Real.exp_pos (4:ℝ)
      field_simp at h1
      linarith
    apply h2.trans
    have hu := mul_le_mul_of_nonneg_right he' hc.le
    linarith
  · have h' : p x / a x ≤ 1/a 0 := by
      gcongr
      · exact (p_lt_one _).le
      · exact a_mono.monotone hx
    apply h'.trans
    have hr : 0 ≤ C*exp 4 := by positivity
    have hv := norm_nonneg x
    dsimp only [k]; rw [one_div]
    have hd : 1 ≤ (1+‖x‖)^2 := by nlinarith
    nlinarith [inv_pos.mpr h₀]
end Layers
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Mills
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §03 scalar log-Jacobian weights. Antitonicity of W via an
elementary argument that integration from -∞ preserves log concavity. -/
noncomputable section
open MeasureTheory Set Real Filter Metric
open scoped Topology NNReal ENNReal
namespace GeneralMahler
namespace Layers

lemma pbot : Tendsto p atBot (𝓝 0) := by
  apply Tendsto.congr' _ rapid_p.tail_limit_bot
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  simp [st,hx]
lemma ptop : Tendsto p atTop (𝓝 1) := by
  have h := pbot.comp tendsto_neg_atTop_atBot
  have he : Tendsto (fun x:ℝ=>1-(p∘fun x:ℝ=>-x) x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h (a := (1:ℝ))
  simpa [Function.comp_def,neg_p] using he

lemma abot (g:ℝ→ℝ) (h : PolyBound g) :
    Tendsto (fun z=>a z*g z) atBot (𝓝 0) := by
  have h₁ := (rapid_phi.product h).tail_limit_bot
  have h₂ := (rapid_p.product (PolyBound.id.mul h)).tail_limit_bot
  have h := h₁.add h₂; rw [zero_add] at h
  apply Tendsto.congr' _ h
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  simp [st,not_le_of_gt hx,a]; ring
lemma abot' : Tendsto a atBot (𝓝 0) := by
  simpa using abot _ (PolyBound.const 1)

lemma mc_pos (x:ℝ) : 0 < MillsC x := div_pos (phi_pos _) (p_pos _)
lemma mj_eq (x:ℝ) : MillsJ x = a x/p x := by
  have hp := (p_pos x)
  unfold a MillsJ MillsC
  field_simp
  ring
lemma mj_pos (x : ℝ) : 0 < MillsJ x := by rw [mj_eq]; exact div_pos (a_pos _) (p_pos _)
lemma mw_pos (x : ℝ) : 0 < MillsW x := mul_pos (mj_pos _) (mc_pos _)

lemma d_mc (x : ℝ) : HasDerivAt MillsC (-MillsW x) x := by
  convert (d_phi x).div (d_p x) (p_pos x).ne' using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (simp only [MillsW,MillsC,MillsJ]; have h:=p_pos x; field_simp; ring)
lemma d_mj (x:ℝ) : HasDerivAt MillsJ (1-MillsW x) x := by
  rw [sub_eq_add_neg]
  exact (hasDerivAt_id' x).add (d_mc x)
lemma d_mw (x:ℝ) : HasDerivAt MillsW (MillsC x*((1-MillsW x)-MillsJ x^2)) x := by
  convert (d_mj x).mul (d_mc x) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (unfold MillsW; ring)

lemma c_mc : Continuous MillsC := continuous_iff_continuousAt.mpr fun x => (d_mc x).continuousAt
lemma c_mj : Continuous MillsJ := continuous_iff_continuousAt.mpr fun x => (d_mj x).continuousAt
lemma c_mw : Continuous MillsW := continuous_iff_continuousAt.mpr fun x => (d_mw x).continuousAt
lemma mc_anti : StrictAnti MillsC :=
  strictAnti_of_deriv_neg (fun x=>by rw [(d_mc x).deriv]; exact neg_lt_zero.mpr (mw_pos _))

-- log-concavity of p implies that of its primitive a and again of ∫a
lemma mw_le (x:ℝ) : MillsW x ≤ 1 := by
  let f := fun y=> p y-MillsC x*a y
  have hd (y) : HasDerivAt f (phi y-MillsC x*p y) y := (d_p y).sub ((d_a y).const_mul _)
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun y=> (hd y).continuousAt
  have h : MonotoneOn f (Iic x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic _) hc.continuousOn
      (fun y _=> (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    have hy' : y≤x := mem_Iic.mp (interior_subset hy)
    rw [(hd y).deriv]
    have hi := mc_anti.antitone hy'
    change MillsC x ≤ phi y/p y at hi
    rw [le_div_iff₀ (p_pos _)] at hi
    linarith
  have hi : Tendsto f atBot (𝓝 0) := by
    have he := pbot.sub (abot'.const_mul (MillsC x))
    simpa [f] using he
  have hh : 0 ≤ f x := le_of_tendsto hi (by filter_upwards [eventually_le_atBot x] with y hy; exact h hy (mem_Iic.mpr (le_refl _)) hy)
  change 0 ≤ _-_ at hh
  rw [MillsW, mj_eq, div_mul_eq_mul_div, div_le_iff₀ (p_pos x)]
  linarith
lemma mj_mono : Monotone MillsJ := by
  apply monotone_of_deriv_nonneg
  · exact fun x=> (d_mj x).differentiableAt
  intro x; rw [(d_mj x).deriv]; linarith [mw_le x]
lemma mw_anti : Antitone MillsW := by
  apply antitone_of_deriv_nonpos (fun x=> (d_mw x).differentiableAt)
  intro x
  let b := fun y=> (p y + y*a y)/2
  have hb (y) : HasDerivAt b (a y) y := by
    convert ((d_p y).add ((hasDerivAt_id' y).mul (d_a y))).div_const 2 using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (simp only [one_mul,a]; ring)
  let f := fun y=> MillsJ x*a y - b y
  have hd (y) : HasDerivAt f (MillsJ x*p y - a y) y :=
    ((d_a y).const_mul _).sub (hb y)
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun y=> (hd y).continuousAt
  have h : MonotoneOn f (Iic x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic _) hc.continuousOn
      (fun y _=> (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    have hy' : y≤x := mem_Iic.mp (interior_subset hy)
    rw [(hd y).deriv]
    have hi := mj_mono hy'
    rw [mj_eq y,div_le_iff₀ (p_pos _)] at hi
    linarith
  have hu : Tendsto b atBot (𝓝 0) := by
    have hv := (pbot.add (abot _ PolyBound.id)).div_const 2
    simpa [b,mul_comm] using hv
  have hi : Tendsto f atBot (𝓝 0) := by simpa [f] using (abot'.const_mul (MillsJ x)).sub hu
  have hh : 0 ≤ f x := le_of_tendsto hi (by filter_upwards [eventually_le_atBot x] with y hy; exact h hy (mem_Iic.mpr (le_refl _)) hy)
  rw [(d_mw x).deriv]
  apply mul_nonpos_of_nonneg_of_nonpos (mc_pos _).le
  change 0 ≤ MillsJ x*a x-(p x+x*a x)/2 at hh
  unfold MillsW
  rw [mj_eq]; rw [mj_eq] at hh
  unfold MillsC
  have hl := p_pos x
  field_simp at hh ⊢
  have he : a x=phi x+x*p x := rfl
  rw [show phi x=a x-x*p x from by linarith]
  nlinarith

lemma mc_lip : LipschitzWith 1 MillsC := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact fun x=> (d_mc x).differentiableAt
  intro x
  rw [(d_mc x).deriv,nnnorm_neg]

  apply NNReal.coe_le_coe.mp
  simpa [Real.norm_of_nonneg (mw_pos x).le] using mw_le x
lemma poly_mc : PolyBound MillsC := PolyBound.lipschitz mc_lip
lemma poly_mj : PolyBound MillsJ := PolyBound.id.add poly_mc
lemma poly_mw : PolyBound MillsW := poly_mj.mul poly_mc

lemma rapid_mcs : rapid (fun x=> MillsC x * st x) := by
  apply (rapid_phi.product (PolyBound.const (2:ℝ))).mono
  intro x
  unfold st; split_ifs with hx
  · rw [mul_one,Real.norm_of_nonneg (mc_pos _).le,
      Real.norm_of_nonneg (mul_nonneg (phi_pos x).le (by norm_num))]
    have hh := p_mono.monotone hx
    rw [p_half] at hh
    unfold MillsC
    rw [div_le_iff₀ (p_pos x)]
    nlinarith [phi_pos x]
  simp
lemma rapid_mws : rapid (fun x=> MillsW x * st x) := by
  convert rapid_mcs.product poly_mj using 1
  all_goals try with_reducible_and_instances rfl
  ext x; unfold MillsW; ring

lemma limit_mc : Tendsto MillsC atTop (𝓝 0) := by
  have h := rapid_phi.tail_limit.div ptop one_ne_zero
  rw [zero_div] at h; exact h

lemma mw_tail (x:ℝ) : IntegrableOn MillsW (Ioi x) ∧
    (∫ z in Ioi x, MillsW z)=MillsC x := by
  have he (x:ℝ) : HasDerivAt (-MillsC) (MillsW x) x := by simpa using (d_mc x).neg
  have h : Tendsto (-MillsC) atTop (𝓝 0) := by have h:= limit_mc.neg; rw [neg_zero] at h; exact h
  have hi := integrableOn_Ioi_deriv_of_nonneg' (a:=x) (fun z _=>he z) (fun z _=>(mw_pos z).le) h
  refine ⟨hi,?_⟩
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (fun z _=>he z) hi h
end Layers
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MillsLog
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Polynomial bounds and primitive integrations for log profiles. -/
noncomputable section
open MeasureTheory Filter Set Real Metric
open scoped Topology NNReal ENNReal
namespace GeneralMahler

namespace Layers
lemma d_lc (x:ℝ) : HasDerivAt LC (-MillsJ x) x := by
  convert (d_mc x).log (mc_pos x).ne' using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (unfold MillsW; field_simp [ne_of_gt (mc_pos x)])
lemma c_lc : Continuous LC := continuous_iff_continuousAt.mpr fun x => (d_lc x).continuousAt
lemma poly_lc : PolyBound LC := poly_of_d d_lc poly_mj.neg
lemma d_lp (x:ℝ) : HasDerivAt LP (MillsC x) x :=
  (d_p x).log (p_pos x).ne'
lemma c_lp : Continuous LP := continuous_iff_continuousAt.mpr fun x=> (d_lp x).continuousAt
lemma poly_lp : PolyBound LP := poly_of_d d_lp poly_mc

lemma int_lp : Integrable (fun x=>phi x*LP x) :=
  (rapid_phi.product poly_lp).integrable_real (c_phi.measurable.mul c_lp.measurable)
lemma int_lc : Integrable (fun x=>phi x*LC x) :=
  (rapid_phi.product poly_lc).integrable_real (c_phi.measurable.mul c_lc.measurable)

lemma logp_average : (∫ x,phi x*LP x)=-1 := by
  let f := fun x=>p x*LP x-p x
  have hd (x:ℝ) : HasDerivAt f (phi x*LP x) x := by
    convert ((d_p x).mul (d_lp x)).sub (d_p x) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (unfold MillsC; field_simp [ne_of_gt (p_pos x)]; ring)
  have ha : Tendsto f atBot (𝓝 0) := by
    have h := ((rapid_p.product poly_lp).tail_limit_bot).sub pbot
    rw [sub_zero] at h
    apply Tendsto.congr' _ h
    filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx; simp [f,st,not_le_of_gt hx]
  have hb : Tendsto f atTop (𝓝 (-1)) := by
    have h : Tendsto LP atTop (𝓝 0) := by have h := ptop.log one_ne_zero; rw [Real.log_one] at h; exact h
    simpa [f] using (ptop.mul h).sub ptop
  simpa using integral_of_hasDerivAt_of_tendsto hd int_lp ha hb

lemma lc_integral_equiv :
    (∫ x,phi x*LC x) = LC 0 + ∫ x,(p x-st x)*MillsJ x := by
  have h := rapid_p.product poly_mj
  have hm := (cp.measurable.sub measurable_st).mul c_mj.measurable
  have hi := h.integrable_real hm
  let f := fun x=>phi x*LC x-(p x-st x)*MillsJ x
  have hf : Integrable f := int_lc.sub hi
  have hc : Tendsto (fun x=>(p x-st x)*LC x) atBot (𝓝 0) :=
    (rapid_p.product poly_lc).tail_limit_bot
  have hd : Tendsto (fun x=>(p x-st x)*LC x) atTop (𝓝 0) :=
    (rapid_p.product poly_lc).tail_limit
  let F := fun x=>p x*LC x
  let G := fun x=>(p x-1)*LC x
  have hl : (∫ x in Iic 0,f x) = F 0 := by
    have hv : Tendsto F atBot (𝓝 0) := by
      apply Tendsto.congr' _ hc
      filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx; simp [st,not_le_of_gt hx,F]
    have hh := integral_Iic_of_hasDerivAt_of_tendsto
      ((cp.mul c_lc).continuousWithinAt (x:=0)) (a:=0) (f:=F) (f':=f) ?_ hf.integrableOn hv
    · simpa using hh
    intro x hx
    convert (d_p x).mul (d_lc x) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (simp [f,st,not_le_of_gt (mem_Iio.mp hx)]; ring)
  have hr : (∫ x in Ioi 0,f x) = -G 0 := by
    have hv : Tendsto G atTop (𝓝 0) := by
      apply Tendsto.congr' _ hd
      filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx; simp [st,hx,G]
    have hh := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a:=0) (f:=G) (f':=f) ?_ hf.integrableOn hv
    · simpa using hh
    intro x hx
    convert ((d_p x).sub_const 1).mul (d_lc x) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (simp [f,st,mem_Ici.mp hx]; ring)
  have He : (∫ x,f x)=LC 0 := by
    rw [← integral_add_compl measurableSet_Iic hf (s:=Iic (0:ℝ)),compl_Iic,hl,hr]
    unfold F G; ring
  unfold f at He
  rw [integral_sub int_lc hi] at He
  linarith
end Layers
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Profiles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §01 the primary profiles and their identities. -/
noncomputable section
open MeasureTheory Filter Set Real Metric
open scoped Topology NNReal ENNReal
namespace GeneralMahler.Profile
open Layers

lemma q_pos (x:ℝ) : 0<1-p x := sub_pos.mpr (p_lt_one x)
lemma xp (x:ℝ) : 0<X x := div_pos (p_pos x) (phi_pos x)
lemma yp (x:ℝ) : 0<Y x := div_pos (q_pos x) (phi_pos x)
lemma Y_ref (x:ℝ) : Y (-x)=X x := by simp [Y,neg_p,neg_phi,X]
lemma j_ref (x:ℝ) : j (-x)=f x := by simp [j,f,neg_p]
lemma dX (x:ℝ) : HasDerivAt X (Xd x) x := by
  convert (d_p x).div (d_phi x) (phi_pos x).ne' using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (unfold Xd X; field_simp [ne_of_gt (phi_pos x)]; ring)
lemma dY (x:ℝ) : HasDerivAt Y (Yd x) x := by
  convert ((hasDerivAt_const x 1).sub (d_p x)).div (d_phi x) (phi_pos x).ne' using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (simp only [Pi.sub_apply]; unfold Yd Y; field_simp [ne_of_gt (phi_pos x)]; ring)

lemma df (x:ℝ) : HasDerivAt f (fd x) x := by
  convert (((hasDerivAt_const x 1).sub (d_p x)).neg.sub ((d_p x).log (p_pos x).ne')) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (unfold fd; field_simp [ne_of_gt (p_pos x)]; ring)
lemma dj (x:ℝ) : HasDerivAt j (jd x) x := by
  convert ((d_p x).neg.sub (((hasDerivAt_const x 1).sub (d_p x)).log (q_pos x).ne')) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (simp only [Pi.sub_apply]; unfold jd; field_simp [ne_of_gt (q_pos x)]; ring)

lemma v_log (x:ℝ) : v x= -LC x-LC (-x) := by
  have he : X x=(MillsC x)⁻¹ := by unfold X MillsC; rw [inv_div]
  have hh : Y x=(MillsC (-x))⁻¹ := by unfold Y MillsC; rw [neg_p,neg_phi,inv_div]
  rw [v,Real.log_mul (xp x).ne' (yp x).ne',he,hh,LC,LC,Real.log_inv,Real.log_inv]; ring
lemma dV (x:ℝ) : HasDerivAt v (MillsJ x-MillsJ (-x)) x := by
  rw [funext v_log]
  convert ((d_lc x).neg.sub ((d_lc (-x)).comp x (hasDerivAt_neg' x))) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | ring
lemma v_deriv (x:ℝ) : deriv v x=MillsJ x-MillsJ (-x) := (dV x).deriv

lemma C_ids (x:ℝ) :
    X x^2*fd x + Y x^2*jd x = 0 ∧
    X x*Xd x*fd x + Y x*Yd x*jd x = -1 ∧
    Xd x^2*fd x + Yd x^2*jd x = -deriv v x := by
  rw [v_deriv]
  have h₁ := (p_pos x).ne'
  have h₂ := (q_pos x).ne'
  have h₃ := (phi_pos x).ne'
  simp only [Xd,Yd,X,Y,fd,jd,MillsJ,MillsC,neg_p,neg_phi]
  refine ⟨?_,?_,?_⟩ <;> field_simp <;> ring

lemma dg (x:ℝ) : HasDerivAt g (gd x) x := by
  have he := (((hasDerivAt_const x 1).sub (((dX x).pow 2).mul (df x))).sub
    (((dY x).pow 2).mul (dj x))).div_const 2
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (unfold gd; have hi := (C_ids x).1; norm_num; nlinarith)

lemma ddX (x:ℝ) : HasDerivAt Xd (X x+x*Xd x) x := by
  convert (((hasDerivAt_id' x).mul (dX x)).const_add 1) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | ring
lemma ddY (x:ℝ) : HasDerivAt Yd (Y x+x*Yd x) x := by
  convert (((hasDerivAt_id' x).mul (dY x)).sub_const 1) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | ring
lemma ddg (x:ℝ) :
    HasDerivAt (deriv g) (x*deriv g x+2*g x-d x) x := by
  rw [funext fun x=>(dg x).deriv]
  convert (((((dX x).mul (ddX x)).mul (df x)).add ((((dY x).mul (ddY x)).mul (dj x)))).neg)
    using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (unfold gd g d; have hi := (C_ids x).2.1; simp only [Pi.mul_apply]; nlinarith)

lemma dd (x:ℝ) : HasDerivAt d (2*x*d x - deriv v x - 2*deriv g x) x := by
  have he := (((ddX x).pow 2).mul (df x)).add (((ddY x).pow 2).mul (dj x))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | skip
  rw [(dg x).deriv]
  unfold gd d Xd Yd
  have h := (C_ids x).2
  unfold Xd Yd at *
  obtain ⟨h,h'⟩ := h
  norm_num
  nlinarith

lemma ddv (x:ℝ) : HasDerivAt (deriv v) (2-MillsW x-MillsW (-x)) x := by
  simp_rw [funext v_deriv]
  convert ((d_mj x).sub ((d_mj (-x)).comp x (hasDerivAt_neg' x))) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | ring
lemma d₃g (x:ℝ) :
    HasDerivAt (deriv (deriv g)) (3*deriv g x+x*deriv (deriv g) x-deriv d x) x := by
  rw [show deriv (deriv g) = fun x=>x*deriv g x+2*g x-d x from funext fun x=>(ddg x).deriv]
  convert ((((hasDerivAt_id' x).mul (ddg x)).add ((dg x).const_mul 2)).sub (dd x)) using 1
  all_goals try with_reducible_and_instances rfl
  simp_rw [(dd x).deriv,(dg x).deriv]; ring

lemma n_identity (x:ℝ) : N2 g x=d x := by rw [N2,N,(ddg x).deriv]; ring
lemma n_d_identity (x:ℝ) : N d x-deriv (deriv v) x= -N2 (fun t=>d t+deriv (deriv g) t) x := by
  have d' (x:ℝ) := ((dd x).differentiableAt.hasDerivAt)
  have v'' := (ddv x).differentiableAt.hasDerivAt
  have g'' (x:ℝ) := (ddg x).differentiableAt.hasDerivAt
  have h (x:ℝ) : deriv (fun t=>d t+deriv (deriv g) t) x =
      3*deriv g x+x*deriv (deriv g) x := by
    have h := ((d' x).fun_add (d₃g x)).deriv; rw [h]; ring
  have hx : deriv (deriv d) x=2*d x+2*x*deriv d x-deriv (deriv v) x-2*deriv (deriv g) x := by
    rw [funext (fun x=>(dd x).deriv)]
    have hi := (((((hasDerivAt_id' x).const_mul 2).mul (d' x)).sub v'').sub ((g'' x).const_mul 2)).deriv
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (rw [(dd x).deriv] at *; ring)
  unfold N2 N
  rw [funext h,hx]
  have hi := (((g'' x).const_mul 3).fun_add ((hasDerivAt_id' x).mul (d₃g x))).deriv
  change x*deriv d x-_ -_ = -(x*_ - deriv (fun x=>3*deriv g x+x*deriv (deriv g) x) x+_)
  rw [show deriv (fun t=>3*deriv g t+t*deriv (deriv g) t) x=_ from hi]
  ring
end GeneralMahler.Profile

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_TestFun
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Real test functions, all orders of polynomial growth used in the proof. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
namespace GeneralMahler

variable {f g:ℝ→ℝ} {n : ℕ}
namespace Moderate
lemma ref (hf:Moderate n f) : Moderate n fun x=>f (-x) := by
  induction n generalizing f with
  | zero=> exact ⟨hf.poly.comp PolyBound.id.neg,hf.dc.comp continuous_neg⟩
  | succ n ih=>
    apply mk' (g:=fun x=> -deriv f (-x)) _ (ih hf.der).neg
    intro x
    convert (hf.diff (-x)).hasDerivAt.comp x (hasDerivAt_neg' x) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | ring
end Moderate

namespace TestF
variable (hf:TestF f)
lemma of_d (hf:∀ x,HasDerivAt f (g x) x) (hg:TestF g) : TestF f :=
  fun n=> Moderate.mono (Moderate.mk' hf (hg n))

include hf in lemma add (hg:TestF g) : TestF fun x=> f x+g x := fun n=>(hf n).add (hg n)
include hf in lemma neg : TestF fun x=> -(f x) := fun n=>(hf n).neg
include hf in lemma ref : TestF fun x=> f (-x) := fun n=>(hf n).ref
end TestF

namespace Layers
lemma mc_test : TestF MillsC := by
  intro n; induction n with
  | zero=> exact ⟨poly_mc,c_mc⟩
  | succ n ih=>
    apply Moderate.mk' d_mc
    exact (((Moderate.id n).add ih).mul ih).neg
lemma mj_test : TestF MillsJ := TestF.id.add mc_test
end Layers
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_ProfileGrowth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Profile regularity by derivative recurrences and log tail bounds. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
namespace GeneralMahler.Profile
open Layers

lemma Y_limitbound (x:ℝ) (hx:0≤x) : Y x ≤ (MillsC 0)⁻¹ := by
  have h : MillsC 0 ≤ MillsC (-x) := mc_anti.antitone (by linarith)
  have he : Y x=(MillsC (-x))⁻¹ := by unfold Y MillsC; rw [neg_p,neg_phi,inv_div]
  rw [he]
  apply (inv_le_inv₀ (mc_pos _) (mc_pos _)).mpr h
lemma f_poly : PolyBound f :=
  (((PolyBound.const 1).sub (PolyBound.of_bound (f:=p) 1 (fun x=>by
    rw [Real.norm_of_nonneg (p_pos x).le]; exact (p_lt_one x).le))).neg).sub poly_lp
lemma f_bounds (x:ℝ) : 0 ≤ f x ∧ f x ≤ (1-p x)^2/p x := by
  have hp := p_pos x
  have hh := Real.log_le_sub_one_of_pos hp
  have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hi
  unfold f
  constructor
  · linarith
  calc
    _ ≤ -(1-p x)+(p x)⁻¹-1 := by linarith
    _ = _ := by field_simp; ring

lemma X2f_poly : PolyBound fun x=> X x^2*f x := by
  obtain ⟨C,n,hc,h⟩ := f_poly
  set b := (MillsC 0)⁻¹
  have hb : 0≤b := (inv_pos.mpr (mc_pos _)).le
  refine ⟨b^2*(C+1),n,by positivity,fun x=>?_⟩
  have hh := f_bounds x
  have hp := xp x
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg (X x)) hh.1)]
  by_cases hx:0≤x
  · have hy := Y_limitbound x hx
    have hf : X x^2*f x ≤ b^2 := calc
      _ ≤ X x^2*((1-p x)^2/p x) :=
        mul_le_mul_of_nonneg_left hh.2 (by positivity)
      _ = p x*Y x^2 := by unfold X Y; have h:=p_pos x; field_simp
      _ ≤ b^2 := by
        have h' := yp x
        nlinarith [mul_le_of_le_one_left (sq_nonneg (Y x)) (p_lt_one x).le]
    have h' : (1:ℝ) ≤ (1+‖x‖)^n := one_le_pow₀ (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    apply hf.trans
    apply le_trans _ (show b^2*(C+1) ≤ _ from le_mul_of_one_le_right (by positivity) h')
    nlinarith
  · have hi := Y_limitbound (-x) (by linarith)
    rw [Y_ref] at hi
    have he := h x
    rw [Real.norm_of_nonneg hh.1] at he
    apply le_trans (mul_le_mul (show X x^2 ≤ b^2 by gcongr) he hh.1 (sq_nonneg _))
    rw [← mul_assoc]; gcongr; linarith
lemma Y2j_poly : PolyBound fun x=>Y x^2*j x := by
  have he := X2f_poly.comp PolyBound.id.neg
  simpa only [← Y_ref,← j_ref,neg_neg] using he
lemma X_M (x:ℝ) : Xd x=MillsJ x*X x := by
  unfold Xd X MillsJ MillsC; have h:=phi_pos x; have h':=p_pos x
  field_simp; ring
lemma Y_M (x:ℝ) : Yd x= -MillsJ (-x)*Y x := by
  have h := X_M (-x)
  rw [Xd,← Y_ref,neg_neg] at h
  unfold Yd; linarith
lemma g_poly : PolyBound g := by
  simp only [funext (show ∀ x,g x=(2:ℝ)⁻¹*(1-X x^2*f x-Y x^2*j x) from
    fun x=>by unfold g; ring)]
  exact (PolyBound.const _).mul (((PolyBound.const _).sub X2f_poly).sub Y2j_poly)
lemma gd_poly : PolyBound gd := by
  let H := fun x=>MillsJ (-x)*(Y x^2*j x)-MillsJ x*(X x^2*f x)
  have he : gd=H := by ext x; unfold gd H; rw [X_M,Y_M]; ring
  rw [he]
  exact ((TestF.poly mj_test.ref).mul Y2j_poly).sub (poly_mj.mul X2f_poly)
lemma d_poly : PolyBound d := by
  let H := fun x=>MillsJ x^2*(X x^2*f x)+MillsJ (-x)^2*(Y x^2*j x)
  have he : d=H := by ext x; unfold d H; rw [X_M,Y_M]; ring
  rw [he]
  exact ((poly_mj.pow 2).mul X2f_poly).add (((TestF.poly mj_test.ref).pow 2).mul Y2j_poly)

lemma v_test : TestF v := TestF.of_d dV (mj_test.sub mj_test.ref)
lemma moderate_dg (n : ℕ) :
    Moderate n g ∧ Moderate n (deriv g) ∧ Moderate n d := by
  induction n with
  | zero=>
    refine ⟨⟨g_poly,?_⟩,⟨?_,?_⟩,⟨d_poly,?_⟩⟩
    · exact continuous_iff_continuousAt.mpr fun x=>(dg x).continuousAt
    · rw [show deriv g=gd from funext fun x=>(dg x).deriv]; exact gd_poly
    · exact continuous_iff_continuousAt.mpr fun x=>(ddg x).continuousAt
    exact continuous_iff_continuousAt.mpr fun x=>(dd x).continuousAt
  | succ n ih=>
    obtain ⟨h,h',hi⟩ := ih
    refine ⟨Moderate.mk' (g:=deriv g) (fun x=>(dg x).differentiableAt.hasDerivAt) h',
      Moderate.mk' ddg ?_,Moderate.mk' dd ?_⟩
    · exact (((Moderate.id n).mul h').add ((Moderate.const _ n).mul h)).sub hi
    exact (((((Moderate.const _ n).mul (Moderate.id n)).mul hi).sub (TestF.der v_test n)).sub
      ((Moderate.const _ n).mul h'))
lemma g_test : TestF g := fun n=>(moderate_dg n).1
lemma d_test : TestF d := fun n=>(moderate_dg n).2.2
end GeneralMahler.Profile

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_HMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
### H_f, A, L from Equation (7) and their growth bounds
-/
noncomputable section
open Set Filter Real Matrix MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
open Layers
variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)

variable [NeZero m] {f : ℝ→ℝ} (h : PolyBound (deriv f))

include h in
lemma H_integrable : Integrable (q.Hmat f) (normal m) :=
  (q.H_poly h).gaussian_integrable q.H_SM.aestronglyMeasurable

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Spectral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Order and functional calculus for real symmetric matrices. -/
noncomputable section
open Set Filter Matrix Real
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
variable {m : ℕ} {A B : Mat m}

theorem cfc_eigen' (f : ℝ → ℝ) (h : A.IsHermitian) (i : Fin m) :
    op (cfc f A) (h.eigenvectorBasis i) = (f (h.eigenvalues i)) • h.eigenvectorBasis i := by
  open Unitary in
    rw [Matrix.IsHermitian.cfc_eq h,Matrix.IsHermitian.cfc,conjStarAlgAut_apply]
    apply WithLp.ofLp_injective
    rw [show op = _ from (rfl : op = Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)),
      Matrix.ofLp_toEuclideanCLM]
    simp only [← mulVec_mulVec, h.star_eigenvectorUnitary_mulVec, Matrix.diagonal_mulVec_single,
      Function.comp_apply,mul_one]
    ext j; simp [dotProduct,mulVec, Pi.single_apply,mul_comm]

variable {l r : ℝ}

lemma cfc_herm (f : ℝ→ℝ) (A : Mat m) : (cfc f A).IsHermitian :=
  (cfc_predicate _ _ : IsSelfAdjoint _)

lemma scalar_cfc_order (f : ℝ→ℝ) (A : Mat m) (hA : A.IsHermitian) :
    (scalar m l ≤ cfc f A ↔ ∀ x∈spectrum ℝ A, l ≤ f x) ∧
    (cfc f A ≤ scalar m r ↔ ∀ x∈spectrum ℝ A, f x ≤ r) := by
  rw [scalar_eq,scalar_eq]
  have hi : IsSelfAdjoint A := hA
  have hf : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f
  exact ⟨algebraMap_le_cfc_iff .., cfc_le_algebraMap_iff ..⟩

lemma spectrum_order (A : Mat m) (hA:A.IsHermitian) :
    (scalar m l ≤ A ↔ ∀ x∈spectrum ℝ A, l ≤ x) ∧
    (A ≤ scalar m r ↔ ∀ x∈spectrum ℝ A, x ≤ r) := by
  have hi : IsSelfAdjoint A := hA
  have h := scalar_cfc_order (l := l) (r := r) id A hA
  rw [cfc_id ℝ A] at h
  exact h

lemma spectrum_norm_box {K : ℝ} (hk : 0 ≤ K) (ha : A.IsHermitian)
    (hb : scalar m (-K) ≤ A) (ht : A ≤ scalar m K) : ‖A‖ ≤ K := by
  have hi : IsSelfAdjoint A := ha
  conv_lhs => rw [← cfc_id ℝ A]
  apply norm_cfc_le hk
  intro x hx
  rw [Real.norm_eq_abs,abs_le]; exact ⟨(spectrum_order (l := -K) (r := K) _ ha).1.mp hb x hx,
    (spectrum_order (l := -K) (r := K) _ ha).2.mp ht x hx⟩

lemma spectrum_poly_le (f : ℝ → ℝ) {C : ℝ} {n : ℕ} (hc : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(1+‖x‖)^n) (ha : A.IsHermitian) :
    ‖cfc f A‖ ≤ C*(1+‖A‖)^n := by
  have hi : IsSelfAdjoint A := ha
  apply norm_cfc_le (by positivity)
  intro x hx
  apply (hf _).trans
  have he := norm_apply_le_norm_cfc (id : ℝ → ℝ) A hx
  rw [cfc_id ℝ A] at he
  change ‖x‖ ≤ ‖A‖ at he
  gcongr

lemma cfc_continuous_herm (f : ℝ → ℝ) (hf : Continuous f) :
    ContinuousOn (cfc f) {x : Mat m | x.IsHermitian} :=
  (continuousOn_id.cfc_of_mem_nhdsSet (s := univ) f Filter.univ_mem
    (fun _ h => (h : IsSelfAdjoint _)) hf.continuousOn)

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Update
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02 covariance equation from scalar inequalities of §01. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler

variable {m : ℕ}

lemma sqPSD {A : Mat m} (ha:A.IsHermitian) : 0 ≤ A*A := by
  change IsSelfAdjoint A at ha
  conv_lhs => skip
  simpa only [ha.star_eq] using star_mul_self_nonneg A

namespace ProjField
variable [NeZero m]

theorem intL (q : ProjField m) {f : ℝ→ℝ} (hm : Continuous f) (hf : PolyBound f) :
    Integrable (fun x=>cfc f (q.Lmat x)) (normal m) := by
  have hc : Continuous fun x=>cfc f (q.Lmat x) :=
    (cfc_continuous_herm f hm).comp_continuous q.L_cont q.L_sym
  obtain ⟨C,n,hc',hf⟩ := hf
  let g := fun x => C*(1+‖q.Lmat x‖)^n
  have h : PolyBound g :=
    (PolyBound.const _).mul (((PolyBound.const 1).add q.L_poly.norm).pow _)
  apply PolyBound.gaussian_integrable _ hc.aestronglyMeasurable
  refine h.mono fun x => ?_
  apply le_trans (spectrum_poly_le _ hc' hf (q.L_sym _))
  change g x ≤ ‖g x‖; exact le_abs_self _

lemma expL_sym (q:ProjField m) {f} (hm : Continuous f) (hf : PolyBound f) :
    (expL f q).IsHermitian :=
  hermitian_integral (q.intL hm hf) (ae_of_all _ fun _ => cfc_herm _ _)

lemma expL_affine_pos (q:ProjField m) {C K : ℝ→ℝ} (hc : Continuous C) (hk : Continuous K)
    (hh : PolyBound C) (hh' : PolyBound K) {x y z : ℝ}
    (he : ∀ t, 0 ≤ x + y*C t+z*K t) :
    0 ≤ scalar m x + y•expL C q + z•expL K q := by
  let f (t:Rn m) := scalar m x + y•cfc C (q.Lmat t)+ z•cfc K (q.Lmat t)
  have ic := (q.intL hc hh).smul y
  have ik := (q.intL hk hh').smul z
  have hp (t:Rn m) : 0 ≤ f t := by
    let A := q.Lmat t
    have hi : IsSelfAdjoint A := q.L_sym t
    have hl := cfc_nonneg (f := (fun t:ℝ=>x+y*C t+z*K t)) (a := A) (fun t _=>he t)
    have HE := cfc_add A (fun t => x+y*C t) (fun t=>z*K t)
      (show ContinuousOn _ (spectrum ℝ A) from (continuous_const.add (continuous_const.mul hc)).continuousOn)
      ((continuous_const.mul hk).continuousOn)
    conv at hl =>
      rhs
      rw [show cfc (fun t=>x+y*C t+z*K t) A = _ from HE, cfc_const_add x (fun t=>y*C t) A ((continuous_const.mul hc).continuousOn) hi, cfc_const_mul y C A hc.continuousOn,cfc_const_mul z K A hk.continuousOn, ← scalar_eq]
    exact hl
  have heq : ∫ t, f t ∂normal m = scalar m x + y•expL C q+z•expL K q := by
    unfold f expL
    rw [integral_add, integral_add, integral_smul,integral_smul]
    · simp; exact integral_smul z _
    all_goals first | exact integrable_const _ | exact ic | exact ik |
      exact (integrable_const _).add ic
  rw [← heq]
  apply Matrix.PosSemidef.nonneg
  exact psd_integral (((integrable_const _).add ic).add ik) (ae_of_all _ fun t=>(hp t).posSemidef)

lemma expL_bounds (q:ProjField m) {C K} (h:UpdatesOK C K) :
    expL C q ≤ scalar m cupper ∧
    0 ≤ scalar m (-(ell0^2)-mstar^2)+(2*ell0)•expL C q + (-(4*lam))•expL K q ∧
    0 ≤ scalar m (lam*tmin^2) + tmin • expL C q+ expL K q ∧
    scalar m (lam*tmax^2) + tmax • expL C q+ expL K q ≤ 0 := by
  have he (x y z) (hi : ∀ t, 0≤ x+y*C t+z*K t) := q.expL_affine_pos h.Cc h.Kc h.Cp h.Kp hi
  refine ⟨?_,he _ _ _ (fun t => by linarith [h.tan t]), ?_,?_⟩
  · have hb := he cupper (-1) 0 (fun t=>by linarith [h.C_hi t])
    simpa [sub_eq_add_neg,← sub_nonneg] using hb
  · have hb := he (lam*tmin^2) tmin 1 (fun t=>by linarith [h.lo t])
    simpa only [one_smul] using hb
  · have hb := he (-(lam*tmax^2)) (-tmax) (-1) (fun t=>by linarith [h.hi t])
    rw [← neg_nonneg]
    simpa only [scalar,neg_smul,one_smul,neg_add] using hb
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_TraceOrder
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Matrix trace order calculus for layer inequalities. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}
lemma trN_cyclic (A B:Mat m) : trN (A*B)=trN (B*A) :=
  congrArg (fun x=>(x:ℝ)/m) (Matrix.trace_mul_comm ..)
lemma trN_add (A B:Mat m) : trN (A+B)=trN A+trN B := by unfold trN; rw [trace_add,add_div]
lemma trN_sub (A B:Mat m) : trN (A-B)=trN A-trN B := by unfold trN; rw [trace_sub,sub_div]
lemma trN_smul (a:ℝ) (A:Mat m) : trN (a•A)=a*trN A := by
  unfold trN; rw [trace_smul]; simp; ring
lemma trN_mono {A B:Mat m} (h:A≤B) : trN A≤trN B := by
  have hi := Matrix.le_iff.mp h
  unfold trN
  have he := hi.trace_nonneg
  rw [trace_sub] at he
  gcongr; linarith
lemma sand_nonneg {A B:Mat m} (ha:0≤A) (hb:B.IsHermitian) : 0 ≤ B*A*B := by
  have he := ha.posSemidef.mul_mul_conjTranspose_same B
  rw [show Bᴴ=B from hb] at he; exact he.nonneg

lemma trN_mul_nonneg {A B : Mat m} (ha:0≤A) (hb:0≤B) : 0 ≤ trN (A*B) := by
  let S := CFC.sqrt B
  have hs : S.IsHermitian := (CFC.sqrt_nonneg B).posSemidef.1
  calc
    _ ≤ trN (S*A*S) := by
      simpa [trN] using trN_mono (sand_nonneg ha hs)
    _ = _ := by
      rw [mul_assoc,trN_cyclic S, mul_assoc,show S*S=B from CFC.sqrt_mul_sqrt_self B hb]
lemma trN_mul_mono {A B C:Mat m} (ha:A≤B) (hc:0≤C) : trN (A*C) ≤ trN (B*C) := by
  have h := trN_mul_nonneg (sub_nonneg.mpr ha) hc
  rwa [sub_mul,trN_sub,sub_nonneg] at h

lemma trN_j (A B:Mat m) : trN (jprod A B)=trN (A*B) := by
  rw [jprod,trN_smul,trN_add,trN_cyclic B]
  ring
lemma trN_one [NeZero m] : trN (1:Mat m)=1 := by simp [trN]
lemma trN_unit {A:Mat m} [NeZero m] (h:0≤A) (hh:A≤1) : 0≤trN A ∧ trN A≤1 := by
  have hi := trN_mono h; have he := trN_mono hh
  rw [show trN (0:Mat m)=0 from by simp [trN]] at hi; rw [trN_one] at he
  exact ⟨hi,he⟩
lemma trN_prod_unit {A B:Mat m} [NeZero m] (ha:0≤A) (ha':A≤1)
    (hb:0≤B) (hb':B≤1) : 0≤trN (A*B) ∧ trN (A*B)≤1 := by
  refine ⟨trN_mul_nonneg ha hb,?_⟩
  have h := trN_mul_mono ha' hb
  rw [one_mul] at h
  exact h.trans (trN_unit hb hb').2

lemma thresh_pd {A:Mat m} (h:0≤A) : (1+A).PosDef := Matrix.PosDef.one.add_posSemidef h.posSemidef

lemma inv_mul' {A:Mat m} (ha:A.PosDef) : A⁻¹*A=1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ha.det_pos.ne')
lemma mul_inv' {A:Mat m} (ha:A.PosDef) : A*A⁻¹=1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ha.det_pos.ne')

/-- Order reversal under inversion: prove by nonnegative remainder. -/
lemma inv_rev {A B:Mat m} (ha:A.PosDef) (hb:B.PosDef) (hh:A≤B) : B⁻¹≤A⁻¹ := by
  rw [← sub_nonneg]
  have hs : 0 ≤ (A⁻¹-B⁻¹)*A*(A⁻¹-B⁻¹) :=
    sand_nonneg ha.posSemidef.nonneg (ha.inv.1.sub hb.inv.1)
  have ht := sand_nonneg (sub_nonneg.mpr hh) hb.inv.1
  apply (add_nonneg hs ht).trans_eq
  calc
    _ = (A⁻¹*A)*A⁻¹ - B⁻¹*(A*A⁻¹) - (A⁻¹*A)*B⁻¹ + (B⁻¹*B)*B⁻¹ := by noncomm_ring
    _ = _ := by rw [inv_mul' ha, mul_inv' ha,inv_mul' hb]; simp

lemma thresh_mono {A B:Mat m} (ha:0≤A) (hh:A≤B) : thresh A ≤ thresh B :=
  sub_le_sub_left (inv_rev (thresh_pd ha) (thresh_pd (ha.trans hh)) (by gcongr)) _
lemma thresh_unit {A:Mat m} (ha:0≤A) : 0≤thresh A ∧ thresh A≤1 := by
  constructor
  · have h := thresh_mono (A:= (0:Mat m)) le_rfl ha
    simpa [thresh] using h
  exact sub_le_self _ (thresh_pd ha).inv.posSemidef.nonneg
lemma thresh_eq {A:Mat m} (ha:0≤A) : thresh A=A*(1+A)⁻¹ := by
  have hh := mul_inv' (thresh_pd ha)
  rw [add_mul,one_mul] at hh
  unfold thresh; exact sub_eq_of_eq_add' hh.symm

-- b > 0 upper bound on I+A gives b⁻¹ A ≤ thresh A via eigenvectors or product of commuting
lemma mul_comm_nonneg {A B:Mat m} (ha:0≤A) (hb:0≤B) (hh:Commute A B) :
    0 ≤ A*B := by
  let S := CFC.sqrt B
  have he : Commute A S := by
    unfold S CFC.sqrt
    first | exact (hh.symm.cfc_nnreal _).symm | exact (hh.symm.cfcₙ_nnreal _).symm
  have hp : 0 ≤ S := CFC.sqrt_nonneg _
  calc
    _ ≤ S*A*S := sand_nonneg ha hp.posSemidef.1
    _ = _ := by rw [← he.eq,mul_assoc,show S*S=B from CFC.sqrt_mul_sqrt_self _ hb]

lemma thresh_low {A:Mat m} {b:ℝ} (ha:0≤A) (hb:0<b) (he:1+A ≤ scalar m b) :
    b⁻¹•A ≤ thresh A := by
  have hc : (scalar m b).PosDef :=
    form_posDef hb (show scalar m b∈specBox m b b from ⟨scalar_sym ..,le_rfl,le_rfl⟩)
  have hi := inv_rev (thresh_pd ha) hc he
  have heq : (scalar m b)⁻¹=scalar m b⁻¹ := by
    have hh := scalar_mul (m:=m) b⁻¹ b
    rw [inv_mul_cancel₀ hb.ne',show scalar m 1=1 from one_smul .. ] at hh
    exact ((left_inv_eq_left_inv (inv_mul' hc) hh))
  rw [heq] at hi
  have hb₁ := inv_mul' (thresh_pd ha)
  have hb₂ := mul_inv' (thresh_pd ha)
  have hp : Commute A ((1+A)⁻¹ - scalar m b⁻¹) := by
    have hh : Commute A (1+A)⁻¹ := by
      rw [mul_add,mul_one] at hb₁
      rw [add_mul,one_mul] at hb₂
      exact add_left_cancel (hb₂.trans hb₁.symm)
    exact hh.sub_right (by simp only [scalar_eq]; exact (Algebra.commutes _ _).symm)
  have hu := mul_comm_nonneg ha (sub_nonneg.mpr hi) hp
  rw [mul_sub,← thresh_eq ha] at hu
  rw [scalar,mul_smul_comm,mul_one,sub_nonneg] at hu
  exact hu
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Edge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Deterministic-endcut layer of PSD contractions. Carries the
precise data needed for log-Jacobian estimate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m:ℕ}

variable [NeZero m]
namespace Edge
variable (e:Edge m)
omit [NeZero m] in
lemma r_poly : PolyBound e.radius := (PolyBound.const _).mul
  ((PolyBound.const _).add PolyBound.id.norm)
omit [NeZero m] in
lemma r_pos (x) : 0 < e.radius x := mul_pos (lt_of_lt_of_le zero_lt_one e.hp) (by positivity)
omit [NeZero m] in
lemma Pcont (x y) : ‖e.P x y‖ ≤ 1 := by
  apply spectrum_norm_box zero_le_one (e.psd ..).posSemidef.1
  · apply le_trans _ (e.psd ..)
    have he := scalar_le' (m:=m) (-1) 0 (by norm_num)
    simpa only [scalar, zero_smul] using he
  simpa [scalar] using e.le_one x y
omit [NeZero m] in
lemma P_poly : PolyBound e.P.uncurry := PolyBound.of_bound 1 fun ⟨x,y⟩=>e.Pcont x y

lemma st_poly : PolyBound st := PolyBound.of_bound 1 fun x=>by unfold st; split <;> simp
omit [NeZero m] in
lemma EP_mixed : mixed e.EP := by
  have h : PolyBound (fun x:ℝ × Rn m=> st x.1 • (1:Mat m)) := (st_poly.comp PolyBound.fst).smul
    (PolyBound.const _)
  apply mixed.of_cutoff (e.P_poly.sub h) e.r_poly
  intro x y hx
  unfold EP st; split_ifs with ht
  · rw [e.tend_pos _ _ (by rw [Real.norm_of_nonneg ht] at hx; exact hx),one_smul,sub_self]
  rw [e.tend_neg _ _ (by rw [Real.norm_eq_abs,abs_of_neg (lt_of_not_ge ht)] at hx;exact hx),zero_smul,sub_self]

omit [NeZero m] in
lemma wp_meas : StronglyMeasurable e.WP.uncurry :=
  ((c_mw.measurable.comp measurable_fst).smul e.meas).stronglyMeasurable
omit [NeZero m] in
lemma wp_psd (z x) : 0 ≤ e.WP z x :=
  smul_nonneg (mw_pos z).le (e.psd ..)
omit [NeZero m] in
lemma wp_le (z x) : e.WP z x≤MillsW z•1 :=
  smul_le_smul_of_nonneg_left (e.le_one ..) (mw_pos z).le
lemma WP_mixed : mixed e.WP := by
  let f := fun z (x:Rn m)=> (MillsW z*st z) • (1:Mat m)
  let g := fun z x => MillsW z • e.EP z x
  have hh : e.WP = fun z x=> f z x+ g z x := by
    funext z x; simp only [WP,f,g,EP,mul_smul,smul_sub]; abel
  rw [hh]
  have hi : mixed f := (mixed.of_rapid (Y:=Rn m) rapid_mws).mono
    (fun z x=>by unfold f; rw [norm_smul]; simp)
  apply hi.add
  let H := fun z (_:Rn m) => MillsW z
  have h : PolyBound H.uncurry := poly_mw.comp PolyBound.fst
  exact e.EP_mixed.product h (fun z x=>by unfold g H; rw [norm_smul,mul_comm])
omit [NeZero m] in
lemma wp_slice_SM (x) : StronglyMeasurable (fun z=> e.WP z x) :=
  e.wp_meas.comp_measurable (measurable_id.prodMk measurable_const)
lemma wp_slice_i (x) : Integrable (fun z=>e.WP z x) :=
  mixed_integrable_left e.WP_mixed x (e.wp_slice_SM x).aestronglyMeasurable
omit [NeZero m] in
lemma Jedge_SM : StronglyMeasurable e.Jedge := e.wp_meas.integral_prod_left
lemma Jedge_poly : PolyBound e.Jedge := poly_integral_left e.WP_mixed fun x=> (e.wp_slice_SM x).aestronglyMeasurable
lemma Jedge_bound (x) : scalar m (MillsC (e.radius x)) ≤ e.Jedge x := by
  let a := e.radius x
  have hf := integral_add_compl measurableSet_Iic (e.wp_slice_i x) (s:=Iic a)
  rw [compl_Iic] at hf
  have hh : (∫ z in Ioi a,e.WP z x) = scalar m (MillsC a) := by
    rw [← (mw_tail a).2,scalar,← integral_smul_const]
    exact setIntegral_congr_fun measurableSet_Ioi fun z hz=>by rw [WP,e.tend_pos _ _ hz]
  have hi : (0:Mat m) ≤ ∫ z in Iic a,e.WP z x :=
    (psd_integral (e.wp_slice_i x).integrableOn (ae_of_all _ fun z=>(e.wp_psd z x).posSemidef)).nonneg
  unfold Jedge
  rw [← hf,hh]; exact le_add_of_nonneg_left hi
lemma Jedge_pd (x) : (e.Jedge x).PosDef := by
  let B := scalar m (MillsC (e.radius x))
  have hi : B.PosDef := form_posDef (mc_pos _)
    (show B∈specBox m (MillsC (e.radius x)) (MillsC (e.radius x)) from ⟨scalar_sym ..,le_rfl,le_rfl⟩)
  have hh := Matrix.le_iff.mp (e.Jedge_bound x)
  have h := hi.add_posSemidef hh
  simpa only [B, add_sub_cancel] using h

end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LogDet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Normalized log determinant; derivative and simple growth estimates. -/
noncomputable section
open Finset MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m:ℕ}

lemma det_cdiff : ContDiff ℝ ⊤ (Matrix.det (n:=Fin m) (R:=ℝ)) := by
  simp_rw [funext det_apply']
  apply ContDiff.sum
  intro σ _
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  exact (coeffMap (σ i) i).contDiff

lemma D_log {A:Mat m} (h:A.PosDef) : ContDiffAt ℝ ⊤ logD A :=
  ((det_cdiff.contDiffAt.log h.det_pos.ne').div_const (m:ℝ))
lemma meas_logD : Measurable (@logD m) :=
  (Real.measurable_log.comp det_cdiff.continuous.measurable).div_const _

lemma perm_moves {σ:Equiv.Perm (Fin m)} (h:σ≠1) (i:Fin m) :
    ∃ j≠i,σ j≠j := by
  by_contra! H
  apply h
  ext j : 1
  change σ j=j
  by_contra hh
  have he : σ (σ j) = σ j := H _ (by
    have hi : j=i := by by_contra a; exact hh (H j a)
    rwa [← hi])
  exact hh (σ.injective he)
lemma det_at_I_curve {f:ℝ→Mat m} {B:Mat m} {x:ℝ} (he : f x=1) (h:HasDerivAt f B x) :
    HasDerivAt (fun t:ℝ=>Matrix.det (f t)) B.trace x := by
  classical
  let e (σ : Equiv.Perm (Fin m)) := (((Equiv.Perm.sign σ).val:ℤ):ℝ)
  have hi (σ:Equiv.Perm (Fin m)) :
      HasDerivAt (fun t => e σ * ∏ i, f t (σ i) i)
        (e σ * ∑ i, (∏ j∈(Finset.univ.erase i), f x (σ j) j) * B (σ i) i) x := by
    have hh (i : Fin m) : HasDerivAt (fun t:ℝ=> f t (σ i) i) (B (σ i) i) x :=
      (coeffMap (σ i) i).hasFDerivAt.comp_hasDerivAt x h
    exact (HasDerivAt.fun_finsetProd (u:=Finset.univ) fun i _=> hh i).const_mul _
  have hh := HasDerivAt.fun_sum (u:=Finset.univ) (fun σ _=>hi σ)
  simp_rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (funext x; exact det_apply' _) | skip
  rw [Finset.sum_eq_single_of_mem (1:Equiv.Perm (Fin m)) (Finset.mem_univ _)]
  · simp [e,Matrix.trace,Matrix.one_apply]
  intro b hb he
  suffices h : (∑ i, (∏ j∈(Finset.univ.erase i), (1:Mat m) (b j) j)*B (b i) i)=0 by rw [h,mul_zero]
  apply Finset.sum_eq_zero
  intro i _
  obtain ⟨j,hj,h⟩ := perm_moves he i
  rw [Finset.prod_eq_zero (f:=fun j=>(1:Mat m) (b j) j) (by simp [hj]) (show (1:Mat m) (b j) j=0 from by simp [h]),zero_mul]

lemma deriv_logD {f:ℝ→Mat m} {B:Mat m} {x:ℝ} (h:HasDerivAt f B x) (hh:(f x).PosDef) :
    HasDerivAt (fun t=>logD (f t)) (trN ((f x)⁻¹ * B)) x := by
  let g := fun t => (f x)⁻¹ * f t
  have hi : HasDerivAt g ((f x)⁻¹ * B) x := h.const_mul _
  have he := det_at_I_curve (show g x=1 from inv_mul' hh) hi
  have heq : (fun t=> Matrix.det (f t)) = fun t=> Matrix.det (f x)* Matrix.det (g t) := by
    ext t
    rw [← Matrix.det_mul,show f x*g t=f t from by unfold g; rw [← mul_assoc,mul_inv' hh,one_mul]]
  have hf := he.const_mul (Matrix.det (f x))
  rw [← heq] at hf
  convert (hf.log hh.det_pos.ne').div_const (m:ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (simp only [trN]; field_simp [hh.det_pos.ne'])

lemma logD_sum {A:Mat m} (ha:A.PosDef) :
    logD A=(∑ i,Real.log (ha.1.eigenvalues i))/(m:ℝ) := by
  rw [logD,ha.1.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [Real.log_prod (fun i _=>?_)]
  exact ne_of_gt (ha.eigenvalues_pos i)

lemma logD_between {A:Mat m} [NeZero m] (ha:A.PosDef) {a:ℝ}
    (h:0<a) (hh:scalar m a ≤ A) :
    Real.log a ≤ logD A ∧ logD A ≤ trN A := by
  rw [logD_sum ha,trN,ha.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  constructor
  · rw [le_div_iff₀ ProjField.m_pos]
    have he (i) : Real.log a ≤ Real.log (ha.1.eigenvalues i) := by
      apply Real.log_le_log h
      apply (spectrum_order A ha.1 (l:=a) (r:=a)).1.mp hh
      rw [ha.1.spectrum_real_eq_range_eigenvalues]
      exact ⟨i,rfl⟩
    apply le_trans _ (Finset.sum_le_sum (fun i _=>he i))
    simp; rw [mul_comm]
  gcongr
  have hx := Real.log_le_sub_one_of_pos (ha.eigenvalues_pos i)
  linarith

lemma logD_scalar [NeZero m] {c:ℝ} : logD (scalar m c)=Real.log c := by
  rw [logD,scalar,det_smul, det_one,mul_one,Real.log_pow]
  simp; have h:= ProjField.m_pos (m:=m); field_simp

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scatter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! The cone-valued maps in the entropy bound. Use cutoffs proven earlier
to get pointwise spatially local Lipschitz control; this allows applying the
injective-area formula directly on a conull set. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m:ℕ}

namespace Scatter
variable (q:Scatter m)
lemma yc : Continuous q.y.uncurry :=
  (coneProj_lip q.cone).continuous.comp
    (((op q.B).continuous.comp continuous_snd).add (q.dc.comp continuous_fst))
lemma yp : PolyBound q.y.uncurry := by
  change PolyBound (fun x:ℝ × Rn m=> coneProj q.cone (op q.B x.2 + q.d x.1))
  exact (PolyBound.lipschitz (coneProj_lip q.cone)).comp
    (((PolyBound.clm (op q.B)).comp PolyBound.snd).add (q.dp.comp PolyBound.fst))
lemma yl (z:ℝ) : LipschitzWith ‖op q.B‖₊ (q.y z) := by
  convert (coneProj_lip q.cone).comp ((op q.B).lipschitz.add (LipschitzWith.const (q.d z)))
    using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | simp
lemma linear_y (z x) (hz:q.M*(1+‖x‖)<z) : q.y z x=op q.B x+q.d z :=
  proj_of_mem _ (q.in_cone z x hz)

lemma kc : Continuous q.ky.uncurry := (c_mw.comp continuous_fst).smul q.yc

lemma km : mixed q.ky := by
  let f := fun z x => (MillsW z * st z) • q.y z x
  let g := fun z x => (MillsW z-MillsW z*st z) • q.y z x
  have he : q.ky = fun z x=>f z x+g z x := by ext; simp only [f,g,sub_smul,ky]; abel_nf
  rw [he]
  have hh : mixed f :=
    (mixed.of_rapid (Y:=Rn m) rapid_mws).product q.yp fun x y=>by unfold f; rw [norm_smul]
  apply hh.add
  have ht := poly_mw.comp (PolyBound.fst (E:=Rn m))
  have hs := Edge.st_poly.comp (PolyBound.fst (E:=Rn m))
  let d := fun x:Rn m=> q.M*(1+‖x‖)
  apply mixed.of_cutoff (show PolyBound g.uncurry from (ht.sub (ht.mul hs)).smul q.yp)
    (show PolyBound d from (PolyBound.const _).mul ((PolyBound.const _).add PolyBound.id.norm))
  intro z x hx
  unfold g st
  split_ifs with h
  · simp
  rw [q.zero_y _ _ (by change q.M*(1+‖x‖)<‖z‖ at hx; rwa [Real.norm_eq_abs,abs_of_neg (lt_of_not_ge h)] at hx),smul_zero]

lemma ki (x:Rn m) : Integrable (fun z=>q.ky z x) :=
  mixed_integrable_left q.km x (q.kc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
lemma Ki : Integrable q.ky.uncurry (volume.prod (normal m)) :=
  mixed_integrable q.km q.kc.aestronglyMeasurable
lemma klip (x:Rn m) :
    ∃ h:ℝ→ℝ, Integrable h ∧ ∀ z w, w∈ball x 1 →
      ‖q.ky z w-q.ky z x‖ ≤ h z*‖w-x‖ := by
  classical
  let L := q.M*(1+‖x‖+1)
  have hm := q.hm
  let S := Ioi (-L-1)
  let f := fun z:ℝ=> ‖op q.B‖*MillsW z
  refine ⟨S.indicator f, (integrable_indicator_iff measurableSet_Ioi).mpr
    ((mw_tail _).1.const_mul _),?_⟩
  intro z w hw
  unfold ky; rw [← smul_sub,norm_smul,Real.norm_of_nonneg (mw_pos z).le]
  by_cases hz:z∈S
  · rw [indicator_of_mem hz]
    have hu := (q.yl z).dist_le_mul w x
    rw [dist_eq_norm,dist_eq_norm] at hu
    exact le_trans (mul_le_mul_of_nonneg_left hu (mw_pos _).le) (by unfold f; simp; apply le_of_eq; ring)
  rw [indicator_of_notMem hz]
  have hh : ‖w‖ ≤ 1+‖x‖ := by
    apply le_trans (show ‖w‖ ≤ ‖w-x‖+‖x‖ by simpa using norm_add_le (w-x) x)
    change dist w x < 1 at hw; rw [dist_eq_norm] at hw; linarith
  change ¬-(q.M*(1+‖x‖+1))-1 < z at hz
  rw [q.zero_y z w (by nlinarith),q.zero_y z x (by nlinarith)]
  simp

lemma tsm : StronglyMeasurable q.t := q.kc.stronglyMeasurable.integral_prod_left
lemma tp : PolyBound q.t := poly_integral_left q.km fun x=>(q.ki x).aestronglyMeasurable
lemma ti : Integrable q.t (normal m) := q.tp.gaussian_integrable q.tsm.aestronglyMeasurable

lemma t_in (x) : q.t x∈ q.cone := by
  apply (show ∀ v, (v:Rn m) ∈ posDual (posDual q.cone) → v∈q.cone from by
    intro v; rw [show posDual (posDual q.cone) = q.cone from ProperCone.innerDual_innerDual _]; exact id)
  rw [mem_posDual]
  intro w hw
  let l : Rn m→L[ℝ]ℝ := innerSL ℝ w
  change 0 ≤ l (∫ z,q.ky z x)
  rw [← l.integral_comp_comm (q.ki x)]
  apply integral_nonneg
  intro z
  change 0 ≤ ⟪w,MillsW z • q.y z x⟫
  rw [real_inner_smul_right,real_inner_comm]
  exact mul_nonneg (mw_pos _).le (mem_posDual.mp hw (proj_mem ..))

lemma t_injective : Function.Injective q.t := by
  intro x y hxy
  by_contra he
  let b := op q.B x-op q.B y
  have hh : b≠0 := sub_ne_zero.mpr (fun heq=>he (q.inj heq))
  let l : Rn m →L[ℝ]ℝ := innerSL ℝ b
  let f := fun z => l (q.ky z x-q.ky z y)
  have hi : Integrable f := l.integrable_comp ((q.ki x).sub (q.ki y))
  have hu : (∫ z,f z)=0 := by
    unfold f
    rw [l.integral_comp_comm (show Integrable (fun z=>q.ky z x-q.ky z y) volume from (q.ki x).sub (q.ki y)), integral_sub (q.ki x) (q.ki y)]
    change l (q.t x - q.t y)=0
    rw [hxy,sub_self,_root_.map_zero]
  let L := max (q.M*(1+‖x‖)) (q.M*(1+‖y‖))
  have hf (z) : f z=MillsW z*⟪b,q.y z x-q.y z y⟫ := by unfold f ky; rw [← smul_sub,_root_.map_smul]; rfl
  have hn (z) : 0 ≤ f z := by
    rw [hf]
    apply mul_nonneg (mw_pos _).le
    have h := proj_firm q.cone (op q.B x+q.d z) (op q.B y+q.d z)
    rw [add_sub_add_right_eq_sub] at h
    exact (sq_nonneg _).trans h
  have he : Ioi L ⊆ Function.support f := by
    intro z hz
    rw [Function.mem_support,hf,q.linear_y _ _ (lt_of_le_of_lt (le_max_left ..) hz),q.linear_y _ _ (lt_of_le_of_lt (le_max_right ..) hz),add_sub_add_right_eq_sub]
    exact (mul_pos (mw_pos _) (real_inner_self_pos.mpr hh)).ne'
  have hpos := (integral_pos_iff_support_of_nonneg hn hi).mpr
    ((isOpen_Ioi.measure_pos volume (nonempty_Ioi (a:=L))).trans_le (measure_mono he))
  linarith

lemma td [NeZero m] : ∀ᵐ x:Rn m, HasFDerivAt q.t (op (q.TJ x)) x := by
  let : CompleteSpace (Rn m →L[ℝ] Rn m) := ContinuousLinearMap.instCompleteSpace
  filter_upwards [q.diff] with x hx
  let F := fun x z=> q.ky z x
  let A := fun z=> q.toEdge.WP z x*q.B
  let f := fun z=> op (A z)
  let l : Mat m→L[ℝ] Mat m := (ContinuousLinearMap.mul ℝ _).flip q.B
  have hi := q.toEdge.wp_slice_i x
  have ha : Integrable A := l.integrable_comp hi
  obtain ⟨b,hb,h⟩ := q.klip x
  have HH := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (F:=F) (F':=f) (𝕜:=ℝ) (ball_mem_nhds x (show (0:ℝ)<1 by norm_num))
    (fun x _=> (q.ki x).aestronglyMeasurable) (q.ki x)
    (opCLE.toContinuousLinearMap.integrable_comp ha).aestronglyMeasurable (ae_of_all _ h) hb ?_
  · have he : (∫ z,f z)=op (q.TJ x) := by
      change ∫ z,opCLE.toContinuousLinearMap (A z)=_
      rw [opCLE.toContinuousLinearMap.integral_comp_comm ha]
      have he : (∫ z,A z)=q.TJ x := l.integral_comp_comm hi
      rw [he]; rfl
    exact he ▸ HH.2
  filter_upwards [hx] with z hz
  unfold f A Edge.WP
  rw [smul_mul_assoc,_root_.map_smul,_root_.map_mul]
  exact hz.const_smul (MillsW z)

end Scatter
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_ScatterField
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Two projection maps implementing Scatter. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Metric Real
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)

lemma X_sc (z:ℝ) : q.primalMap.y z=q.XT z := by
  unfold Scatter.y primalMap
  ext x; simp_rw [← q.Z_def]; rfl
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_DefectLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! μ functionals and integrable density algebra for Section §03-04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Metric Real
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile

namespace rapid
variable {f g:ℝ→ℝ}
lemma rfadd (hf:rapid f) (hg:rapid g) : rapid fun x=> f x+g x := by
  intro n
  obtain ⟨C,hc,h⟩ := hf n
  obtain ⟨D,hd,h'⟩ := hg n
  refine ⟨C+D, by positivity, fun x=>?_⟩
  apply le_trans (mul_le_mul_of_nonneg_right (norm_add_le ..) (by positivity))
  rw [add_mul]; exact add_le_add (h x) (h' x)
lemma rfneg (hf:rapid f) : rapid fun x=> -f x := hf.mono (by simp)
lemma rfsub (hf:rapid f) (hg:rapid g) : rapid fun x=> f x-g x := by
  simpa only [sub_eq_add_neg] using hf.rfadd hg.rfneg
end rapid
lemma rapid_half_a : rapid fun x=> a x*(1-st x) := by
  apply rapid_phi.mono
  intro x
  unfold st; split_ifs with h
  · simp
  rw [sub_zero,mul_one,Real.norm_of_nonneg (a_pos _).le,
    Real.norm_of_nonneg (phi_pos _).le]
  simpa only [neg_neg,neg_phi] using a_high (-x) (by linarith)
namespace MomentF
variable {f g:ℝ→ℝ}
lemma inte (hf:MomentF f) : Integrable f := by simpa using hf (fun _ => 1) measurable_const (PolyBound.const _)
lemma add (hf:MomentF f) (hg:MomentF g) : MomentF fun x=>f x+g x := by
  intro u hu h; simp_rw [add_mul]
  exact (hf u hu h).add (hg u hu h)
lemma neg (hf:MomentF f) : MomentF fun x=> -f x := by
  intro u hu h
  simp_rw [neg_mul]; exact (hf u hu h).neg
lemma sub (hf:MomentF f) (hg:MomentF g) : MomentF fun x=> f x-g x := by simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma mul (hf:MomentF f) (hg:PolyBound g) (hm:Measurable g) : MomentF fun x=>f x*g x := by
  intro u hu h
  simp_rw [mul_assoc]; exact hf _ (hm.mul hu) (hg.mul h)
lemma mono (hf:MomentF f) (hm:Measurable g) (h:∀ x,‖g x‖ ≤ ‖f x‖) :
    MomentF g := by
  intro u hu h'
  apply (hf u hu h').mono (hm.mul hu).aestronglyMeasurable
  exact ae_of_all _ fun x=>by rw [Pi.mul_apply,norm_mul,norm_mul]; exact mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)
end MomentF
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)

lemma dB_poly : PolyBound q.dB := q.Bt_poly.sub
  ((PolyBound.const _).mul (poly_a.comp PolyBound.id.neg))

lemma dB_tail : rapid fun z=> q.dB z*st z := by
  convert q.B_tail.rfsub (rapid_ar.product (PolyBound.const q.s0)) using 1
  all_goals try with_reducible_and_instances rfl
  ext x; unfold dB; ring
lemma pB_tail : rapid fun z=> p z*q.dB z := by
  convert ((rapid_p.product q.dB_poly).rfadd q.dB_tail) using 1
  all_goals try with_reducible_and_instances rfl
  ext x; ring
lemma aB_tail : rapid fun z=> a z*q.dB z := by
  convert (rapid_half_a.product q.dB_poly).rfadd (q.dB_tail.product poly_a) using 1
  all_goals try with_reducible_and_instances rfl
  ext x; ring
lemma hd_tail : rapid q.hDel := by
  convert q.tail_H.rfsub (rapid_p.product (PolyBound.const q.s0)) using 1
  all_goals try with_reducible_and_instances rfl
  ext x; unfold hDel; ring

lemma ar_moment : MomentF fun x=>a x*q.r1 x :=
  q.moment_w.mono (ca.measurable.mul q.Bt_cd.continuous_deriv_one.measurable.neg) (fun x=>by
    rw [Real.norm_of_nonneg (mul_nonneg (a_pos x).le (q.r1_pos x).le),
      Real.norm_of_nonneg (q.w_positive x).le]
    exact le_add_of_nonneg_left (mul_nonneg (p_pos x).le (q.Bt_nonneg x)))
lemma arDelta_moment : MomentF fun x=> a x*q.dr x := by
  have hf : MomentF (fun x=>a x*(1-p x)) :=
    (MomentF.of_rapid rapid_phi c_phi.measurable).mono
      (ca.measurable.mul (measurable_const.sub cp.measurable)) (fun x=> by
        rw [Real.norm_of_nonneg (mul_pos (a_pos _) (q_pos _)).le,
          Real.norm_of_nonneg (phi_pos _).le]
        exact (le_add_of_nonneg_left (mul_nonneg (p_pos x).le (a_pos (-x)).le)).trans_eq (a0_id _))
  convert q.ar_moment.sub (hf.mul (PolyBound.const q.s0) measurable_const) using 1
  all_goals try with_reducible_and_instances rfl
  ext x; unfold dr; ring
lemma prDelta_moment : MomentF fun x=>p x*q.dr x := by
  convert q.arDelta_moment.mul ratio_bound (cp.measurable.div ca.measurable) using 1
  all_goals try with_reducible_and_instances rfl
  ext x; field_simp [ne_of_gt (a_pos x)]
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_DefectIBP
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar layer δ integration identities (including Eq 12). -/
noncomputable section
open MeasureTheory Filter Set Real Metric
open scoped Topology ENNReal NNReal
namespace GeneralMahler
open Profile Layers
lemma rapid_ftc {f g:ℝ→ℝ} (hf:rapid f) (hd:∀ x,HasDerivAt f (g x) x) (hi:Integrable g) :
    (∫ x,g x)=0 := by
  simpa using integral_of_hasDerivAt_of_tendsto hd hi hf.tail_limit_bot hf.tail_limit
lemma MomentF.int_test {f g:ℝ→ℝ} (hf:MomentF f) (hg:TestF g) :
    Integrable fun x=> f x*g x := hf g hg.cont.measurable hg.poly
lemma N2_test {f:ℝ→ℝ} (hf:TestF f) : TestF (N2 f) :=
  ((TestF.id.mul hf.der).sub hf.der.der).add ((TestF.const 2).mul hf)
variable {m:ℕ}
namespace ProjField
variable (q:ProjField m)
lemma dB_d (x:ℝ) : HasDerivAt q.dB (-q.dr x) x := by
  convert ((q.Bt_d x).sub (((d_a (-x)).comp x (hasDerivAt_neg' x)).const_mul q.s0)) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (rw [neg_p]; unfold dr; ring)
lemma hd_d (x:ℝ) : HasDerivAt q.hDel (q.dm x) x := (q.H_deriv x).sub ((d_p x).const_mul _)
lemma dm_eq (x:ℝ) : q.dm x=q.pb x+a x*q.dr x := by
  unfold dm pb layerW dr dB
  rw [← a0_id x]; ring
lemma ab_d (x:ℝ) : HasDerivAt q.ab (q.pb x-a x*q.dr x) x := by
  convert (d_a x).mul (q.dB_d x) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (unfold pb; ring)
lemma pb_d (x:ℝ) : HasDerivAt q.pb (phi x*q.dB x-p x*q.dr x) x := by
  convert (d_p x).mul (q.dB_d x) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | ring
lemma dB_c : Continuous q.dB := continuous_iff_continuousAt.mpr fun x=>(q.dB_d x).continuousAt
lemma hd_c : Continuous q.hDel := continuous_iff_continuousAt.mpr fun x=>(q.hd_d x).continuousAt

variable [NeZero m]

lemma pb_m : MomentF q.pb := .of_rapid q.pB_tail (cp.mul q.dB_c).measurable
lemma hd_m : MomentF q.hDel := .of_rapid q.hd_tail q.hd_c.measurable
lemma dm_m : MomentF q.dm := by
  rw [show q.dm=_ from funext q.dm_eq]
  exact q.pb_m.add q.arDelta_moment
lemma rk_m : MomentF q.rk := q.prDelta_moment.add q.hd_m

lemma mass : (∫ x,q.pb x)=0 ∧ (∫ x,a x*q.dr x)=0 := by
  have he := rapid_ftc (f:=q.ab) q.aB_tail q.ab_d
    (q.pb_m.inte.sub q.arDelta_moment.inte)
  have hi := rapid_ftc q.hd_tail q.hd_d q.dm_m.inte
  rw [integral_sub q.pb_m.inte q.arDelta_moment.inte] at he
  simp_rw [q.dm_eq] at hi
  rw [integral_add q.pb_m.inte q.arDelta_moment.inte] at hi
  constructor <;> linarith

lemma hd_test {f:ℝ→ℝ} (hf:TestF f) :
    (∫ x,q.dm x*f x)= -(∫ x,q.hDel x*deriv f x) := by
  have h (x:ℝ) : HasDerivAt (fun x=>q.hDel x*f x) (q.dm x*f x+q.hDel x*deriv f x) x :=
    (q.hd_d x).fun_mul (hf.diff x).hasDerivAt
  have he := rapid_ftc (q.hd_tail.product hf.poly) h
    ((q.dm_m.int_test hf).add (q.hd_m.int_test hf.der))
  rw [integral_add (q.dm_m.int_test hf) (q.hd_m.int_test hf.der)] at he
  linarith

lemma eq12 {f:ℝ→ℝ} (hf:TestF f) :
    (∫ x,q.pb x*N2 f x+q.rk x*deriv f x)=0 := by
  let g := fun x=>(q.ab x+q.hDel x)*f x-q.pb x*deriv f x
  have hr : rapid g :=
    ((q.aB_tail.rfadd q.hd_tail).product hf.poly).rfsub (q.pB_tail.product hf.der.poly)
  have hd (x:ℝ) : HasDerivAt g (q.pb x*N2 f x+q.rk x*deriv f x) x := by
    convert ((((q.ab_d x).fun_add (q.hd_d x)).fun_mul (hf.diff x).hasDerivAt).fun_sub
      ((q.pb_d x).fun_mul (hf.der.diff x).hasDerivAt)) using 1
    all_goals try with_reducible_and_instances rfl
    rw [q.dm_eq]
    unfold rk N2 N ab pb a
    ring
  apply rapid_ftc hr hd
  exact (q.pb_m.int_test (N2_test hf)).add (q.rk_m.int_test hf.der)

lemma delta_eq {f:ℝ→ℝ} (hf:TestF f) :
    q.delt f = -(2*(∫ x,q.pb x*f x)+∫ x,q.rk x*shiftD f x) := by
  have he : TestF (shiftD f) :=
    (((TestF.const 2).mul TestF.id).mul hf).sub hf.der
  have hi := q.rk_m.int_test he
  have hu : (fun x=>2*p x*q.dB x*f x)=fun x=>2*(q.pb x*f x) := by ext; unfold pb; ring
  unfold delt; simp_rw [congrFun hu]
  change -(∫ x,2*(q.pb x*f x)+q.rk x*shiftD f x)=_
  rw [integral_add,integral_const_mul]
  · exact (q.pb_m.int_test hf).const_mul _
  exact hi

lemma delta_d : q.delt Profile.d= -(∫ x,q.rk x*deriv Profile.v x) := by
  have h := q.eq12 g_test
  simp_rw [Profile.n_identity] at h
  have hi := q.pb_m.int_test Profile.d_test
  have hh := q.rk_m.int_test g_test.der
  have hv := q.rk_m.int_test v_test.der
  rw [integral_add hi hh] at h
  rw [q.delta_eq d_test]
  have he (x) : q.rk x*shiftD d x=q.rk x*deriv Profile.v x+2*(q.rk x*deriv g x) := by
    unfold shiftD; rw [(Profile.dd x).deriv]; ring
  simp_rw [he]; rw [integral_add hv (hh.const_mul _),integral_const_mul]
  linarith
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LogPath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Path z↦c(z)I+∫_{-∞}^z WP, for fixed standard input. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]
namespace Edge
variable (e:Edge m) (x:Rn m)
lemma H_diff (z w:ℝ) :
    e.H x w-e.H x z= ∫ t in z..w,e.WP t x := by
  unfold H
  exact (intervalIntegral.integral_Iic_sub_Iic (a:=z) (b:=w)
    (e.wp_slice_i x).integrableOn (e.wp_slice_i x).integrableOn)
lemma H_nonneg (z:ℝ) : 0 ≤ e.H x z :=
  (psd_integral (e.wp_slice_i x).integrableOn (ae_of_all _ fun y=>(e.wp_psd y x).posSemidef)).nonneg
lemma H_lip : LipschitzWith 1 (e.H x) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm,dist_eq_norm,e.H_diff]
  have hi (t:ℝ) : ‖e.WP t x‖ ≤ 1 := by
    rw [WP,norm_smul,Real.norm_of_nonneg (mw_pos t).le]
    exact (mul_le_mul_of_nonneg_right (mw_le t) (norm_nonneg _)).trans
      (by simpa only [one_mul] using e.Pcont t x)
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _=>hi t)
lemma H_deriv :
    ∀ᵐ z:ℝ, HasDerivAt (e.H x) (e.WP z x) z := by
  have h := LocallyIntegrable.ae_hasDerivAt_integral (e.wp_slice_i x).locallyIntegrable
  filter_upwards [h] with z hz
  have he : e.H x= fun t=> e.H x 0+∫ y in (0:ℝ)..t,e.WP y x := by
    funext t; rw [← e.H_diff]; abel
  rw [he]; exact (hz 0).const_add _

lemma path_pd (z) : (e.path x z).PosDef :=
  (form_posDef (mc_pos z) (show scalar m (MillsC z)∈specBox m (MillsC z) (MillsC z) from
    ⟨scalar_sym ..,le_rfl,le_rfl⟩)).add_posSemidef (e.H_nonneg x z).posSemidef
lemma path_d :
    ∀ᵐ z:ℝ, HasDerivAt (e.path x) ((-MillsW z) • (1-e.P z x)) z := by
  filter_upwards [e.H_deriv x] with z hz
  have h : HasDerivAt (fun t=> scalar m (MillsC t)) ((-MillsW z)•1) z :=
    (d_mc z).smul_const _
  have hh := h.add hz
  simp only [smul_sub,neg_smul,sub_neg_eq_add] at hh ⊢
  exact hh
lemma path_lip : LipschitzWith 2 (e.path x) := by
  have h : LipschitzWith 1 (fun z=>scalar m (MillsC z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp_rw [scalar,dist_eq_norm,← sub_smul,norm_smul]
    have he := mc_lip.dist_le_mul z w
    simpa [dist_eq_norm] using he
  convert h.add (e.H_lip x) using 1 <;> first | rfl | norm_num

lemma F_AC (a b:ℝ) : AbsolutelyContinuousOnInterval (e.Fedge x) a b := by
  let f := e.path x
  have hi := e.path_lip x
  have hf : Continuous f := hi.continuous
  let S := f '' (uIcc a b)
  have hc : IsCompact S := isCompact_uIcc.image hf
  have hl : LocallyLipschitzOn S logD := by
    rintro q ⟨t,ht,rfl⟩
    have h : ContDiffAt ℝ 1 logD (f t) :=
      (D_log (e.path_pd x t)).of_le le_top
    obtain ⟨K,s,hs,hK⟩ := h.exists_lipschitzOnWith
    exact ⟨K,s,mem_nhdsWithin_of_mem_nhds hs,hK⟩
  obtain ⟨K,hK⟩ := hl.exists_lipschitzOnWith_of_compact hc
  exact (hK.comp hi.lipschitzOnWith
    (show MapsTo f (uIcc a b) S from mapsTo_image _ _)).absolutelyContinuousOnInterval

lemma Sh_nonneg (z:ℝ) : 0 ≤ e.Sh x z :=
  smul_nonneg (inv_pos.mpr (mc_pos _)).le (e.H_nonneg _ _)
lemma beta_bound (z:ℝ) : 0 ≤ e.beta x z ∧ e.beta x z ≤ MillsJ z := by
  have h := thresh_unit (e.Sh_nonneg x z)
  have hi := trN_prod_unit h.1 h.2 (sub_nonneg.mpr (e.le_one z x))
    (sub_le_self _ (e.psd z x))
  exact ⟨mul_nonneg (mj_pos z).le hi.1, mul_le_of_le_one_right (mj_pos z).le hi.2⟩

lemma Fedge_d :
    ∀ᵐ z:ℝ, HasDerivAt (e.Fedge x)
      (-MillsJ z*(1-e.h1 x z)+e.beta x z) z := by
  filter_upwards [e.path_d x] with z hz
  have hp := e.path_pd x z
  have hd := deriv_logD hz hp
  set c := MillsC z
  set B := 1+e.Sh x z
  have hc : 0 < c := mc_pos z
  have hb : e.path x z=c•B := by
    simp only [path,B,Sh,smul_add,smul_smul]; change c•1+_ = c•1+ (c*c⁻¹)•_
    rw [mul_inv_cancel₀ hc.ne',one_smul]
  have he : (e.path x z)⁻¹=c⁻¹ • B⁻¹ := by
    have hpd : B.PosDef := thresh_pd (e.Sh_nonneg x z)
    apply left_inv_eq_left_inv (inv_mul' hp)
    rw [hb,smul_mul_assoc,mul_smul_comm,smul_smul, inv_mul_cancel₀ hc.ne',inv_mul' hpd,one_smul]
  rw [he, smul_mul_assoc,mul_smul_comm,smul_smul,trN_smul] at hd
  have he' : c⁻¹ * -MillsW z = -MillsJ z := by change c⁻¹ * -(MillsJ z*c)=_; field_simp
  rw [he'] at hd
  suffices H : -MillsJ z*(1-e.h1 x z)+e.beta x z =
      -MillsJ z*trN (B⁻¹*(1-e.P z x)) by rw [H]; exact hd
  unfold beta thresh h1
  rw [sub_mul,one_mul,trN_sub,trN_sub,trN_one]
  unfold B; ring

-- Endpoint saturation from cutoff
lemma path_neg {z:ℝ} (h : z < -e.radius x) :
    e.H x z=0 ∧ e.Fedge x z=LC z ∧ e.beta x z=0 ∧ e.h1 x z=0 := by
  have he (y:ℝ) (hy : y≤z) : e.P y x=0 :=
    e.tend_neg y x (show e.radius x < -y by linarith)
  have hh : e.H x z=0 := by
    calc
      _ = ∫ y in Iic z,(0:Mat m) :=
        setIntegral_congr_fun measurableSet_Iic fun y hy=> by simp only [WP,he y hy,smul_zero]
      _ = 0 := integral_zero ..
  refine ⟨hh, ?_, ?_, ?_⟩
  · unfold Fedge path LC; rw [hh,add_zero,logD_scalar]
  · unfold beta Sh thresh; simp [hh,trN]
  unfold h1; rw [he z le_rfl]; simp [trN]

lemma path_pos {z:ℝ} (h : e.radius x < z) :
    e.Fedge x z=logD (e.Jedge x) ∧ e.beta x z=0 ∧ e.h1 x z=1 := by
  have he (y:ℝ) (hy:z≤y) := e.tend_pos y x (h.trans_le hy)
  have hh := integral_add_compl measurableSet_Iic (e.wp_slice_i x) (s:=Iic z)
  rw [compl_Iic] at hh
  have hi : (∫ y in Ioi z,e.WP y x)=scalar m (MillsC z) := by
    rw [← (mw_tail z).2,scalar, ← integral_smul_const]
    exact setIntegral_congr_fun measurableSet_Ioi fun y hy=>by rw [WP,he y (mem_Ioi.mp hy).le]
  change e.H x z+ _ = e.Jedge x at hh
  rw [hi,add_comm] at hh
  exact ⟨congrArg logD hh, by unfold beta; simp [he z le_rfl,trN],
    by unfold h1; rw [he z le_rfl,trN_one]⟩

end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_GainIndent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Exact linear and nonnegative surplus terms in the log identity. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]
omit [NeZero m] in
lemma meas_trN : Measurable (@trN m) := by simp_rw [← funext trL_apply]; exact trL.continuous.measurable
omit [NeZero m] in
lemma poly_trN : PolyBound (@trN m) := by simp_rw [← funext trL_apply]; exact PolyBound.clm _
omit [NeZero m] in
lemma meas_inv : Measurable (fun A:Mat m=>A⁻¹) := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv]
  exact det_cdiff.continuous.measurable.inv.smul continuous_id.matrix_adjugate.measurable
omit [NeZero m] in
lemma meas_thresh : Measurable (@thresh m) :=
  measurable_const.sub (meas_inv.comp (measurable_const.add measurable_id))

namespace Edge
variable (e:Edge m)
omit [NeZero m] in
lemma path_int_meas : Measurable fun v:ℝ × Rn m=> e.H v.2 v.1 := by
  classical
  let f := fun x:ℝ × (ℝ × Rn m)=> e.WP x.1 x.2.2
  let S : Set (ℝ × (ℝ × Rn m)) := {x|x.1≤x.2.1}
  have hs : MeasurableSet S := (isClosed_le continuous_fst (continuous_fst.comp continuous_snd)).measurableSet
  have hm : StronglyMeasurable (S.indicator f) :=
    (e.wp_meas.comp_measurable (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).indicator hs
  have he (v:ℝ×Rn m) : e.H v.2 v.1=∫ x,S.indicator f (x,v) := by
    unfold H
    rw [← integral_indicator measurableSet_Iic]
    congr 1
  simp_rw [he]
  let g := fun x (v:ℝ×Rn m)=>S.indicator f (x,v)
  exact ((show StronglyMeasurable g.uncurry from hm).integral_prod_left).measurable
omit [NeZero m] in
lemma meas_beta : Measurable fun v:ℝ×Rn m=>e.beta v.2 v.1 :=
  (c_mj.measurable.comp measurable_fst).mul
    (meas_trN.comp ((meas_thresh.comp
      (((c_mc.measurable.comp measurable_fst).inv).smul e.path_int_meas)).mul
      (measurable_const.sub e.meas)))

omit [NeZero m] in
lemma meas_h1 : Measurable fun v:ℝ×Rn m=> e.h1 v.2 v.1 :=
  meas_trN.comp e.meas
lemma beta_mixed : mixed fun z x=> e.beta x z := by
  have he : PolyBound (fun v:ℝ × Rn m=> e.beta v.2 v.1) :=
    (poly_mj.comp PolyBound.fst).mono fun v=>by
      change ‖e.beta _ _‖≤‖MillsJ _‖
      rw [Real.norm_of_nonneg (mj_pos _).le,Real.norm_of_nonneg (e.beta_bound ..).1]
      exact (e.beta_bound ..).2
  apply mixed.of_cutoff he e.r_poly
  intro z x hz
  rw [Real.norm_eq_abs,lt_abs] at hz
  rcases hz with h|h
  · exact (e.path_pos x h).2.1
  exact (e.path_neg x (by linarith)).2.2.1

omit [NeZero m] in
lemma meas_T : StronglyMeasurable e.LinearT.uncurry :=
  ((c_mj.measurable.comp measurable_fst).mul
    (e.meas_h1.sub (measurable_st.comp measurable_fst))).stronglyMeasurable
lemma mixed_T : mixed e.LinearT := by
  have hi : PolyBound (fun v:ℝ × Rn m=> e.h1 v.2 v.1) := poly_trN.comp e.P_poly
  have ht : PolyBound e.LinearT.uncurry := (poly_mj.comp PolyBound.fst).mul
    (hi.sub (st_poly.comp PolyBound.fst))
  apply mixed.of_cutoff ht e.r_poly
  intro z x hz
  rw [Real.norm_eq_abs,lt_abs] at hz
  rcases hz with h|h
  · have hi := e.path_pos x h
    simp only [LinearT, hi.2.2,st,ite_eq_left ((e.r_pos x).trans h).le,sub_self,mul_zero]
  have hi := e.path_neg x (z:=z) (by linarith)
  have hh : ¬0 ≤ z := by have hh := e.r_pos x; linarith
  simp [LinearT,hi.2.2.2,st,hh]

lemma gain_poly : PolyBound fun x=>logD (e.Jedge x) := by
  have h := (poly_lc.comp e.r_poly).norm.add ((poly_trN.comp e.Jedge_poly).norm)
  apply h.mono
  intro x
  obtain ⟨hh,h'⟩ := logD_between (e.Jedge_pd x) (mc_pos _) (e.Jedge_bound x)
  change LC _ ≤ _ at hh
  change ‖logD _‖ ≤ ‖‖LC _‖+‖trN _‖‖
  rw [Real.norm_of_nonneg (show 0≤‖LC (e.radius x)‖+‖trN (e.Jedge x)‖ by positivity)]
  rw [Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,abs_le]
  refine ⟨le_trans ?_ hh,h'.trans ?_⟩ <;> grind
lemma gain_int : Integrable (fun x=>logD (e.Jedge x)) (normal m) :=
  e.gain_poly.gaussian_integrable
    (meas_logD.comp e.Jedge_SM.measurable).aestronglyMeasurable

lemma gain_exact (x) :
    logD (e.Jedge x)=LC 0+(∫ z,e.LinearT z x) + ∫ z,e.beta x z := by
  let F := e.Fedge x
  let f := fun z=>e.LinearT z x + e.beta x z
  let a := e.radius x+1
  have hi : 0<a := by unfold a; have h := e.r_pos x; linarith
  have hf : Integrable (fun z=> e.LinearT z x) := mixed_integrable_left e.mixed_T x
    (e.meas_T.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hg : Integrable (e.beta x) := mixed_integrable_left e.beta_mixed x
    (e.meas_beta.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hh : (∫ z in -a..a,f z)=∫ z,f z := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rcases (show z≤ -a ∨ a<z from by simp only [mem_Ioc] at hz; grind) with h|h
    · have he : z < -e.radius x := by unfold a at h; linarith
      have h' := e.path_neg x he
      have hx : ¬0≤z := by linarith
      simp [f,LinearT,h'.2.2,hx,st]
    have he : e.radius x < z := by unfold a at h; linarith
    have h' := e.path_pos x he
    have hx : 0 ≤ z := by linarith
    simp [f,LinearT,h'.2,hx,st]
  have hJ : IntervalIntegrable f volume (-a) (0:ℝ) :=
    (hf.add hg).intervalIntegrable ..
  have ht := e.Fedge_d x
  have hR : (∫ z in (0:ℝ)..a,f z)= F a - F 0 := by
    rw [← (e.F_AC x 0 a).integral_deriv_eq_sub]
    rw [intervalIntegral.integral_of_le hi.le,intervalIntegral.integral_of_le hi.le]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae ht, ae_restrict_mem measurableSet_Ioc] with z hz hy
    have hy' : 0≤z := le_of_lt (mem_Ioc.mp hy).1
    rw [hz.deriv]
    unfold f LinearT st; rw [ite_eq_left hy']; ring
  have hL : (∫ z in -a..(0:ℝ),f z)+(LC 0-LC (-a)) = F 0-F (-a) := by
    have hj (x:ℝ) : deriv LC x= -MillsJ x := (d_lc x).deriv
    have he : (∫ z in -a..(0:ℝ), -MillsJ z) = LC 0-LC (-a) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _=> d_lc z) (c_mj.neg.intervalIntegrable ..)
    rw [← he, ← intervalIntegral.integral_add hJ (show IntervalIntegrable (fun z=> -MillsJ z) volume (-a) 0 from c_mj.neg.intervalIntegrable ..),
      ← (e.F_AC x (-a) 0).integral_deriv_eq_sub]
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    apply integral_congr_ae
    have h₀ : ∀ᵐ z:ℝ, z≠0 := by rw [ae_iff]; simp
    filter_upwards [ae_restrict_of_ae ht,ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae h₀] with z hz hy hh
    have hy' : ¬0≤z := not_le_of_gt (lt_of_le_of_ne (mem_Ioc.mp hy).2 hh)
    rw [hz.deriv]
    unfold f LinearT st; rw [ite_eq_right hy']; ring
  have hl : F (-a)=LC (-a) := (e.path_neg x (by unfold a; linarith)).2.1
  have hr : F a=logD (e.Jedge x) := (e.path_pos x (by unfold a; linarith)).1
  rw [hr] at hR; rw [hl] at hL
  have hu : (∫ z in -a..(0:ℝ),f z)+(∫ z in (0:ℝ)..a,f z)=
      (∫ z,e.LinearT z x)+∫ z,e.beta x z :=
    (intervalIntegral.integral_add_adjacent_intervals hJ ((hf.add hg).intervalIntegrable ..)).trans
      (hh.trans (integral_add hf hg))
  linarith
end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_EntropyMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Change of variables/Jensen for the projection scatter map. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Matrix Real
open scoped NNReal ENNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma det_op (A:Mat m) : (op A).det=A.det := by
  change LinearMap.det (Matrix.toEuclideanLin A)=_
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]

omit [NeZero m] in
lemma logDensity (x:Rn m) : Real.log (nDensity x) = m*logN0- ‖x‖^2/2 := by
  unfold nDensity logN0; rw [Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_exp]; ring

omit [NeZero m] in
lemma i_N2 : Integrable (fun x:Rn m => ‖x‖^2) (normal m) :=
  (PolyBound.id.norm.pow _).gaussian_integrable ((continuous_norm.pow _).aestronglyMeasurable)
omit [NeZero m] in
lemma N2_area : (∫ x:Rn m,‖x‖^2 ∂normal m)=m := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  have he (i:Fin m) (x:Rn m) : ⟪x,b i⟫=x i := by
    rw [real_inner_comm]
    exact (b.repr_apply_apply x i).symm
  have hh (i:Fin m) : (∫ x:Rn m, (x i)^2 ∂normal m)=1 := by
    let l := ProjField.coord i
    have hx (x:Rn m) : fderiv ℝ l x (b i)=1 := by
      rw [l.fderiv]
      change b i i = _
      simp [b]
    have h := normal_IBP_lipschitz l.lipschitz (b i)
    simp_rw [hx,he] at h
    simp only [smul_eq_mul,l,ProjField.coord_apply] at h
    simpa [pow_two] using h.symm
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp [hh]
  exact fun i _ => ((PolyBound.clm (ProjField.coord i)).pow _).gaussian_integrable
    (((ProjField.coord i).continuous.pow _).aestronglyMeasurable)

namespace Scatter
variable (q:Scatter m) (v:Rn m)
omit [NeZero m] in
lemma i_cost : Integrable (fun x=>⟪v,q.t x⟫) (normal m) :=
  (innerSL ℝ v).integrable_comp q.ti

theorem entropy (h:v∈interior (posDual q.cone:Set (Rn m))) (hq:q.B.det≠0) :
    -logN0+1/2 + logD q.B + (∫ x,logD (q.toEdge.Jedge x) ∂normal m) - q.cost v / m
      ≤ Real.log (chi q.cone v)/m := by
  let g (x:Rn m) := Real.exp (-⟪v,x⟫)
  let f (x:Rn m) := g (q.t x)*|(op (q.TJ x)).det|
  have hd := q.td
  let bad : Set (Rn m) := {x|¬ HasFDerivAt q.t (op (q.TJ x)) x}
  have Hb : volume bad = 0 := ae_iff.mp hd
  obtain ⟨u,hu,hm,hU⟩ := exists_measurable_superset_of_null Hb
  let S := uᶜ
  have hs : MeasurableSet S := hm.compl
  have he : ∀ x∈S,HasFDerivWithinAt q.t (op (q.TJ x)) S x := by
    intro x hx
    have h₁ : x∉bad := fun h' => hx (hu h')
    exact (not_not.mp h₁).hasFDerivWithinAt
  have hr : volume.restrict S=(volume:Measure (Rn m)) := restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; simpa [S] using hU)
  have hg := chi_integrable h
  have ht : q.t '' S ⊆ (q.cone:Set (Rn m)) := by rintro x ⟨y,hy,rfl⟩; exact q.t_in _
  have he' := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (volume:Measure (Rn m)) hs he q.t_injective.injOn g
  have hF : Integrable f := by
    have h := he'.mp (hg.mono_set ht)
    unfold IntegrableOn at h; rw [hr] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext x; change _*_= _*_ ; ring
  have H : (∫ x,f x) ≤ chi q.cone v := by
    have hi := integral_image_eq_integral_abs_det_fderiv_smul
      (volume:Measure (Rn m)) hs he q.t_injective.injOn g
    rw [hr] at hi
    calc
      _ = ∫ x in q.t '' S,g x := by rw [hi]; congr 1; ext x; change _*_=_*_; ring
      _ ≤ _ := setIntegral_mono_set hg (ae_of_all _ fun x=>Real.exp_nonneg _) (Filter.Eventually.of_forall ht)
  let K := fun x=>f x/(nDensity x)
  have hj (x:Rn m) : nDensity x • K x=f x := by
    unfold K
    rw [smul_eq_mul]
    field_simp [ne_of_gt (nDensity_pos _)]
  have hK : Integrable K (normal m) := normal_integrable_iff.mpr (by simp_rw [hj]; exact hF)
  have heK (x:Rn m) :
      |(op (q.TJ x)).det|=(q.toEdge.Jedge x).det*|q.B.det| := by
    rw [det_op,TJ,det_mul,abs_mul,abs_of_pos (q.toEdge.Jedge_pd x).det_pos]
  have hp (x:Rn m) : 0<K x := by
    unfold K f g; rw [heK]
    exact div_pos
      (mul_pos (Real.exp_pos _) (mul_pos (q.toEdge.Jedge_pd x).det_pos (abs_pos.mpr hq))) (nDensity_pos _)
  let c := ∫ x,K x ∂normal m
  have hc : 0 < c := by
    apply (integral_pos_iff_support_of_nonneg (fun x=>(hp x).le) hK).mpr
    rw [show Function.support K=univ from eq_univ_of_forall fun x=>(hp x).ne',measure_univ]
    norm_num
  have hl : c ≤ chi q.cone v := by unfold c; rw [normal_integral]; simp_rw [hj]; exact H
  let a (x:Rn m) := (m:ℝ)*logD q.B + (m:ℝ)*logD (q.toEdge.Jedge x)
  let b (x:Rn m) := (m:ℝ)*logN0 - ‖x‖^2/2
  have Mm := ProjField.m_pos (m:=m)
  have ha (x:Rn m) : Real.log (K x) = a x-⟪v,q.t x⟫-b x := by
    unfold K f g
    rw [heK,Real.log_div,Real.log_mul,Real.log_exp,logDensity,Real.log_mul]
    · unfold a b logD; rw [Real.log_abs]; field_simp; ring
    all_goals
      have h₁ := (q.toEdge.Jedge_pd x).det_pos; have h₂ := abs_pos.mpr hq; have h₃ := nDensity_pos x; positivity
  have ia₁ := q.toEdge.gain_int.const_mul (m:ℝ)
  have ia : Integrable a (normal m) := (integrable_const _).add ia₁
  have ib : Integrable b (normal m) := (integrable_const _).sub (i_N2.div_const _)
  have iK : Integrable (fun x=>Real.log (K x)) (normal m) := by
    simp_rw [ha]
    exact (ia.sub (q.i_cost v)).sub ib
  have hh : (∫ x,Real.log (K x) ∂normal m) ≤ Real.log (chi q.cone v) := by
    apply le_trans _ (Real.log_le_log hc hl)
    let W (x:Rn m) := Real.log c+(K x / c-1)
    have hv := hK.div_const c
    have ih := hv.sub (integrable_const (1:ℝ))
    have he := integral_mono iK (show Integrable W (normal m) from
      (integrable_const _).add ih) (fun x=> ?_)
    · apply he.trans_eq
      unfold W
      rw [integral_add,integral_sub hv (integrable_const _),integral_div]
      · change (∫ x:Rn m,Real.log c ∂normal m)+(c/c-_) = _
        rw [div_self hc.ne']; simp
      all_goals first | exact integrable_const _ | exact ih
    · have h := Real.log_le_sub_one_of_pos (div_pos (hp x) hc)
      rw [Real.log_div (hp x).ne' hc.ne'] at h
      unfold W; linarith
  simp_rw [ha] at hh
  rw [integral_sub,integral_sub ia (q.i_cost v)] at hh
  · unfold a b at hh
    rw [integral_add (integrable_const _) ia₁,integral_sub,integral_const_mul, integral_div,N2_area] at hh
    · simp only [integral_const,probReal_univ,one_smul] at hh
      rw [integral_const_mul] at hh
      rw [le_div_iff₀ Mm]
      unfold cost
      field_simp
      nlinarith
    all_goals first | exact i_N2.div_const _ | exact integrable_const _
  · exact ia.sub (q.i_cost v)
  · exact ib

end Scatter
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_EntScalar
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Entropy scalar simplification. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped NNReal ENNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers Profile
lemma c_mul_p (x:ℝ) : MillsC x*p x=phi x := by unfold MillsC; field_simp [ne_of_gt (p_pos x)]
lemma cR_v (x:ℝ) : MillsC (-x)=2*a x-p x*deriv Profile.v x := by
  rw [v_deriv]
  unfold MillsJ a
  have h := c_mul_p x
  have he := c_mul_p (-x)
  rw [neg_phi,neg_p] at he; linarith

lemma LC_average : (∫ x,phi x*LC x)= logN0 + 1/2 := by
  have hi : Integrable (fun x:ℝ=>phi x*x^2) :=
    (rapid_phi.product (PolyBound.id.pow 2)).integrable_real
      ((c_phi.mul (continuous_id.pow 2)).measurable)
  have hh : (∫ x:ℝ,phi x*x^2)=1 := by
    have ht (x:ℝ) : HasDerivAt (fun x:ℝ=>phi x*x) (phi x-phi x*x^2) x := by
      convert (d_phi x).fun_mul (hasDerivAt_id' x) using 1 <;> first | rfl | ring
    have ha := rapid_ftc (rapid_phi.product PolyBound.id) ht (i_phi.sub hi)
    rw [integral_sub i_phi hi,e_phi] at ha; linarith
  have he (x:ℝ) : phi x*LC x= logN0*phi x-phi x*x^2/2-phi x*LP x := by
    unfold LC MillsC; rw [Real.log_div (phi_pos _).ne' (p_pos _).ne']
    have hf : Real.log (phi x)=logN0-x^2/2 := by
      unfold logN0; rw [phi_apply,Real.log_mul (by positivity) (by positivity),Real.log_exp]; ring
    rw [hf]; unfold LP; ring
  simp_rw [he]
  rw [integral_sub,integral_sub,integral_const_mul,integral_div,e_phi,hh,logp_average]
  · ring
  all_goals first | exact i_phi.const_mul _ | exact hi.div_const _ | exact int_lp |
    exact (i_phi.const_mul _).sub (hi.div_const _)

lemma rapid_ca_prod : rapid fun x=>MillsC x*a x := by
  convert (rapid_mcs.product poly_a).rfadd (rapid_half_a.product poly_mc) using 1
  all_goals try with_reducible_and_instances rfl
  ext x; ring
lemma rapid_wa : rapid fun x=>MillsW x*a x := by
  convert rapid_ca_prod.product poly_mj using 1
  all_goals try with_reducible_and_instances rfl
  ext x; unfold MillsW; ring
lemma int_wa : Integrable fun x=>MillsW x*a x :=
  rapid_wa.integrable_real (c_mw.mul ca).measurable
lemma wa_area : (∫ x,MillsW x*a x)=1 := by
  have hd (x:ℝ) : HasDerivAt (fun x=>MillsC x*a x) (phi x - MillsW x*a x) x := by
    convert (d_mc x).fun_mul (d_a x) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (rw [c_mul_p]; ring)
  have hh := rapid_ftc rapid_ca_prod hd (i_phi.sub int_wa)
  rw [integral_sub i_phi int_wa,e_phi] at hh; linarith

variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)

lemma rapid_cdBy : rapid fun x=>MillsC (-x)*q.dB x := by
  have h : rapid (fun x=>MillsC (-x)*(1-st x)) := by
    intro n
    obtain ⟨C,hc,h⟩ := rapid_mcs n
    refine ⟨C,hc,fun x=>?_⟩
    specialize h (-x)
    unfold st at *
    dsimp at h ⊢
    split_ifs with hx
    · simp [hc]
    · have he : 0≤ -x := by linarith
      simpa [hx,he] using h
  convert (q.dB_tail.product mc_test.ref.poly).rfadd (h.product q.dB_poly) using 1
  all_goals try with_reducible_and_instances rfl
  ext x; ring
lemma i_wdB : Integrable (fun x=>MillsW (-x)*q.dB x) := by
  have h := q.rapid_cdBy.product mj_test.ref.poly
  have hh : rapid (fun x=>MillsW (-x)*q.dB x) := by convert h using 1; ext; unfold MillsW; ring
  exact hh.integrable_real (((c_mw.comp continuous_neg).mul q.dB_c).measurable)
lemma i_ca_neg : Integrable (fun x:ℝ=> MillsW (-x)*a (-x)) :=
  (measurePreserving_neg volume).integrable_comp_emb (Homeomorph.neg _).measurableEmbedding |>.mpr int_wa

lemma cBy_eq :
    q.delt d=q.cBy-q.s0+(∫ x,q.dm x*Profile.v x) := by
  have hi (x:ℝ) : HasDerivAt (fun x=>MillsC (-x)*q.dB x)
      (MillsW (-x)*q.dB x-(2*(a x*q.dr x)-p x*q.dr x*deriv Profile.v x)) x := by
    convert (((d_mc (-x)).comp x (hasDerivAt_neg' x)).fun_mul (q.dB_d x)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (simp only [Function.comp_apply]; rw [cR_v]; ring)
  have ig : Integrable (fun x=>p x*q.dr x*deriv Profile.v x) :=
    q.prDelta_moment.int_test v_test.der
  have ih : Integrable (fun x=>2*(a x*q.dr x)) := q.arDelta_moment.inte.const_mul _
  have hh := rapid_ftc q.rapid_cdBy hi (q.i_wdB.sub (ih.sub ig))
  rw [integral_sub,integral_sub ih ig,integral_const_mul,q.mass.2] at hh
  · have he (x:ℝ) : MillsW (-x)*q.Bt x=MillsW (-x)*q.dB x+q.s0*(MillsW (-x)*a (-x)) := by
      unfold dB; ring
    have hx := integral_neg_eq_self (fun x=>MillsW x*a x) volume
    change (∫ x,MillsW (-x)*a (-x))=_ at hx
    unfold cBy; simp_rw [he]
    rw [integral_add q.i_wdB (i_ca_neg.const_mul _), integral_const_mul,hx,wa_area,
      q.delta_d,q.hd_test v_test]
    unfold rk
    simp_rw [add_mul]
    rw [integral_add ig (q.hd_m.int_test v_test.der)]
    linarith
  all_goals first | exact q.i_wdB | exact ih.sub ig

omit [NeZero m] in
lemma cost_eq (q:Scatter m) (v:Rn m) :
    q.cost v= ∫ z,MillsW z*⟪v,∫ x,q.y z x ∂normal m⟫ := by
  let l : Rn m→L[ℝ]ℝ := innerSL ℝ v
  have hi := l.integrable_comp q.Ki
  have hp (x) : ⟪v,q.t x⟫ = ∫ z,l (q.ky z x) := (l.integral_comp_comm (q.ki _)).symm
  unfold Scatter.cost; simp_rw [hp]
  rw [integral_integral_swap]
  · congr 1
    ext z
    have hh : Integrable (q.y z) (normal m) :=
      (PolyBound.lipschitz (q.yl z)).gaussian_integrable (q.yl z).continuous.aestronglyMeasurable
    rw [l.integral_comp_comm (show Integrable (q.ky z) (normal m) from hh.smul (MillsW z))]
    unfold Scatter.ky; rw [integral_smul,_root_.map_smul]; rfl
  have he : Integrable (fun u:ℝ×Rn m=>l (q.ky u.1 u.2)) (volume.prod (normal m)) := hi
  exact he.swap

lemma X_cost : q.primalMap.cost q.V=(m:ℝ) := by
  rw [cost_eq]
  simp_rw [q.X_sc,q.XT_mean,real_inner_smul_right]
  rw [real_inner_comm q.U,q.ip]
  simp_rw [← mul_assoc]; rw [integral_mul_const,wa_area]; ring

lemma Y_cost : q.dualMap.cost q.U=q.cBy*m := by
  rw [cost_eq]
  simp_rw [q.Y_sc]
  have H (z:ℝ) : ⟪q.U,∫ x,q.YT z x ∂normal m⟫=q.Bt z*m := by
    unfold Bt; have h:= m_pos (m:=m); field_simp
  simp_rw [H,← mul_assoc]; rw [integral_mul_const]
  have he := integral_neg_eq_self (fun x=>MillsW (-x)*q.Bt x) volume
  simp only [neg_neg] at he; rw [he]; rfl
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_EdgeBand
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Lower bound for beta on the band l∈[-z,z] for z≥0, using
integration by parts against 1/W; equivalent to the subprobability
argument in the paper. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]

namespace Edge
variable (e:Edge m) (x:Rn m) (z:ℝ)
lemma BH_both (l:ℝ) (hl:l≤z) :
    0 ≤ e.BH x z l ∧ e.BH x z l ≤ scalar m (MillsC l-MillsC z) := by
  rw [BH,e.H_diff,intervalIntegral.integral_of_le hl]
  let μ := volume.restrict (Ioc l z)
  have hi : Integrable (fun y=> e.WP y x) μ := (e.wp_slice_i x).integrableOn
  constructor
  · exact (psd_integral hi (ae_of_all _ fun y=>(e.wp_psd y x).posSemidef)).nonneg
  let f := fun y:ℝ=> MillsW y • (1:Mat m)
  have hh : IntervalIntegrable MillsW volume l z := c_mw.intervalIntegrable ..
  have he := hh.1
  have hF : Integrable f μ := he.smul_const _
  have hu : scalar m (MillsC l-MillsC z) = ∫ y in Ioc l z,f y := by
    unfold f scalar; rw [integral_smul_const, ← intervalIntegral.integral_of_le hl]
    have h (t:ℝ) : HasDerivAt (-MillsC) (MillsW t) t := by simpa using (d_mc t).neg
    have hx := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> h t) hh
    rw [hx]; simp [sub_eq_add_neg,add_comm]
  rw [hu, ← sub_nonneg]
  change 0 ≤ (∫ y,f y ∂μ)-∫ y,e.WP y x ∂μ
  rw [← integral_sub hF hi]
  exact (psd_integral (hF.sub hi) (ae_of_all _ fun y=> (sub_nonneg.mpr (e.wp_le y x)).posSemidef)).nonneg
lemma BH_beta (l:ℝ) (hl:l≤z) :
    (MillsC l)⁻¹ • e.BH x z l ≤ thresh (e.Sh x z) := by
  let c := MillsC z; let d := MillsC l; let B := e.BH x z l
  have hc : 0 < c := mc_pos z
  have hd : 0 < d := mc_pos l
  let D := c⁻¹ • B
  have hi : 0 ≤ D := smul_nonneg (inv_pos.mpr hc).le (e.BH_both x z l hl).1
  have ht : D≤e.Sh x z := smul_le_smul_of_nonneg_left
    (sub_le_self _ (e.H_nonneg x l)) (inv_pos.mpr hc).le
  apply le_trans _ (thresh_mono hi ht)
  have hh : 1+D ≤ scalar m (c⁻¹*d) :=
    le_trans (show 1+D ≤ 1+c⁻¹ • scalar m (d-c) from add_le_add le_rfl
      (smul_le_smul_of_nonneg_left (e.BH_both x z l hl).2 (inv_pos.mpr hc).le)) (by
        apply le_of_eq
        have hx : 1+c⁻¹*(d-c)=c⁻¹*d := by field_simp; ring
        simp only [scalar,smul_smul]
        conv_rhs => rw [← hx,add_smul,one_smul])
  apply le_trans _ (thresh_low hi (mul_pos (inv_pos.mpr hc) hd) hh)
  apply le_of_eq; change d⁻¹•B=(c⁻¹*d)⁻¹•(c⁻¹•B); rw [smul_smul]
  congr 1
  field_simp

lemma ntb_both (l:ℝ) : 0 ≤ e.ntb x z l ∧ e.ntb x z l ≤ 1 :=
  trN_prod_unit (e.psd ..) (e.le_one ..) (sub_nonneg.mpr (e.le_one ..)) (sub_le_self _ (e.psd ..))

lemma FF_upper (l:ℝ) (hl:l≤z) :
    e.FF x z l ≤ e.beta x z/MillsJ z*MillsC l := by
  have hh := trN_mul_mono (e.BH_beta x z l hl) (sub_nonneg.mpr (e.le_one z x))
  rw [smul_mul_assoc,trN_smul] at hh
  have ht := mj_pos z
  unfold beta FF
  rw [mul_div_cancel_left₀ _ ht.ne']
  rwa [inv_mul_eq_div,div_le_iff₀ (mc_pos _)] at hh

omit [NeZero m] in
lemma trC_eq (A:Mat m) : e.trC x z A=trN (A*(1-e.P z x)) := by simp [trC,mul_sub,trN_sub]

lemma FF_lip : ∃ K,LipschitzWith K (e.FF x z) := by
  rw [show e.FF x z=(e.trC x z) ∘ e.BH x z from funext (fun l=> (e.trC_eq x z _).symm)]
  exact ⟨_, (e.trC x z).lipschitz.comp
    ((LipschitzWith.const (e.H x z)).sub (e.H_lip x))⟩
lemma FF_deriv :
    ∀ᵐ l:ℝ, HasDerivAt (e.FF x z) (-(MillsW l * e.ntb x z l)) l := by
  filter_upwards [e.H_deriv x] with l hl
  have hf : HasDerivAt (e.BH x z) (-e.WP l x) l := by
    have h := (hasDerivAt_const l (e.H x z)).sub hl
    rw [zero_sub] at h
    exact h
  have hh := (e.trC x z).hasFDerivAt.comp_hasDerivAt l hf
  rw [_root_.map_neg,WP,_root_.map_smul,e.trC_eq] at hh
  have he : e.FF x z=(e.trC x z) ∘ e.BH x z := by ext; simp [FF,e.trC_eq]
  rw [he]; exact hh

lemma d_wi₀ (t:ℝ) : HasDerivAt Wi (-(MillsC t*((1-MillsW t)-MillsJ t^2))/((MillsW t)^2)) t :=
  (d_mw t).inv (mw_pos _).ne'
lemma d_wi (t:ℝ) : HasDerivAt Wi (deriv Wi t) t := (d_wi₀ t).differentiableAt.hasDerivAt
lemma dw_cont : Continuous (deriv Wi) := by
  simp_rw [funext (fun t=>(d_wi₀ t).deriv)]
  exact (((c_mc.mul ((continuous_const.sub c_mw).sub (c_mj.pow 2))).neg).div (c_mw.pow 2)
    (fun t=>pow_ne_zero 2 (mw_pos _).ne'))
lemma wi_cd : ContDiff ℝ 1 Wi :=
  contDiff_one_iff_deriv.mpr ⟨fun t=>(d_wi t).differentiableAt,dw_cont⟩
lemma dwi_nonneg (t:ℝ) : 0 ≤ deriv Wi t :=
  (show Monotone Wi from fun _x _y h=> (inv_le_inv₀ (mw_pos _) (mw_pos _)).mpr (mw_anti h)).deriv_nonneg

lemma ntb_int (a b:ℝ) : IntervalIntegrable (e.ntb x z) volume a b := by
  have he : Measurable (e.ntb x z) :=
    meas_trN.comp (((e.meas.comp (measurable_id.prodMk measurable_const)).mul measurable_const))
  apply intervalIntegrable_iff.mpr
  let μ := volume.restrict (Ι a b)
  have : IsFiniteMeasure μ := by
    apply isFiniteMeasure_restrict.mpr
    exact (lt_of_le_of_lt (measure_mono uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top).ne
  exact (integrable_const (μ:=μ) (1:ℝ)).mono' he.aestronglyMeasurable (ae_of_all _ fun t=> by
    rw [Real.norm_of_nonneg (e.ntb_both x z t).1]; exact (e.ntb_both x z t).2)

lemma band (hz:0≤z) :
    (∫ l in -z..z,e.ntb x z l) ≤ 4*e.beta x z := by
  let f := e.FF x z
  let b := e.beta x z/MillsJ z
  have hb : 0 ≤ b := div_nonneg (e.beta_bound ..).1 (mj_pos _).le
  have he : -z ≤ z := by linarith
  obtain ⟨K,h⟩ := e.FF_lip x z
  have hf : Continuous f := h.continuous
  have ha := (h.lipschitzOnWith (s:=uIcc (-z) z)).absolutelyContinuousOnInterval
  have hc : AbsolutelyContinuousOnInterval Wi (-z) z :=
    wi_cd.contDiffOn.absolutelyContinuousOnInterval
  let G := fun t=>f t*deriv Wi t
  have hg : Continuous G := hf.mul dw_cont
  have hbase := (ha.fun_mul hc).integral_deriv_eq_sub
  have h₀ : f z=0 := by unfold f FF BH; simp [trN]
  have hh : (∫ l in -z..z,e.ntb x z l)=f (-z)*Wi (-z)+(∫ l in -z..z,G l) := by
    have hi : (∫ l in -z..z,deriv (fun t=>f t*Wi t) l) =
        ∫ l in -z..z,(G l-e.ntb x z l) := by
      rw [intervalIntegral.integral_of_le he,intervalIntegral.integral_of_le he]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (e.FF_deriv x z)] with t ht
      have hu : deriv (fun t=>f t*Wi t) t=-(MillsW t*e.ntb x z t)*Wi t+f t*deriv Wi t :=
        (ht.fun_mul (d_wi t)).deriv
      rw [hu]; unfold G Wi; field_simp [ne_of_gt (mw_pos t)]; ring
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable ..) (e.ntb_int ..)] at hi
    change (∫ l in -z..z,deriv (fun t=> f t*Wi t) l)=_ at hbase
    change _= f z*Wi z-f (-z)*Wi (-z) at hbase
    rw [h₀] at hbase; linarith
  let H := fun t=>MillsC t*deriv Wi t
  have ht : Continuous H := c_mc.mul dw_cont
  have hH : MillsC (-z)*Wi (-z)+(∫ t in -z..z,H t)=MillsC z*Wi z+2*z := by
    have hd (t:ℝ) : HasDerivAt (fun t=>MillsC t*Wi t) (H t-1) t := by
      convert (d_mc t).fun_mul (d_wi t) using 1
      all_goals try with_reducible_and_instances rfl
      all_goals first | rfl | (unfold H Wi; field_simp [ne_of_gt (mw_pos t)]; ring)
    have hu := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> hd t)
      ((ht.sub continuous_const).intervalIntegrable (-z) z)
    rw [intervalIntegral.integral_sub (ht.intervalIntegrable ..)
      (continuous_const.intervalIntegrable ..)] at hu
    simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one] at hu
    linarith
  have hw : Wi (-z) ≥ 0 := (inv_pos.mpr (mw_pos _)).le
  have hu : ∫ l in -z..z,G l ≤ ∫ l in -z..z,b*H l :=
    intervalIntegral.integral_mono_on he (hg.intervalIntegrable ..)
      ((continuous_const.mul ht).intervalIntegrable ..) fun l hl=>
      le_trans (mul_le_mul_of_nonneg_right (e.FF_upper x z l hl.2) (dwi_nonneg l))
        (by unfold b H; rw [mul_assoc])
  rw [intervalIntegral.integral_const_mul] at hu
  calc
    _ = _ := hh
    _ ≤ (b*MillsC (-z))*Wi (-z)+ b* (∫ l in -z..z,H l) :=
      add_le_add (mul_le_mul_of_nonneg_right (e.FF_upper x z (-z) he) hw) hu
    _ = b*(MillsC z*Wi z+2*z) := by rw [← hH]; ring
    _ ≤ b*(4*MillsJ z) := by
      apply mul_le_mul_of_nonneg_left _ hb
      have hp := mj_pos z
      have hc := mc_pos z
      have hx : MillsC z*Wi z = (MillsJ z)⁻¹ := by unfold Wi MillsW; field_simp
      have hz' : z ≤ MillsJ z := by unfold MillsJ; linarith
      rw [hx]
      have hy : 1≤2*MillsJ z^2 := by
        have hh := mj_mono hz
        have he : MillsJ 0^2=2/π := by
          unfold MillsJ MillsC; rw [p_half,phi_apply]
          have he := Real.sq_sqrt (show 0≤2*π by positivity)
          have hi : 0 < √(2*π) := by positivity
          simp only [zero_add,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true, zero_pow,neg_zero,zero_div, Real.exp_zero,mul_one]
          field_simp
          nlinarith
        have h₁ := Real.pi_lt_four
        have h₂ := Real.pi_pos
        have h₃ : 1≤2*MillsJ 0^2 := by rw [he]; apply le_of_sub_nonneg; field_simp; linarith
        nlinarith [mj_pos 0]
      rw [← one_div]
      have hh : 1/MillsJ z ≤ 2*MillsJ z := (div_le_iff₀ hp).mpr (by nlinarith)
      linarith
    _ = _ := by unfold b; field_simp [ne_of_gt (mj_pos z)]
end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_NtLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Nonthreshold kernel and integration over the ordered halves.
We use (l,z) as pair of variables and ordinary product volume. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers
variable {m:ℕ}

namespace Edge
variable (e:Edge m)
lemma nt_sym (u x) : e.nt0 u.swap x=e.nt0 u x := by simp [nt0,NTm,min_comm,max_comm]
lemma nt_pos (u x) : 0 ≤ e.nt0 u x := by
  unfold nt0 NTm; rw [trN_j]
  exact trN_mul_nonneg (e.psd ..) (sub_nonneg.mpr (e.le_one ..))
lemma nt_meas : Measurable e.NTm.uncurry := by
  let m₁ := fun v:Plane×Rn m=> e.P (min v.1.1 v.1.2) v.2
  let m₂ := fun v:Plane×Rn m=> 1-e.P (max v.1.1 v.1.2) v.2
  have he : Measurable m₁ := e.meas.comp (show Measurable (fun v:Plane×Rn m => (min v.1.1 v.1.2,v.2)) from by fun_prop)
  have hh : Measurable m₂ := measurable_const.sub (e.meas.comp (show Measurable (fun v:Plane×Rn m => (max v.1.1 v.1.2,v.2)) from by fun_prop))
  exact (show Measurable (fun _:Plane × Rn m=> (1/2:ℝ)) from measurable_const).smul ((he.mul hh).add (hh.mul he))
lemma nt_mixed : mixed e.NTm := by
  let f := fun v:Plane × Rn m => e.P (min v.1.1 v.1.2) v.2
  let g := fun v:Plane × Rn m => e.P (max v.1.1 v.1.2) v.2
  have hf : PolyBound f := PolyBound.of_bound 1 fun v=> e.Pcont ..
  have hg : PolyBound g := PolyBound.of_bound 1 fun v=> e.Pcont ..
  have hh := (PolyBound.const 1).sub hg
  have hp : PolyBound e.NTm.uncurry :=
    (PolyBound.const _).smul ((hf.mul hh).add (hh.mul hf))
  apply mixed.of_cutoff hp e.r_poly
  rintro ⟨z,w⟩ x hx
  let c := e.radius x
  change c < max ‖z‖ ‖w‖ at hx
  have hr : c< max z w ∨ min z w < -c := by
    simp only [Real.norm_eq_abs,lt_max_iff,lt_abs,min_lt_iff] at *
    grind
  rcases hr with h|h
  · simp only [NTm,e.tend_pos (max z w) x h,sub_self,jprod,mul_zero,zero_mul,add_zero,smul_zero]
  have he : e.P (min z w) x=0 := e.tend_neg _ _ (show c < -min z w by linarith)
  simp [NTm,he,jprod]

lemma n0_meas : StronglyMeasurable e.nt0.uncurry := (meas_trN.comp e.nt_meas).stronglyMeasurable
lemma n0_mixed : mixed e.nt0 := by
  let f := fun (_:Plane) (_:Rn m) => ‖(trL:Mat m→L[ℝ]ℝ)‖
  have hf : PolyBound f.uncurry := PolyBound.const _
  apply e.nt_mixed.product hf
  intro u x
  unfold nt0 f
  rw [← trL_apply,Real.norm_of_nonneg (norm_nonneg (trL:Mat m→L[ℝ]ℝ)),mul_comm]
  apply ContinuousLinearMap.le_opNorm
lemma n0_i (x:Rn m) : Integrable (fun u=> e.nt0 u x) :=
  mixed_integrable_left e.n0_mixed x
    ((e.n0_meas.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
lemma n0_int : Integrable e.nt0.uncurry (volume.prod (normal m)) :=
  mixed_integrable e.n0_mixed e.n0_meas.aestronglyMeasurable

-- reflection swap on ordered band
lemma nt_ref (u x) : e.ref.nt0 (-u.swap) x=e.nt0 u x := by
  change trN (jprod (1-e.P (-(min (-u.2) (-u.1))) x) (1-(1-e.P (-(max (-u.2) (-u.1))) x)))= _
  rw [show -(min (-u.2) (-u.1))=max u.1 u.2 from by grind, show -(max (-u.2) (-u.1))=min u.1 u.2 from by grind]
  simp [nt0,NTm,jprod,add_comm]

lemma meas_BS : MeasurableSet BandS :=
  ((isClosed_le continuous_const continuous_snd).inter
    ((isClosed_le continuous_snd.neg continuous_fst).inter
      (isClosed_le continuous_fst continuous_snd))).measurableSet

variable [NeZero m]

lemma band_area (x:Rn m) :
    (∫ u:Plane in BandS,e.nt0 u x) ≤ 4*∫ l,e.beta x l := by
  classical
  let f := fun u:Plane=> e.nt0 u x
  let g := BandS.indicator f
  have hi := (e.n0_i x).indicator meas_BS
  have he (z:ℝ) :
      (∫ l:ℝ,g (l,z)) ≤ 4*e.beta x z := by
    by_cases hz : 0≤z
    · have hh : (fun l:ℝ=>g (l,z)) = (Icc (-z) z).indicator (e.ntb x z) := by
        ext l
        by_cases hu:l∈Icc (-z) z
        · have hh : l≤z := hu.2
          unfold g; rw [indicator_of_mem (show (l,z)∈BandS from ⟨hz,hu⟩),indicator_of_mem hu]
          unfold f ntb nt0 NTm
          simp only [min_eq_left hh,max_eq_right hh,trN_j]
        unfold g; rw [indicator_of_notMem (show (l,z)∉BandS from fun h=>hu h.2),indicator_of_notMem hu]
      apply le_trans _ (e.band x z hz)
      rw [intervalIntegral.integral_of_le (by linarith),hh,integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc]
    have hh : (fun l:ℝ=>g (l,z))=fun _=>0 := by
      ext l
      exact indicator_of_notMem (show (l,z)∉BandS from fun h=> hz h.1) f
    rw [hh,integral_zero]; exact mul_nonneg (by norm_num) (e.beta_bound ..).1
  have hb : Integrable (e.beta x) := mixed_integrable_left e.beta_mixed x
    (e.meas_beta.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  rw [← integral_indicator meas_BS]
  change (∫ u:Plane,g u ∂volume.prod volume) ≤ _
  rw [integral_prod_symm _ hi,← integral_const_mul]
  exact integral_mono hi.integral_prod_right (hb.const_mul _) he

lemma rs_int (f:Plane→ℝ) : (∫ u,f (rs u))=∫ u,f u := by
  change (∫ u:Plane,(fun u=>f (-u)) u.swap ∂volume.prod volume)=∫ u,f u
  rw [integral_prod_swap (fun u:Plane=> f (-u))]
  exact integral_neg_eq_self f volume

lemma total_surplus (x:Rn m) :
    (∫ u:Plane,e.nt0 u x) ≤ 8*((∫ l,e.beta x l)+(∫ l,e.ref.beta x l)) := by
  classical
  let f := fun u:Plane=>e.nt0 u x
  let g := BandS.indicator f
  let h := BandS.indicator fun u:Plane=>e.ref.nt0 u x
  have he (u:Plane) :
      f u ≤ g u+g u.swap+h (rs u)+h (rs u.swap) := by
    have hi (w:Plane) : h (rs w)=if rs w∈BandS then f w else 0 := by
      unfold h; simp [indicator,e.nt_ref,f,rs]; rfl
    rw [hi,hi]
    have Hv : f u.swap=f u := e.nt_sym ..
    unfold g
    rw [Set.indicator_apply,Set.indicator_apply]
    rw [Hv]
    have hx := e.nt_pos u x
    change 0 ≤ f u at hx
    by_cases hs:u.1≤u.2
    · by_cases ht:0≤u.1+u.2
      · have hb:u∈BandS := by change 0≤_ ∧ _ ≤ _ ∧ _ ≤ _; grind
        split_ifs <;> linarith
      have hb:rs u∈BandS := by change 0 ≤ -_ ∧ - -_ ≤ -_ ∧ -_ ≤ -_; grind
      split_ifs <;> linarith
    by_cases ht:0≤u.1+u.2
    · have hb:u.swap∈BandS := by change 0≤u.1∧ _≤u.2 ∧ _ ≤ u.1; grind
      split_ifs <;> linarith
    have hb:rs u.swap∈BandS := by change 0≤ -u.2∧ - -u.2≤ -u.1 ∧ -u.1≤ -u.2; grind
    split_ifs <;> linarith
  have hi : Integrable f := e.n0_i x
  have hg : Integrable g := hi.indicator meas_BS
  have hh : Integrable h := (e.ref.n0_i x).indicator meas_BS
  have hu : Integrable (fun u=> h (rs u)) := by
    have ha : Integrable (fun u=>h (-u)) :=
      (Measure.measurePreserving_neg volume).integrable_comp_emb (Homeomorph.neg _).measurableEmbedding |>.mpr hh
    apply ha.swap
  apply le_trans (integral_mono hi (((hg.add hg.swap).add hu).add hu.swap) he)
  let v := fun u=>h (rs u)
  change (∫ u:Plane,g u+g u.swap+v u+v u.swap) ≤ _
  rw [integral_add, integral_add, integral_add]
  · have Hb := e.band_area x
    have Hc := e.ref.band_area x
    rw [← integral_indicator meas_BS] at Hb Hc
    have Hv := rs_int h
    change (∫ u,v u)=_ at Hv
    have H₁ (f:Plane→ℝ) : (∫ u:Plane,f u.swap)=∫ u,f u := integral_prod_swap _
    rw [H₁,H₁,Hv]
    change (∫ u,g u) ≤ _ at Hb; change (∫ u,h u) ≤ _ at Hc
    linarith
  all_goals first | exact hg | exact hg.swap | exact hu |
    exact hu.swap | exact hg.add hg.swap | exact (hg.add hg.swap).add hu

end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_GainFinal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Combine the log-gains of the two matrices. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ} [NeZero m]

lemma eGain_exact (e:Edge m) : eGain e= LC 0 +
    (∫ x,(∫ z,e.LinearT z x) ∂normal m)+surplus e := by
  unfold eGain surplus
  simp_rw [e.gain_exact]
  have hi := (mixed_integrable e.mixed_T (μ:=volume) (ν:=normal m)
    e.meas_T.aestronglyMeasurable).integral_prod_right
  have hh := (mixed_integrable e.beta_mixed (μ:=volume) (ν:=normal m)
    e.meas_beta.aestronglyMeasurable).integral_prod_right
  rw [integral_add,integral_add]
  · simp
  all_goals first | exact integrable_const _ | exact hi | exact hh |
    exact (integrable_const _).add hi

lemma surplus_lower (e:Edge m) : eNt e/8 ≤ surplus e+surplus e.ref := by
  rw [div_le_iff₀ (by norm_num : 0 < (8:ℝ))]
  unfold eNt surplus; rw [integral_integral_swap]
  have hh (e:Edge m) := (mixed_integrable e.beta_mixed (μ:=volume) (ν:=normal m)
    e.meas_beta.aestronglyMeasurable).integral_prod_right
  · rw [← integral_add (show Integrable (fun x=>∫ z,e.beta x z) (normal m) from hh e)
      (show Integrable (fun x=>∫ z,e.ref.beta x z) (normal m) from hh e.ref),mul_comm _ 8,
      ← integral_const_mul]
    exact integral_mono e.n0_int.integral_prod_right (((hh e).add (hh e.ref)).const_mul _)
      (fun x=>e.total_surplus x)
  exact e.n0_int
namespace Edge
lemma pm_lin (e:Edge m) : mixed e.Plin := by
  have h := mixed.of_rapid (Y:=Rn m) (rapid_p.product poly_mj)
  convert e.mixed_T.sub h using 1
  all_goals try with_reducible_and_instances rfl
  funext z x; unfold Plin LinearT; ring
omit [NeZero m] in
lemma plSM (e:Edge m) : StronglyMeasurable e.Plin.uncurry :=
  (((c_mj.measurable.comp measurable_fst)).mul
    (e.meas_h1.sub (cp.measurable.comp measurable_fst))).stronglyMeasurable

lemma lin_alt (e:Edge m) (x) :
    LC 0+(∫ z,e.LinearT z x)=(∫ z,phi z*LC z)+(∫ z,e.Plin z x) := by
  rw [lc_integral_equiv]
  have hi : Integrable (fun z=>e.Plin z x) := mixed_integrable_left e.pm_lin x
    ((e.plSM.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  have hh := (rapid_p.product poly_mj).integrable_real
    ((cp.measurable.sub measurable_st).mul c_mj.measurable)
  rw [add_assoc,← integral_add hh hi]
  congr 2; ext x; unfold LinearT Plin; ring

lemma gain_alt (e:Edge m) :
    eGain e=(∫ z,phi z*LC z) +
      (∫ x,(∫ z,e.Plin z x) ∂normal m)+surplus e := by
  rw [eGain_exact]
  have hi := (mixed_integrable e.pm_lin (μ:=volume) (ν:=normal m)
    e.plSM.aestronglyMeasurable).integral_prod_right
  have hh := (mixed_integrable e.mixed_T (μ:=volume) (ν:=normal m)
    e.meas_T.aestronglyMeasurable).integral_prod_right
  congr 1
  have he : (∫ x:Rn m,(LC 0+∫ z,e.LinearT z x) ∂normal m) =
      (∫ x:Rn m,((∫ z,phi z*LC z)+∫ z,e.Plin z x) ∂normal m) := by
    congr 1; ext x; rw [lin_alt]
  rw [integral_add,integral_add] at he
  · simpa using he
  all_goals first | exact integrable_const _ | exact hi | exact hh

lemma h1_ref (e:Edge m) (x z) : e.ref.h1 x (-z)=1-e.h1 x z := by
  unfold ref h1; simp only [neg_neg,trN_sub,trN_one]
end Edge
namespace ProjField
variable (q:ProjField m)
lemma vp_lin (x) : (∫ z,q.edge.Plin z x)+(∫ z,q.edge.ref.Plin z x) = -trN (q.Hmat Profile.v x) := by
  have hi (e:Edge m) : Integrable (fun z=>e.Plin z x) := mixed_integrable_left e.pm_lin x
    ((e.plSM.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  let g := fun z=>q.edge.ref.Plin z x
  have hh : Integrable (fun z:ℝ=>g (-z)) :=
    ((Measure.measurePreserving_neg volume).integrable_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding).mpr (hi _)
  change (∫ z,q.edge.Plin z x)+(∫ z,g z)=_
  rw [← integral_neg_eq_self g volume,← integral_add (hi _) hh]
  unfold Hmat; rw [← trL_apply,← trL.integral_comp_comm
    (q.H_left_int (v_test.der.poly) _), ← integral_neg]
  congr 1
  ext z
  unfold kerH g Edge.Plin
  rw [_root_.map_smul,trL_apply,Edge.h1_ref,neg_p,v_deriv, PD,trN_sub,trN_smul,trN_one]
  change _+ _ = -(_*((p z*1)-q.edge.h1 x z))
  ring

lemma gain_eq11 :
    2*(∫ z,phi z*LC z) - et (q.Hmat v) + eNt q.edge/8 ≤
      eGain q.edge + eGain q.edge.ref := by
  have hi (e:Edge m) : Integrable (fun x=>∫ z,e.Plin z x) (normal m) :=
    (mixed_integrable e.pm_lin (μ:=volume) (ν:=normal m)
      e.plSM.aestronglyMeasurable).integral_prod_right
  rw [Edge.gain_alt,Edge.gain_alt]
  have hh := integral_add (hi q.edge) (hi q.edge.ref)
  change (∫ x,(∫ z,q.edge.Plin z x)+(∫ z,q.edge.ref.Plin z x) ∂normal m) = _ at hh
  simp_rw [q.vp_lin] at hh; rw [integral_neg] at hh
  unfold et
  linarith [surplus_lower q.edge]
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Entropy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Entropy bound (10), in normalized trace notation. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma etL_apply (B A:Mat m) : etL B A=trN (B*A) := by simp [etL]

omit [NeZero m] in
lemma int_etw (B:Mat m) {A:Rn m→Mat m} (h:Integrable A (normal m)) :
    Integrable (fun x=>trN (B*A x)) (normal m) := by
  simp_rw [← etL_apply]
  exact (etL B).integrable_comp h

omit [NeZero m] in
lemma etw_add {A:Rn m→Mat m} (h:Integrable A (normal m)) (B C:Mat m) :
    etw (B+C) A=etw B A + etw C A := by
  unfold etw et; simp_rw [add_mul,trN_add]
  exact integral_add (int_etw _ h) (int_etw _ h)

namespace ProjField
variable (q:ProjField m)
lemma h_weighted {f:ℝ→ℝ} (hf:TestF f) :
    etw q.covMat (q.Hmat f) = ∫ x,q.dm x*f x := by
  let l := etL q.covMat
  have hp := hf.der.poly
  have hm := q.H_mixed hp
  have hi := mixed_integrable (ν:=normal m) (μ:=volume) hm q.H_sm.aestronglyMeasurable
  have he (x:Rn m) : trN (q.covMat*q.Hmat f x) = ∫ z,l (q.kerH f z x) := by
    rw [← etL_apply,l.integral_comp_comm (q.H_left_int hp _)]
    rfl
  have hy (z:ℝ) : (∫ x,l (q.kerH f z x) ∂normal m)=- (q.hDel z*deriv f z) := by
    let P := q.Pmat z
    have iP : Integrable P (normal m) := meanJac_integrable ..
    have ie : (∫ x,P x ∂normal m)=meanJac q.C q.root (q.shift z) := rfl
    have hP : Integrable (fun x=> p z • (1:Mat m)- P x) (normal m) :=
      (integrable_const _).sub iP
    rw [l.integral_comp_comm (show Integrable (q.kerH f z) (normal m) from hP.smul (deriv f z))]
    change l (∫ x,deriv f z • (p z • (1:Mat m)-P x) ∂normal m)=_
    rw [integral_smul,integral_sub (integrable_const _) iP,ie]
    simp only [integral_const, probReal_univ, one_smul,_root_.map_smul,smul_eq_mul,
      _root_.map_sub,l, etL_apply,mul_one,hDel,avH,s0]
    ring
  rw [q.hd_test hf]; unfold etw et; simp_rw [he]
  rw [integral_integral_swap]
  · simp_rw [hy]; rw [integral_neg]
  have hh : Integrable (fun u:ℝ×Rn m=>l (q.kerH f u.1 u.2)) (volume.prod (normal m)) :=
    l.integrable_comp hi
  exact hh.swap

omit [NeZero m] in
lemma logD_cov : logD q.covMat=2*logD q.S := by
  unfold covMat logD
  rw [det_mul,Real.log_mul q.pos.det_pos.ne' q.pos.det_pos.ne']
  ring

/-- entropy bound Eq10. Replacing τ log by logD is a notation choice;
see trN_logD_eq. -/
theorem entropy10 {T:Mat m} (he:1+T=q.covMat) :
    logD q.covMat - trN T + etw T (q.Hmat v) - q.delt d + eNt q.edge/8 ≤
      Real.log (chi q.C q.V*chi q.D q.U)/m := by
  have hp := q.pos.det_pos
  have HH : q.V ∈ interior ((posDual q.C):Set (Rn m)) := q.V_in
  have hc := chi_pos (C:=q.C) ⟨q.U,q.U_in⟩ q.V_in
  have hq : q.U ∈ interior ((posDual q.D):Set (Rn m)) := by
    rw [show posDual q.D=q.C from ProperCone.innerDual_innerDual _]; exact q.U_in
  have hd := chi_pos (C:=q.D) ⟨q.V,q.V_in⟩ hq
  have hX := q.primalMap.entropy q.V HH hp.ne'
  have hv : (-q.S).det≠0 := by rw [det_neg]; positivity
  have hY := q.dualMap.entropy q.U hq hv
  rw [q.X_cost] at hX; rw [q.Y_cost] at hY
  change -logN0+1/2+logD q.S+eGain q.edge-m/(m:ℝ) ≤ _ at hX
  change -logN0+1/2+logD (-q.S)+eGain q.edge.ref-q.cBy*m/(m:ℝ) ≤ _ at hY
  change _ ≤ Real.log (chi q.C q.V)/m at hX
  change _ ≤ Real.log (chi q.D q.U)/m at hY
  have hg := q.gain_eq11; rw [LC_average] at hg
  rw [q.cBy_eq,q.logD_cov,Real.log_mul hc.ne' hd.ne',add_div]
  have hm := m_pos (m:=m)
  rw [div_self hm.ne'] at hX
  have heq : logD (-q.S)=logD q.S := by
    rw [logD,det_neg,Real.log_mul (by positivity) hp.ne',Real.log_pow]
    simp [logD]
  rw [heq,mul_div_cancel_right₀ _ hm.ne'] at hY
  have hu := q.h_weighted v_test
  rw [← he,etw_add (q.H_integrable v_test.der.poly)] at hu
  have ht : q.s0=1+trN T := by rw [s0,← he,trN_add,trN_one]
  rw [show etw 1 (q.Hmat v)= _ from (show etw 1 (q.Hmat v)=et (q.Hmat v) by simp [etw])] at hu
  linarith

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_Multi
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Tensor Hermite modes, Gaussian multivariate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
open Layers
variable {m:ℕ}

lemma ee (x:Rn m) (i) : ⟪x,e i⟫=x i := by
  rw [real_inner_comm]; exact ((EuclideanSpace.basisFun ..).repr_apply_apply _ _).symm
lemma dir_line (x:Rn m) (i:Fin m) :
    HasDerivAt (fun t:ℝ=>x+t • e i) (e i) 0 := by
  convert (((hasDerivAt_id' (0:ℝ)).smul_const (e i)).const_add x) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | simp
lemma part_lower (a:MI m) (i) (x:Rn m) :
    fderiv ℝ (MM a) x (e i)=sn (a i)*MM (decM a i) x := by
  let L := fun t:ℝ=> x+t • e i
  have hL : L 0=x := by simp [L]
  let v := ∏ j ∈ Finset.univ.erase i,H (a j) (x j)
  have he : MM a ∘ L=fun t=> H (a i) (x i+t)*v := by
    ext t
    rw [Function.comp_apply,factor _ _ i,show L t i=x i+t from ?_]
    · congr 1
      apply Finset.prod_congr rfl; intro j hj
      have hh : i≠j := (Finset.ne_of_mem_erase hj).symm
      simp [L,e,hh]
    simp [L,e]
  have hi : HasDerivAt (MM a ∘ L) (fderiv ℝ (MM a) x (e i)) 0 := by
    convert ((M_diff a (L 0)).hasFDerivAt.comp_hasDerivAt 0 (dir_line x i)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | rw [hL]
  have hu : HasDerivAt (MM a ∘ L) (deriv (H (a i)) (x i)*v) 0 := by
    rw [he]
    have hh := ((((ht (a i)).diff (x i+ (0:ℝ))).hasDerivAt).comp 0
      ((hasDerivAt_id' (0:ℝ)).const_add (x i))).mul_const v
    simpa [Function.comp_def] using hh
  rw [hi.unique hu,Hder, decM,factor_upd]
  unfold v; ring
end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_Gradient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Hermite coefficient recurrence for functions with suitable local
Lipschitz bounds. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Metric Real ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ}
variable {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
lemma shift_bound_poly {f:Rn m→F} (hf:PolyBound f) :
    ∃ g:Rn m→ℝ, PolyBound g ∧ Continuous g ∧ ∀ x y:Rn m, y∈closedBall x 1 → ‖f y‖ ≤ g x := by
  obtain ⟨C,n,hc,h⟩ := hf
  let g := fun x:Rn m=> C*(2+‖x‖)^n
  refine ⟨g,(PolyBound.const _).mul (((PolyBound.const _).add PolyBound.id.norm).pow _),
    by unfold g; fun_prop,fun x y hy => ?_⟩
  apply le_trans (h y)
  unfold g; gcongr C * ?_ ^ n; change dist y x ≤ 1 at hy; rw [dist_eq_norm] at hy
  have he : ‖y‖ ≤ ‖y-x‖+‖x‖ := by simpa using norm_add_le (y-x) x
  linarith

namespace PLip
omit [FiniteDimensional ℝ F] in
lemma smul {f:Rn m→ℝ} {h:Rn m→F} (hf:PolyBound f) (hh:PolyBound h) -- measurable h via cont
    (hc:Continuous h) (hl:PLip f) (hl':PLip h) : PLip fun x=> f x • h x := by
  obtain ⟨g,hg,hg',H⟩ := shift_bound_poly hf
  obtain ⟨c,h₁,h₂,he⟩ := hl
  obtain ⟨d,h₃,h₄,ht⟩ := hl'
  let k := fun x=> g x*d x + ‖h x‖*c x
  refine ⟨k,(hg.mul h₃).add (hh.norm.mul h₁),(hg'.mul h₄).add (hc.norm.mul h₂),fun x b hb => ?_⟩
  have hy : x+b∈closedBall x 1 := by simpa only [mem_closedBall,dist_eq_norm,
    add_sub_cancel_left] using hb.le
  have hh := H x (x+b) hy
  have ha := he x b hb
  have hu := ht x b hb
  have hp : 0 ≤ g x := le_trans (norm_nonneg _) hh
  calc
    _ = ‖f (x+b) • (h (x+b)-h x) + (f (x+b)-f x) • h x‖ := by rw [smul_sub,sub_smul]; congr 1; abel
    _ ≤ _ := norm_add_le ..
    _ ≤ k x*‖b‖ := by
      rw [norm_smul,norm_smul]
      apply le_trans (add_le_add (mul_le_mul hh hu (norm_nonneg _) hp)
        (mul_le_mul_of_nonneg_right ha (norm_nonneg _)))
      apply le_of_eq; unfold k; ring
omit [FiniteDimensional ℝ F] in
lemma fd {f:Rn m→F} (hf:Differentiable ℝ f)
    (hp:PolyBound (fderiv ℝ f)) : PLip f := by
  obtain ⟨g,hg,hc,h⟩ := shift_bound_poly hp
  use g
  refine ⟨hg,hc,fun x b hb=>?_⟩
  have hs := closedBall x (1:ℝ)
  have hy : x+b∈closedBall x 1 := by change dist (x+b) x≤1; simpa [dist_eq_norm] using hb.le
  have he := (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le (fun y _=>hf y)
    (fun y hy => h x y hy) (mem_closedBall_self (by norm_num)) hy
  simpa only [add_sub_cancel_left] using he
end PLip

lemma p_sum {I X F:Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup F]
    {f:I→X→F} (h:∀ i,PolyBound (f i)) (s:Finset I) :
    PolyBound fun x=> ∑ i∈s, f i x := by
  classical
  induction s using Finset.induction with
  | empty=>simpa using PolyBound.const (X:=X) (0:F)
  | insert x u h' ih=>simpa [h'] using (h x).add ih

lemma fdMP (a:MI m) : PolyBound (fderiv ℝ (MM a)) := by
  let B := EuclideanSpace.basisFun (Fin m) ℝ
  let g := fun i (x:Rn m)=> (sn (a i)*MM (decM a i) x) • (ProjField.coord i)
  have he (x:Rn m) : fderiv ℝ (MM a) x = ∑ i, g i x := by
    ext y
    have hl := B.sum_repr y
    calc
      _ = ∑ i, B.repr y i * (fderiv ℝ (MM a) x (e i)) := by
        conv_lhs => rw [← hl]
        rw [_root_.map_sum]; simp [B,e]
      _ = _ := by simp_rw [part_lower]; simp [g,B,mul_comm]
  rw [show fderiv ℝ (MM a)=_ from funext he]
  apply p_sum (f:=g)
  intro i
  exact ((PolyBound.const _).mul (M_poly _)).smul (PolyBound.const _)

omit [FiniteDimensional ℝ F] in
lemma i_cof {f:Rn m→F} (hf:PolyBound f) (hm:AEStronglyMeasurable f (normal m)) (a:MI m) :
    Integrable (fun x=>MM a x • f x) (normal m) :=
  ((M_poly a).smul hf).gaussian_integrable ((M_cont a).aestronglyMeasurable.smul hm)
lemma coef_raise {f:Rn m→F} (hf:PolyBound f) (hF:PLip f) (hc:Continuous f)
    {D:Rn m→(Rn m→L[ℝ]F)}
    (hD:∀ᵐ x∂normal m,HasFDerivAt f (D x) x)
    (i:Fin m)
    (hP:PolyBound (fun x=> D x (e i))) (hm:AEStronglyMeasurable (fun x=>D x (e i)) (normal m))
    (a:MI m) :
    cof (fun x=> D x (e i)) a=sn (a i+1) • cof f (inc a i) := by
  let g := fun x=> MM a x • f x
  obtain ⟨b,h₁,h₂,hb⟩ :=
    PLip.smul (M_poly a) hf hc (PLip.fd (M_diff a) (fdMP a)) hF
  have he : ∀ᵐ x∂normal m,
      DifferentiableAt ℝ g x ∧ fderiv ℝ g x (e i) =
        sn (a i) • (MM (decM a i) x • f x)+ MM a x • D x (e i) := by
    filter_upwards [hD] with x hx
    have hh := (M_diff a x).hasFDerivAt.smul hx
    refine ⟨hh.differentiableAt,?_⟩
    rw [show fderiv ℝ g x=_ from hh.fderiv]
    simp only [_root_.add_apply,_root_.smul_apply,smulRight_apply,part_lower,mul_smul]; rw [add_comm]
  have h := normal_IBP (f:=g) ((M_poly a).smul hf) ((M_cont a).smul hc)
    (he.mono fun x hx=> hx.1) (h₁.gaussian_integrable h₂.aestronglyMeasurable) hb (e i)
  have hi := i_cof hP hm a
  have ih (a) := i_cof hf hc.aestronglyMeasurable a
  have hr (x:Rn m) :
      ⟪x,e i⟫ • g x=sn (a i+1) • (MM (inc a i) x • f x)+sn (a i) • (MM (decM a i) x • f x) := by
    rw [ee]; unfold g
    simp only [smul_smul,ladder,add_smul]
  rw [integral_congr_ae (he.mono fun x hx=>hx.2)] at h; simp_rw [hr] at h
  rw [integral_add,integral_add,integral_smul,integral_smul] at h
  · exact add_left_cancel (h.trans (add_comm _ _))
  all_goals first | exact (ih _).smul (_:ℝ) | exact hi
end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_Pair
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Parseval identities for finite-dimensional Gaussian fields and bilinear pairings. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ} [NeZero m]
variable {F E:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace regular
variable {f:Rn m→F} (hf:regular f)
omit [NeZero m] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
lemma ig (hf:regular f) : Integrable f (normal m) :=
  hf.p.gaussian_integrable hf.meas
omit [NeZero m] [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] in
lemma lin (hf:regular f) (l:F→L[ℝ]E) :
    regular (fun x=>l (f x)) := ⟨(PolyBound.clm _).comp hf.p,(l.integrable_comp hf.ig).aestronglyMeasurable⟩
omit [NeZero m] [FiniteDimensional ℝ F] in
lemma smul (hf:regular f) {g:Rn m→ℝ} (hg:regular g) : regular fun x=>g x • f x :=
  ⟨hg.p.smul hf.p,hg.meas.smul hf.meas⟩
omit [NeZero m] in
lemma mul {f g:Rn m→ℝ} (hf:regular f) (hg:regular g) : regular fun x=>f x*g x := hg.smul hf
end regular

end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_CovHerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Eq13 coefficient-pair (weighted K multiplier via coefficients). -/
noncomputable section
open Set Filter Metric MeasureTheory MeasureTheory.Measure Matrix Real
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma pJ_eq (B A C:Mat m) : PJ B A C=Pj B A C := by simp [PJ,Pj,jprod,mul_add, trN_add,trN_smul,etL_apply]

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Frame_Diagonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Borel choice of diagonalizing frame. Everything computed in a
diagonalization is defined on a full orthogonal matrix and its entries. -/
noncomputable section
open Set Filter MeasureTheory Metric Matrix Real
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m:ℕ}
namespace Frm
variable (u v:Frm m)
lemma m₂ : u.val*star u.val=1 := u.property.2

lemma fix_loc (A:Mat m) : u.fixMat (u.loc A)=A := by
  unfold loc fixMat; simp only [mul_assoc]
  rw [u.m₂,mul_one,← mul_assoc,u.m₂,one_mul]

lemma loc_inj : Function.Injective u.loc := fun _ b h =>
  (u.fix_loc _).symm.trans ((congrArg u.fixMat h).trans (u.fix_loc b))

lemma loc_mul (A B:Mat m) : u.loc (A*B)=u.loc A*u.loc B := by
  unfold loc; simp only [mul_assoc]
  rw [show u.val*(star u.val*(B*u.val))=B*u.val from by rw [← mul_assoc,u.m₂,one_mul]]

lemma loc_star (A:Mat m) : u.loc (star A)=star (u.loc A) := by
  unfold loc; rw [star_mul,star_mul,star_star,mul_assoc]
lemma loc_trace (A:Mat m) : trace (u.loc A) = trace A := by
  unfold loc; rw [trace_mul_comm,← mul_assoc,u.m₂,one_mul]
lemma loc_norm (A:Mat m) : ‖u.loc A‖=‖A‖ := by
  unfold loc; rw [CStarRing.norm_mul_mem_unitary _ u.property,CStarRing.norm_mem_unitary_mul]
  exact (star u).property

lemma loc_zero : u.loc 0=0 := by simp [loc]

lemma fix_mul_cross (A:Mat m) :
    star u.val*A*v.val=u.loc A*(star u.val*v.val) := by
  unfold loc; simp only [mul_assoc]
  rw [show u.val*(star u.val*v.val)=v.val from by rw [← mul_assoc,u.m₂,one_mul]]
lemma fix_mul_cross' (A:Mat m) :
    star u.val*A*v.val= (star u.val*v.val)*v.loc A := by
  unfold loc
  simp only [mul_assoc]
  rw [show v.val*(star v.val*(A*v.val))=A*v.val from by rw [← mul_assoc,v.m₂,one_mul]]

lemma cross_cancel (A B:Mat m) (h:star u.val*A*v.val= star u.val*B*v.val) : A=B := by
  have hi (A:Mat m) : u.val*(star u.val*A*v.val)*star v.val=A := by
    simp only [mul_assoc]; rw [v.m₂,mul_one,← mul_assoc,u.m₂,one_mul]
  exact (hi A).symm.trans ((congrArg (fun x=> u.val*x*star v.val) h).trans (hi B))

lemma lSpecEq (A:Mat m) (f:ℝ→ℝ) : u.loc (u.specEval A f) = Matrix.diagonal (fun i=> f (u.eig A i)) :=
  u.loc_fix ..

lemma frame_cross {A:Mat m} (h:u.Dgn A) (g:v.Dgn A) (i j):
    u.eig A i*(star u.val*v.val) i j=(star u.val*v.val) i j*v.eig A j := by
  have hh := (u.fix_mul_cross v A).symm.trans (u.fix_mul_cross' v A)
  rw [show u.loc A=_ from h, show v.loc A=_ from g] at hh
  simpa only [Matrix.diagonal_mul,Matrix.mul_diagonal] using congrFun (congrFun hh i) j

lemma spec_unique {A:Mat m} (h:u.Dgn A) (g:v.Dgn A) (f:ℝ→ℝ) :
    u.specEval A f=v.specEval A f := by
  apply u.cross_cancel v
  rw [u.fix_mul_cross,u.fix_mul_cross',u.lSpecEq,v.lSpecEq]
  ext i j
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal]
  have hh := u.frame_cross v h g i j
  rcases eq_or_ne ((star u.val*v.val) i j) 0 with hz|hz
  · simp [hz]
  have he : u.eig A i=v.eig A j := mul_right_cancel₀ hz (hh.trans (mul_comm ..))
  rw [he,mul_comm]

lemma loc_cfc {A:Mat m} (h:A.IsHermitian) (hu:u.Dgn A) (f:ℝ→ℝ) :
    u.loc (cfc f A)= Matrix.diagonal (fun i=>f (u.eig A i)) := by
  rw [← u.lSpecEq A]
  congr 1
  rw [u.spec_unique (eu h) hu (eu_d h) f,specEval,eu_eig]
  open Unitary in
    rw [Matrix.IsHermitian.cfc_eq h,Matrix.IsHermitian.cfc,conjStarAlgAut_apply]
    simp only [Function.comp_def]
    rfl

lemma fr_m : Measurable (@fr m) := selectU.choose_spec.1
lemma fr_d (A:SH m) : (fr A).Dgn A.val := selectU.choose_spec.2 A
end Frm
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Indicator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! p-to-indicator score and layer integration formulas. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile
lemma jump_m : Measurable (Function.uncurry jump) :=
  Measurable.ite ((isClosed_le continuous_snd continuous_fst).measurableSet)
    measurable_const measurable_const
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Threshold
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Thresholds of arbitrary moderate-growth random Hermitian fields
(in particular A and L) §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

namespace FieldMat
variable (B:FieldMat m)
lemma Fr_D (x) : (B.Fr x).Dgn (B.A x) := Frm.fr_d _
lemma fr_m : Measurable B.Fr := Frm.fr_m.comp (B.hM.measurable.subtype_mk (h:=B.sym))
lemma ev_m (i) : Measurable fun x=> B.ev x i :=
  (measurable_pi_iff.mp (Frm.cdiag.measurable.comp
    (Frm.cont_loc.measurable.comp (B.hM.measurable.prodMk B.fr_m)))) i

lemma evfrm (x) (f) :
    (B.Fr x).loc (B.eval f x)= Matrix.diagonal (fun i=> f (B.ev x i)) :=
  Frm.loc_cfc _ (B.sym x) (B.Fr_D x) f
lemma evfrm' (x) (f) : B.eval f x= (B.Fr x).fixMat (Matrix.diagonal (fun i=> f (B.ev x i))) := by
  rw [← B.evfrm x f,Frm.fix_loc]

lemma theta_gen_meas {f:ℝ→ℝ→ℝ} (hf:Measurable f.uncurry) :
    Measurable (fun u:ℝ × Rn m=>B.eval (f u.1) u.2) := by
  simp_rw [B.evfrm',Frm.fixMat]
  have hg : Measurable (fun u:ℝ×Rn m=>(B.Fr u.2).val) :=
    measurable_subtype_coe.comp (B.fr_m.comp measurable_snd)
  have hh : Measurable fun u:ℝ×Rn m=> Matrix.diagonal (fun i=> f u.1 (B.ev u.2 i)) :=
    Frm.cdiagonal.measurable.comp (measurable_pi_iff.mpr fun i=> hf.comp
      (measurable_fst.prodMk ((B.ev_m _).comp measurable_snd)))
  exact (hg.mul hh).mul (continuous_star.measurable.comp hg)

lemma eval_reg {f:ℝ→ℝ} (hf:TestF f) : regular (B.eval f) := by
  have hm : Measurable (B.eval f) := by
    have h := B.theta_gen_meas (f:=fun _ x=>f x) (hf.cont.measurable.comp measurable_snd)
    exact h.comp (show Measurable (fun x:Rn m=>((0:ℝ),x)) by fun_prop)
  obtain ⟨C,n,hc,h⟩ := hf.poly
  have hp : PolyBound (fun x=>C*(1+‖B.A x‖)^n) :=
    (PolyBound.const _).mul (((PolyBound.const _).add B.poly.norm).pow _)
  refine ⟨hp.mono (fun x=>?_ ), hm.aestronglyMeasurable⟩
  apply le_trans (spectrum_poly_le f hc h (B.sym x)); exact le_abs_self _

lemma thetaM : StronglyMeasurable B.Θ.uncurry := (B.theta_gen_meas jump_m).stronglyMeasurable
lemma theta_nn (z x) : 0 ≤ B.Θ z x := by
  have hi : IsSelfAdjoint (B.A x) := B.sym x
  apply cfc_nonneg
  intro y _; unfold jump; split_ifs <;> norm_num
lemma theta_le (z x) : B.Θ z x ≤ 1 := by
  have hi := (scalar_cfc_order (jump z) (B.A x) (B.sym x) (l:=0) (r:=1)).2.mpr
    (fun y _=> by unfold jump; split_ifs <;> norm_num)
  simpa [Θ,eval,scalar] using hi
lemma theta_norm (z x) : ‖B.Θ z x‖ ≤ 1 := by
  apply spectrum_norm_box zero_le_one (B.theta_nn ..).posSemidef.1
  · apply le_trans _ (B.theta_nn z x)
    have he := scalar_le' (m:=m) (-1) 0 (by norm_num)
    simpa only [scalar, zero_smul] using he
  simpa [scalar] using B.theta_le z x

lemma theta_exact (z x) (hx : ‖B.A x‖< |z|) : B.QP z x=0 := by
  let A := B.A x
  have hi : IsSelfAdjoint A := B.sym x
  have he (t:ℝ) (ht:t∈spectrum ℝ A) : ‖t‖ ≤ ‖A‖ := by
    have h := norm_apply_le_norm_cfc id A ht
    rw [cfc_id ℝ A] at h
    exact h
  have hh : cfc (jump z) A=cfc (fun _=>st z) A := cfc_congr fun t ht=> by
    have hv := he t ht
    change ‖A‖<_ at hx
    unfold jump st; rw [Real.norm_eq_abs] at hv; split_ifs <;> grind
  unfold QP; change cfc (jump z) A-_ = _
  rw [hh,cfc_const (st z) A hi,Algebra.algebraMap_eq_smul_one,sub_self]
lemma qp_mixed : mixed B.QP := by
  apply mixed.of_cutoff
    (show PolyBound B.QP.uncurry from
      (PolyBound.of_bound (f:=B.Θ.uncurry) 1 (fun ⟨z,x⟩=>B.theta_norm z x)).sub
        ((poly_st.comp PolyBound.fst).smul (PolyBound.const (1:Mat m))))
    B.poly.norm
  exact fun z x=> B.theta_exact z x
end FieldMat
namespace ProjField
variable [NeZero m] (q:ProjField m) (B:FieldMat m)
lemma eM : mixed (q.EZ B) := by
  convert q.Pstep_mixed.sub B.qp_mixed using 1
  all_goals try with_reducible_and_instances rfl
  funext y x; simp only [EZ,Pstep,Gstep,FieldMat.QP]; abel
lemma eSM : StronglyMeasurable (q.EZ B).uncurry :=
  q.edge.meas.stronglyMeasurable.sub B.thetaM

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_EvalGap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Primitive identities and notation for layer to spectral comparisons. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

lemma pj_sym (B A C:Mat m) : Pj B A C=Pj B C A := by simp only [Pj,jprod,add_comm]
lemma j_smul_left (A C:Mat m) (a:ℝ) : jprod (a•A) C=a•jprod A C := by
  simp only [jprod,smul_mul_assoc,mul_smul_comm,smul_add]; rw [smul_comm,smul_comm (1/2:ℝ) a]
lemma pj_norm {A B C:Mat m} :
    ‖Pj B A C‖ ≤ (‖etL B‖ * ‖A‖)*‖C‖ := by
  rw [Pj,← etL_apply]
  have h : ‖jprod A C‖≤‖A‖*‖C‖ := by
    unfold jprod; rw [norm_smul,Real.norm_of_nonneg (by norm_num)]
    have hh := norm_add_le (A*C) (C*A)
    linarith [norm_mul_le A C,norm_mul_le C A]
  apply ((etL B).le_opNorm _).trans
  rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
lemma pj_scale (a b:ℝ) (B A C:Mat m) :
    Pj B (a•A) (b•C)=a*(b*Pj B A C) := by
  unfold Pj
  have h (x y:Mat m):jprod x y=jprod y x := by unfold jprod; rw [add_comm]
  rw [j_smul_left,h A,j_smul_left,h C]
  simp only [mul_smul_comm,trN_smul]

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Beta
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §04 Eq15, threshold comparison. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

lemma pj_cont (W:Mat m) : Continuous (Pj W).uncurry := by
  change Continuous (fun p:Mat m × Mat m=>Pj W p.1 p.2)
  have he : Continuous (trN:Mat m→ℝ) := by simp_rw [← funext trL_apply]; exact trL.continuous
  unfold Pj jprod
  fun_prop

lemma pj_p {X:Type*} [NormedAddCommGroup X] {f g:X→Mat m}
    (hf:PolyBound f) (hg:PolyBound g) (W:Mat m) :
    PolyBound fun x=>Pj W (f x) (g x) := by
  let h := fun x=> ‖etL W‖*‖g x‖
  have hh : PolyBound h := (PolyBound.const _).mul hg.norm
  apply PolyBound.of_prod_le hf hh
  intro x
  apply pj_norm.trans
  unfold h; rw [Real.norm_of_nonneg (by positivity)]; exact le_of_eq (by ring)
lemma pj_M (W:Mat m) {X Y:Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {f g:X→Y→Mat m} (hf:mixed f) (hg:PolyBound g.uncurry) :
    mixed (fun x y=>Pj W (f x y) (g x y)) := by
  let h := fun x y=> ‖etL W‖*‖g x y‖
  apply hf.product (g:=h)
    (show PolyBound h.uncurry from (PolyBound.const _).mul hg.norm)
  intro x y; apply pj_norm.trans
  unfold h; rw [Real.norm_of_nonneg (by positivity)]; exact le_of_eq (by ring)

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Compare
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer evaluation comparisons (16). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma pj_I (W A:Mat m) : Pj W A 1=trN (W*A) := by
  have hi : jprod A 1=A := by unfold jprod; simp only [mul_one,one_mul]; module
  unfold Pj; rw [hi]

namespace FieldMat
variable (B:FieldMat m)
omit [NeZero m] in
lemma eval_scale {f:ℝ→ℝ} (hf:TestF f) (a:ℝ) (x) :
    B.eval (fun z=>a*f z) x=a•B.eval f x := cfc_const_mul a f _ hf.cont.continuousOn
omit [NeZero m] in
lemma eval_mul {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (x) :
    B.eval (fun z=>f z*g z) x=B.eval f x*B.eval g x :=
  cfc_mul f g _ hf.cont.continuousOn hg.cont.continuousOn
omit [NeZero m] in
lemma eval_sub {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (x) :
    B.eval (fun z=>f z-g z) x=B.eval f x-B.eval g x :=
  cfc_sub f g _ hf.cont.continuousOn hg.cont.continuousOn
omit [NeZero m] in
lemma eval_const (a:ℝ) (x) : B.eval (fun _=>a) x=scalar m a := by
  unfold eval; rw [scalar_eq,cfc_const a (B.A x) (show IsSelfAdjoint (B.A x) from B.sym x)]
omit [NeZero m] in
lemma ccomm (x) (f g) : Commute (B.eval f x) (B.eval g x) := cfc_commute_cfc ..
end FieldMat
namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)

omit [NeZero m] in
lemma delta_reg {f} (hf:TestF f): regular (BDiff B f) :=
  ⟨(B.eval_reg hf).p.sub (PolyBound.const _),
    (B.eval_reg hf).meas.sub aestronglyMeasurable_const⟩

omit [NeZero m] in
lemma proj_int (W:Mat m) {f g:Rn m→Mat m} (hf:regular f) (hg:regular g) :
    Integrable (fun x=>PJ W (f x) (g x)) (normal m) := by
  simp_rw [pJ_eq]
  have h := (pj_cont W).comp_aestronglyMeasurable (hf.meas.prodMk hg.meas)
  exact (pj_p hf.p hg.p W).gaussian_integrable
    h
omit [NeZero m] in
lemma etwReg (W:Mat m) {f:Rn m→Mat m} (hf:regular f) :
    Integrable (fun x=>trN (W*f x)) (normal m) := int_etw W hf.ig

omit [NeZero m] in
lemma Delta_sub {f j} (hf:TestF f) (hj:TestF j) :
    LDel B W (fun x=>f x-j x)=LDel B W f-LDel B W j := by
  unfold LDel etw et
  have he (x:Rn m) : BDiff B (fun x=>f x-j x) x= BDiff B f x-BDiff B j x := by
    unfold BDiff; rw [B.eval_sub hf hj,ga_sub hf hj]; unfold scalar; module
  simp_rw [he,mul_sub,trN_sub]
  exact integral_sub (etwReg _ (delta_reg B hf)) (etwReg _ (delta_reg B hj))

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Frame_Sec
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Divided difference evaluated on two possibly different frames. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ}

lemma bav_con {f:ℝ→ℝ} (hf:Continuous f) : Continuous (bav f) := by
  have hm : Continuous fun p:Plane × ℝ=> f (along p.1 p.2) := by unfold along; fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hm 0 1
lemma bav_same (f:ℝ→ℝ) (x:ℝ) : bav f (x,x)=f x := by
  have he (t) : along (x,x) t=x := by unfold along; ring
  unfold bav; simp_rw [he]; simp
lemma delta_eq {f} (hf:TestF f) (x y:ℝ) :
    f x-f y=bav (deriv f) (x,y)*(x-y) := by
  have he (t:ℝ) : HasDerivAt (fun t=>along (x,y) t) (y-x) t := by
    convert ((((hasDerivAt_const t 1).sub (hasDerivAt_id' t)).mul_const x).fun_add
      ((hasDerivAt_id' t).mul_const y)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | ring
  have hd (t:ℝ) : HasDerivAt (fun t=> f (along (x,y) t)) (deriv f (along (x,y) t)*(y-x)) t :=
    ((hf.diff _).hasDerivAt).comp t (he t)
  have hc : Continuous (fun t:ℝ=> deriv f (along (x,y) t)*(y-x)) :=
    ((hf.der.cont.comp (by unfold along; fun_prop)).mul continuous_const)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>hd t)
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_mul_const,show along (x,y) 1=y from by unfold along; ring,
    show along (x,y) 0=x from by unfold along; ring] at hh
  unfold bav; linarith

lemma bav_bound {f} (hf:PolyBound f) : PolyBound (bav f) := by
  obtain ⟨C,n,hc,h⟩ := hf
  refine ⟨C,n,hc,fun u=>?_⟩
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun t=>f (along u t))
    (C:=C*(1+‖u‖)^n) (a:=0) (b:=1) ?_
  · unfold bav; convert he using 1; first | rfl | simp
  intro z hz
  have ha : 0≤z ∧ z≤1 := by rw [uIoc_of_le zero_le_one] at hz; exact ⟨le_of_lt hz.1,hz.2⟩
  apply (h _).trans
  have hb : ‖along u z‖≤‖u‖ := by
    change |(1-z)*u.1+z*u.2| ≤ max |u.1| |u.2|
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul,abs_of_nonneg ha.1,abs_of_nonneg (by linarith)]
    calc
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left |u.1| |u.2|) (sub_nonneg.mpr ha.2))
        (mul_le_mul_of_nonneg_left (le_max_right |u.1| |u.2|) ha.1)
      _ = _ := by ring
  gcongr

namespace Frm
variable (u v w:Frm m)
lemma reveal (A:Mat m) : u.showM v (u.hideM v A)=A := by
  unfold showM hideM
  simp only [mul_assoc]; rw [v.m₁,mul_one,← mul_assoc,u.m₁,one_mul]
lemma combine (C:Mat m) (v w:Frm m) :
    u.showM w C=(u.showM v C)*(v.showM w 1) := by
  unfold showM; simp only [mul_one,mul_assoc]
  rw [show v.val*(star v.val*w.val)=w.val from by rw [← mul_assoc,v.m₂,one_mul] ]

lemma sec_eq (A B C:Mat m) (g:Plane→ℝ) (i j) :
    u.showM v (u.sec v A B g C) i j = g (u.eig A i,v.eig B j)*u.showM v C i j := by
  rw [sec,reveal]; rfl

lemma Aentry (A:Mat m) (h:u.Dgn A) (i j) :
    u.showM v A i j= u.eig A i * u.showM v 1 i j := by
  unfold showM; rw [mul_one,u.fix_mul_cross v A,show u.loc A=_ from h,Matrix.diagonal_mul]
lemma Bentry (A:Mat m) (h:v.Dgn A) (i j) :
    u.showM v A i j=u.showM v 1 i j*v.eig A j := by
  unfold showM; rw [mul_one,u.fix_mul_cross' v A,show v.loc A=_ from h,Matrix.mul_diagonal]
lemma Aeval (A:Mat m) (h:A.IsHermitian) (hh:u.Dgn A) (f:ℝ→ℝ) (i j):
    u.showM v (cfc f A) i j=f (u.eig A i)*u.showM v 1 i j := by
  unfold showM; rw [mul_one,u.fix_mul_cross v,u.loc_cfc h hh f,Matrix.diagonal_mul]
lemma Beval (A:Mat m) (h:A.IsHermitian) (hh:v.Dgn A) (f:ℝ→ℝ) (i j):
    u.showM v (cfc f A) i j=u.showM v 1 i j*f (v.eig A j) := by
  unfold showM; rw [mul_one,u.fix_mul_cross' v,v.loc_cfc h hh f,Matrix.mul_diagonal]
lemma show_sub (A B:Mat m) : u.showM v (A-B)=u.showM v A-u.showM v B := by
  simp only [showM,mul_sub,sub_mul]

lemma exact_sec {A B:Mat m} (ha:A.IsHermitian) (hb:B.IsHermitian)
    (hu:u.Dgn A) (hv:v.Dgn B) {f:ℝ→ℝ} (hf:TestF f) :
    cfc f A-cfc f B=u.sec v A B (bav (deriv f)) (A-B) := by
  apply u.cross_cancel v
  change u.showM v _ = u.showM v _
  ext i j
  rw [sec_eq,u.show_sub,u.show_sub]; simp only [Matrix.sub_apply]
  rw [u.Aentry v A hu,u.Bentry v B hv,u.Aeval v A ha hu,u.Beval v B hb hv]
  have hh := delta_eq hf (u.eig A i) (v.eig B j)
  linear_combination u.showM v 1 i j*hh

-- Right frame independence for all test kernels on entries
lemma sec_ind (A B C:Mat m) (g:Plane→ℝ) (hv:v.Dgn B) (hw:w.Dgn B) :
    u.sec v A B g C=u.sec w A B g C := by
  apply u.cross_cancel w
  change u.showM w _= u.showM w _
  ext i j
  rw [sec_eq,combine u (u.sec v A B g C) v w, combine u C v w]
  simp_rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [sec_eq]
  by_cases h : v.showM w 1 k j=0
  · rw [h]; ring
  have he : v.eig B k=w.eig B j := by
    have he := (v.Aentry w B hv k j).symm.trans (v.Bentry w B hw k j)
    exact mul_right_cancel₀ h (he.trans (mul_comm ..))
  rw [he]; ring
end Frm
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MatrixDeriv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Derivative of spectral function of linear field. Avoid polynomial
approximation by exact secant identity and Borel frame compactness. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Asymptotics
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace Frm
omit [NeZero m] in
lemma cont_DL (u:Frm m) (A:Mat m) {g:Plane→ℝ} (hg:Continuous g) :
    Continuous (fun v:Mat m × Frm m=> u.DL v.2 A v.1 g) := by
  rw [continuous_clm_apply]
  intro C
  let k := fun v:Mat m × Frm m=> v.2.val
  have hk : Continuous k := continuous_subtype_val.comp continuous_snd
  change Continuous fun v:Mat m × Frm m=> u.val*(u.secDiag v.2 A v.1 g C)*star (k v)
  have ha : Continuous fun v:Mat m × Frm m=> (u.secDiag v.2 A v.1 g C) := by
    apply continuous_matrix
    intro i j
    have hi : Continuous fun v:Mat m × Frm m=> v.2.eig v.1 j :=
      (continuous_apply _).comp (cdiag.comp cont_loc)
    exact (hg.comp (continuous_const.prodMk hi)).mul ((coeffMap i j).continuous.comp
      (continuous_const.mul hk))
  exact (continuous_const.mul ha).mul hk.star

omit [NeZero m] in
lemma DL_ind (u v w:Frm m) (A B:Mat m) (g:Plane→ℝ) (hv:v.Dgn B) (hw:w.Dgn B) :
    u.DL v A B g=u.DL w A B g := by
  ext C : 1
  exact u.sec_ind v w A B C g hv hw
end Frm

section p
variable {X:Type*} [NormedAddCommGroup X]

-- Tool: matrix-coordinate bounds for moderate functions
omit [NeZero m] in
lemma mat_poly {A:X→Mat m} (ha:∀ i j:Fin m,PolyBound (fun x=>A x i j)) :
    PolyBound A := by
  classical
  let b := fun i j:Fin m=> Matrix.single i j (1:ℝ)

  let h := fun i j (x:X)=> A x i j • b i j
  have he : A=fun x=>∑ i,∑ j,h i j x := by
    ext x i j; simp [h,b,Matrix.sum_apply,Matrix.single, ite_and]
  rw [he]
  apply p_sum (f:=fun i x=>∑ j,h i j x)
  intro i; exact p_sum (f:=h i) (fun j=> (ha i j).smul (PolyBound.const _)) _
lemma unitPoly (v:X→Frm m) :
    PolyBound (fun x=> (v x).val) := PolyBound.of_bound 1 (fun x=> le_of_eq
      (CStarRing.norm_of_mem_unitary (v x).property))
lemma unitStarPoly (v:X→Frm m) :
    PolyBound (fun x=> star (v x).val) := (unitPoly v).mono fun x=> by rw [norm_star]
lemma poly_eig {A:X→Mat m} (hA:PolyBound A) (u:X→Frm m) (i:Fin m) :
    PolyBound (fun x=> (u x).eig (A x) i) := by
  have he : PolyBound (fun x=> (u x).loc (A x)) :=
    ((unitStarPoly u).mul hA).mul (unitPoly u)
  exact (PolyBound.clm (coeffMap i i)).comp he
lemma poly_sec {A:X→Mat m} (hA:PolyBound A) {g:Plane→ℝ} (hg:PolyBound g)
    (v:X→Frm m) (C:Mat m) : PolyBound fun x=>(v x).sec (v x) (A x) (A x) g C := by
  let f := fun x=>(v x).secDiag (v x) (A x) (A x) g C
  have h : PolyBound f := by
    have he := ((unitStarPoly v).mul (PolyBound.const C)).mul (unitPoly v)
    apply mat_poly
    intro i j; exact (hg.comp ((poly_eig hA v i).prodMk (poly_eig hA v j))).mul
      ((PolyBound.clm (coeffMap i j)).comp he)
  exact ((unitPoly v).mul h).mul (unitStarPoly v)
lemma clm_poly_from {E F:Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
    {f:X→E→L[ℝ]F} (h:∀ y:E,PolyBound fun x=>f x y) : PolyBound f := by
  classical
  let b := Module.finBasis ℝ E
  let c := fun i=> (b.coord i).toContinuousLinearMap
  let g := fun i (x:X)=> (c i).smulRight (f x (b i))
  have he : f=fun x=> ∑ i,g i x := by
    ext x y
    conv_lhs => rw [← b.sum_repr y]
    simp only [_root_.map_sum,_root_.map_smul,_root_.sum_apply,g,ContinuousLinearMap.smulRight_apply]
    rfl
  rw [he]
  apply p_sum (f:=g)
  intro i
  exact (PolyBound.clm (ContinuousLinearMap.smulRightL ℝ E F (c i))).comp (h _)
end p
namespace ProjField
variable (q:ProjField m)
omit [NeZero m] in
lemma ell_eq (x) : q.ell x=q.Lmat x := congrFun q.L_linear.choose_spec x

lemma hasdl (x:Rn m) {f:ℝ→ℝ} (hf:TestF f) :
    HasFDerivAt (q.FL.eval f) (q.Ld x f) x := by
  let u := q.FL.Fr x
  let g := bav (deriv f)
  have hg := bav_con hf.der.cont
  let t := fun z=> (u.DL (q.FL.Fr z) (q.Lmat x) (q.Lmat z) g).comp q.ell
  have he (z:Rn m) :
      q.FL.eval f z-q.FL.eval f x=t z (z-x) := by
    let A := q.FL
    have hi := u.exact_sec (A.Fr z) (A.sym x) (A.sym z) (A.Fr_D x) (A.Fr_D z) hf
    have hh : A.eval f x-A.eval f z=u.DL (A.Fr z) (q.Lmat x) (q.Lmat z) g (q.Lmat x-q.Lmat z) := hi
    have hp : A.eval f x-A.eval f z=t z (x-z) := by rw [hh]; simp only [t,
      ContinuousLinearMap.comp_apply,_root_.map_sub,q.ell_eq]; rfl
    change A.eval f z-A.eval f x=_
    rw [show z-x= -(x-z) by abel,_root_.map_neg, ← hp,neg_sub]

  have hh : ContinuousAt t x := by
    apply tendsto_of_subseq_tendsto
    intro ns hn
    obtain ⟨v,ms,hms,h⟩ := CompactSpace.tendsto_subseq (fun n=> q.FL.Fr (ns n))
    have hA : Tendsto (fun n=> (q.Lmat (ns (ms n)),q.FL.Fr (ns (ms n)))) atTop
        (𝓝 (q.Lmat x,v)) :=
      ((q.L_cont.tendsto x).comp (hn.comp hms.tendsto_atTop)).prodMk_nhds h
    have hs : ∀ᶠ n in atTop,(q.Lmat (ns (ms n)),q.FL.Fr (ns (ms n)))∈
        {p:Mat m × Frm m|p.2.Dgn p.1} :=
      Eventually.of_forall fun n=> q.FL.Fr_D (ns (ms n))
    have hv := Frm.Dgn_closed.mem_of_tendsto hA hs
    let D := fun p:Mat m × Frm m=> (u.DL p.2 (q.Lmat x) p.1 g).comp q.ell
    have hi := Frm.cont_DL u (q.Lmat x) hg
    have hu := ((ContinuousLinearMap.compL ℝ (Rn m) (Mat m) (Mat m)).flip q.ell).continuous.comp hi
    have hd : Continuous D := hu
    have heq : t x = D (q.Lmat x,v) := by
      unfold t D
      have hx : v.Dgn (q.Lmat x) := hv
      have hi : (q.FL.Fr x).Dgn (q.Lmat x):=q.FL.Fr_D x
      rw [u.DL_ind _ v _ _ _ hi hx]
    refine ⟨ms,?_⟩
    have ha := hd.tendsto (q.Lmat x,v)
    have hu := ha.comp hA
    rw [← heq] at hu; exact hu
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,isLittleO_iff]
  intro c hc
  have hi : ContinuousAt (fun y=> ‖t (x+y)-t x‖) 0 := by
    let : IsTopologicalAddGroup (Rn m →L[ℝ] Mat m) :=
      inferInstance
    let : ContinuousSub (Rn m →L[ℝ] Mat m) :=
      IsTopologicalAddGroup.to_continuousSub
    have hl : ContinuousAt (fun y=> t (x+y)) 0 :=
      ContinuousAt.comp_of_eq hh (continuousAt_const.add continuousAt_id) (add_zero _)
    have he : ContinuousAt (fun y=> t (x+y)-t x) 0 := hl.sub continuousAt_const
    have hb := continuous_norm (E:=Rn m →L[ℝ] Mat m)
    exact hb.continuousAt.comp he
  filter_upwards [hi.eventually (gt_mem_nhds (show ‖t (x+0)-t x‖ < c by rw [add_zero, sub_self, show ‖(0:Rn m →L[ℝ] Mat m)‖=0 from norm_zero (E:=Rn m →L[ℝ] Mat m)]; exact hc))]
    with y hy
  change ‖q.FL.eval f (x+y)-q.FL.eval f x-q.Ld x f y‖≤_
  rw [he, add_comm x y,add_sub_cancel_right]
  change ‖(t (y+x)-t x) y‖≤_
  apply ((t (y+x)-t x).le_opNorm y).trans
  rw [add_comm y x]
  apply mul_le_mul_of_nonneg_right (le_of_lt hy) (norm_nonneg _)

lemma dPoly {f:ℝ→ℝ} (hf:TestF f) : PolyBound (fderiv ℝ (q.FL.eval f)) := by
  rw [show fderiv ℝ (q.FL.eval f)=_ from funext (fun x=>(q.hasdl x hf).fderiv)]
  apply clm_poly_from
  intro y; exact poly_sec q.L_poly (bav_bound hf.der.poly) q.FL.Fr (q.ell y)

lemma LD_reg (i:Fin m) {f} (hf:TestF f) :
    regular fun x=> fderiv ℝ (q.FL.eval f) x (e i) :=
  ⟨(PolyBound.clm (ContinuousLinearMap.apply ℝ _ (e i))).comp (q.dPoly hf),
    (((continuous_id.clm_apply continuous_const).comp_stronglyMeasurable
      ((by
        exact (measurable_fderiv ℝ (q.FL.eval f)).stronglyMeasurable)))).aestronglyMeasurable⟩

omit [NeZero m] in
lemma ell_M (i:Fin m) : q.ell (e i)=q.M i := by
  rw [q.ell_eq]
  simp [e,Lmat]
lemma mder_frame (i j k:Fin m) {f:ℝ→ℝ} (hf:TestF f) (x:Rn m) :
    (q.FL.Fr x).loc (fderiv ℝ (q.FL.eval f) x (e i)) j k=
      bav (deriv f) (q.FL.ev x j,q.FL.ev x k)*(q.FL.Fr x).loc (q.M i) j k := by
  rw [(q.hasdl x hf).fderiv,Ld,ContinuousLinearMap.comp_apply,q.ell_M]
  apply Frm.sec_eq
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Packet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Fixed profiles supplementing Profile.d,v,g, exact constants
and layered profiles. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.Profile

namespace LayerOK
variable (h:LayerOK)
include h
lemma f_test : TestF FF := (TestF.const _).add ((TestF.const _).mul h.q_test)
lemma fN (x) : N2 FF x=2*cc+2*kk*N2 qu x := by
  have hh (x:ℝ) : deriv FF x=2*kk*deriv qu x :=
    ((((h.q_test.diff x).hasDerivAt).const_mul (2*kk)).const_add cc).deriv
  have ht : deriv (deriv FF) x=2*kk*deriv (deriv qu) x := by
    rw [funext hh]
    exact ((((h.q_test.der.diff x).hasDerivAt).const_mul _)).deriv
  unfold N2 N; rw [ht,hh]
  unfold FF; ring
end LayerOK
end GeneralMahler.Profile

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_BiWeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer functional ℒ and polynomial-growth calculus. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers

namespace Bwt
variable {l g:Plane→ℝ}
lemma add (h:Bwt l) (hh:Bwt g) : Bwt fun x=> l x+g x :=
  ⟨h.c.add hh.c,h.p.add hh.p⟩
lemma sub (h:Bwt l) (hh:Bwt g) : Bwt fun x=> l x-g x :=
  ⟨h.c.sub hh.c,h.p.sub hh.p⟩
lemma mul (h:Bwt l) (hh:Bwt g) : Bwt fun x=> l x*g x :=
  ⟨h.c.mul hh.c,h.p.mul hh.p⟩
lemma fst {f:ℝ→ℝ} (hf:TestF f) : Bwt fun u:Plane=> f u.1 :=
  ⟨hf.cont.comp continuous_fst,hf.poly.comp PolyBound.fst⟩
lemma snd {f:ℝ→ℝ} (hf:TestF f) : Bwt fun u:Plane=> f u.2 :=
  ⟨hf.cont.comp continuous_snd,hf.poly.comp PolyBound.snd⟩
lemma const (c:ℝ) : Bwt fun _=>c := ⟨continuous_const,PolyBound.const _⟩
lemma bar (h:Bwt g) : Bwt (bAv g) := by
  constructor
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f:=fun (u:Plane) t=>g (u.1,along u t)) (h.c.comp (show Continuous (fun u:Plane×ℝ=>(u.1.1,along u.1 u.2)) by unfold along; fun_prop)) _ _
  obtain ⟨C,n,hc,h⟩ := h.p
  refine ⟨C,n,hc,fun u=>?_⟩
  have he (t:ℝ) (hh:t∈Ι (0:ℝ) 1) : ‖g (u.1,along u t)‖≤ C*(1+‖u‖)^n := by
    apply le_trans (h _)
    rw [uIoc_of_le zero_le_one] at hh
    gcongr;
    have ht := mem_Ioc.mp hh
    change max ‖u.1‖ ‖along u t‖ ≤ max _ _
    apply max_le (le_max_left ..)
    change |(1-t)*u.1+t*u.2| ≤ max |u.1| |u.2|
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul,abs_of_nonneg ht.1.le,abs_of_nonneg (by linarith [ht.2])]
    rcases max_choice |u.1| |u.2| with h|h
    · have hx := le_max_right |u.1| |u.2|
      rw [h] at *
      nlinarith [ht.1,ht.2]
    have hx := le_max_left |u.1| |u.2|
    rw [h] at *
    nlinarith [ht.1,ht.2]
  have hu := intervalIntegral.norm_integral_le_of_norm_le_const he
  unfold bAv; convert hu using 1 ; first | rfl | simp
end Bwt
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Segment
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar exterior and middle estimates via Cauchy--Schwarz. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace Interval
namespace GeneralMahler.Seg
open Roots Layers

lemma integral_sq_le (f:ℝ→ℝ) (hf:Continuous f) (a b:ℝ) (h:a≤b) :
    (∫ x in a..b,f x)^2 ≤ (b-a)*∫ x in a..b,f x^2 := by
  rcases h.eq_or_lt with rfl|h
  · simp
  have ht : 0<b-a := sub_pos.mpr h
  let c := (∫ x in a..b,f x)/(b-a)
  have hq : (∫ x in a..b,f x)=c*(b-a) := by unfold c; field_simp
  have hp := intervalIntegral.integral_nonneg h.le (f:=fun x=>(f x-c)^2)
    (μ:=volume) (fun x _=>sq_nonneg _)
  have hi (x) : (f x-c)^2=f x^2-(2*c)*f x+c^2 := by ring
  simp_rw [hi] at hp
  rw [intervalIntegral.integral_add,intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hp
  · rw [hq] at *
    change 0≤ _-_+(b-a)*c^2 at hp
    nlinarith [mul_nonneg hp ht.le]
  all_goals first | exact (hf.pow _).intervalIntegrable .. |
    exact ((continuous_const.mul hf).intervalIntegrable ..) |
    exact (continuous_const.intervalIntegrable ..) |
    exact (((hf.pow _).sub (continuous_const.mul hf)).intervalIntegrable ..)
lemma bar_sq (g:Plane→ℝ) (hg:Bwt g) (u:Plane) :
    bAv g u^2 ≤ bAv (fun v=>g v^2) u := by
  have hh := integral_sq_le (fun x=>g (u.1,along u x)) (hg.c.comp
    (by unfold along; fun_prop)) 0 1 zero_le_one
  simpa [bAv] using hh

end GeneralMahler.Seg

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LFun
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! ℒ evaluation; linearity and spectral form. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace FieldMat
variable (B:FieldMat m)
omit [NeZero m] in
lemma bmat_loc (f:Plane→ℝ) (z x) :
    (B.Fr x).loc (B.bmat f z x)=Matrix.diagonal (fun i=>f (z,B.ev x i)) := B.evfrm ..

omit [NeZero m] in
lemma bsmb {f:Plane→ℝ} (hf:Bwt f) :
    StronglyMeasurable (B.bmat f).uncurry :=
  (B.theta_gen_meas (f:=fun x y=>f (x,y)) (by exact hf.c.measurable)).stronglyMeasurable
lemma p_bmat {f:Plane→ℝ} (hf:Bwt f) :
    PolyBound (B.bmat f).uncurry := by
  let u := fun w:ℝ×Rn m=> B.Fr w.2
  let D := fun w:ℝ×Rn m=>Matrix.diagonal (fun i=>f (w.1,B.ev w.2 i))
  have he (w:ℝ×Rn m): (B.bmat f).uncurry w=(u w).val*D w*star (u w).val :=
    B.evfrm' w.2 _
  rw [funext he]
  have hp : PolyBound D := by
    apply mat_poly
    intro i j
    have hg : PolyBound (fun w:ℝ×Rn m=> f (w.1,B.ev w.2 i)) :=
      hf.p.comp (PolyBound.fst.prodMk
        ((poly_eig B.poly B.Fr i).comp PolyBound.snd))
    by_cases hi:i=j
    · subst j; simpa only [D,Matrix.diagonal_apply_eq] using hg
    · unfold D; simp_rw [Matrix.diagonal_apply_ne _ hi]; exact PolyBound.const _
  exact ((unitPoly u).mul hp).mul (unitStarPoly u)
end FieldMat

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Blocks
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Algebra of the positive layer blocks (with no commutation
assumptions). All entries here are in a fixed spectral frame. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Seg Roots Layers Profile
variable {m:ℕ}
lemma symm_entry {A:Mat m} (h:A.IsHermitian) (i j) : A i j=A j i := by
  have he:= congrFun (congrFun h i) j; simpa using he.symm
lemma trace_pair (A B:Mat m) : trN (A*B)=mats (fun i=>∑ j,A i j*B j i) := by
  unfold trN trace mats; rfl
lemma traceDiag (A:Mat m) (f:Fin m→ℝ) :
    trN (A*Matrix.diagonal f)=mats (fun i=>A i i*f i) := by
  unfold trN trace mats; simp only [Matrix.diag,Matrix.mul_diagonal]
lemma hsN_eq (A:Mat m) : hsN A=mats (fun i=>∑ j,A i j^2) := by
  rw [hsN,trace_pair]; congr 1; ext; simp [pow_two]
lemma hsN_pos (A:Mat m) : 0 ≤ hsN A := by rw [hsN_eq]; unfold mats; positivity
lemma hsN_loc (A:Mat m) (u:Frm m) : hsN (u.loc A)=hsN A := by
  rw [hsN,hsN,← u.loc_star,← u.loc_mul,trN,trN,u.loc_trace]

lemma cmu_eig (A B:Mat m) (u:Frm m) (he:u.Dgn A) :
    hsN (cmu A B)=mats (fun i=>∑ j,(u.eig A i-u.eig A j)^2 * (u.loc B i j)^2) := by
  rw [← hsN_loc (cmu A B) u,hsN_eq]
  unfold cmu
  rw [u.loc_sub,u.loc_mul,u.loc_mul,show u.loc A=_ from he]
  congr 1; ext i; apply Finset.sum_congr rfl; intro j _
  rw [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  ring

lemma mats_add (f g:Fin m→ℝ) :
    mats (fun i=>f i+g i)=mats f+mats g := by unfold mats; rw [Finset.sum_add_distrib,add_div]
lemma mats_s (a:ℝ) (f:Fin m→ℝ) :
    mats (fun i=>a*f i)=a*mats f := by unfold mats; rw [← Finset.mul_sum]; ring
lemma mats_le {f g:Fin m→ℝ} (h:∀ i,f i≤g i) : mats f ≤ mats g := by unfold mats; gcongr; apply h

namespace block
variable (b:block m)

lemma az (i:Fin m) : b.a i*b.L i=b.x i-b.z := by
  unfold a L signE; split_ifs with h
  · rw [abs_of_pos (sub_pos.mpr h)]; ring
  rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))]; ring
lemma Sspec (i j) :
    b.S i j = (if b.L i=b.L j then b.L i*√(b.a i)*√(b.a j) else 0)*b.E i j := rfl
lemma Her : b.E.IsHermitian :=
  b.hp.posSemidef.1.sub (Matrix.isHermitian_diagonal_iff.mpr fun _=> rfl)
lemma Spar : 0≤b.S := by
  let f := fun i=> if b.z<b.x i then √(b.a i) else 0
  let g := fun i=> if b.z<b.x i then 0 else √(b.a i)
  let F := Matrix.diagonal f
  let G := Matrix.diagonal g
  have hp (f:Fin m→ℝ) : (Matrix.diagonal f).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr fun _=> rfl
  have hi := add_nonneg (sand_nonneg b.hp (hp f)) (sand_nonneg (sub_nonneg.mpr b.hi) (hp g))
  apply hi.trans_eq
  change F*b.P*F+G*(1-b.P)*G=b.S
  ext i j
  unfold F G
  rw [Matrix.add_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.diagonal_mul,b.Sspec]
  unfold f g E jump L signE
  by_cases h:i=j
  · subst j
    rcases lt_or_ge b.z (b.x i) with h|h
    · simp [h,not_le_of_gt h]; ring
    simp [h,not_lt_of_ge h]; ring
  by_cases h₁:b.z<b.x i <;> by_cases h₂:b.z<b.x j <;>
    norm_num [h,h₁,h₂] <;> ring

lemma Sdiag (i) : b.S i i=b.a i*b.L i*b.E i i := by
  rw [b.Sspec,ite_eq_left rfl,mul_assoc (b.L i),← pow_two,Real.sq_sqrt]
  · ring
  exact abs_nonneg _
lemma Ed2 (i) :
    (∑ j,b.E i j^2) ≤ b.L i*b.E i i := by
  have he (A:Mat m) (h:A.IsHermitian) : (∑ j,A i j^2)=(A*A) i i := by
    rw [Matrix.mul_apply]; congr 1; ext j; rw [symm_entry h i j, pow_two]
  rw [he b.E b.Her,E,sub_mul,mul_sub,mul_sub]
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.diagonal_apply_eq]
  have hi : b.P*b.P ≤ b.P := by
    have hu : Commute b.P (1-b.P) := (Commute.one_right _).sub_right (Commute.refl _)
    have h := mul_comm_nonneg b.hp (sub_nonneg.mpr b.hi) hu
    rwa [mul_sub,mul_one,sub_nonneg] at h
  have hz : 0 ≤ (b.P-b.P*b.P) i i := (Matrix.le_iff.mp hi).diag_nonneg
  unfold L signE jump; split_ifs <;> simp only [Matrix.sub_apply] at * <;> grind

end block
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Variation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Inverse-kernel and variation identity Eq14. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler
open Profile Layers
lemma nr_test {f:ℝ→ℝ} (hf:TestF f) : TestF (Nr f) :=
  hf.add ((TestF.id.mul hf.der).sub hf.der.der)

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Prim
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar primitive conventions and calculus for §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Profile
open Layers
lemma prim_d {l} (hf:TestF l) (x) : HasDerivAt (prim l) (l x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf.cont.intervalIntegrable ..)
    (hf.cont.stronglyMeasurableAtFilter volume _) hf.cont.continuousAt
lemma p_test {l} (hf:TestF l) : TestF (prim l) := TestF.of_d (prim_d hf) hf

lemma pl_test {l} (hf:TestF l) : TestF (pl l) :=
  (p_test hf).sub (TestF.const _)
lemma pl_d {l} (hf:TestF l) : deriv (pl l)=l :=
  funext fun x=> ((prim_d hf x).sub_const (ga (prim l))).deriv
lemma ga_const (c:ℝ) : ga (fun _=>c)=c := by unfold ga; rw [integral_mul_const,e_phi]; ring
lemma N_test {l} (hl:TestF l) : TestF (N l) :=
  (TestF.id.mul hl.der).sub hl.der.der
lemma fl_test {l} (hl:TestF l) : TestF (fl l) := nr_test (pl_test hl)
lemma ps_test {l} (hl:TestF l) : TestF (ps l) :=
  p_test ((N_test (pl_test hl)).sub (pl_test hl))
lemma fl_d {l} (hl:TestF l) : deriv (fl l)=N2 l := by
  unfold fl Nr N
  rw [pl_d hl]
  ext x
  have he := (((pl_test hl).diff x).hasDerivAt.fun_add (((hasDerivAt_id' x).fun_mul
    (hl.diff x).hasDerivAt).fun_sub (hl.der.diff x).hasDerivAt)).deriv
  simp only [pl_d hl] at he
  unfold N2 N; rw [he]; ring
lemma ps_d {l} (hl:TestF l) (x) : deriv (ps l) x=fl l x-2*pl l x := by
  rw [show deriv (ps l) x=_ from (prim_d ((N_test (pl_test hl)).sub (pl_test hl)) x).deriv]
  unfold fl Nr; ring
lemma Nr_ga {b} (hb:TestF b) : ga (Nr b)=ga b := by
  unfold Nr
  rw [ga_add hb (N_test hb)]; unfold N
  rw [ga_sub (TestF.id.mul hb.der) hb.der.der,
    ga_parts hb.der]; ring
end GeneralMahler.Profile

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Forms
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Forms on the Hermite coefficients. D and sigma in paper §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}
lemma pJ_smul_left (W:Mat m) (A C:Mat m) (a:ℝ) :
    Pj W (a•A) C=a*Pj W A C := by simpa using pj_scale a 1 W A C
lemma pJ_smul_right (W:Mat m) (A C:Mat m) (a:ℝ) :
    Pj W A (a•C)=a*Pj W A C := by simpa using pj_scale 1 a W A C

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_ScalarForm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Integrating functionals; ext modulo constants. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ} [NeZero m]
-- simple contractions
namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)
omit [NeZero m] in
lemma L_ext {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (he:deriv f=deriv g) :
    LDel B W f=LDel B W g := by
  let h := fun x=> f x-g x
  have ih := fun x=>((hf.diff x).hasDerivAt.fun_sub (hg.diff x).hasDerivAt)
  have hh (x) : HasDerivAt h 0 x := by
    have h := ih x; rw [he,sub_self] at h
    exact h
  have eq : h=fun x=> h 0 := by
    ext x
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=x)
      (f:=h) (f':=fun _=> (0:ℝ)) (fun x _=>hh x) (continuous_const.intervalIntegrable ..)
    simp only [intervalIntegral.integral_zero] at hi; exact sub_eq_zero.mp hi.symm
  have H : LDel B W h=0 := by
    unfold LDel etw et BDiff
    rw [eq,ga_const]
    simp [B.eval_const,trN]
  have hi := Delta_sub B W hf hg
  change LDel B W h=_ at hi; linarith
omit [NeZero m] in
lemma L_cmul (a:ℝ) {f:ℝ→ℝ} (hf:TestF f) :
    LDel B W (fun x=>a*f x)=a*LDel B W f := by
  unfold LDel etw et
  have hi (x) : BDiff B (fun x=>a*f x) x=a• BDiff B f x := by
    rw [BDiff,B.eval_scale hf,ga_mul]
    unfold scalar BDiff; module
  simp_rw [hi,mul_smul_comm,trN_smul,integral_const_mul]

omit [NeZero m] in
lemma L_formula {f:ℝ→ℝ} (hf:TestF f) :
    etw W (B.eval f) = LDel B W f+trN W*ga f := by
  unfold LDel etw et BDiff
  simp_rw [mul_sub,scalar,mul_smul_comm,mul_one,trN_sub,trN_smul]
  rw [integral_sub (int_etw W (B.eval_reg hf).ig) (integrable_const _)]
  simp; ring
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_FormSquare
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §04 profile quadratic identity. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ} [NeZero m]

namespace ProjField
omit [NeZero m] in
lemma tw_add {B:FieldMat m} {f j:ℝ→ℝ} (W:Mat m) (hf:TestF f) (hj:TestF j) :
    LDel B W (fun x=> f x+j x)=LDel B W f+LDel B W j := by
  have h : (fun x=> f x) = fun x=> (f x+j x)-j x := by ext; ring
  have he := Delta_sub B W (hf.add hj) hj
  rw [← h] at he; linarith

variable (q:ProjField m)

lemma evId (x:Rn m) : q.FL.eval (fun x=> x) x=q.Lmat x := by
  unfold FieldMat.eval
  rw [cfc_id' ℝ _ (show IsSelfAdjoint (q.FL.A x) from q.FL.sym x)]; rfl

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LowDegree
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Linear chaos coefficients for balance. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m)
omit [NeZero m] in
lemma Mzero (x:Rn m) : MM 0 x=1 := by simp only [MM]; simp [H]
omit [NeZero m] in
lemma Mi1 (i:Fin m) (x:Rn m) : MM (inc 0 i) x=x i := by
  rw [inc,factor_upd]; simp [H,sn]

omit [NeZero m] in
lemma l_reg : regular q.Lmat := ⟨q.L_poly,q.L_cont.aestronglyMeasurable⟩

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LinTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Test/functional linearities. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
namespace Profile
variable {f g:ℝ→ℝ}
lemma sq_test (hf:TestF f) : TestF (fun x=>f x^2) := by
  simpa only [pow_two] using hf.mul hf
lemma drv_sub (hf:TestF f) (hg:TestF g) :
    deriv (fun x=>f x-g x)=fun x=>deriv f x-deriv g x := by
  ext x; exact ((hf.diff x).hasDerivAt.fun_sub (hg.diff x).hasDerivAt).deriv
end Profile
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Eq18
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Eq18 with fixed profiles. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m)
lemma wt_deriv {f g} (hf:TestF f) (hg:TestF g) :
    Bwt fun u:Plane=>deriv f u.1*deriv g u.2 :=
  (Bwt.fst hf.der).mul (Bwt.snd hg.der)
lemma wt_Hp (h:LayerOK) : Bwt Hp0 :=
  ((Bwt.const 2).mul (wt_deriv TestF.id (pl_test h.f_test))).add (wt_deriv (fl_test h.f_test) TestF.id)
lemma wt_part {f} (hf:TestF f) : Bwt (Hpart f) :=
  (Bwt.const 2).mul (wt_deriv (fl_test hf) (pl_test hf))

lemma H_decomp (h:LayerOK) :
    HH=fun u=> Hp0 u-Hpart uc u-Hpart us u-Hpart qu u := by
  ext u; unfold Hpart Hp0
  simp_rw [fl_d h.f_test,fl_d h.c_test,fl_d h.s_test,fl_d h.q_test,h.fN,
    pl_d h.c_test,pl_d h.s_test,pl_d h.q_test,pl_d h.f_test,deriv_id'']
  unfold HH FF; ring
lemma H_ok (h:LayerOK) : Bwt HH := by
  rw [H_decomp h]
  exact (((wt_Hp h).sub (wt_part h.c_test)).sub (wt_part h.s_test)).sub
    (wt_part h.q_test)

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Degree
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Per Gaussian degree proof of the form estimate Eq19. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile HMode Layers
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma j_same (A:Mat m) : jprod A A=A*A := by unfold jprod; module
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Extract
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Frame decomposition of layer functionals. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ}
lemma Frm.trNL (u:Frm m) (A:Mat m) : trN (u.loc A)=trN A := by unfold trN; rw [u.loc_trace]
lemma Frm.pjL (u:Frm m) (W A C:Mat m) : Pj (u.loc W) (u.loc A) (u.loc C)=Pj W A C := by
  have he : jprod (u.loc A) (u.loc C)=u.loc (jprod A C) := by
    unfold jprod; rw [u.loc_smul,u.loc_add,u.loc_mul,u.loc_mul]
  unfold Pj; rw [he,← u.loc_mul,u.trNL]
lemma Frm.HL (u:Frm m) {A:Mat m} (h:A.IsHermitian) :
    (u.loc A).IsHermitian := by
  change star (u.loc A)= _
  rw [← u.loc_star,show star A=A from h]

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)

lemma BLe (x z) : (q.BL B x z).E=(B.Fr x).loc (q.EZ B z x) := by
  unfold BL block.E EZ
  rw [Frm.loc_sub,FieldMat.Θ,B.evfrm]

lemma lin_w {f} (h:Bwt f): Bwt (linW f) :=
  ((Bwt.snd TestF.id).sub (Bwt.fst TestF.id)).mul h
section
variable [NeZero m]

lemma bmMS {f} (h:Bwt f) : mixed (q.bmZ B f)∧StronglyMeasurable (q.bmZ B f).uncurry := by
  have hm := pj_M (1:Mat m) (q.eM B) (B.p_bmat (lin_w h))
  have hh := (pj_cont (1:Mat m)).comp_stronglyMeasurable ((q.eSM B).prodMk
    (B.bsmb (lin_w h)))
  exact ⟨hm,hh⟩
lemma bmh {f} (h:Bwt f) (x) : Integrable (fun z=>q.bmZ B f z x) := by
  have hi := q.bmMS B h
  exact mixed_integrable_left hi.1 x
    ((hi.2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
lemma bmah {f} (h:Bwt f) : Integrable (fun x=>∫ z,q.bmZ B f z x) (normal m) := by
  have hi := q.bmMS B h
  exact (mixed_integrable (μ:=volume) (ν:=normal m) hi.1 hi.2.aestronglyMeasurable).integral_prod_right

end

lemma bm_trace (x z f) :
    let b := q.BL B x z
    q.bmZ B f z x=mats (fun i=> b.S i i*f (z,b.x i)) := by
  intro b
  let u := B.Fr x
  rw [bmZ, ← u.pjL]
  rw [u.loc_one,← q.BLe,B.bmat_loc,Pj,one_mul,trN_j,traceDiag]
  congr 1; ext i
  change b.E i i *linW f (z,b.x i)=_
  unfold linW
  rw [b.Sdiag,b.az]
  rw [show b.z=z from rfl]; ring

section
variable [NeZero m]

lemma bm_pos (x z) (f:Plane→ℝ) (h:∀ w,0≤f w) :
    0 ≤ q.bmZ B f z x := by
  rw [q.bm_trace]
  unfold mats
  apply div_nonneg _ m_pos.le
  apply Finset.sum_nonneg
  intro i _; apply mul_nonneg
  · exact (q.BL B x z).Spar.posSemidef.diag_nonneg
  apply h

end

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Klimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Pointwise Young estimate assembled before integrating; common
lemma for the two kernel estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Roots Seg
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma mats_s2 (a:ℝ) (f:Fin m→Fin m→ℝ) :
    a*mats (fun i=>∑ j,f i j) = mats (fun i=>∑ j,a*f i j) := by
  simp_rw [← Finset.mul_sum]; rw [mats_s]

omit [NeZero m] in
lemma Frm.loc_s (u:Frm m) (t:ℝ) : u.loc (scalar m t)=scalar m t := by
  simp only [scalar,u.loc_smul,u.loc_one]
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Tbound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §05 the two layer estimates, retained penalties. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots

variable {m:ℕ}
lemma Bvpp : Bwt (fun u:Plane=>deriv (deriv v) u.2) := Bwt.snd v_test.der.der
lemma sq_wt {f} (hf:Bwt f) : Bwt (fun u=>f u^2) := by simpa [pow_two] using hf.mul hf
lemma bhj (h:LayerOK) : Bwt Hh := ((ProjField.H_ok h).add Bvpp).sub (Bwt.const _)
lemma P0_wt (h:LayerOK) : Bwt P0 := by
  have hp := N2_test h.q_test
  exact ((Bwt.const _).add (((Bwt.const _).mul (.fst hp)).mul (.snd hp))).add (Bwt.const _)
lemma Rwt (h:LayerOK) : Bwt wwR := by
  unfold wwR; simp only [div_eq_mul_inv]
  have ht := (bhj h).bar
  exact ((Bwt.const _).mul ht).sub ((Bwt.const _).mul ((Bwt.const _).add
    ((sq_wt ht).mul (Bwt.const _))))
lemma wwt (h:LayerOK) : Bwt ww :=
  ((ProjField.H_ok h).sub (P0_wt h)).bar.add (Rwt h)
lemma w0t (h:LayerOK) : Bwt ww0 := by
  unfold ww0; simp only [div_eq_mul_inv]
  exact ((sq_wt (bhj h)).bar.mul (Bwt.const _))
lemma alpha_p : 0<alpha := by norm_num [alpha]

lemma wpos (h:LayerOK) (v:Plane) : ww v > ww0 v ∧ 0≤ww0 v := by
  have hj := bhj h
  have hs := sq_wt hj
  have hx:= bar_sq Hh hj v
  let l := fun t=> (v.1,along v t)
  have hl : Continuous l := by unfold l along; fun_prop
  let a := fun t=> HH (l t)-P0 (l t)
  let b := fun t=> Hh (l t)
  let F := fun t=> a t+tc*b t - tr/2*(h₀+b t^2/h₀)-b t^2/alpha
  have HF (t:ℝ): 0<F t := by
    unfold F a b
    have hi := h.bh_layer (l t); unfold P0 ap; linarith
  have ha : Continuous a := ((ProjField.H_ok h).c.sub (P0_wt h).c).comp hl
  have hb : Continuous b := hj.c.comp hl
  have hF : Continuous F := by unfold F; fun_prop
  have he : 0< ∫ t in (0:ℝ)..1,F t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (a:= (0:ℝ)) (b:=1) (hF.intervalIntegrable ..) (fun x _=>HF x) ?_
  · refine ⟨?_,div_nonneg (le_trans (sq_nonneg _) hx) alpha_p.le⟩
    let H (f:ℝ→ℝ):=∫ t in (0:ℝ)..1,f t
    have he' : 0 < H a+tc* H b-tr/2*(h₀+H (fun t=>b t^2)/h₀)-H (fun t=>b t^2)/alpha := by
      unfold H
      unfold F at he
      rw [intervalIntegral.integral_sub,intervalIntegral.integral_sub,
        intervalIntegral.integral_add, intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add, intervalIntegral.integral_div,intervalIntegral.integral_div,
        intervalIntegral.integral_const] at he
      · simpa using he
      all_goals (apply Continuous.intervalIntegrable; fun_prop)
    change H (fun t=>a t)+(tc*H b-tr/2*(h₀+(H b)^2/h₀)) > H (fun t=>b t^2)/alpha
    change (H b)^2 ≤ H (fun t=>b t^2) at hx
    unfold Profile.tr h₀ at *
    linarith
  norm_num

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Penalty
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Constant-layer penalty and commutator remainder accounting. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)
lemma nn_eq : q.NK 1=eNt q.edge := by
  rw [eNt, integral_integral_swap q.edge.n0_int]
  unfold NK Nt nTK Edge.nt0; simp

omit [NeZero m] in
lemma cmCL (T:Mat m) : ∃ l: Mat m→L[ℝ]Mat m,(l:Mat m→Mat m)=fun x=>cmu x T := by
  let l := ContinuousLinearMap.mul ℝ (Mat m)
  exact ⟨l.flip T-l T,rfl⟩
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_FinalR
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interaction with R and cost of Sigma. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Profile HMode
variable {m:ℕ}
lemma trace_star_r (A:Mat m) : trN (star A)=trN A := by unfold trN; rw [show star A=Aᴴ from rfl,trace_conjTranspose]; rfl
lemma pj_cyc3 {X T A:Mat m} (ht:T.IsHermitian)
    (hx:X.IsHermitian) (ha:A.IsHermitian) :
    Pj T X A=trN (X*A*T) := by
  have h : trN (A*X*T)= trN (X*A*T) := by
    rw [← trace_star_r]
    simp only [star_mul,(show star X=X from hx),(show star T=T from ht),
      (show star A=A from ha)]
    rw [trN_cyclic T]
  rw [Pj,jprod,mul_smul_comm,trN_smul,mul_add,trN_add,trN_cyclic T,trN_cyclic T,h]
  ring
lemma ipN_ent (A B:Mat m): ipN A B=mats (fun i=>∑ j,A i j*B i j) := by
  unfold ipN; rw [trace_pair]; congr 1
lemma young_H (X Y:Mat m) {d:ℝ} (hd:0<d) :
    -d*hsN X-ipN X Y ≤ (4*d)⁻¹*hsN Y := by
  rw [hsN_eq,hsN_eq,ipN_ent,mats_s2,mats_s2]
  have he (x y:ℝ) : -d*x^2-x*y ≤ (4*d)⁻¹*y^2 := by
    field_simp; nlinarith [sq_nonneg (2*d*x+y)]
  have hh :
      mats (fun i=> ∑ j, -d*X i j^2)≤ mats (fun i=>∑ j,(4*d)⁻¹*Y i j^2)+
        mats (fun i=>∑ j,X i j*Y i j) := by
    rw [← mats_add]
    apply mats_le; intro i; rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum
    intro j _; linarith [he (X i j) (Y i j)]
  linarith
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_SpectralIBP
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06 Gaussian spectral averaging functional. Eq24 in normalized trace pairing. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}
lemma reg_constM (W:Mat m): regular (fun _:Rn m=>W) :=
  ⟨PolyBound.const _,aestronglyMeasurable_const⟩
lemma int_Pj (W:Mat m) {f g:Rn m→Mat m} (hf:regular f) (hg:regular g) :
    Integrable (fun x=>Pj W (f x) (g x)) (normal m) := by
  simp_rw [← pJ_eq]; apply ProjField.proj_int _ hf hg

namespace ProjField
variable [NeZero m] (q:ProjField m) (W:Mat m)

lemma DRi (l:Fin m) {f:ℝ→ℝ} (hf:TestF f) :
    Integrable (q.locR W l f) (normal m) :=
  (int_Pj _ (reg_constM _) (q.LD_reg l (pl_test hf))).sub
    (int_Pj _ (reg_constM _) (q.FL.eval_reg hf))

lemma dl_again (i:Fin m) {f:ℝ→ℝ} (hf:TestF f) (x:Rn m) :
    q.DLMat (deriv f) x i=fderiv ℝ (q.FL.eval f) x (e i) := by
  unfold DLMat
  apply (q.FL.Fr x).loc_inj
  ext j k
  rw [q.mder_frame _ _ _ hf x,q.mder_frame _ _ _ (pl_test hf.der) x,pl_d hf.der]

lemma xf_reg (l:Fin m) (f:ℝ→ℝ) (hf:TestF f) :
    regular (fun x:Rn m=> x l • q.FL.eval f x) :=
  (q.FL.eval_reg hf).smul
    (show regular (coord l) from ⟨PolyBound.clm _,(coord l).continuous.aestronglyMeasurable⟩)
lemma dl_identity (i:Fin m) {f:ℝ→ℝ} (hf:TestF f) :
    (∫ x,q.DLMat (deriv f) x i ∂normal m)= ∫ x:Rn m,x i • q.FL.eval f x ∂normal m := by
  let g := q.FL.eval f
  let h := fun (x:Rn m)=> fderiv ℝ g x (e i)
  have hg : regular g := q.FL.eval_reg hf
  have he : Differentiable ℝ g := fun x=> (q.hasdl x hf).differentiableAt
  have hh : regular h := q.LD_reg i hf
  have ht := coef_raise hg.p (PLip.fd he (q.dPoly hf)) he.continuous
    (ae_of_all _ fun x=> (he x).hasFDerivAt) i hh.p hh.meas 0
  simp_rw [q.dl_again i hf]
  unfold cof at ht
  simpa only [Mzero, Mi1, one_smul, Pi.zero_apply,Nat.zero_add,sn,Nat.cast_one,Real.sqrt_one] using ht

lemma coord_pb (l:Fin m) {f:ℝ→ℝ} (hf:TestF f) :
    (∫ x,Pj W (q.M l) (q.DLMat (deriv f) x l) ∂normal m) =
      ∫ x:Rn m,Pj W (q.M l) (x l • q.FL.eval f x) ∂normal m := by
  simp_rw [← pJ_eq]
  let g := PJ W (q.M l)
  let D := fun x=>q.DLMat (deriv f) x l
  have hi : regular D := q.LD_reg l (pl_test hf.der)
  change (∫ x,g (D x) ∂normal m)= ∫ x:Rn m,g _ ∂normal m
  rw [g.integral_comp_comm hi.ig,g.integral_comp_comm (q.xf_reg l f hf).ig,
    show (∫ x, D x ∂normal m) =_ from q.dl_identity l hf]

-- the evaluation weighted by W
lemma L_identity {f:ℝ→ℝ} (hf:TestF f) :
    etw W (fun x:Rn m=> q.Lmat x*q.FL.eval f x) =
      ∑ i:Fin m, (∫ x,Pj W (q.M i) (q.DLMat (deriv f) x i) ∂normal m) := by
  have he (x:Rn m) : trN (W*(q.Lmat x*q.FL.eval f x)) =
      ∑ i:Fin m, Pj W (q.M i) (x i • q.FL.eval f x) := by
    let A := q.FL.eval f x
    have hh : jprod (q.Lmat x) A=q.Lmat x*A := by
      have hx := (q.FL.ccomm x f (fun z=>z)).eq
      rw [q.evId] at hx
      change A*q.Lmat x=_ at hx; unfold jprod
      rw [hx]; module
    rw [show trN (W*(q.Lmat x*q.FL.eval f x))=Pj W (q.Lmat x) A from
      (congrArg (fun z=>trN (W*z)) hh).symm]
    unfold Lmat; simp_rw [← pJ_eq]
    rw [_root_.map_sum,_root_.sum_apply]
    congr 1
    ext i
    rw [pJ_eq,pJ_eq,pJ_smul_left,pJ_smul_right]
  unfold etw et; simp_rw [he,q.coord_pb W _ hf]
  rw [integral_finsetSum]
  intro i _; exact int_Pj W (reg_constM _) (q.xf_reg i f hf)

lemma RM_Form {g:ℝ→ℝ} (hg:TestF g) :
    q.RM W (deriv g)= etw W (fun x=> q.Lmat x*q.FL.eval g x)-
      Pj W q.sumS (q.expL (deriv g)) := by
  unfold RM sumS
  simp_rw [q.L_identity W hg,locR, integral_sub (int_Pj _
    (reg_constM _) (show regular (fun x=>q.DLMat (deriv g) x _) from q.LD_reg _ (pl_test hg.der)))
    (int_Pj _ (reg_constM _) (q.FL.eval_reg hg.der))]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp_rw [← pJ_eq]
  rw [_root_.map_sum,_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (PJ W _).integral_comp_comm (q.FL.eval_reg hg.der).ig

lemma W_int {f:ℝ→ℝ} (hf:TestF f) :
    etw W (q.FL.eval f)=trN (W*q.expL f) := by
  unfold etw et
  simp_rw [← pj_I, pj_sym, ← pJ_eq]
  exact (PJ W _).integral_comp_comm (q.FL.eval_reg hf).ig

lemma eq24 {f:ℝ→ℝ} (hf:TestF f) :
    LDel q.FL W (N f)=Pj W (q.sumS-1) (q.expL (deriv (deriv f))) +
      q.RM W (deriv (deriv f)) := by
  have hh : ga (N f)=0 := by
    have he := Nr_ga hf
    change ga (fun x=>f x+N f x)=ga f at he
    rw [ga_add hf (N_test hf)] at he
    linarith
  rw [show LDel q.FL W _= etw W (q.FL.eval (N f)) from by
    have hi := L_formula q.FL W (N_test hf)
    rw [hh,mul_zero,add_zero] at hi; exact hi.symm]
  have he : etw W (q.FL.eval (N f))=
      etw W (fun x=>q.Lmat x*q.FL.eval (deriv f) x) -
        trN (W*q.expL (deriv (deriv f))) := by
    rw [← q.W_int W hf.der.der]
    let h := fun x:ℝ=> x*deriv f x
    have H := TestF.id.mul hf.der
    have he (x) : q.FL.eval (N f) x=q.FL.eval h x-q.FL.eval (deriv (deriv f)) x :=
      q.FL.eval_sub H hf.der.der _
    have hx (x) : q.Lmat x*q.FL.eval (deriv f) x=q.FL.eval h x := by
      rw [show q.FL.eval h x=_ from q.FL.eval_mul TestF.id hf.der _,q.evId]
    unfold etw et; simp_rw [he,hx,mul_sub,trN_sub]
    exact integral_sub (etwReg _ (q.FL.eval_reg H)) (etwReg _ (q.FL.eval_reg hf.der.der))
  rw [he,q.RM_Form W hf.der]
  let A := q.expL (deriv (deriv f))
  have h : Pj W (q.sumS-1) A=Pj W q.sumS A-trN (W*A) := by
    simp_rw [← pj_I,pj_sym W A 1, ← pJ_eq,_root_.map_sub,_root_.sub_apply]
  rw [show Pj W (q.sumS-1) _=_ from h]
  unfold A; ring
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Comm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06. Commuting normalization controls weighted norm. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}

lemma sum_hsn (X Y:Mat m) : hsN (X+Y)≤125/100*hsN X+5*hsN Y := by
  simp only [hsN_eq]
  rw [mats_s2,mats_s2,← mats_add]
  apply mats_le; intro i
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro j _
  rw [Matrix.add_apply]
  nlinarith [sq_nonneg (X i j-4*Y i j)]

lemma H_J_frame {X W:Mat m} (u:Frm m) (l:Fin m→ℝ) (h:u.loc W=diagonal l):
    hsN (jprod W X)=mats (fun i=>∑ j,((l i+l j)/2)^2*(u.loc X i j)^2) := by
  rw [← hsN_loc (jprod W X) u,hsN_eq]; unfold jprod
  rw [u.loc_smul,u.loc_add,u.loc_mul,u.loc_mul,h]
  congr 1; ext i; apply Finset.sum_congr rfl; intro j _
  simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,Matrix.diagonal_mul,Matrix.mul_diagonal]
  ring

lemma Jgap_lower {W:Mat m} (hw:W.IsHermitian) (hu: scalar m mstar ≤ W) (X:Mat m) :
    mstar^2*hsN X≤ hsN (jprod W X) := by
  let u := Frm.eu hw
  let f := u.eig W
  have hi : u.loc W=diagonal f := Frm.eu_d hw
  have hp (i:Fin m) : mstar≤f i := by
    have he : f i∈ spectrum ℝ W := by
      unfold f u; rw [hw.spectrum_real_eq_range_eigenvalues,Frm.eu_eig]; exact ⟨_,rfl⟩
    exact (spectrum_order W hw (l:=mstar) (r:=mstar)).1.mp hu _ he
  rw [H_J_frame u f hi,← hsN_loc X u,hsN_eq,mats_s2]
  apply mats_le; intro i; apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hv := hp i; have hf := hp j; unfold mstar at *
  nlinarith

lemma Jdev_upper {W:Mat m} (hW:W∈specBox m tmin tmax) (X:Mat m) :
    hsN (jprod (W-scalar m tc) X) ≤ Profile.tr^2*hsN X := by
  let u := Frm.eu hW.1
  let f := u.eig W
  have hi : u.loc W=diagonal f := Frm.eu_d hW.1
  have hh : u.loc (W-scalar m tc)=diagonal (fun i=>f i-tc) := by
    rw [u.loc_sub,hi,u.loc_s]
    ext i j; by_cases he:i=j
    · subst j; simp [scalar]
    simp [scalar,he]
  have hp (i:Fin m) : tmin≤f i ∧ f i≤tmax := by
    have he : f i∈ spectrum ℝ W := by
      unfold f u; rw [hW.1.spectrum_real_eq_range_eigenvalues,Frm.eu_eig]; exact ⟨_,rfl⟩
    have h := spectrum_order W hW.1 (l:=tmin) (r:=tmax)
    exact ⟨h.1.mp hW.2.1 _ he,h.2.mp hW.2.2 _ he⟩
  rw [H_J_frame u _ hh,← hsN_loc X u,hsN_eq,mats_s2]
  apply mats_le; intro i; apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hv := hp i; have hf := hp j
  unfold tmin tmax tc Profile.tr at *; nlinarith [hv.1,hv.2,hf.1,hf.2]

lemma commute_update {C K T:Mat m} (h:updEq C K T=0) (M:Mat m):
    jprod (updGap C T) (cmu M T)=cmu M (K+tc • C)+jprod (T-scalar m tc) (cmu M C) := by
  have he : K= -(lam • (T*T)+jprod C T) := by
    unfold updEq at h
    apply eq_neg_of_add_eq_zero_left
    rwa [add_comm]
  rw [he]
  dsimp only [jprod,updGap,cmu]
  simp only [add_mul,mul_add, mul_sub,sub_mul,neg_mul,mul_neg,
    smul_mul_assoc,mul_smul_comm,scalar,one_mul,mul_one,mul_assoc]
  module

theorem Comm_bound {C K T:Mat m} (hc:C.IsHermitian)
    (hT:T∈specBox m tmin tmax)
    (he:updEq C K T=0) (hH:scalar m mstar ≤ updGap C T) (M:Mat m) :
    mstar^2*hsN (cmu M T) ≤
      (125/100)*hsN (cmu M (K+tc • C))+ (5*Profile.tr^2)*hsN (cmu M C) := by
  have hh : (updGap C T).IsHermitian :=
    hc.neg.sub (hT.1.smul (by simp [IsSelfAdjoint]))
  have hi := Jgap_lower hh hH (cmu M T)
  rw [commute_update he] at hi
  apply (hi.trans (sum_hsn _ _)).trans
  apply add_le_add le_rfl; rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (Jdev_upper hT _) (by norm_num)
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Powers
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Eq25 scalar-functional profiles. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ} [NeZero m]
namespace Profile
variable {f h:ℝ→ℝ}
lemma testC : TestF Cp :=
  d_test.neg.add ((TestF.const _).mul g_test.der.der)
lemma testK : TestF Kp :=
  d_test.sub ((TestF.const _).mul g_test)
lemma KN : Kp=N g := by
  ext x; have h := n_identity x
  unfold Kp; unfold N2 at h; linarith
lemma Kzero : ga Kp=0 := by
  have he := Nr_ga g_test
  rw [KN]
  change ga (fun x=>g x+N g x)=ga g at he
  rw [ga_add g_test (N_test g_test)] at he
  linarith
lemma Dadd (hf:TestF f) (hh:TestF h):
    deriv (fun x=>f x+h x)=fun x=>deriv f x+deriv h x :=
  funext fun x=>(((hf.diff x).hasDerivAt).fun_add (hh.diff x).hasDerivAt).deriv
lemma Dmul (hf:TestF f) (c:ℝ) :
    deriv (fun x=>c*f x)=fun x=>c*deriv f x :=
  funext fun x=>((hf.diff x).hasDerivAt.const_mul c).deriv
lemma N2sum (hf:TestF f) (hh:TestF h):
    N2 (fun x=>f x+h x)=fun x=>N2 f x+N2 h x := by
  unfold N2 N; rw [Dadd hf hh,Dadd hf.der hh.der]; ext; ring
lemma N2scale (hf:TestF f) (c:ℝ) :
    N2 (fun x=>c*f x)=fun x=> c*N2 f x := by
  unfold N2 N; rw [Dmul hf c,Dmul hf.der c]; ext; ring

lemma ND (hf:TestF f) (x) : deriv (N f) x=
    deriv f x + x*deriv (deriv f) x-deriv (deriv (deriv f)) x := by
  have he := ((((hasDerivAt_id' x).fun_mul ((hf.der.diff x).hasDerivAt))).fun_sub
    (hf.der.der.diff x).hasDerivAt).deriv
  unfold N; rw [he]; ring
lemma ND2 (hf:TestF f) :
    deriv (deriv (N f)) = N2 (deriv (deriv f)) := by
  rw [funext (ND hf)]
  ext x
  have hi := ((((hf.der.diff x).hasDerivAt.fun_add ((hasDerivAt_id' x).fun_mul
    (hf.der.der.diff x).hasDerivAt))).fun_sub (hf.der.der.der.diff x).hasDerivAt).deriv
  rw [hi]; unfold N2 N; ring

lemma second_f (hf:TestF f) : deriv (deriv (ps f))=N f := by
  rw [funext (ps_d hf),drv_sub (fl_test hf) ((TestF.const _).mul (pl_test hf)),fl_d hf,
    Dmul (pl_test hf) _,pl_d hf]
  ext x; unfold N2; ring
lemma second_D : deriv (deriv (ps d))= N2 Kp := by
  have he : Kp=fun x=>d x+(-2)*g x := by ext x; unfold Kp; ring
  rw [second_f d_test,he,N2sum d_test ((TestF.const _).mul g_test),
    N2scale g_test (-2)]
  ext x; dsimp only []; rw [n_identity]; unfold N2; ring
lemma second_C : deriv (deriv (fun x=>ps d x-v x+ar*Kp x))=N2 Cp := by
  have he : Cp=fun x=> (-1)*(d x+deriv (deriv g) x)+ar*deriv (deriv g) x := by ext x; unfold Cp; ring
  have hj := ps_test d_test
  rw [Dadd (hj.sub v_test) ((TestF.const _).mul testK),
    Dadd (hj.sub v_test).der (((TestF.const _).mul testK).der),
    drv_sub hj v_test,drv_sub hj.der v_test.der,Dmul testK ar,Dmul testK.der ar,
    second_f d_test,KN,ND2 g_test]
  have h := d_test.add g_test.der.der
  rw [he,N2sum ((TestF.const _).mul h) ((TestF.const _).mul g_test.der.der),
    N2scale h (-1),N2scale g_test.der.der ar]
  ext x; dsimp only []; rw [n_d_identity]; ring

-- use any second primitive; tilt so first derivatives match
lemma exists_N (hf:TestF f) (hh:TestF h)
    (he:deriv (deriv f)=N2 h) :
    ∃ F:ℝ→ℝ, TestF F ∧ deriv (deriv F)=h ∧ deriv f=deriv (N F) := by
  let g:= pl (pl h)
  have hG := pl_test hh
  have hg : TestF g := pl_test hG
  let c:= deriv f 0-deriv (N g) 0
  let F:=fun x=>g x+c*x
  have hF : TestF F := hg.add ((TestF.const _).mul TestF.id)
  have di : deriv g=pl h := pl_d hG
  have dF : deriv F=fun x=>deriv g x+c := by
    unfold F; rw [Dadd hg ((TestF.const _).mul TestF.id),Dmul TestF.id c]; ext; simp
  have dG : deriv (deriv g)=h := by rw [di, pl_d hh]
  have dF2 : deriv (deriv F)=h := by rw [dF,Dadd hg.der (TestF.const _),dG]; simp
  have dz : deriv f 0=deriv (N F) 0 := by
    rw [ND hF,dF2,dF]; unfold c; rw [ND hg,dG]; ring
  have hei : deriv (deriv f)=deriv (deriv (N F)) := by rw [he,ND2 hF,dF2]
  refine ⟨F,hF,dF2,?_⟩
  ext x
  have hi {w:ℝ→ℝ} (hw:TestF w) :
      (∫ t in (0:ℝ)..x,deriv (deriv w) t)=deriv w x-deriv w 0 := by
    apply intervalIntegral.integral_deriv_eq_sub (fun t _=>hw.der.diff t) (hw.der.der.cont.intervalIntegrable ..)
  have hp := hi hf
  rw [hei,dz] at hp
  exact sub_left_inj.mp (hp.symm.trans (hi (N_test hF)))

end Profile
namespace ProjField
variable (q:ProjField m) (T:Mat m)
lemma rm_diff {f j:ℝ→ℝ} (hf:TestF f) (hj:TestF j) (he:deriv (deriv f)=N2 j) :
    LDel q.FL T f=Pj T (q.sumS-1) (q.expL j)+q.RM T j := by
  obtain ⟨b,hb,hbj,h⟩ := exists_N hf hj he
  rw [L_ext _ _ hf (N_test hb) h,q.eq24 T hb,hbj]
lemma DelP_form :
    q.DelP T=Pj 1 (q.sumS-1) (q.expL Kp)+q.RM 1 Kp +
      (Pj T (q.sumS-1) (q.expL Cp)+q.RM T Cp -ar*trN (T*q.expL Kp)) := by
  have h := ps_test d_test
  have hb := h.sub v_test
  unfold DelP
  rw [q.rm_diff 1 h testK second_D]
  have hi := q.rm_diff T (hb.add ((TestF.const _).mul testK)) testC second_C
  rw [tw_add T hb ((TestF.const _).mul testK),L_cmul q.FL T ar testK] at hi
  have hu := L_formula q.FL T testK
  rw [Kzero,mul_zero,add_zero,q.W_int T testK] at hu
  rw [← hu] at hi; unfold ar at *
  linarith
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Eq25
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Linear field: normalization substitution. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Profile
variable {m:ℕ}
lemma pj_outer (A W C:Mat m): Pj W A C=Pj A W C := by
  have h (A B C:Mat m) : trN (A*(B*C))=trN (B*(C*A)) := by
    rw [trN_cyclic A,mul_assoc]
  unfold Pj jprod
  simp_rw [mul_smul_comm,trN_smul,mul_add,trN_add]
  rw [h W A C,← h A W C]; ring

lemma Eq_replace (C K S T:Mat m) (he:updEq C K T=0) :
    Pj 1 (S-1) K + Pj T (S-1) C-ar*trN (T*K) =
      -lam*trN (S*(T*T))-
        trN (((-ar)•C-(ar*lam)•T-scalar m lam)*(T*T)) := by
  have he' : K+jprod T C= -(lam • (T*T)) := by
    unfold updEq jprod at *
    rw [add_comm (T*C),add_comm]
    exact eq_neg_of_add_eq_zero_left (by rw [add_assoc] at he; rw [add_comm]; exact he)
  have hi : Pj 1 (S-1) K + Pj T (S-1) C= -lam*trN ((S-1)*(T*T)) := by
    rw [Pj,one_mul,trN_j,pj_outer,Pj,← trN_add,← mul_add,he',mul_neg]
    have hh (A:Mat m):trN (-A)= -trN A := by unfold trN; rw [trace_neg]; ring
    rw [hh,mul_smul_comm,trN_smul]; ring
  have hh : trN (T*K)= -lam*trN (T*(T*T))-trN (C*(T*T)) := by
    have heJ : trN (T*jprod T C)=trN (C*(T*T)) := by
      rw [← show Pj T T C=trN (T*jprod T C) from rfl,pj_sym,pj_outer,Pj,j_same]
    have h : K = ((-lam) • (T*T))- jprod T C := by simp only [neg_smul]; rw [← he']; abel
    rw [h,mul_sub,trN_sub,mul_smul_comm,trN_smul,heJ]
  rw [hi,hh]
  simp only [sub_mul,trN_sub,smul_mul_assoc,trN_smul,scalar,one_mul]
  ring
lemma pairGap (T C:Mat m) (hc:C ≤ scalar m cupper) (hH:scalar m mstar≤updGap C T) :
    scalar m (194/100) ≤ (-ar) • C - (ar*lam) • T -scalar m lam := by
  have hu : scalar m (ar*(mstar-cupper)/2-lam) ≤ (-ar) • C-(ar*lam) • T-scalar m lam := by
    have he := smul_le_smul_of_nonneg_left (sub_le_sub hH hc) (show (0:ℝ)≤ar/2 by norm_num [ar])
    have hh := sub_le_sub_right he (scalar m lam)
    apply le_trans _ (le_trans hh _)
    · apply le_of_eq; simp only [scalar]; module
    apply le_of_eq; simp only [scalar,updGap]; module
  apply le_trans _ hu
  apply scalar_le'
  norm_num [mstar,cupper,lam,ar]

namespace ProjField
variable [NeZero m] (q:ProjField m) (T:Mat m)
lemma eq25 (he:updEq (q.expL Cp) (q.expL Kp) T=0)
    (ht:T.IsHermitian) (hH: scalar m mstar≤updGap (q.expL Cp) T)
    (hc:q.expL Cp ≤ scalar m cupper) :
    q.DelP T ≤ q.RM 1 Kp+ q.RM T Cp -
      lam * trN (q.sumS*(T*T)) - (194/100)* trN (T*T) := by
  rw [q.DelP_form]
  have hi := Eq_replace _ _ q.sumS T he
  have hu := trN_mul_mono (pairGap T _ hc hH) (sqPSD ht)
  have he : trN (scalar m (194/100)*(T*T))=(194/100)*trN (T*T) := by
    simp only [scalar,smul_mul_assoc,one_mul,trN_smul]
  rw [he] at hu
  linarith
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Segments
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! End point profile tests for Eq26-27. Segment condition Eq4 (proved in scalar part). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace Interval
namespace GeneralMahler
namespace Segment
open Profile

lemma Wav {f:ℝ→ℝ} (hf:TestF f) : Bwt (bav f) := ⟨bav_con hf.cont,bav_bound hf.poly⟩
lemma bav_sym {f:ℝ→ℝ} (hf:TestF f) (u:Plane): bav f u.swap=bav f u := by
  obtain ⟨x,y⟩:=u
  rcases eq_or_ne x y with h|h
  · subst x; rfl
  have ht := pl_test hf
  have h1 := delta_eq ht x y
  have h2 := delta_eq ht y x
  rw [pl_d hf] at h1 h2
  change bav f (y,x)= bav f (x,y)
  apply mul_right_cancel₀ (show x-y≠0 from sub_ne_zero.mpr h)
  linear_combination h1 + h2

lemma Wflip {f:Plane→ℝ} (hf:Bwt f) : Bwt (fun x:Plane=> f x.swap) :=
  ⟨hf.c.comp continuous_swap,hf.p.comp (PolyBound.snd.prodMk PolyBound.fst)⟩
lemma Wsq {f:Plane→ℝ} (hf:Bwt f): Bwt (fun x=> f x^2) := by simp_rw [pow_two]; exact hf.mul hf

variable {f:ℝ→ℝ}
lemma Wr (hf:TestF f): Bwt (rest f) := (Wav hf).sub (Bwt.fst hf)
lemma Ws (hf:TestF f): Bwt (dis f) := (Wav hf).sub (Bwt.snd hf)
lemma Wm (hf:TestF f): Bwt (mdis f) :=
  ((Wav (sq_test hf)).sub (((Bwt.const _).mul (Wav hf)).mul (Bwt.snd hf))).add
    (Bwt.snd (sq_test hf))
lemma Wv (hf:TestF f): Bwt (vdis f) :=
  (Wav (sq_test hf)).sub (Wsq (Wav hf))
lemma Wa (hf:TestF f): Bwt (fun u=> anti u f) := (Bwt.snd hf).sub (Bwt.fst hf)
lemma Wg : Bwt sgamma :=
  (Bwt.const _).mul
    (((Bwt.const _).mul (Wsq ((Wa testK).add ((Bwt.const _).mul (Wa testC))))).add
      ((Bwt.const _).mul (Wsq (Wa testC))))
lemma Wd (h:LayerOK) : Bwt dsum :=
  ((Wsq (Ws h.c_test)).add (Wsq (Ws h.s_test))).add (Wsq (Ws h.q_test))
lemma Wb (h:LayerOK) : Bwt bstar :=
  (Wr testC).sub (((Wm h.c_test).add (Wm h.s_test)).add (Wm h.q_test))
lemma Wvs (h:LayerOK) : Bwt vsum :=
  ((Wv h.c_test).add (Wv h.s_test)).add (Wv h.q_test)
lemma Wres (h:LayerOK) : Bwt resid :=
  ((((Wr testK).add Wg).add ((Bwt.const _).mul (Wsq (Wb h)))).add
    ((Bwt.const _).mul (Wd h))).sub (Wvs h)
lemma WR (h:LayerOK) : Bwt symR :=
  (Bwt.const _).mul ((Wres h).add (Wflip (Wres h)))

lemma diagR (x:ℝ) : symR (x,x)=0 := by
  have he : resid (x,x)=0 := by
    simp_rw [resid,rest,bstar,vsum,rsum,dsum,sgamma,anti,rest,dis,vdis,mdis,sqav,bav_same]
    ring
  unfold symR
  change (1/2:ℝ)*(resid (x,x)+resid (x,x))=_
  rw [he]; ring
lemma Rflip (x:Plane) : symR x=symR x.swap := by simp [symR,add_comm]
lemma negR (h:SegmentOK) (u:Plane) (hu:u.1≠u.2): symR u<0 := by
  obtain ⟨x,y⟩:=u
  rcases lt_or_gt_of_ne hu with hi|hi
  · exact h _ _ hi
  rw [Rflip]; exact h _ _ hi
lemma Rle (h:SegmentOK) (u:Plane) : symR u≤0 := by
  obtain ⟨x,y⟩:=u
  rcases eq_or_ne x y with he|he
  · subst x; rw [diagR]
  exact le_of_lt (negR h _ he)
end Segment
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Nu
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Positive endpoint functional Nu. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Segment
variable {m:ℕ}
namespace LPt
variable (M:Mat m) (l:Fin m→ℝ)

lemma n_add (f g:Plane→ℝ) : npt M l (fun u=>f u+g u)=npt M l f+npt M l g := by
  simp_rw [npt,mul_add,Finset.sum_add_distrib]
  apply mats_add
lemma n_sub (f g:Plane→ℝ) : npt M l (fun u=>f u-g u)=npt M l f-npt M l g := by
  have he := n_add M l (fun u=>f u-g u) g
  have hh : (fun u=>f u-g u+g u)=f := by ext; ring
  rw [hh] at he; linarith
lemma n_s (a:ℝ) (f:Plane→ℝ) :
    npt M l (fun u=>a*f u)=a*npt M l f := by
  unfold npt
  simp_rw [mul_left_comm (_^2:ℝ), ← Finset.mul_sum]; apply mats_s
lemma n_flip (u:Plane→ℝ) (hm:M.IsHermitian) :
    npt M l (fun x:Plane=>u x.swap) = npt M l u := by
  unfold npt mats
  congr 1; rw [Finset.sum_comm]; apply Finset.sum_congr rfl
  intro i _; apply Finset.sum_congr rfl; intro j _
  rw [symm_entry hm]; rfl
lemma hsout (f:Plane→ℝ) :
    hsN (mout M l f)= npt M l (fun u=> f u^2) := by
  rw [hsN_eq,npt]; congr 1
  ext; simp only [mout,Matrix.of_apply,mul_pow]

lemma ipnout (f:Plane→ℝ) :
    ipN M (mout M l f) = npt M l f := by
  rw [ipN_ent,npt]; congr 1; ext
  simp only [mout,Matrix.of_apply,pow_two,mul_assoc]

lemma out_her (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) :
    (mout M l (bav f)).IsHermitian := by
  change star _=_
  ext i j
  change M j i *bav f (l j,l i)=M i j*bav f (l i,l j)
  rw [symm_entry hm j i]
  rw [show bav f (l j,l i)=_ from bav_sym hf (l i,l j)]
end LPt
namespace ProjField
open LPt
variable [NeZero m] (q:ProjField m)

-- measurable rotation argument
omit [NeZero m] in
lemma ContLoc (A:Mat m): Continuous (fun u:Frm m=> u.loc A) := by
  let k := fun u:Frm m=>u.val
  have hk : Continuous k := continuous_subtype_val
  exact (hk.star.mul (show Continuous (fun _:Frm m=>A) from continuous_const)).mul hk
omit [NeZero m] in
lemma MeasLoc (f:Rn m→Frm m) (hf:Measurable f) (A:Mat m):
    Measurable (fun x=> (f x).loc A) := (ContLoc A).measurable.comp hf
lemma locMe (_i:Fin m) (A:Mat m):
    regular (fun x:Rn m=> (q.FL.Fr x).loc A) := by
  constructor
  · apply PolyBound.of_bound ‖A‖
    intro x; rw [Frm.loc_norm]
  have he : Continuous (fun u:Frm m=> u.loc A) := ContLoc A
  have hm : Measurable (fun x:Rn m=> (q.FL.Fr x).loc A) := MeasLoc q.FL.Fr q.FL.fr_m A
  exact hm.aestronglyMeasurable
lemma nu_i {f:Plane→ℝ} (hf:Bwt f) (i:Fin m) :
    Integrable (fun x=> q.nupt i x f) (normal m) := by
  let l := q.FL.ev
  let M := fun x=> (q.FL.Fr x).loc (q.M i)
  have hi (j k:Fin m) : regular (fun x:Rn m=> (M x j k)^2*f (l x j,l x k)) := by
    have he := ((q.locMe i (q.M i)).lin (coeffMap j k))
    have hp : regular (fun x:Rn m=> f (l x j, l x k)) :=
      ⟨hf.p.comp ((poly_eig q.FL.poly q.FL.Fr j).prodMk (poly_eig q.FL.poly q.FL.Fr k)),
        (hf.c.measurable.comp ((q.FL.ev_m j).prodMk (q.FL.ev_m k))).aestronglyMeasurable⟩
    simp_rw [pow_two]
    exact (he.mul he).mul hp
  unfold nupt LPt.npt mats
  refine Integrable.div_const (integrable_finsetSum _ ?_) _
  exact fun j _=> integrable_finsetSum _ (fun k _=> (hi j k).ig)
lemma nu_add {f g:Plane→ℝ} (hf:Bwt f) (hg:Bwt g) :
    q.nu (fun u=>f u+g u)=q.nu f+q.nu g := by
  have he (i:Fin m) (x:Rn m) :
    q.nupt i x (fun u=>f u+g u)=q.nupt i x f+q.nupt i x g:= n_add ..
  unfold nu; simp_rw [he,integral_add (q.nu_i hf _) (q.nu_i hg _),Finset.sum_add_distrib]
lemma nu_sub {f g:Plane→ℝ} (hf:Bwt f) (hg:Bwt g) :
    q.nu (fun u=>f u-g u)=q.nu f-q.nu g := by
  have he := q.nu_add (hf.sub hg) hg
  rw [show (fun x=>f x-g x+g x)=f by ext; ring] at he; linarith
lemma nu_s (f:Plane→ℝ) (a:ℝ) :
    q.nu (fun u=>a*f u)=a*q.nu f := by
  unfold nu nupt; simp_rw [n_s,integral_const_mul,← Finset.mul_sum]
lemma nu_flip (f:Plane→ℝ) :
    q.nu (fun x:Plane=>f x.swap)=q.nu f := by
  unfold nu nupt
  simp_rw [n_flip _ _ f ((q.FL.Fr _).HL (q.M_sym _))]
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Gram
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06 weighted Dirichlet inequality: in a spectral frame. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
namespace LPt
open HMode Profile Layers Segment
variable {m:ℕ}
variable (M W:Mat m) (l:Fin m→ℝ)

lemma uf_sym (f:ℝ→ℝ) : (uf l f).IsHermitian :=
  Matrix.isHermitian_diagonal_iff.mpr fun _=> rfl
lemma base_PJ {A B C:Mat m} (ha:A.IsHermitian) (hb:B.IsHermitian) (hc:C.IsHermitian) :
    Pj A B C=ipN (A*B) C := by
  rw [pj_cyc3 ha hb hc,trN_cyclic _ A]; unfold ipN; rw [mul_assoc,show star C=C from hc]

lemma RR0_eq (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) (hw:W.IsHermitian) :
    RR0 M W l f=ipN (W*M) (mout M l (rest f)) := by
  have h : mout M l (rest f)=mout M l (bav f)-uf l f*M := by
    ext i j; rw [Matrix.sub_apply]
    unfold uf rest mout; rw [Matrix.diagonal_mul]; simp only [Matrix.of_apply]; ring
  have hi : Pj W (M*M) (uf l f)=ipN (W*M) (uf l f*M) := by
    rw [base_PJ hw (sqPSD hm).posSemidef.1 (uf_sym ..)]
    unfold ipN; rw [star_mul,show star M=M from hm,mul_assoc]; simp only [mul_assoc]
  rw [RR0, hi, h,base_PJ hw hm (out_her M l _ hf hm)]
  unfold ipN; rw [star_sub,mul_sub,trN_sub]

lemma RR0_I (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) :
    RR0 M 1 l f= npt M l (rest f) := by
  rw [RR0_eq _ _ _ _ hf hm isHermitian_one,one_mul,ipnout]
lemma JJ0_I (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) :
    JJ0 M 1 l f= npt M l (vdis f) := by
  rw [JJ0,base_PJ isHermitian_one hm (out_her _ _ _ (sq_test hf) hm),one_mul,
    ipnout,Pj,j_same,one_mul]
  let A := mout M l (bav f)
  have he : trN (A*A) = hsN A := by unfold hsN; rw [show star A=A from out_her _ _ _ hf hm]
  rw [show trN (_* _)=_ from he]
  unfold vdis; rw [n_sub]; unfold A; rw [hsout]; rfl

lemma vpc {T U M D:Mat m} (h:T.IsHermitian) (ha:U.IsHermitian)
    (hm:M.IsHermitian) (hd:D.IsHermitian):
    trN (T*(D*U*M))=trN (T*(M*U*D)) := by
  rw [← trace_star_r]
  simp only [star_mul,show star T=T from h, show star U=U from ha,
    show star M=M from hm,show star D=D from hd]
  rw [trN_cyclic _ T]
  simp only [mul_assoc]

lemma JJ0_eq (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) (hw:W.IsHermitian) :
    let X := mout M l (dis f)
    JJ0 M W l f=
      ipN (W*M) (mout M l (mdis f))-trN (W*(X*star X)) := by
  intro X
  let D := mout M l (bav f)
  let U := uf l f
  let A := mout M l (sqav f)
  have he : X = D-M*U := by
    ext i j
    unfold X D U uf; rw [Matrix.sub_apply,Matrix.mul_diagonal]
    unfold mout dis; simp only [Matrix.of_apply]; ring
  have hh : mout M l (mdis f)=A-(2:ℝ)•(D*U)+M*U*U := by
    ext i j; unfold mdis A D U uf; rw [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
      Matrix.mul_diagonal,Matrix.mul_diagonal,Matrix.mul_diagonal]
    simp [mout]; ring
  have hd : D.IsHermitian := out_her M l _ hf hm
  have hu : U.IsHermitian := uf_sym ..
  have hA : A.IsHermitian := out_her M l _ (sq_test hf) hm
  have hy := vpc hw hu hm hd
  change Pj W M A-Pj W D D = _
  rw [base_PJ hw hm hA,Pj,j_same,he,hh]
  unfold ipN
  simp only [star_add,star_sub,star_smul,star_mul,(show star U=U from hu),
    (show star M=M from hm),(show star D=D from hd),mul_smul_comm,trN_smul,
    sub_mul,mul_sub,mul_add,trN_add,trN_sub,mul_assoc,RCLike.star_def,map_ofNat] -- star reals
  simp only [mul_assoc] at hy; rw [hy]; ring

lemma JJ0_le (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) (hw:W.IsHermitian)
    (ht: W ≤ scalar m tmax) :
    ipN (W*M) (mout M l (mdis f)) - JJ0 M W l f ≤
      tmax*npt M l (fun u=> dis f u^2) := by
  let X := mout M l (dis f)
  have h := trN_mul_mono ht (mul_star_self_nonneg X)
  have he : trN ((scalar m tmax)*(X*star X))=tmax*npt M l (fun u=>dis f u^2) := by
    rw [scalar,smul_mul_assoc,one_mul,trN_smul,← hsout]; rfl
  rw [he] at h
  rw [JJ0_eq M W l f hf hm hw]
  simpa [X] using h

lemma BstarP :
    ipN (W*M) (mout M l bstar)=
      ipN (W*M) (mout M l (rest Cp))-ipN (W*M) (mout M l (mdis uc))-
        ipN (W*M) (mout M l (mdis us))-ipN (W*M) (mout M l (mdis qu)) := by
  have h : mout M l bstar=mout M l (rest Cp)-mout M l (mdis uc)-
      mout M l (mdis us)-mout M l (mdis qu) := by
    ext i j; simp only [mout,bstar,rsum,Matrix.sub_apply,Matrix.of_apply]; ring
  unfold ipN; rw [h]; simp_rw [star_sub,mul_sub,trN_sub]

lemma pt26 (hm:M.IsHermitian) (hw:W.IsHermitian)
    (ht: W ≤ scalar m tmax) (h:LayerOK) :
    RR0 M W l Cp-JJ0 M W l uc-JJ0 M W l us-JJ0 M W l qu ≤
      lam*hsN (W*M)+(1/(4*lam))*npt M l (fun u=> bstar u^2)+
        tmax*npt M l dsum := by
  rw [RR0_eq M W l Cp testC hm hw]
  have hi : ipN (W*M) (mout M l bstar) ≤
      lam*hsN (W*M)+(1/(4*lam))*npt M l (fun u=>bstar u^2) := by
    let A := W*M
    let Y := mout M l bstar
    have hj := young_H (-A) Y (show 0<lam by norm_num [lam])
    have hx : ipN (-A) Y= -ipN A Y := by unfold ipN trN; simp [neg_mul]; ring
    have hz : hsN (-A)=hsN A := by unfold hsN; simp
    rw [hx,hz,show hsN Y=_ from hsout M l bstar] at hj
    exact (by unfold lam at *; norm_num at *; unfold A Y at *; linarith)
  rw [BstarP] at hi
  have hh := JJ0_le M W l uc h.c_test hm hw ht
  have he := JJ0_le M W l us h.s_test hm hw ht
  have hu := JJ0_le M W l qu h.q_test hm hw ht
  unfold dsum; rw [n_add,n_add]; unfold tmax at *; linarith
end LPt
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Eq26
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06 weighted Dirichlet inequality. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open LPt HMode Profile Layers Segment
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (W:Mat m)
lemma DLherm (i:Fin m) {f} (hf:TestF f):
    regular (fun x=>q.DLMat f x i) := q.LD_reg _ (pl_test hf)
lemma DJi (i:Fin m) {f} (hf:TestF f):
    Integrable (q.locJ W i f) (normal m) :=
  (int_Pj _ (reg_constM _) (q.DLherm _ (sq_test hf))).sub
    (int_Pj _ (q.DLherm i hf) (q.DLherm i hf))
lemma locJ_form {f} (hf:TestF f):
    q.Jtest W f=
      ∑ i:Fin m,(∫ x,q.locJ W i f x ∂normal m) := by
  have hh := sq_test hf
  unfold Jtest; rw [q.L_identity W (pl_test hh),pl_d hh]
  unfold dirF Pt locJ
  simp_rw [integral_sub (int_Pj _ (reg_constM _) (q.DLherm _ hh)) (int_Pj _
    (q.DLherm _ hf) (q.DLherm _ hf)),Finset.sum_sub_distrib]
lemma mDout (i:Fin m) (x) {f} (hf:TestF f):
    let u := q.FL.Fr x
    u.loc (q.DLMat f x i)=mout (u.loc (q.M i)) (q.FL.ev x) (bav f) := by
  intro u
  unfold DLMat mout
  ext j k
  have he := q.mder_frame i j k (pl_test hf) x
  rw [pl_d hf] at he
  rw [show u.loc _ j k=_ from he]; simp only [Matrix.of_apply,mul_comm]; rfl
lemma Rpt_eq (i:Fin m) (x) {f} (hf:TestF f):
    let u := q.FL.Fr x
    q.locR W i f x=RR0 (u.loc (q.M i)) (u.loc W) (q.FL.ev x) f := by
  intro u
  unfold locR RR0
  rw [← u.pjL, ← u.pjL W (q.M i*q.M i)]
  rw [u.loc_mul,show u.loc (q.DLMat _ _ _)=_ from q.mDout i x hf,
    show u.loc (q.FL.eval f x)=_ from q.FL.evfrm x f]
  rfl
lemma Jpt_eq (i:Fin m) (x) {f} (hf:TestF f):
    let u:= q.FL.Fr x
    q.locJ W i f x=JJ0 (u.loc (q.M i)) (u.loc W) (q.FL.ev x) f := by
  intro u
  unfold locJ JJ0
  rw [← u.pjL, ← u.pjL W (q.DLMat _ x i)]
  rw [show u.loc (q.DLMat _ _ _)=_ from q.mDout i x (sq_test hf),
    show u.loc (q.DLMat _ _ _)=_ from q.mDout i x hf]

lemma R_nu {f} (hf:TestF f) :
    q.RM 1 f=q.nu (rest f) := by
  have he (i x) :
      q.locR 1 i f x=q.nupt i x (rest f) := by
    rw [q.Rpt_eq 1 i x hf]
    rw [Frm.loc_one,LPt.RR0_I _ _ _ hf ((q.FL.Fr x).HL (q.M_sym _))]
    rfl
  unfold nu RM; simp_rw [he]
lemma J_nu {f} (hf:TestF f): q.Jtest 1 f=q.nu (vdis f) := by
  have he (i x) :
      q.locJ 1 i f x=q.nupt i x (vdis f) := by
    rw [q.Jpt_eq 1 i x hf]
    rw [Frm.loc_one,LPt.JJ0_I _ _ _ hf ((q.FL.Fr x).HL (q.M_sym _))]; rfl
  rw [q.locJ_form 1 hf]
  unfold nu; simp_rw [he]
lemma J_sum (T:Mat m) {f} (hf:TestF f):
    q.Jtest (W+T) f=q.Jtest W f+q.Jtest T f := by
  have he (i x) : q.locJ (W+T) i f x=q.locJ W i f x+q.locJ T i f x := by
    unfold locJ Pj; simp_rw [add_mul,trN_add]; ring
  simp_rw [q.locJ_form _ hf,he,integral_add (q.DJi W _ hf) (q.DJi T _ hf),
    Finset.sum_add_distrib]
lemma J_vec (h:LayerOK):
    q.JVec (1+W)=q.nu vsum + q.JVec W := by
  unfold JVec vsum
  rw [q.J_sum _ _ h.c_test,q.J_sum _ _ h.s_test,q.J_sum _ _ h.q_test,
    q.J_nu h.c_test,q.J_nu h.s_test,q.J_nu h.q_test,
    q.nu_add ((Wv h.c_test).add (Wv h.s_test)) (Wv h.q_test),
    q.nu_add (Wv h.c_test) (Wv h.s_test)]; ring

lemma S_W (i:Fin m) (ht:W.IsHermitian) :
    hsN (W*q.M i)=trN ((q.M i*q.M i)*(W*W)) := by
  unfold hsN
  rw [star_mul,show star W=W from ht,show star (q.M i)=_ from q.M_sym i,mul_assoc,trN_cyclic W]
  simp only [mul_assoc]
lemma S_pair (ht:W.IsHermitian) :
    (∑ i:Fin m,hsN (W*q.M i)) = trN (q.sumS*(W*W)) := by
  unfold sumS; simp_rw [q.S_W W _ ht,← trL_apply,Finset.sum_mul,_root_.map_sum]
lemma eq26pt (i:Fin m) (hh:LayerOK) (ht:W∈specBox m tmin tmax) (x:Rn m):
    q.locR W i Cp x-q.locJ W i uc x-q.locJ W i us x-q.locJ W i qu x ≤
      lam*hsN (W*q.M i)+(1/(4*lam))*q.nupt i x (fun u=>bstar u^2)+
        tmax*q.nupt i x dsum := by
  let U:=q.FL.Fr x
  rw [q.Rpt_eq W _ _ testC,q.Jpt_eq W _ _ hh.c_test,q.Jpt_eq W _ _ hh.s_test,
    q.Jpt_eq W _ _ hh.q_test,← hsN_loc _ U,U.loc_mul]
  apply LPt.pt26 _ _ _ (U.HL (q.M_sym i)) (U.HL ht.1) _ hh
  have hi := U.loc_le ht.2.2
  rwa [scalar,U.loc_smul,U.loc_one] at hi
lemma eq26sum (i:Fin m) (hh:LayerOK) (ht:W∈specBox m tmin tmax) :
    (∫ x,q.locR W i Cp x ∂normal m)-(∫ x,q.locJ W i uc x ∂normal m)-
      (∫ x,q.locJ W i us x ∂normal m)-(∫ x,q.locJ W i qu x ∂normal m) ≤
      lam*hsN (W*q.M i)+(1/(4*lam))*(∫ x,q.nupt i x (fun u=>bstar u^2) ∂normal m)+
        tmax*(∫ x,q.nupt i x dsum ∂normal m) := by
  have h := q.DRi W i testC
  have ha := q.DJi W i hh.c_test
  have hb := q.DJi W i hh.s_test
  have hc := q.DJi W i hh.q_test
  have hi := (q.nu_i (Wsq (Wb hh)) i).const_mul (1/(4*lam))
  have hj := (q.nu_i (Wd hh) i).const_mul tmax
  have H := integral_mono (Integrable.sub (((h.sub ha).sub hb)) hc)
    (((integrable_const _).add hi).add hj) (q.eq26pt W i hh ht)
  rw [integral_sub' ((h.sub ha).sub hb) hc,integral_sub' (h.sub ha) hb,integral_sub' h ha,
    integral_add' ((integrable_const _).add hi) hj,integral_add' (integrable_const _) hi] at H
  simpa only [integral_const_mul,integral_const,probReal_univ,one_smul] using H

lemma eq26 (hh:LayerOK) (ht:W∈specBox m tmin tmax) :
    q.RM W Cp-q.JVec W ≤
      lam*trN (q.sumS*(W*W))+(1/(4*lam))*q.nu (fun u=>bstar u^2)+
        tmax*q.nu dsum := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i (_:i∈Finset.univ)=>q.eq26sum W i hh ht)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum] at h
  rw [q.S_pair W ht.1] at h
  rw [RM,JVec,q.locJ_form W hh.c_test,q.locJ_form W hh.s_test,q.locJ_form W hh.q_test]
  unfold nu; linarith
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Gauss
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Squared norm averaging. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}

lemma ihSq {f:Rn m→ℝ} (hf:regular f): Integrable (fun x=>f x^2) (normal m) := by
  simp_rw [pow_two]; exact (hf.mul hf).ig
lemma var_le1 {f:Rn m→ℝ} (hf:regular f):
    (∫ x,f x ∂normal m)^2 ≤ ∫ x,f x^2 ∂normal m := by
  let c:= ∫ x,f x ∂normal m
  have hi : 0 ≤ ∫ x,f x^2-(2*c)*f x+c^2 ∂normal m := by
    apply integral_nonneg; intro x; change (0:ℝ)≤ f x^2-_+_; nlinarith [sq_nonneg (f x-c)]
  rw [integral_add (show Integrable (fun x=>f x^2-(2*c)*f x) (normal m) from ((ihSq hf).sub (hf.ig.const_mul _))) (integrable_const _), integral_sub
    (ihSq hf) (hf.ig.const_mul _),integral_const_mul,integral_const,probReal_univ,one_smul] at hi
  change c^2 ≤ _
  change 0 ≤ _-(2*c)*c+_ at hi; linarith

lemma hs_entry (f:Rn m→Mat m) (hf:regular f):
    (∫ x,hsN (f x) ∂normal m)=
      mats (fun i=>∑ j,∫ x,(f x i j)^2 ∂normal m) := by
  have h (i j) : Integrable (fun x=>(f x i j)^2) (normal m) := ihSq (hf.lin (coeffMap i j))
  simp_rw [hsN_eq]; unfold mats
  rw [integral_div]; congr 1
  rw [integral_finsetSum]
  · congr; ext i; exact integral_finsetSum _ fun j _=>h i j
  exact fun i _=> integrable_finsetSum _ fun j _=>h i j

lemma hs_le_exp (f:Rn m→Mat m) (hf:regular f):
    hsN (∫ x,f x ∂normal m) ≤ ∫ x,hsN (f x) ∂normal m := by
  rw [hs_entry f hf,hsN_eq]
  apply mats_le; intro i; apply Finset.sum_le_sum; intro j _
  have hi : (∫ x,f x ∂normal m) i j=∫ x,f x i j ∂normal m := ((coeffMap i j).integral_comp_comm hf.ig).symm
  rw [hi]
  exact var_le1 (hf.lin (coeffMap i j))

lemma hsCm (A B:Mat m): hsN (cmu A B)=hsN (cmu B A) := by
  rw [show cmu A B= -(cmu B A) from by simp [cmu] ]
  simp [hsN]

namespace ProjField
lemma coord_reg (i:Fin m):
    regular (coord i) :=
  ⟨PolyBound.clm _,(coord i).continuous.aestronglyMeasurable⟩
lemma avg_sq_lin (f:Rn m→ℝ) (h:Fin m→ℝ) (he:∀ x:Rn m,f x=∑ i,x i*h i):
    (∫ x,f x^2 ∂normal m) = ∑ i,h i^2 := by
  have ha (i j:Fin m):
      Integrable (fun x:Rn m=> (x i*x j)*(h i*h j)) (normal m) :=
    ((coord_reg i).mul (coord_reg j)).ig.mul_const _
  have hx (x:Rn m): f x^2=
      ∑ i:Fin m,∑ j:Fin m,(x i*x j)*(h i*h j) := by
    rw [he x,pow_two,Finset.sum_mul]; congr 1; ext i
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hu (i j:Fin m):
    (∫ x:Rn m,x i*x j ∂normal m) = if i=j then (1:ℝ) else 0 := by
    simp_rw [← Mi1, M_inner]
    by_cases hi:i=j
    · subst j; simp
    have hv : inc (0:MI m) i ≠ inc 0 j := by
      intro h; have hk:=congrFun h i; simp [inc,hi] at hk
    simp [hv,hi]
  simp_rw [hx]
  rw [integral_finsetSum]
  · have hv (i:Fin m) :
        (∫ x:Rn m,(∑ j,(x i*x j)*(h i*h j)) ∂normal m)=h i^2 := by
      rw [integral_finsetSum]
      · simp_rw [integral_mul_const,hu]
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
        · simp [pow_two]
        intro j _ hj; simp [hj.symm]
      exact fun j _=>ha i j
    simp_rw [hv]
  exact fun i _=>integrable_finsetSum _ (fun j _=>ha i j)

lemma Comm_L (q:ProjField m) (T:Mat m):
    Hcomm q.Lmat T=∑ i,hsN (cmu (q.M i) T) := by
  obtain ⟨D,hD⟩:=cmCL T
  let f := fun x=>cmu (q.Lmat x) T
  let g := fun i=>cmu (q.M i) T
  have hf : regular f := by unfold f; simp_rw [← congrFun hD]; exact q.l_reg.lin D
  have hl (x:Rn m) : f x=∑ i,x i • g i := by
    unfold f g
    simp_rw [← congrFun hD,Lmat,_root_.map_sum,_root_.map_smul]
  have hh (i j:Fin m) :
      (∫ x,(f x i j)^2 ∂normal m)=∑ k:Fin m,(g k i j)^2 := by
    apply avg_sq_lin; intro x; rw [hl]
    simp_rw [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  unfold Hcomm
  change (∫ x, hsN (f x) ∂normal m)=∑ i,hsN (g i)
  rw [hs_entry f hf]
  simp_rw [hh,hsN_eq]; unfold mats
  rw [← Finset.sum_div]; congr 1
  have he (i:Fin m) : (∑ j:Fin m,∑ k:Fin m,(g k i j)^2)=∑ k,∑ j,(g k i j)^2 := by rw [Finset.sum_comm]
  simp_rw [he]
  rw [Finset.sum_comm]

variable [NeZero m]

lemma comm_expect (q:ProjField m) (M:Mat m) {f:ℝ→ℝ} (hf:TestF f) :
    hsN (cmu M (q.expL f)) ≤ ∫ x,hsN (cmu (q.FL.eval f x) M) ∂normal m := by
  obtain ⟨D,hD⟩:=cmCL M
  have he (A:Mat m) : cmu A M=D A := by rw [← congrFun hD]
  let F:=q.FL.eval f
  rw [hsCm]
  simp_rw [he]
  have h : q.expL f= ∫ x,F x ∂normal m := rfl
  rw [h,← D.integral_comp_comm (q.FL.eval_reg hf).ig]
  exact hs_le_exp _ ((q.FL.eval_reg hf).lin D)
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Eq27
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06 final commutator comparison. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open LPt Profile HMode Segment Layers
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
lemma cmb_test : TestF cmbf := testK.add ((TestF.const _).mul testC)
lemma expcmb : q.expL cmbf=q.expL Kp+tc•q.expL Cp := by
  let f:=tc
  have he (x:Rn m):
      q.FL.eval cmbf x=q.FL.eval Kp x+tc•q.FL.eval Cp x := by
    have h (g:ℝ→ℝ) (hg:TestF g) :
        q.FL.eval (fun x=>Kp x+g x) x=q.FL.eval Kp x+q.FL.eval g x :=
      cfc_add (q.Lmat x) _ _ testK.cont.continuousOn hg.cont.continuousOn
    unfold cmbf; rw [h (fun x=>tc*Cp x) ((TestF.const _).mul testC),q.FL.eval_scale testC]
  have hi (f:ℝ→ℝ) : q.expL f=∫ x,q.FL.eval f x ∂normal m := rfl
  rw [hi,hi,hi]; simp_rw [he]
  rw [integral_add (q.FL.eval_reg testK).ig (show Integrable (fun x=>tc • q.FL.eval Cp x) (normal m) from Integrable.smul tc (q.FL.eval_reg testC).ig),integral_smul]

lemma eiganti (i:Fin m) (f:ℝ→ℝ) (x:Rn m):
    hsN (cmu (q.FL.eval f x) (q.M i))=q.nupt i x (fun u=>anti u f^2) := by
  let A :=q.FL.eval f x
  let U:=q.FL.Fr x
  have h : U.loc A = diagonal (fun i=>f (q.FL.ev x i)) := q.FL.evfrm x f
  have he : U.eig A=fun i=>f (q.FL.ev x i) := by unfold Frm.eig; rw [h,Matrix.diag_diagonal]
  have hh : U.Dgn A := by unfold Frm.Dgn; rw [h,he]
  rw [cmu_eig A _ U hh,he]
  unfold nupt npt; congr 1; ext j; apply Finset.sum_congr rfl
  intro k _
  dsimp only [anti,U]; ring

lemma eq27elem (T:Mat m) (he:updEq (q.expL Cp) (q.expL Kp) T=0)
    (ht:T∈specBox m tmin tmax)
    (hH: scalar m mstar ≤ updGap (q.expL Cp) T) (i:Fin m):
    (80/100)*hsN (cmu (q.M i) T) ≤ (∫ x,q.nupt i x sgamma ∂normal m) := by
  have hx := Comm_bound (q.expL_sym testC.cont testC.poly) ht he hH (q.M i)
  rw [← q.expcmb] at hx
  let f := fun u:Plane=> anti u cmbf^2
  let g := fun u:Plane=> anti u Cp^2
  have h (x:Rn m) :
      q.nupt i x sgamma = (80/100/mstar^2)*((125/100)*q.nupt i x f+
        5*Profile.tr^2*q.nupt i x g) := by
    unfold nupt
    have he : sgamma=fun u=>(80/100/mstar^2)*((125/100)*f u+5*Profile.tr^2*g u) := by
      ext; unfold sgamma f g cmbf anti; ring
    rw [he,n_s,n_add,n_s,n_s]
  have hi:= q.comm_expect (q.M i) cmb_test
  have hj:= q.comm_expect (q.M i) testC
  simp_rw [q.eiganti] at hi hj
  change hsN _ ≤ ∫ x,q.nupt i x f ∂normal m at hi
  change hsN _ ≤ ∫ x,q.nupt i x g ∂normal m at hj
  simp_rw [h,integral_const_mul]
  have hfi := (q.nu_i (Wsq (Wa cmb_test)) i).const_mul (125/100)
  have hgi := (q.nu_i (Wsq (Wa testC)) i).const_mul (5*Profile.tr^2)
  rw [integral_add (show Integrable (fun x=>125/100*q.nupt i x f) (normal m) from hfi)
    (show Integrable (fun x=> (5*Profile.tr^2)*q.nupt i x g) (normal m) from hgi),
    integral_const_mul,integral_const_mul]
  unfold mstar Profile.tr at *; norm_num at *; linarith

lemma eq27 (T:Mat m) (he:updEq (q.expL Cp) (q.expL Kp) T=0)
    (ht:T∈specBox m tmin tmax)
    (hH: scalar m mstar ≤ updGap (q.expL Cp) T) :
    (80/100)*Hcomm q.Lmat T ≤ q.nu sgamma := by
  rw [q.Comm_L,Finset.mul_sum]; unfold nu
  exact Finset.sum_le_sum (fun i _=> q.eq27elem T he ht hH i)
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Final
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06 final inequalities before rigidity. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open HMode Profile Segment Layers
variable {m:ℕ} [NeZero m]

lemma hsn_eq_zero (A:Mat m) (h:hsN A=0) : A=0 := by
  rw [hsN_eq] at h
  unfold mats at h
  have hm : (m:ℝ)≠0:= (ProjField.m_pos (m:=m)).ne'
  have hi := (div_eq_zero_iff.mp h).resolve_right hm
  have hh (i:Fin m) : (∑ j,A i j^2)=0 := by
    have he : 0≤∑ j,A i j^2 := by positivity
    refine le_antisymm ?_ he
    have hv := Finset.single_le_sum (f:=fun i=>∑ j,A i j^2) (s:=Finset.univ)
      (fun j _=> by positivity) (Finset.mem_univ i)
    rwa [hi] at hv
  ext i j
  have hv := Finset.single_le_sum (f:=fun j=>A i j^2) (s:=Finset.univ)
    (fun j _=> by positivity) (Finset.mem_univ j)
  rw [hh] at hv; change _=0; nlinarith

namespace ProjField
variable (q:ProjField m) (T:Mat m)

lemma nuR (h:LayerOK) :
    q.nu symR=q.nu (rest Kp)+q.nu sgamma+(1/(4*lam))*q.nu (fun u=>bstar u^2) +
      tmax*q.nu dsum-q.nu vsum := by
  unfold symR
  have hh := Wres h
  rw [q.nu_s,q.nu_add hh (Wflip hh),q.nu_flip,show (1/2:ℝ)*(q.nu resid+q.nu resid)=q.nu resid from by ring]
  unfold resid
  have he := (Wr testK).add Wg
  have hu := (Bwt.const (1/(4*lam))).mul (Wsq (Wb h))
  have hv := (Bwt.const tmax).mul (Wd h)
  rw [q.nu_sub ((he.add hu).add hv) (Wvs h),q.nu_add (he.add hu) hv,
    q.nu_add he hu,q.nu_add (Wr testK) Wg,q.nu_s,q.nu_s]
lemma nupt_neg (i:Fin m) (x) (h:SegmentOK) :
    q.nupt i x symR ≤ 0 := by
  unfold nupt LPt.npt mats
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  apply Finset.sum_nonpos; intro i _
  apply Finset.sum_nonpos; intro j _
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (Rle h _)
lemma nuR_neg (h:SegmentOK) : q.nu symR ≤ 0 := by
  unfold nu
  apply Finset.sum_nonpos
  intro i _; exact integral_nonpos fun x=> q.nupt_neg i x h

lemma Bpositive (h:LayerOK) (x): 0<Bgap x := sub_pos.mpr (wpos h x).1
lemma Btest (h:LayerOK): Bwt Bgap := (wwt h).sub (w0t h)
lemma Bgap_pos (h:LayerOK) :
    0 ≤ q.BB q.FL Bgap :=
  integral_nonneg fun x=> integral_nonneg fun z=> q.bm_pos q.FL x z Bgap fun u=>(Bpositive h u).le

lemma E_last (h:Balanced q T) (hc:UpdatesOK Cp Kp) (hh:LayerOK) :
    q.scoreE T ≤ q.nu symR - (14/100)*trN (T*T)- q.BB q.FL Bgap := by
  have ha := q.budget T h.ht h.cov hh h.avg
  have he := q.eq25 T h.eqn h.ht.1 h.gap (q.expL_bounds hc).1
  have hu := q.eq26 T hh h.ht
  have hv := q.eq27 T h.eqn h.ht h.gap
  rw [← h.cov,q.J_vec T hh] at ha
  rw [q.R_nu testK] at he
  rw [q.nuR hh]; unfold Bgap
  linarith
lemma entropy_pt (h:1+T=q.covMat):
    -q.scoreE T ≤ Real.log (chi q.C q.V*chi q.D q.U)/(m:ℝ) := by
  unfold scoreE
  have hh := q.entropy10 h
  rw [q.nn_eq]
  linarith
omit [NeZero m] in
lemma PairPos : 0 < chi q.C q.V*chi q.D q.U := by
  apply mul_pos
  · apply chi_pos (C:=q.C) ⟨q.U,q.U_in⟩ q.V_in
  have hq : q.U ∈ interior ((posDual q.D):Set (Rn m)) := by
    rw [show posDual q.D=q.C from ProperCone.innerDual_innerDual _]; exact q.U_in
  exact chi_pos (C:=q.D) ⟨q.V,q.V_in⟩ hq

lemma E_sign (h:Balanced q T) (hc:UpdatesOK Cp Kp) (hh:LayerOK) (hi:SegmentOK):
    q.scoreE T≤0 ∧ (q.scoreE T=0 → T=0∧q.nu symR=0 ∧ q.BB q.FL Bgap=0) := by
  have hz := q.E_last T h hc hh
  have hT : hsN T = trN (T*T) := by unfold hsN; rw [show star T=T from h.ht.1]
  rw [← hT] at hz
  have he := q.nuR_neg hi
  have hx := q.Bgap_pos hh
  have hm := hsN_pos T
  constructor
  · linarith
  intro hH
  refine ⟨hsn_eq_zero _ ?_,?_,?_⟩ <;> linarith

theorem Bound_pt (h:Balanced q T) (hc:UpdatesOK Cp Kp) (hh:LayerOK) (hi:SegmentOK):
    (1 ≤ chi q.C q.V*chi q.D q.U) ∧ (chi q.C q.V*chi q.D q.U=1 →
      T=0∧q.nu symR=0 ∧ q.BB q.FL Bgap=0) := by
  have hl := q.entropy_pt T h.cov
  obtain ⟨hj,hk⟩:= q.E_sign T h hc hh hi
  constructor
  · have he : 0 ≤ Real.log (chi q.C q.V*chi q.D q.U)/(m:ℝ) := by linarith
    have hv := (le_div_iff₀ m_pos).mp he
    rw [← Real.log_le_log_iff zero_lt_one q.PairPos, Real.log_one]
    linarith
  intro he; rw [he,Real.log_one,zero_div] at hl
  apply hk; linarith
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Rigid_Basis
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Joint eigenbasis and transfer of diagonality to projection.
Allows a nonorthogonal eigenbasis too. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Function
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma cfc_eig_all {A:Mat m} (ha:A.IsHermitian) {x:Rn m} {c:ℝ} (hc:op A x=c • x)
    (f:ℝ→ℝ) : op (cfc f A) x=f c • x := by
  let b:=ha.eigenvectorBasis
  apply b.repr.injective
  ext i
  rw [b.repr_apply_apply,b.repr_apply_apply]
  have he := op_iff_hermitian.mp ha (b i) x
  have h1 := op_iff_hermitian.mp (cfc_herm f A) (b i) x
  rw [hc,op_eigen ha] at he
  rw [cfc_eigen' f ha] at h1
  rw [← h1]
  simp only [real_inner_smul_left,real_inner_smul_right] at *
  change f _* ⟪b i,x⟫=_
  change _*⟪b i,x⟫=_ at he
  rcases eq_or_ne ⟪b i,x⟫ 0 with hz|hz
  · rw [hz]; ring
  rw [mul_right_cancel₀ hz he]

omit [NeZero m] in
lemma joint_exists (M:Fin m→Mat m) (h:∀ i,(M i).IsHermitian)
    (hh:∀ i j,cmu (M i) (M j)=0):
    ∃ b:Basis (Fin m) ℝ (Rn m),∀ j,∃ l:Fin m→ℝ,∀ i,op (M i) (b j)=l i • b j := by
  classical
  let T := fun i=> (op (M i)).toLinearMap
  let s : Set (Rn m) := {x| ∃ l:Fin m→ℝ,∀ i,op (M i) x=l i • x}
  have he : ⊤ ≤ Submodule.span ℝ s := by
    have hT (i) : (T i).IsSymmetric := op_iff_hermitian.mp (h i)
    have hC : Pairwise (Commute on T) := by
      intro i j _
      have h₁:= congrArg op (sub_eq_zero.mp (hh i j))
      rw [_root_.map_mul,_root_.map_mul] at h₁
      exact congrArg (fun x:Rn m→L[ℝ]Rn m=>x.toLinearMap) h₁
    rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC]
    apply iSup_le
    intro l x hx
    apply Submodule.subset_span
    refine ⟨l,fun i=>?_⟩
    exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx i)
  let b:=Basis.ofSpan he
  let b₀ : Basis (Fin m) ℝ (Rn m) := (EuclideanSpace.basisFun _ _).toBasis
  let k:=b.indexEquiv b₀
  refine ⟨b.reindex k,fun i=>?_⟩
  apply Basis.ofSpan_subset he
  rw [Basis.reindex_apply]
  exact ⟨_,rfl⟩

omit [NeZero m] in
lemma tendsto_aff_vol (B : Rn m ≃L[ℝ] Rn m) (a : Rn m):
    Tendsto (affineN B a) (ae volume) (ae volume) :=
  (tendsto_ae_affineN B a).mono_left ac_normal.ae_le

namespace ProjField
variable (q:ProjField m)
lemma projD (hm:∀ i j,cmu (q.M i) (q.M j)=0)
    (hz:∃ z:ℝ,∀ᵐ x∂normal m,q.Pmat z x=q.FL.Θ z x):
    ∃ b:Basis (Fin m) ℝ (Rn m),diagDeriv q.C b := by
  obtain ⟨b,hb⟩:=joint_exists q.M q.M_sym hm
  obtain ⟨z,hz⟩:=hz
  let F := affineN q.root (q.shift z)
  have he : ∀ᵐ x:Rn m,q.Pmat z x=q.FL.Θ z x := ac_normal.ae_le hz
  let G:=affineN q.root.symm (-(q.root.symm (q.shift z)))
  have hi : Tendsto G (ae volume) (ae volume) := tendsto_aff_vol ..
  refine ⟨b,?_⟩
  unfold diagDeriv
  filter_upwards [hi.eventually he] with x hx
  have hG : F (G x) = x := by simp [F,G,affineN]
  have hP : op (q.FL.Θ z (G x)) = fderiv ℝ (coneProj q.C) x := by
    rw [← hx]
    change op (op.symm (fderiv ℝ _ (F (G x))))=_
    rw [hG]; simp
  rw [← hP]
  intro j
  obtain ⟨l,hj⟩:=hb j
  let c:=∑ i:Fin m,(G x i)*l i
  have hl : op (q.Lmat (G x)) (b j)=c • b j := by
    unfold Lmat c
    simp_rw [_root_.map_sum,_root_.sum_apply,_root_.map_smul,_root_.smul_apply,hj]
    rw [Finset.sum_smul]; simp only [smul_smul]
  exact ⟨jump z c,cfc_eig_all (q.L_sym _) hl _⟩
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Rigid_Axes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Lipschitz/homogeneous with diagonal Jacobian a.e. ⇒
separate coordinates. Uses smoothG (gaussian averaging, §02). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open Layers
variable {m:ℕ}
private lemma lp_homo (C:ProperCone ℝ (Rn m)) {r:ℝ} (hr:0 < r) (x:Rn m):
    coneProj C (r • x)=r • coneProj C x := by
  let A := coneProj C x
  apply proj_unique C (C.smul_mem (proj_mem C _) hr.le)
  intro y hy
  have he := proj_vi C x (C.smul_mem hy (inv_pos.mpr hr).le)
  have hh : y-r • A=r • (r⁻¹ • y-A) := by rw [smul_sub,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  change ⟪r • x-r • A,y-r • A⟫≤_
  rw [hh,← smul_sub,real_inner_smul_left,real_inner_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos hr.le (mul_nonpos_of_nonneg_of_nonpos hr.le he)

lemma lp_same_smooth (g:Rn m→ℝ) {K:ℝ≥0} (hk:LipschitzWith K g)
    (x v:Rn m)
    (hh:∀ᵐ y:Rn m,fderiv ℝ g y v=0) : smoothG g x=smoothG g (x+v) := by
  let f := fun t:ℝ=> x+t • v
  have he (t:ℝ) : HasDerivAt (smoothG g ∘ f) 0 t := by
    obtain ⟨h,h'⟩:= smoothG_derivative_lipschitz hk (f t)
    have hd : HasDerivAt f v t := by
      convert ((hasDerivAt_const t x).fun_add ((hasDerivAt_id' t).smul_const v)) using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | simp
    have hp := h'.comp_hasDerivAt _ hd
    rw [ContinuousLinearMap.integral_apply h] at hp
    have ht : ∀ᵐ y∂normal m,fderiv ℝ g (y+f t) v=0 :=
      normal_ac.ae_le ((measurePreserving_add_right volume (f t)).quasiMeasurePreserving.tendsto_ae.eventually hh)
    rw [show (∫ y,fderiv ℝ g (y+f t) v ∂normal m)=0 from integral_eq_zero_of_ae ht] at hp
    exact hp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>he t)
    (continuous_const.intervalIntegrable 0 1)
  simp only [intervalIntegral.integral_zero,Function.comp_apply,f,zero_smul,one_smul,add_zero] at hi
  exact (sub_eq_zero.mp hi.symm).symm

lemma lp_mean_close (g:Rn m→ℝ) {K:ℝ≥0} (hk:LipschitzWith K g) (x:Rn m):
    ‖smoothG g x-g x‖ ≤ (∫ y:Rn m,(K:ℝ)*‖y‖ ∂normal m) := by
  let f := fun y:Rn m=>g (y+x)
  let L := fun y:Rn m=>(K:ℝ)*‖y‖
  have hc : Continuous f := hk.continuous.comp (continuous_id.add continuous_const)
  have hi : PolyBound f := (PolyBound.lipschitz hk).comp ((PolyBound.id).add (PolyBound.const _))
  have hv : Integrable f (normal m) := hi.gaussian_integrable hc.aestronglyMeasurable
  have ie : Integrable L (normal m) := (((PolyBound.const _).mul (PolyBound.id.norm)).gaussian_integrable
    (continuous_const.mul (continuous_norm (E:=Rn m))).aestronglyMeasurable)
  let j:= fun y:Rn m=> f y-g x
  have hh (y) : ‖j y‖≤ L y := by
    have he:=hk.dist_le_mul (y+x) x
    simpa only [dist_eq_norm,add_sub_cancel_right] using he
  have he : smoothG g x-g x=∫ y,j y ∂normal m := by
    unfold j; rw [integral_sub hv (integrable_const _)]
    simp; rfl
  rw [he]
  apply (norm_integral_le_integral_norm _).trans
  exact integral_mono (show Integrable j (normal m) from hv.sub (integrable_const _)).norm ie hh

variable (C:ProperCone ℝ (Rn m)) (b:Basis (Fin m) ℝ (Rn m))
lemma lp_comp (h:diagDeriv C b) (i:Fin m) (x y:Rn m) (he:b.coord i x=b.coord i y):
    b.coord i (coneProj C x)=b.coord i (coneProj C y) := by
  let B: Rn m→L[ℝ]ℝ := (b.coord i).toContinuousLinearMap
  let g := fun x:Rn m=>B (coneProj C x)
  let K := ‖B‖₊*1
  have hk : LipschitzWith K g:= B.lipschitz.comp (coneProj_lip C)
  let M := ∫ y:Rn m,(K:ℝ)*‖y‖ ∂normal m
  have hv (v:Rn m) (he:B v=0) : ∀ᵐ t:Rn m,fderiv ℝ g t v=0 := by
    filter_upwards [h,(coneProj_lip C).ae_differentiableAt] with t ht hp
    let d := fderiv ℝ (coneProj C) t
    have hd : fderiv ℝ g t = B.comp d := (B.hasFDerivAt.comp t hp.hasFDerivAt).fderiv
    rw [hd]
    conv_lhs => rw [← b.sum_repr v, _root_.map_sum]
    apply Finset.sum_eq_zero
    intro j _
    simp only [_root_.map_smul,ContinuousLinearMap.comp_apply]
    obtain ⟨l,hl⟩:=ht j
    rw [show d (b j)=_ from hl,_root_.map_smul]
    by_cases h:i=j
    · subst j; change b.repr v i • _=_
      change b.repr v i = 0 at he; rw [he,zero_smul]
    have h' : B (b j)=0 := by
      change b.coord i (b j)=0
      simp [h]
    rw [h',smul_zero,smul_zero]
  have hh (r:ℝ) (hr:0 < r) : r*‖g x-g y‖ ≤ 2*M := by
    let u := r • y-r • x
    have hb : B u=0 := by
      unfold u; rw [_root_.map_sub,_root_.map_smul,_root_.map_smul]
      change r • b.coord i y-r • b.coord i x=0
      rw [he,sub_self]
    have ht := lp_same_smooth g hk (r • x) u (hv u hb)
    have hu : r • x+u=r • y := by unfold u; abel
    rw [hu] at ht
    have hp (x:Rn m) : g (r • x)=r • g x := by unfold g; rw [lp_homo C hr,_root_.map_smul]
    have hi := norm_sub_le (g (r • x)-smoothG g (r • x)) (g (r • y)-smoothG g (r • y))
    rw [norm_sub_rev (g _), norm_sub_rev (g (r • y))] at hi
    have ha : g (r • x)-smoothG g (r • x)-(g (r • y)-smoothG g (r • y))=
        r • (g x-g y) := by rw [ht,hp,hp,smul_sub]; abel
    rw [ha,norm_smul,Real.norm_of_nonneg hr.le] at hi
    have hh (x:Rn m): ‖smoothG g x-g x‖ ≤ M:= lp_mean_close g hk _
    linarith [hh (r • x),hh (r • y)]
  change g x=g y
  by_contra hx
  have ht : 0 < ‖g x-g y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hp : 0<M := by linarith [hh 1 zero_lt_one]
  have hi := hh ((2*M+1)/‖g x-g y‖) (by positivity)
  rw [div_mul_cancel₀ _ ht.ne'] at hi
  linarith
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Rigid_Support
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06 equality from strict signs, support of two layer functionals. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open LPt Profile Segment Layers
variable {m:ℕ}
private lemma sZeroPt {f:Fin m→ℝ} (h:∀ i,0≤f i) (hh:∑ i,f i=0) (i:Fin m) : f i=0 := by
  refine le_antisymm ?_ (h i)
  have hi := Finset.single_le_sum (s:=Finset.univ) (fun j _=>h j) (Finset.mem_univ i)
  rwa [hh] at hi
private lemma s0n {f:Fin m→ℝ} (h:∀ i,f i≤0) (hh:∑ i,f i=0) (i:Fin m) : f i=0 := by
  have he : ∀ i,0 ≤ -f i := fun j=> neg_nonneg.mpr (h j)
  have hi : (∑ i,-f i)=0 := by rw [Finset.sum_neg_distrib,hh,neg_zero]
  exact neg_eq_zero.mp (sZeroPt he hi i)
variable [NeZero m]

private lemma m0 {f:Fin m→ℝ} (hh:mats f=0): ∑ i, f i=0 := by
  unfold mats at hh
  exact (div_eq_zero_iff.mp hh).resolve_right (show (m:ℝ)≠0 from (ProjField.m_pos (m:=m)).ne')

namespace ProjField
variable (q:ProjField m)
lemma pt_czero (i:Fin m) (x:Rn m) (h:SegmentOK) (hz:q.nupt i x symR=0) :
    hsN (cmu (q.Lmat x) (q.M i))=0 := by
  let l:=q.FL.ev x
  let u:=q.FL.Fr x
  let M:=u.loc (q.M i)
  let f := fun j k:Fin m=>M j k^2*symR (l j,l k)
  have hh (j k) : f j k≤0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (Rle h _)
  have hp (j) : ∑ k,f j k=0 :=
    s0n (fun j=> Finset.sum_nonpos (s:=Finset.univ) (f:=f j) (fun k _=>hh j k))
      (m0 (show mats (fun i=>∑ k,f i k)=0 from hz)) j
  have he (j k) : (l j-l k)^2*M j k^2 =0 := by
    have hi := s0n (hh j) (hp j) k
    unfold f at hi
    by_cases h': l j=l k
    · simp [h']
    have h : symR (l j,l k)<0 := negR h _ h'
    rw [(mul_eq_zero.mp hi).resolve_right h.ne,mul_zero]
  rw [cmu_eig (q.Lmat x) (q.M i) u (q.FL.Fr_D x)]
  change mats (fun j=>∑ k,(l j-l k)^2*M j k^2)=0
  simp [he,mats]

lemma nu_comm (h:LayerOK) (hs:SegmentOK) (hz:q.nu symR=0) (i j:Fin m):
    cmu (q.M j) (q.M i)=0 := by
  let f:= fun k x=> q.nupt k x symR
  have hh (i:Fin m) : (∫ x,f i x ∂normal m)=0 :=
    s0n (f:=fun i=> ∫ x,f i x ∂normal m)
      (fun j=> integral_nonpos fun x=>q.nupt_neg j x hs) hz i
  have hp : ∀ᵐ x∂normal m,f i x=0 := by
    have hi : (∫ x,-f i x ∂normal m)=0 := by rw [integral_neg,hh,neg_zero]
    have hv : (0: Rn m→ℝ)≤ fun x=> -f i x :=
      fun x=> neg_nonneg.mpr (q.nupt_neg i _ hs)
    filter_upwards [(integral_eq_zero_iff_of_nonneg hv (show Integrable _ _ from
      (q.nu_i (WR h) i).neg)).mp hi] with x hx
    exact neg_eq_zero.mp hx
  have he : (∑ j,hsN (cmu (q.M j) (q.M i)))=0 := by
    rw [← q.Comm_L,Hcomm]
    apply integral_eq_zero_of_ae
    exact hp.mono fun x hx=> q.pt_czero i x hs hx
  exact hsn_eq_zero _ (sZeroPt (fun i=> hsN_pos _) he j)

lemma BLzero (h:LayerOK) (x z)
    (hd:∀ i,q.FL.ev x i≠z) (he:q.bmZ q.FL Bgap z x=0): q.EZ q.FL z x=0 := by
  let b:= q.BL q.FL x z
  have hi (i:Fin m) : b.S i i=0 := by
    have hp := q.bm_trace q.FL x z Bgap
    rw [hp] at he
    have h₀ : ∑ i,b.S i i*Bgap (z,b.x i)=0 := m0 he
    have hi (i:Fin m): 0 ≤ b.S i i*Bgap (z,b.x i) :=
      mul_nonneg (b.Spar.posSemidef.diag_nonneg) (Bpositive h _).le
    exact (mul_eq_zero.mp (sZeroPt hi h₀ i)).resolve_right (Bpositive h _).ne'
  have hE : b.E=0 := by
    ext i j
    have he := b.Ed2 i
    have hz := hi i
    have hp : b.a i≠0 := abs_ne_zero.mpr (sub_ne_zero.mpr (hd i))
    rw [b.Sdiag,mul_assoc] at hz
    have hv : b.L i*b.E i i=0 := (mul_eq_zero.mp hz).resolve_left hp
    rw [hv] at he
    have hi := Finset.single_le_sum (f:=fun j=>b.E i j^2) (s:=Finset.univ)
      (fun j _ => by positivity) (Finset.mem_univ j)
    change _ = 0; nlinarith
  apply (q.FL.Fr x).loc_inj
  rw [Frm.loc_zero,← q.BLe]
  exact hE

lemma B_layer (h:LayerOK) (hz:q.BB q.FL Bgap=0):
    ∃ z:ℝ,∀ᵐ x∂normal m,q.Pmat z x=q.FL.Θ z x := by
  let F:=q.bmZ q.FL Bgap
  have hp (z x) : 0≤F z x := q.bm_pos q.FL x z Bgap fun u=> (Bpositive h u).le
  have he : ∀ᵐ x∂normal m, (∫ z,F z x)=0 :=
    (integral_eq_zero_iff_of_nonneg (show (0:Rn m→ℝ)≤ fun x=>∫ z,F z x from
      fun x=>integral_nonneg fun z=>hp z x) (q.bmah q.FL (Btest h))).mp hz
  let p := fun (x:Rn m) (z:ℝ)=>q.EZ q.FL z x=0
  have hm : MeasurableSet {x:Rn m × ℝ| p x.1 x.2} :=

    ((q.eSM q.FL).measurable.comp measurable_swap) measurableSet_eq
  have hh : ∀ᵐ z:ℝ,∀ᵐ x∂normal m,p x z := by
    apply (Measure.ae_ae_comm hm).mp
    filter_upwards [he] with x hx
    have hj : ∀ᵐ z:ℝ,F z x=0 := (integral_eq_zero_iff_of_nonneg
      (show (0:ℝ→ℝ)≤ fun z=> F z x from fun z=>hp z x)
      (q.bmh q.FL (Btest h) x)).mp hx
    have ha (i:Fin m): ∀ᵐ z:ℝ, z≠ q.FL.ev x i := by
      apply Measure.ae_ne
    filter_upwards [hj, ae_all_iff.mpr ha] with z hz he
    exact q.BLzero h x z (fun i=> Ne.symm (he i)) hz
  obtain ⟨z,hz⟩:= hh.exists
  exact ⟨z,hz.mono fun x hx=> sub_eq_zero.mp hx⟩
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Rigid_Rays
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Cone image orthant rigidity. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Profile Segment
variable {m:ℕ}

theorem cone_axes (C:ProperCone ℝ (Rn m))
    {u v:Rn m} (hu:u∈interior (C:Set (Rn m))) (hv:v∈interior (posDual C:Set (Rn m)))
    (b:Basis (Fin m) ℝ (Rn m))
    (hh:diagDeriv C b): IsLinearOrthant m C := by
  classical
  have hs (x:Rn m) (hx:x∈C) (i:Fin m):
      b.coord i x • b i ∈ C := by
    let p:=b.coord i x • b i
    have h : coneProj C p=p := by
      apply b.equivFun.injective
      ext j; change b.coord j (coneProj C p)=b.coord j p
      by_cases he:i=j
      · subst j
        have hp : b.coord i p=b.coord i x := by simp [p]
        rw [lp_comp C b hh i p x hp,proj_of_mem _ hx,hp]
      have hp : b.coord j p=b.coord j 0 := by simp [p,Ne.symm he]
      rw [lp_comp C b hh j p 0 hp,proj_of_mem C C.zero_mem,hp]
    change p∈C; exact h ▸ proj_mem C p
  have h' (i:Fin m) : ∃ c:ℝ,c≠0 ∧ c • b i ∈ C := by
    by_cases hz: b.coord i u=0
    · let f := fun x:ℝ=> u+x • b i
      have hi : Continuous f := by unfold f; fun_prop
      have he : ∀ᶠ x in 𝓝[>] (0:ℝ),f x ∈ (C : Set (Rn m)) :=
        nhdsWithin_le_nhds ((hi.tendsto 0) (by simpa [f] using mem_interior_iff_mem_nhds.mp hu))
      obtain ⟨x,hx,hR⟩:= (he.and (show ∀ᶠ x in 𝓝[>] (0:ℝ),0<x from self_mem_nhdsWithin)).exists
      refine ⟨b.coord i (f x),?_,hs _ hx _⟩
      have ht : b.coord i (f x)=x := by rw [show f x=_ from rfl,_root_.map_add,hz]; simp
      rw [ht]; exact hR.ne'
    exact ⟨_, hz, hs u (interior_subset hu) i⟩
  choose c hc hcb using h'
  let w := fun i=> Units.mk0 (c i) (hc i)
  let d := b.unitsSMul w
  have he (i): d i=c i • b i := Basis.unitsSMul_apply i
  have hd (i): d i∈C := he i ▸ hcb i
  have hp (x:Rn m) (hx:x∈C) (i:Fin m): d.coord i x • d i ∈ C := by
    have heq : d.coord i x • d i=b.coord i x • b i := by
      rw [he]
      change d.repr x i • _= b.repr x i • b i
      rw [Basis.repr_unitsSMul]
      change ((c i)⁻¹*b.repr x i) • (c i • b i)=_
      rw [smul_smul,mul_comm _ (c i),← mul_assoc,mul_inv_cancel₀ (hc _),one_mul]
    rw [heq]; exact hs x hx i
  obtain ⟨a,ha,hav⟩:= interior_dual_bound hv
  have hv (i) : 0<⟪v,d i⟫ := lt_of_lt_of_le
    (mul_pos ha (norm_pos_iff.mpr (d.ne_zero i))) (hav _ (hd i))
  refine ⟨d,?_⟩
  ext x; rw [mem_orthant]; constructor
  · intro h i
    have hp := hp x h i
    have ht := hav _ hp; rw [real_inner_smul_right] at ht
    have hi := hv i
    change 0 ≤ d.coord i x; nlinarith [norm_nonneg (d.coord i x • d i)]
  intro h
  have ha (s:Finset (Fin m)) : ∑ i∈s,d.repr x i • d i ∈ C := by
    induction s using Finset.induction_on with
    | empty=> rw [Finset.sum_empty]; exact C.zero_mem
    | @insert i s hi hr =>
      rw [Finset.sum_insert hi]; exact C.add_mem (C.smul_mem (hd i) (h i)) hr
  simpa only [d.sum_repr] using ha Finset.univ

namespace ProjField
variable [NeZero m]

theorem C_bound_oai (q:ProjField m) (T:Mat m) (h:Balanced q T) (hc:UpdatesOK Cp Kp)
    (hh:LayerOK) (hi:SegmentOK):
    1 ≤ chi q.C q.V*chi q.D q.U ∧ (chi q.C q.V*chi q.D q.U=1 →
      IsLinearOrthant m q.C) := by
  obtain ⟨h,h'⟩:= q.Bound_pt T h hc hh hi; refine ⟨h,?_⟩
  intro hz
  obtain ⟨_,h₁,h₂⟩ := h' hz
  have he (i j:Fin m): cmu (q.M i) (q.M j)=0 := q.nu_comm hh hi h₁ j i
  obtain ⟨b,hb⟩:= q.projD he (q.B_layer hh h₂)
  exact cone_axes _ q.U_in q.V_in b hb
end ProjField
end GeneralMahler

end

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.ProjField.C_bound_oai := @OAI.GeneralMahler.ProjField.C_bound_oai

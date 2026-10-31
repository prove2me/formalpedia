-- Prove2me | solution 1 for OAI.GeneralMahler.ProjField.entropy_decomp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:41:32.170848+00:00
-- url     : https://prove2.me/submissions/1b7ecc93-7449-4836-be47-c7ef984b1245

import Mathlib
import Definitions.Def_GeneralMahler
import Definitions.Def_OAIQ026G002

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

namespace mixed
variable {f g : X → Y → E}

lemma poly (hf : mixed f) : PolyBound f.uncurry := by
  obtain ⟨C,k,hc,h⟩ := hf 0
  simp only [pow_zero,mul_one] at h
  refine ⟨C,k,hc,?_⟩
  rintro ⟨x,y⟩
  apply (h x y).trans
  gcongr; exact le_max_right ..

end mixed

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MixedField
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer integrals and error estimates. -/
noncomputable section
open Filter Set Real Matrix MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
open Layers
variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)

lemma meas_XT : Continuous (q.XT.uncurry) := by
  unfold XT sample affineN Function.uncurry
  exact (coneProj_lip q.C).continuous.comp
    ((q.root.continuous.comp continuous_snd).add (q.shift_cd.continuous.comp continuous_fst))

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LayerMeasure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02 scalar measure from the derivative of avH. Real densities here. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology ENNReal
namespace GeneralMahler

open Layers
variable {m : ℕ} [NeZero m]
namespace ProjField
variable (q : ProjField m)

lemma H_infty : Tendsto q.avH atTop (𝓝 q.s0) := by
  have he := (q.tail_H.tail_limit).add_const q.s0
  rw [zero_add] at he
  apply Tendsto.congr' _ he
  filter_upwards [Ioi_mem_atTop (0:ℝ)] with x hx

  simp [st,(le_of_lt (show 0<x from hx))]

lemma H_bot : Tendsto q.avH atBot (𝓝 0) := by
  have h : rapid (fun x : ℝ => q.avH (-x)-st (-x)*q.s0) := by
    intro n
    obtain ⟨C,hc,h⟩ := q.tail_H n
    exact ⟨C,hc,fun x => by simpa only [norm_neg] using h (-x)⟩
  have he : Tendsto (fun x:ℝ => q.avH (-x)) atTop (𝓝 0) := by
    apply Tendsto.congr' _ h.tail_limit
    filter_upwards [Ioi_mem_atTop (0:ℝ)] with x hx

    simp [st,show ¬0 ≤ -x by have ha : 0 < x := hx; linarith]
  simpa [Function.comp_def] using he.comp tendsto_neg_atBot_atTop

theorem integrable_w : Integrable q.layerW := by simpa using q.w_moment 0
theorem integral_w : ∫ x, q.layerW x = q.s0 := by
  simpa using integral_of_hasDerivAt_of_tendsto q.H_deriv q.integrable_w q.H_bot q.H_infty

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Mills
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma c_mc : Continuous MillsC := continuous_iff_continuousAt.mpr fun x => (d_mc x).continuousAt
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

lemma mc_lip : LipschitzWith 1 MillsC := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact fun x=> (d_mc x).differentiableAt
  intro x
  rw [(d_mc x).deriv,nnnorm_neg]

  apply NNReal.coe_le_coe.mp
  simpa [Real.norm_of_nonneg (mw_pos x).le] using mw_le x
lemma poly_mc : PolyBound MillsC := PolyBound.lipschitz mc_lip
lemma poly_mj : PolyBound MillsJ := PolyBound.id.add poly_mc
end Layers
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MillsLog
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
lemma d_lp (x:ℝ) : HasDerivAt LP (MillsC x) x :=
  (d_p x).log (p_pos x).ne'
lemma poly_lp : PolyBound LP := poly_of_d d_lp poly_mc

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
lemma d_test : TestF d := fun n=>(moderate_dg n).2.2
end GeneralMahler.Profile

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Spectral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
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

variable {l r : ℝ}

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
lemma trN_add (A B:Mat m) : trN (A+B)=trN A+trN B := by unfold trN; rw [trace_add,add_div]
lemma trN_sub (A B:Mat m) : trN (A-B)=trN A-trN B := by unfold trN; rw [trace_sub,sub_div]
lemma trN_smul (a:ℝ) (A:Mat m) : trN (a•A)=a*trN A := by
  unfold trN; rw [trace_smul]; simp; ring
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scatter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
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
lemma yp : PolyBound q.y.uncurry := by
  change PolyBound (fun x:ℝ × Rn m=> coneProj q.cone (op q.B x.2 + q.d x.1))
  exact (PolyBound.lipschitz (coneProj_lip q.cone)).comp
    (((PolyBound.clm (op q.B)).comp PolyBound.snd).add (q.dp.comp PolyBound.fst))

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

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Entropy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
lemma inc_at (a:MI m) (i) : inc a i i=a i+1 := Function.update_self ..

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_L2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar coefficient calculus. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ} [NeZero m]
omit [NeZero m] in
lemma qcf_ip' (f:G2 m) (a) : qcf f a=⟪f,ModL a⟫ := (qcf_ip ..).trans (real_inner_comm ..)

lemma qcf_sum {f g:Rn m→ℝ} (hf:MemLp f 2 (normal m)) (hg:MemLp g 2 (normal m)) :
    HasSum (fun a=> qcf f a*qcf g a) (∫ x,f x*g x ∂normal m) := by
  let F := hf.toLp f
  let G := hg.toLp g
  have hF : F=ᵐ[normal m] f := MemLp.coeFn_toLp ..
  have hG : G=ᵐ[normal m] g := MemLp.coeFn_toLp ..
  have hi (a) := qcf_congr hF a
  have hh (a) := qcf_congr hG a
  have hv := (HB m).hasSum_inner_mul_inner F G
  simp_rw [HB_eq,← qcf_ip', ← qcf_ip,hi,hh] at hv
  have he : ⟪F,G⟫ = ∫ x,f x*g x ∂normal m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF,hG] with x hx hy
    rw [hx,hy]
    exact mul_comm ..
  rwa [he] at hv
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
omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
lemma lip {f:Rn m→F} {K:ℝ≥0} (hk:LipschitzWith K f) : PLip f := by
  use fun _=> (K:ℝ)
  refine ⟨PolyBound.const _,continuous_const,fun x b _ =>?_⟩
  simpa only [dist_eq_norm, add_sub_cancel_left] using hk.dist_le_mul (x+b) x
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
lemma qcf_cof (f:Rn m→ℝ) (a) : qcf f a=cof f a := by
  unfold qcf cof; congr 1; ext x; exact mul_comm ..
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
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
omit [NeZero m] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
lemma add {g:Rn m→F} (hf:regular f) (hg:regular g) : regular fun x=>f x+g x :=
  ⟨hf.p.add hg.p,hf.meas.add hg.meas⟩
omit [NeZero m] [FiniteDimensional ℝ F] in
lemma smul (hf:regular f) {g:Rn m→ℝ} (hg:regular g) : regular fun x=>g x • f x :=
  ⟨hg.p.smul hf.p,hg.meas.smul hf.meas⟩
omit [NeZero m] in
lemma mul {f g:Rn m→ℝ} (hf:regular f) (hg:regular g) : regular fun x=>f x*g x := hg.smul hf
end regular

variable {f:Rn m→E} {g:Rn m→F}
omit [NeZero m] in
lemma cof_clm (hf:regular f) (l:E→L[ℝ]F) (a:MI m) : l (cof f a)=cof (fun x=>l (f x)) a := by
  unfold cof
  rw [← l.integral_comp_comm (i_cof hf.p hf.meas a)]
  simp only [map_smul]
lemma cof_form (hf:regular f) (hg:regular g) (l:E→L[ℝ]ℝ) (k:F→L[ℝ]ℝ) :
    HasSum (fun a=> l (cof f a)*k (cof g a))
      (∫ x,l (f x)*k (g x) ∂normal m) := by
  have hi := hf.lin l
  have hh := hg.lin k
  simp_rw [cof_clm hf,cof_clm hg,← qcf_cof]
  exact qcf_sum (lp_poly hi.p hi.meas) (lp_poly hh.p hh.meas)

-- Function of a bilinear form, prove via finite-dimensional basis projections
lemma cof_bil (hf:regular f) (hg:regular g) (l:E→L[ℝ]F→L[ℝ]ℝ) :
    HasSum (fun a=>l (cof f a) (cof g a)) (∫ x,l (f x) (g x) ∂normal m) := by
  let b := Module.finBasis ℝ E
  let c := fun i=> (b.coord i).toContinuousLinearMap
  have he (x:E) (y:F) : l x y= ∑ i,c i x*l (b i) y := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [_root_.map_sum,_root_.sum_apply,_root_.map_smul,_root_.smul_apply,smul_eq_mul]
    rfl
  have h (i) := cof_form hf hg (c i) (l (b i))
  rw [show (fun x=> l (f x) (g x))=_ from funext (fun x=> he (f x) (g x)), show (fun a=> l (cof f a) (cof g a))=_ from funext (fun x=> he (cof f x) (cof g x))]
  rw [integral_finsetSum]
  · exact hasSum_sum fun i _=> h i
  exact fun i _=> ((hf.lin (c i)).mul (hg.lin (l (b i)))).ig

lemma cof_vec (f g:Rn m→Rn m) (hf:regular f) (hg:regular g) :
    HasSum (fun a=>⟪cof f a,cof g a⟫) (∫ x,⟪f x,g x⟫ ∂normal m) :=
  cof_bil hf hg (innerSL ℝ)

omit [NeZero m] in
lemma deg_inc (a:MI m) (i) : deg (inc a i)=deg a+1 := by
  simp only [deg,inc]
  classical
  simp only [← Finset.sum_erase_add _ _ (Finset.mem_univ i),Function.update_self]
  have hi : (∑ k∈Finset.univ.erase i,Function.update a i (a i+1) k) =
      ∑ k∈Finset.univ.erase i,a k := Finset.sum_congr rfl fun k hk=> Function.update_of_ne
        (Finset.ne_of_mem_erase hk) ..
  rw [hi]; omega
omit [NeZero m] in
lemma dz (a:MI m) : deg a=0 ↔ a=0 := by
  unfold deg; simp [Finset.sum_eq_zero_iff,funext_iff]

omit [NeZero m] in
lemma inc_sum (i:Fin m) (a:MI m→ℝ) (he:∀ x:MI m,x i=0→a x=0) :
    (Summable a ↔ Summable fun x=>a (inc x i)) ∧
    (∑' x,a x)=∑' x,a (inc x i) := by
  classical
  have h : Function.support a⊆userS i := fun x hx hs=> hx (he x hs)
  -- reindex via embedding
  have hi (t:ℝ) : HasSum a t ↔ HasSum (fun x=>a (inc x i)) t := by
    let l := incE i
    have he : (fun x=> a (inc x i))=(fun x:userS i=> a x.val) ∘ l := rfl
    rw [he,l.hasSum_iff]
    exact (hasSum_subtype_iff_of_support_subset h).symm
  have he' : Summable a ↔ Summable fun x=>a (inc x i) := exists_congr hi
  refine ⟨he',?_⟩
  by_cases hs:Summable a
  · exact (HasSum.tsum_eq ((hi _).mp hs.hasSum)).symm
  rw [tsum_eq_zero_of_not_summable hs,tsum_eq_zero_of_not_summable (he'.not.mp hs)]

omit [NeZero m] in
lemma iDeg (a:MI m) (i) : a i ≤ deg a :=
  Finset.single_le_sum (fun k _=> Nat.zero_le (a k)) (Finset.mem_univ i)

omit [NeZero m] in
lemma sum_spectral (C:MI m→ℝ) (hh:C 0=0) (hs:Summable C) :
    ∑' a,C a = ∑ i:Fin m,∑' a, C (inc a i)*((a i+1:ℕ):ℝ)/(1+deg a) := by
  let f (i:Fin m) (a:MI m) := (C a*((a i:ℕ):ℝ))/(deg a:ℝ)
  have hf (a:MI m) : C a=∑ i,f i a := by
    unfold f; rw [← Finset.sum_div,← Finset.mul_sum,show (∑ i:Fin m,(a i:ℝ)) = (deg a:ℝ)
      from by simp [deg]]
    rcases eq_or_ne (deg a) 0 with h|h
    · rw [h, Nat.cast_zero,div_zero]; exact dz a |>.mp h ▸ hh
    have hp : (deg a:ℝ)≠0 := by exact_mod_cast h
    field_simp
  have hi (i:Fin m) : Summable (f i) := by
    apply Summable.of_norm_bounded hs.norm
    intro a
    unfold f; rw [norm_div,norm_mul]; norm_cast
    have hv := iDeg a i
    by_cases hj:deg a=0
    · simp [hj]
    have hp : 0 < (deg a:ℝ) := by positivity
    rw [div_le_iff₀ hp]
    gcongr
  have he (i:Fin m) := inc_sum i (f i) (fun x hx=>by simp [f,hx])
  calc
    _ = ∑' a,∑ i,f i a := tsum_congr hf
    _ = ∑ i,∑' a,f i a := Summable.tsum_finsetSum (fun i _=>hi i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(he i).2]
      apply tsum_congr; intro a; unfold f; rw [inc_at,deg_inc]; push_cast; ring
end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_GradientLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! The centered fields W_f from §02,04. We use coefficient
derivatives (Hermite) as justified by differentiation by parts:
rather than interchanging weak derivatives, integrate the coefficient
identity using the layer cutoff bounds. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
lemma XPbound : PolyBound q.XT.uncurry := by
  have h := q.primalMap.yp
  simp_rw [show q.primalMap.y=q.XT from funext q.X_sc] at h; exact h
lemma YPbound : PolyBound q.YT.uncurry := by
  change PolyBound (fun u:ℝ×Rn m=>coneProj q.D (-(q.Z u.2+q.shift u.1)))
  have hp : PolyBound (fun u:ℝ×Rn m=> -(q.Z u.2+q.shift u.1)) :=
    (((PolyBound.clm q.root.toContinuousLinearMap).comp PolyBound.snd).add
      (q.s_poly.comp PolyBound.fst)).neg
  exact (PolyBound.lipschitz (coneProj_lip q.D)).comp hp

lemma XbM : mixed q.Xb := by
  let v := q.primalMap
  apply mixed.of_cutoff (show PolyBound q.Xb.uncurry from
    (((PolyBound.const (1:ℝ)).sub poly_st).comp PolyBound.fst).smul q.XPbound)
    (show PolyBound (fun x:Rn m=> v.M*(1+‖x‖)) from
      (PolyBound.const _).mul ((PolyBound.const _).add PolyBound.id.norm))
  intro z x hx
  unfold Xb st; split_ifs with h
  · simp
  rw [Real.norm_eq_abs,abs_of_neg (lt_of_not_ge h)] at hx
  have hi := v.zero_y z x hx
  rw [show v.y z= _ from q.X_sc _] at hi
  simp only [hi,smul_zero]
lemma YbM : mixed q.Yb := by
  let v := q.dualMap
  apply mixed.of_cutoff (show PolyBound q.Yb.uncurry from
    (poly_st.comp PolyBound.fst).smul q.YPbound)
    (show PolyBound (fun x:Rn m=> v.M*(1+‖x‖)) from
      (PolyBound.const _).mul ((PolyBound.const _).add PolyBound.id.norm))
  intro z x hx
  unfold Yb st; split_ifs with h
  · rw [Real.norm_of_nonneg h] at hx
    have hi := v.zero_y (-z) x (by simpa using hx)
    rw [show v.y (-z)= _ from q.Y_sc _,neg_neg] at hi
    simp only [hi,smul_zero]
  simp

omit [NeZero m] in
lemma WW_mean (z:ℝ) : (∫ x,q.WW z x ∂normal m)=0 := by
  have he : Integrable q.Z (normal m) := by
    have hZ : PolyBound q.Z := PolyBound.clm q.root.toContinuousLinearMap
    exact hZ.gaussian_integrable q.root.continuous.aestronglyMeasurable
  unfold WW
  have hi : Integrable (fun x=> p z • q.Z x) (normal m) := he.smul (p z)
  rw [integral_add,integral_sub hi (q.X_int z), q.XT_mean, integral_smul]
  · have he : (∫ x,q.Z x ∂normal m)=0 := by
      have h := affineN_mean q.root 0
      simpa only [affineN,Z,add_zero] using h
    rw [he]; simp
  · exact hi.sub (q.X_int z)
  exact integrable_const _

omit [NeZero m] in
lemma WW_eq (z x) :
    q.WW z x=(p z-st z) • q.Z x-q.Xb z x -q.Yb z x+
      (∫ y,q.Xb z y ∂normal m)+(∫ y,q.Yb z y ∂normal m) := by
  unfold WW Xb Yb
  rw [integral_smul,integral_smul,q.XT_mean,q.Y_mean,q.YT_sub]
  module
lemma WW_m : mixed q.WW := by
  let f := fun z x=> (p z-st z) • q.Z x
  have hp : PolyBound q.Z := PolyBound.clm q.root.toContinuousLinearMap
  have hf : mixed f := (mixed.of_rapid (Y:=Rn m) rapid_p).product (g:=fun _ x=>q.Z x)
    (show PolyBound (fun u:ℝ×Rn m=> q.Z u.2) from hp.comp PolyBound.snd) (fun x y=>by rw [show f x y= _ from rfl,norm_smul])
  have hx := mixed_integral_right q.XbM fun z=> (show Integrable (q.Xb z) (normal m)
    from (q.X_int z).smul (1-st z)).aestronglyMeasurable
  have hy := mixed_integral_right q.YbM fun z=> (show Integrable (q.Yb z) (normal m)
    from (q.Y_int z).smul (st z)).aestronglyMeasurable
  rw [show q.WW= _ from funext fun z=>funext fun x=>q.WW_eq z x]
  exact (((hf.sub q.XbM).sub q.YbM).add (mixed.of_rapid hx)).add (mixed.of_rapid hy)

omit [NeZero m] in
lemma WW_c : Continuous q.WW.uncurry :=
  (((cp.comp continuous_fst).smul (q.root.continuous.comp continuous_snd)).sub q.meas_XT).add
    ((ca.comp continuous_fst).smul continuous_const)

omit [NeZero m] in
lemma WK_SM (f) : StronglyMeasurable (q.WK f).uncurry :=
  (((measurable_deriv f).comp measurable_fst).stronglyMeasurable).smul q.WW_c.stronglyMeasurable
lemma WK_m {f} (hf:TestF f) : mixed (q.WK f) := by
  let g := fun (z:ℝ) (_:Rn m)=> deriv f z
  apply q.WW_m.product (show PolyBound g.uncurry from hf.der.poly.comp PolyBound.fst)
  intro z x
  unfold WK g; rw [norm_smul,mul_comm]
lemma WH_reg {f} (hf:TestF f) : regular (q.WH f) :=
  ⟨poly_integral_left (q.WK_m hf) (fun _x=> (((q.WK_SM f).comp_measurable
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable)),
    (q.WK_SM f).integral_prod_left.aestronglyMeasurable⟩
lemma WH_mean {f} (hf:TestF f) : (∫ x,q.WH f x ∂normal m)=0 := by
  unfold WH
  rw [integral_integral_swap]
  · unfold WK; simp_rw [integral_smul,q.WW_mean]; simp
  exact (mixed_integrable (μ:=volume) (ν:=normal m) (q.WK_m hf)
    (q.WK_SM f).aestronglyMeasurable).swap

omit [NeZero m] in
lemma WWd (z:ℝ) :
    ∀ᵐ x∂normal m, HasFDerivAt (q.WW z)
      ((op (q.PD z x)).comp (op q.S)) x := by
    filter_upwards [q.XT_diff z] with x hx
    have hf := ((((q.root.hasFDerivAt).const_smul (p z)).sub hx).add_const (Layers.a z • q.U))
    have hl : (op (q.PD z x)).comp (op q.S)=p z•q.root.toContinuousLinearMap - (op (q.Pmat z x)).comp (op q.S) := by
      unfold PD
      rw [q.matrix_eq]
      change op (p z • 1 - _)*op q.S=p z•op q.S-op (q.Pmat z x)*op q.S
      rw [← _root_.map_mul,sub_mul,smul_mul_assoc,one_mul,_root_.map_sub,_root_.map_smul,_root_.map_mul]
    rw [hl]; exact hf
omit [NeZero m] in
lemma WW_lip (z:ℝ) : ∃ K,LipschitzWith K (q.WW z) := by
    obtain ⟨K,hk⟩ := q.XT_lipschitz z
    exact ⟨_, (((p z • q.root.toContinuousLinearMap).lipschitz).sub hk).add (LipschitzWith.const _)⟩
lemma WDer_p (z:ℝ) (i:Fin m) :
    PolyBound (fun x=> q.act i (q.PD z x)) := by
  have hh : PolyBound (q.PD z) :=
    (q.mixed_PD.poly).comp (f:=(fun x=>(z,x))) ((PolyBound.const z).prodMk PolyBound.id)
  exact (PolyBound.clm (q.act i)).comp hh
lemma WW_recur (z:ℝ) (i:Fin m) (a:MI m) :
    cof (fun x=> q.act i (q.PD z x)) a=sn (a i+1) • cof (q.WW z) (inc a i) := by
  obtain ⟨K,hk⟩ := q.WW_lip z
  let D := fun x=> (op (q.PD z x)).comp (op q.S)
  have hm : AEStronglyMeasurable (fun x=>q.act i (q.PD z x)) (normal m) :=
    ((q.act i).continuous.comp_stronglyMeasurable (q.PD_sm.comp_measurable
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have ht : (fun x=>D x (HMode.e i))=(fun x=>q.act i (q.PD z x)) := by funext x; rfl
  have hi := coef_raise (PolyBound.lipschitz hk) (PLip.lip hk) hk.continuous (D:=D) (q.WWd z) i
    (ht.symm ▸ q.WDer_p z i) (ht.symm ▸ hm) a
  rw [ht] at hi; exact hi

-- Linear coefficient interchange with layer integral, natural powers
omit [NeZero m] in
lemma cof_layer {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f:ℝ→Rn m→F} (hf:mixed f) (hm:StronglyMeasurable f.uncurry) (a:MI m) :
    cof (fun x=>∫ z,f z x) a=∫ z,cof (f z) a := by
  let g := fun z x=> MM a x • f z x
  have hh : StronglyMeasurable g.uncurry :=
    ((M_cont a).stronglyMeasurable.comp_measurable measurable_snd).smul hm
  have hg : mixed g := hf.product (g:=fun _ x=>MM a x)
    (show PolyBound (fun u:ℝ × Rn m=>MM a u.2) from (M_poly a).comp PolyBound.snd)
    (fun z x=>by unfold g; rw [norm_smul,mul_comm])
  unfold cof; simp_rw [← integral_smul]
  exact integral_integral_swap (mixed_integrable (μ:=volume) (ν:=normal m) hg hh.aestronglyMeasurable).swap

lemma WH_rec {f} (hf:TestF f) (i:Fin m) (a:MI m) :
    q.act i (cof (q.Hmat f) a)=sn (a i+1) • cof (q.WH f) (inc a i) := by
  let g := fun z x=> q.act i (q.kerH f z x)
  have hh (x) : q.act i (q.Hmat f x)=∫ z,g z x := ( (q.act i).integral_comp_comm
    (q.H_left_int hf.der.poly _)).symm
  have he : mixed g := (q.H_mixed hf.der.poly).product (g:=fun _ _=>‖q.act i‖)
    (show PolyBound (fun _:ℝ × Rn m=>‖q.act i‖) from PolyBound.const _)
    (fun z x=>by unfold g; rw [Real.norm_of_nonneg (norm_nonneg (q.act i)),mul_comm]; apply ContinuousLinearMap.le_opNorm)
  have hi (z) : cof (g z) a=sn (a i+1) • cof (q.WK f z) (inc a i) := by
    have h := q.WW_recur z i a
    have hf (v:Rn m→Rn m) (a:MI m) : cof (fun x=> deriv f z • v x) a=deriv f z • cof v a := by
      unfold cof; rw [← integral_smul]; congr 1; ext; rw [smul_comm]
    unfold WK g kerH; simp_rw [_root_.map_smul]
    rw [hf,hf,h,smul_comm]
  have hm : regular (q.Hmat f) := ⟨q.H_poly hf.der.poly,q.H_SM.aestronglyMeasurable⟩
  rw [cof_clm hm]
  simp_rw [hh]
  rw [cof_layer he (((q.act i).continuous).comp_stronglyMeasurable q.H_sm)]
  simp_rw [hi, integral_smul]
  rw [show cof (q.WH f) _=_ from cof_layer (q.WK_m hf) (q.WK_SM _) (inc a i)]
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_CovHerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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

lemma pt_sum {B:Mat m} {A C:Rn m→Mat m} (ha:regular A) (hc:regular C) :
    HasSum (CpPair B A C) (Pt B A C) := by
  have hi := cof_bil ha hc (PJ B)
  simp_rw [pJ_eq] at hi; exact hi

omit [NeZero m] in
lemma summable_k {f:MI m→ℝ} (hf:Summable f) :
    Summable (fun a=> f a*kMode a) := by
  apply Summable.of_norm_bounded hf.norm
  intro a
  have he : 0 ≤ (deg a:ℝ) := by exact_mod_cast Nat.zero_le _
  have hc : 0 < 1+(deg a:ℝ) := by linarith
  unfold kMode
  rw [norm_mul,Real.norm_of_nonneg (inv_pos.mpr hc).le]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [← one_div,div_le_iff₀ hc]; linarith

lemma K_sum {B:Mat m} {A C:Rn m→Mat m} (ha:regular A) (hc:regular C) :
    Summable (fun a=> CpPair B A C a*kMode a) := summable_k (pt_sum ha hc).summable

namespace ProjField
variable (q:ProjField m)
lemma regH {f:ℝ→ℝ} (hf:TestF f) : regular (q.Hmat f) :=
  ⟨q.H_poly hf.der.poly,q.H_SM.aestronglyMeasurable⟩
lemma cfH_sym {f} (hf:TestF f) (a:MI m) :
    (cof (q.Hmat f) a).IsHermitian :=
  hermitian_integral (i_cof (q.H_poly hf.der.poly) q.H_SM.aestronglyMeasurable a)
    (ae_of_all _ fun x=> (q.H_hermitian hf.der.poly _).smul (by simp [IsSelfAdjoint]))
lemma pj_sum {A C:Mat m} (hA:A.IsHermitian) (hC:C.IsHermitian) :
    (∑ i,⟪q.act i A,q.act i C⟫)=(m:ℝ)*Pj q.covMat A C := by
  let s := q.S
  have he (A C:Mat m) (ha:A.IsHermitian) :
      trace (q.covMat*(A*C))=∑ i,⟪q.act i A,q.act i C⟫ := by
    rw [q.trace_SPS]
    apply Finset.sum_congr rfl; intro i _
    rw [_root_.map_mul]
    change ⟪op s (e i),op A (op C (op s (e i)))⟫ = _
    rw [← op_iff_hermitian.mp ha]; rfl
  unfold Pj jprod trN
  rw [mul_smul_comm,mul_add,trace_smul,trace_add,he _ _ hA, he _ _ hC]
  have hp : (∑ i,⟪q.act i C,q.act i A⟫)=(∑ i,⟪q.act i A,q.act i C⟫) :=
    Finset.sum_congr rfl fun i _=> real_inner_comm ..
  rw [hp,smul_eq_mul]
  have h:= m_pos (m:=m)
  field_simp; ring

lemma pt_k_cov {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    (∫ x,⟪q.WH f x,q.WH g x⟫ ∂normal m)/(m:ℝ) =
      KP q.covMat (q.Hmat f) (q.Hmat g) := by
  let S : MI m→ℝ := fun a=> ⟪cof (q.WH f) a,cof (q.WH g) a⟫
  let A := q.Hmat f
  let B := q.Hmat g
  let aR := fun i a=> q.act i (cof A a)
  let bR := fun i a=> q.act i (cof B a)
  let I := fun (i:Fin m) (a:MI m)=> ⟪aR i a,bR i a⟫*kMode a
  have hu (a:MI m) (i:Fin m) :
      S (inc a i)*((a i+1:ℕ):ℝ)/(1+deg a)=I i a := by
    have hf' : aR i a= _ := q.WH_rec hf i a
    have hg' : bR i a= _ := q.WH_rec hg i a
    unfold I; rw [hf',hg',real_inner_smul_left,real_inner_smul_right,← mul_assoc,← pow_two,snsq]
    unfold S kMode; ring
  have hp : HasSum S (∫ x,⟪q.WH f x,q.WH g x⟫ ∂normal m) :=
    cof_vec _ _ (q.WH_reg hf) (q.WH_reg hg)
  have hZ : S 0=0 := by
    unfold S cof
    simp [MM,H,q.WH_mean hf]
  have h := sum_spectral S hZ hp.summable
  simp_rw [hu] at h
  have hi (i:Fin m) : Summable (I i) := by
    have ha := q.regH hf
    have hb := q.regH hg
    have hh := (cof_vec (fun x=>q.act i (A x)) (fun x=>q.act i (B x)) (ha.lin _) (hb.lin _)).summable
    apply summable_k
    unfold aR bR A B
    simp_rw [cof_clm ha,cof_clm hb]
    exact hh
  have heq (a) : ∑ i,I i a=(m:ℝ)*(CpPair q.covMat A B a*kMode a) := by
    unfold I aR bR CpPair
    rw [← Finset.sum_mul,q.pj_sum (q.cfH_sym hf _) (q.cfH_sym hg _),mul_assoc]
  rw [← Summable.tsum_finsetSum fun i _=>hi i] at h
  simp_rw [heq] at h; rw [tsum_mul_left] at h
  rw [← hp.tsum_eq,h]
  change _/(m:ℝ)=∑' a,CpPair q.covMat A B a*kMode a
  have hx:=m_pos (m:=m); field_simp

end ProjField
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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Kernel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Kernel integrations for §04. Plane is Euclidean pair (with product
volume), split along diagonal. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile

lemma Rlo_m : MeasurableSet Rlo := (isOpen_lt continuous_fst continuous_snd).measurableSet
lemma upper2 (f:Plane→ℝ) (hf:IntegrableOn f Rlo) :
    (∫ u in Rlo,f u)=∫ b:ℝ,∫ a in Iio b,f (a,b) := by
  classical
  let g := Rlo.indicator f
  have hi : Integrable g := (integrable_indicator_iff Rlo_m).mpr hf
  rw [← integral_indicator Rlo_m,show volume=volume.prod volume from rfl, integral_prod_symm _ hi]
  congr 1; ext; rw [← integral_indicator measurableSet_Iio]; rfl
lemma off_diag : ∀ᵐ u:Plane,u.1≠u.2 := by
  apply (ae_prod_iff_ae_ae (((isClosed_eq continuous_fst continuous_snd).measurableSet.compl))).mpr
  filter_upwards with x
  rw [ae_iff]; simp []
lemma split_plane (f:Plane→ℝ) (hf:Integrable f) :
    (∫ u,f u) = (∫ u in Rlo,f u)+(∫ u in Rlo,f u.swap) := by
  classical
  rw [← integral_add_compl Rlo_m hf]
  congr 1
  rw [← integral_indicator Rlo_m.compl,← integral_indicator Rlo_m]
  let g := Rloᶜ.indicator f
  have he : (∫ u,g u)=(∫ u:Plane,g u.swap) :=
    (integral_prod_swap (μ:=volume) (ν:=volume) g).symm
  change (∫ u,g u)=_
  rw [he]
  apply integral_congr_ae
  filter_upwards [off_diag] with u hu
  rcases lt_or_gt_of_ne hu with h|h
  · have hh:u∈Rlo := h
    have h':u.swap∈Rloᶜ := not_lt_of_ge h.le
    unfold g; rw [indicator_of_mem h',indicator_of_mem hh]
  have hh : u∉Rlo := not_lt_of_ge h.le
  have h': u.swap∉Rloᶜ := fun he=> he (show u.swap∈Rlo from h)
  unfold g; rw [indicator_of_notMem h',indicator_of_notMem hh]

lemma real_slice (K:Plane→ℝ) (hK:Measurable K) (hp:∀ u,0≤K u) (hm:ℝ→ℝ)
    (hi:∀ x:ℝ, Integrable fun y=>K (x,y)) (he:∀ x, (∫ y,K (x,y))=hm x)
    (hh:MomentF hm) (n:ℕ) :
    Integrable fun u:Plane=> K u*(1+‖u.1‖)^n := by
  let f := fun u:Plane=> K u*(1+‖u.1‖)^n
  have hf : Measurable f := hK.mul (by fun_prop)
  apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ fun x=> (hi x).mul_const ((1+‖x‖)^n),?_⟩
  have hv (x y:ℝ) : ‖f (x,y)‖=K (x,y)*(1+‖x‖)^n :=
    Real.norm_of_nonneg (mul_nonneg (hp _) (by positivity))
  simp_rw [hv,integral_mul_const,he]
  exact hh _ (by fun_prop) (((PolyBound.const _).add PolyBound.id.norm).pow _)

lemma pairMoment (K:Plane→ℝ) (hK:Measurable K) (hp:∀ u,0≤K u) (hm:ℝ→ℝ)
    (hi:∀ x:ℝ, Integrable fun y=>K (x,y)) (he:∀ x, (∫ y,K (x,y))=hm x)
    (hh:MomentF hm) (hs:∀ u:Plane,K u.swap=K u)
    {f:Plane→ℝ} (hf:PolyBound f) (hf':Measurable f) :
    Integrable fun u=>K u*f u := by
  obtain ⟨C,n,hc,h⟩ := hf
  let g := fun u:Plane=> K u*(1+‖u.1‖)^n
  have hg : Integrable g := real_slice K hK hp hm hi he hh n
  let G := fun u:Plane=> C*(g u+g u.swap)
  have hi : Integrable G := (hg.add hg.swap).const_mul _
  apply hi.mono' (hK.mul hf').aestronglyMeasurable (ae_of_all _ ?_)
  intro u; change ‖K u*f u‖≤_
  rw [norm_mul,Real.norm_of_nonneg (hp _)]
  apply le_trans (mul_le_mul_of_nonneg_left (h u) (hp _))
  change _ ≤ C*(K u*(1+‖u.1‖)^n+K u.swap*(1+‖u.2‖)^n)
  rw [hs]
  have h₁ : ‖u‖ = max ‖u.1‖ ‖u.2‖ := rfl
  rw [h₁]
  rcases max_choice ‖u.1‖ ‖u.2‖ with h|h <;> rw [h] <;> rw [← sub_nonneg] <;>
    ring_nf <;> have he := hp u <;> positivity

namespace rightLayer
variable (q:rightLayer)

lemma p_slice (x:ℝ) : IntegrableOn p (Iic x) ∧ (∫ y in Iic x,p y) = a x := by
  have he : IntegrableOn p (Iic x) := by
    -- comparison used in §02
    obtain ⟨C,hc,h⟩ := p_small
    let c := max x (0:ℝ)
    have hu : IntegrableOn p (Iic 0) := by
      refine ((i_phi.mul_const C).integrableOn).mono'
        cp.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
      have he := h (-y) (neg_nonneg.mpr (mem_Iic.mp hy))
      simpa only [Real.norm_of_nonneg (p_pos _).le,neg_neg,neg_phi] using he
    exact (hu.union (cp.integrableOn_Icc (a:=0) (b:=c))).mono_set (fun z hz=>by
      by_cases h:z≤0
      · exact Or.inl h
      exact Or.inr ⟨le_of_lt (lt_of_not_ge h),(mem_Iic.mp hz).trans (le_max_left ..)⟩)
  exact ⟨he,by simpa using integral_Iic_of_hasDerivAt_of_tendsto' (fun y _=>d_a y) he abot'⟩
lemma r_slice (x:ℝ) : IntegrableOn q.r (Ioi x) ∧ (∫ y in Ioi x,q.r y)=q.B x := by
  have h : Tendsto q.B atTop (𝓝 0) := by
    apply Tendsto.congr' _ q.hb.tail_limit
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx; simp [st,hx]
  have hh (x:ℝ) : HasDerivAt (fun x=> -q.B x) (q.r x) x := by
    convert (q.drB x).neg using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | simp
  have hi : Tendsto (fun x=> -q.B x) atTop (𝓝 0) := by simpa using h.neg
  have he := integrableOn_Ioi_deriv_of_nonneg' (fun y _=>hh y) (a:=x) (fun y _=>q.hr y) hi
  exact ⟨he,by simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (fun y _=>hh y) he hi⟩
lemma marg (x:ℝ) :
    Integrable (fun y=>q.Km (x,y)) ∧ (∫ y,q.Km (x,y))=q.mrg x := by
  classical
  let s := Iic x
  let f := s.indicator fun y=>p y*q.r x
  let g := (Ioi x).indicator fun y=>p x*q.r y
  have hf : Integrable f := (integrable_indicator_iff measurableSet_Iic).mpr ((p_slice x).1.mul_const _)
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr ((q.r_slice x).1.const_mul _)
  have he : (fun y=>q.Km (x,y))=fun y=> f y+g y := by
    ext y
    rcases le_or_gt y x with h|h
    · simp [f,g,s,Km,h,not_lt_of_ge h]
    simp [f,g,s,Km,h,h.le,not_le_of_gt h]
  rw [he]
  refine ⟨hf.add hg,?_⟩
  rw [integral_add hf hg,show (∫ y,f y)= _ from integral_indicator measurableSet_Iic,
    show (∫ y,g y)=_ from integral_indicator measurableSet_Ioi,
    integral_mul_const,integral_const_mul, (p_slice x).2,(q.r_slice x).2]
  unfold mrg; ring
lemma K_pair {f:Plane→ℝ} (h:PolyBound f) (hf:Measurable f) :
    Integrable fun u=> q.Km u*f u :=
  pairMoment q.Km ((cp.measurable.comp (by fun_prop)).mul (q.hc.measurable.comp (by fun_prop)))
    (fun u=>mul_nonneg (p_pos _).le (q.hr _)) q.mrg (fun x=>(q.marg x).1)
    (fun x=>(q.marg x).2) q.hw (fun u=>by simp [Km,min_comm,max_comm]) h hf

lemma Q_int {f j:ℝ→ℝ} (hf:TestF f) (hj:TestF j) :
    Integrable fun u:Plane=>q.Km u*(f u.1*j u.2) :=
  q.K_pair ((hf.poly.comp PolyBound.fst).mul (hj.poly.comp PolyBound.snd))
    ((hf.cont.measurable.comp measurable_fst).mul (hj.cont.measurable.comp measurable_snd))

lemma Q_split {f j:ℝ→ℝ} (hf:TestF f) (hj:TestF j) :
    q.Q f j=(∫ x,q.r x*j x*∫ y in Iio x,p y*f y)+
      (∫ x,q.r x*f x*∫ y in Iio x,p y*j y) := by
  let g : Plane→ℝ := fun u=> q.Km u*(f u.1*j u.2)
  have hi := q.Q_int hf hj
  have h (f j:ℝ→ℝ) (hi:IntegrableOn (fun u:Plane=>q.Km u*(f u.1*j u.2)) Rlo) :
      (∫ u in Rlo,q.Km u*(f u.1*j u.2))=(∫ x,q.r x*j x*∫ y in Iio x,p y*f y) := by
    rw [upper2 _ hi]
    congr 1; ext x
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iio
    intro y hy
    have h := mem_Iio.mp hy
    dsimp only [Km]; rw [min_eq_left h.le,max_eq_right h.le]; ring
  unfold Q
  rw [split_plane _ hi,h _ _ hi.integrableOn]
  have he (x:Plane) : g x.swap=q.Km x*(j x.1*f x.2) := by simp [g,Km,min_comm,max_comm,mul_comm]
  congr 1
  rw [← h j f (q.Q_int hj hf).integrableOn]
  change (∫ x in Rlo,g x.swap)=_
  simp_rw [he]
end rightLayer
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Indicator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

lemma score_m : Measurable score.uncurry := (cp.measurable.comp measurable_fst).sub jump_m

lemma score_rapid : mixed score := by
  let f := fun z (_:ℝ)=> p z-st z
  let g := fun z y=>st z-jump z y
  rw [show score=fun z y=> f z y+g z y from funext fun x=>funext fun y=>by unfold score f g; ring]
  apply (mixed.of_rapid rapid_p).add
  apply mixed.of_cutoff (show PolyBound g.uncurry from PolyBound.of_bound 1 fun ⟨x,y⟩=>by
    change ‖st x-jump x y‖≤1; unfold st jump; split_ifs <;> norm_num)
    (show PolyBound (fun x:ℝ=>‖x‖) from PolyBound.id.norm)
  intro x y hx
  simp only [Real.norm_eq_abs] at hx
  unfold g st jump; split_ifs <;> grind

lemma ss_m {f:ℝ→ℝ} (hf:TestF f) : mixed (ss f) :=
  score_rapid.product (g:=fun x _=>deriv f x) (show PolyBound (fun u:Plane=> deriv f u.1) from hf.der.poly.comp PolyBound.fst)
    fun _x _y=> (norm_mul _ _).le
lemma ss_sm (f) : Measurable (ss f).uncurry :=
  score_m.mul ((measurable_deriv f).comp measurable_fst)

lemma centered_s {f:ℝ→ℝ} (hf:TestF f) (x:ℝ) :
    (∫ z,ss f z x)= f x-ga f := by
  let g := fun z=>ss f z x+phi z*f z
  have hg (t:ℝ) : HasDerivAt (fun z=>p z*f z)
      (phi t*f t+p t*deriv f t) t :=
    (d_p t).fun_mul (hf.diff t).hasDerivAt
  have hg' (t:ℝ) : HasDerivAt (fun z=>(p z-1)*f z)
      (phi t*f t+(p t-1)*deriv f t) t :=
    ((d_p t).sub_const 1).fun_mul (hf.diff t).hasDerivAt
  have ht := rapid_p.product hf.poly
  have hi := mixed_integrable_left (μ:=volume) (ss_m hf) x
    ((ss_sm f).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hh : Integrable g := hi.add (ga_i hf)
  have h₀ : Tendsto (fun x=>p x*f x) atBot (𝓝 0) := by
    apply Tendsto.congr' _ ht.tail_limit_bot
    filter_upwards [eventually_lt_atBot (0:ℝ)] with z hz; simp [st,not_le_of_gt hz]
  have h₁ : Tendsto (fun x=>(p x-1)*f x) atTop (𝓝 0) := by
    apply Tendsto.congr' _ ht.tail_limit
    filter_upwards [eventually_ge_atTop (0:ℝ)] with z hz; simp [st,hz]
  have ha : (∫ t in Iic x,g t)=p x*f x := by
    have hh := integral_Iic_of_hasDerivAt_of_tendsto ((hg x).continuousAt.continuousWithinAt)
      (fun t ht => ?_) hh.integrableOn h₀
    · simpa using hh
    have he : g t=phi t*f t+p t*deriv f t := by simp only [g,ss,score,jump,
      ite_eq_right (not_le_of_gt (mem_Iio.mp ht)),sub_zero]; ring
    exact he.symm ▸ hg t
  have hb : (∫ t in Ioi x,g t)= -((p x-1)*f x) := by
    have hh := integral_Ioi_of_hasDerivAt_of_tendsto ((hg' x).continuousAt.continuousWithinAt)
      (fun t ht => ?_) hh.integrableOn h₁
    · simpa using hh
    have he : g t=phi t*f t+(p t-1)*deriv f t :=
      by simp only [g,ss,score,jump,ite_eq_left (mem_Ioi.mp ht).le]; ring
    exact he.symm ▸ hg' t
  have hx : (∫ t,g t)=f x := by
    rw [← integral_add_compl measurableSet_Iic (s:=Iic x) hh,compl_Iic,ha,hb]; ring
  rw [show (∫ t,g t) = _ from integral_add hi (ga_i hf)] at hx
  unfold ga; linarith

lemma two_scores {f j:ℝ→ℝ} (hf:TestF f) (hj:TestF j) :
    mixed fun u:Plane => fun y=>ss f u.1 y*ss j u.2 y := by
  intro n
  obtain ⟨C,m,hc,h⟩ := ss_m hf n
  obtain ⟨D,k,hd,h'⟩ := ss_m hj n
  use C*D,m+k,mul_nonneg hc hd
  intro u y
  rw [norm_mul]
  have ha : (1+‖u‖)^n ≤ (1+‖u.1‖)^n*(1+‖u.2‖)^n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    change 1+max _ _ ≤ _
    rcases max_choice ‖u.1‖ ‖u.2‖ with h|h <;> rw [h] <;> nlinarith [norm_nonneg u.1,norm_nonneg u.2]
  apply le_trans (mul_le_mul_of_nonneg_left ha (by positivity))
  calc
    _ = (‖ss f u.1 y‖*(1+‖u.1‖)^n)*(‖ss j u.2 y‖*(1+‖u.2‖)^n) := by ring
    _ ≤ _ := mul_le_mul (h _ _) (h' _ _) (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; ring

lemma moment_mix {w:ℝ→ℝ} (hw:MomentF w) (hm:Measurable w) (hp:∀ x,0≤w x)
    {f:Plane→ℝ→ℝ} (hf:mixed f) (hf':Measurable f.uncurry) :
    Integrable (fun v:Plane×ℝ=> w v.2*f v.1 v.2) := by
  let d := Module.finrank ℝ Plane+1
  obtain ⟨C,n,hc,h⟩ := hf d
  let b := fun x:Plane=> ((1+‖x‖)^d)⁻¹
  have hh : Integrable b := envelope_inv_int
  let g := fun x:ℝ=>w x * (C*(1+‖x‖)^n)
  have hg : Integrable g := hw _ (by fun_prop)
    ((PolyBound.const _).mul (((PolyBound.const _).add PolyBound.id.norm).pow n))
  apply (hh.mul_prod hg).mono' ((hm.comp measurable_snd).mul hf').aestronglyMeasurable
    (ae_of_all _ ?_)
  rintro ⟨x,y⟩
  change ‖w y*f x y‖ ≤ b x*g y
  rw [norm_mul,Real.norm_of_nonneg (hp _)]
  have he : ‖f x y‖ ≤ C*(1+‖y‖)^n*b x := by
    unfold b
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact h x y
  unfold g
  apply le_trans (mul_le_mul_of_nonneg_left he (hp _)); apply le_of_eq; ring

variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
lemma H_jump (x:ℝ) :
    (∫ z,q.layerW z*jump x z)=q.avH x := by
  rw [show (fun z=>q.layerW z*jump x z)=(Iic x).indicator q.layerW from by ext t; by_cases h:t≤x <;> simp [jump,h]]
  rw [integral_indicator measurableSet_Iic]
  have hh := integral_Iic_of_hasDerivAt_of_tendsto'
    (f:=q.avH) (a:=x) (fun t _=>q.H_deriv t) q.integrable_w.integrableOn q.H_bot
  simpa using hh

lemma H_score (u:Plane) : q.Hcov u=∫ y,q.layerW y*(score u.1 y*score u.2 y) := by
  let f := fun x z => q.layerW z*jump x z
  have hi (x) : Integrable (f x) := q.moment_w (jump x)
    (jump_m.comp (measurable_const.prodMk measurable_id)) (PolyBound.of_bound 1
      (fun y=>by unfold jump; split<;>norm_num))
  set a := u.1; set b := u.2
  have he (y) : q.layerW y*(score a y*score b y) =
      (q.layerW y*(p a*p b)-f b y*p a-f a y*p b)+f (min a b) y := by
    unfold f score
    have hh : jump a y*jump b y=jump (min a b) y := by unfold jump; split_ifs <;> grind
    rw [← hh]; ring
  simp_rw [he]
  have ha := (hi a).mul_const (p b)
  have hb := (hi b).mul_const (p a)
  have hd := q.integrable_w.mul_const (p a*p b)
  rw [integral_add,integral_sub,integral_sub hd hb]
  · unfold f; simp_rw [integral_mul_const, q.H_jump,q.integral_w]
    unfold Hcov a b; ring
  all_goals first | exact hi _ | exact ha | exact hd.sub hb | exact (hd.sub hb).sub ha

lemma H_cov_I {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    Integrable (fun x:Plane=>q.Hcov x*(deriv f x.1*deriv g x.2)) ∧
    (∫ x:Plane,q.Hcov x*(deriv f x.1*deriv g x.2))=
      ∫ x,q.layerW x*((f x-ga f)*(g x-ga g)) := by
  let F := fun u:Plane=>fun x:ℝ=>ss f u.1 x*ss g u.2 x
  let C := fun u:Plane×ℝ=>q.layerW u.2*F u.1 u.2
  have hm : Measurable F.uncurry :=
    ((ss_sm f).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      ((ss_sm g).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hi : Integrable C :=
    moment_mix q.moment_w q.w_cont.measurable (fun x=>(q.w_positive x).le) (two_scores hf hg) hm
  have hh (u:Plane) : q.Hcov u*(deriv f u.1*deriv g u.2)=∫ y,C (u,y) := by
    rw [q.H_score, ← integral_mul_const]
    congr 1; ext; unfold C F ss; ring
  simp_rw [hh]
  refine ⟨hi.integral_prod_left,?_⟩
  rw [integral_integral_swap]
  · congr 1; ext y; dsimp only [C,F]; rw [integral_const_mul,show (volume:Measure Plane)=volume.prod volume from rfl,
      integral_prod_mul (fun x=>ss f x y) (fun x=>ss g x y), centered_s hf,centered_s hg]
  exact hi
end ProjField
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

lemma zm {f:ℝ→ℝ} (hf:TestF f) : mixed (q.zE B f) := by
  apply (q.eM B).product (g:=fun z _=>deriv f z)
    (show PolyBound (fun u:ℝ × Rn m=>deriv f u.1) from hf.der.poly.comp PolyBound.fst)
  intro z x; unfold zE; rw [norm_smul,mul_comm]
lemma zSM (f) : StronglyMeasurable (q.zE B f).uncurry :=
  (((measurable_deriv f).comp measurable_fst).stronglyMeasurable).smul (q.eSM B)
lemma zi {f:ℝ→ℝ} (hf:TestF f) (x) :
    Integrable fun z=>q.zE B f z x := mixed_integrable_left (q.zm B hf) x
      (((q.zSM B f).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)

lemma mb_eq {f:ℝ→ℝ} (hf:TestF f) (x:Rn m) :
    q.MB B f x= -(∫ z,q.zE B f z x) := by
  have iH := q.H_left_int hf.der.poly x; have iZ := q.zi B hf x
  let u := B.Fr x
  let g := fun z=> q.kerH f z x + q.zE B f z x
  have he (z) :
      u.loc (g z)=Matrix.diagonal (fun i=>ss f z (B.ev x i)) := by
    unfold g kerH zE PD EZ
    rw [← smul_add]
    have ht : p z • (1:Mat m)-q.Pmat z x+(q.Pmat z x-B.Θ z x)= p z • 1-B.Θ z x := by abel
    rw [ht, u.loc_smul,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.Θ z x)= _ from B.evfrm x _]
    ext i j
    by_cases h:i=j
    · subst j; simp [ss,score,mul_comm]
    simp [h]
  let l : Mat m→L[ℝ]Mat m := LinearMap.toContinuousLinearMap (𝕜:=ℝ)
    { toFun:=u.loc, map_add':=u.loc_add, map_smul':=u.loc_smul }
  have hl : ∫ z,g z = B.eval f x - scalar m (ga f) := by
    apply u.loc_inj
    rw [u.loc_sub,u.loc_smul, u.loc_one,show u.loc (B.eval f x)= _ from B.evfrm x f]
    have hi := iH.add iZ
    have ig : Integrable g := iH.add iZ
    change l _=_
    rw [← l.integral_comp_comm ig]
    have hh (z) : l (g z)= _ := he z
    have hh' (i j:Fin m) := (coeffMap i j).integral_comp_comm
      (l.integrable_comp ig)
    ext i j
    rw [show (∫ z,l (g z)) i j=(∫ z,l (g z) i j) from (hh' i j).symm]
    simp_rw [hh]
    by_cases h:i=j
    · subst j
      simpa using centered_s hf (B.ev x i)
    simp [h]
  have h := integral_add iH iZ
  change ∫ z,g z=_ at h
  rw [hl] at h
  unfold MB Hmat
  rw [show (∫ z,q.kerH f z x)=_ from eq_sub_of_add_eq h.symm]
  abel

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_EvalGap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
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

namespace FieldMat
variable (B:FieldMat m)
lemma pEval {f} (hf:TestF f) : PolyBound (B.eVal f).uncurry :=
  (((B.eval_reg hf).p).comp PolyBound.snd).sub
    ((hf.poly.comp PolyBound.fst).smul (PolyBound.const _))
lemma smEval {f} (hf:TestF f) : StronglyMeasurable (B.eVal f).uncurry :=
  ((B.theta_gen_meas (f:=fun _ y=>f y) (hf.cont.measurable.comp measurable_snd)).stronglyMeasurable).sub
    (((hf.cont.comp continuous_fst).stronglyMeasurable).smul stronglyMeasurable_const)

end FieldMat
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Beta
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
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

namespace ProjField
variable [NeZero m] (q:ProjField m) (B:FieldMat m) (W:Mat m)

lemma bMS {f j} (hf:TestF f) (hj:TestF j) : mixed (q.betaK B W f j) ∧
    StronglyMeasurable (q.betaK B W f j).uncurry :=
  by
    have hi := pj_M W (g:=B.eVal j) (q.zm B hf) (B.pEval hj)
    have hh := (pj_cont W).comp_stronglyMeasurable
      ((q.zSM B f).prodMk (B.smEval hj))
    exact ⟨hi,hh⟩

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Compare
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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
lemma mb_plus {f} (x:Rn m) : q.Hmat f x=q.MB B f x+BDiff B f x := by unfold MB BDiff; abel

omit [NeZero m] in
lemma delta_reg {f} (hf:TestF f): regular (BDiff B f) :=
  ⟨(B.eval_reg hf).p.sub (PolyBound.const _),
    (B.eval_reg hf).meas.sub aestronglyMeasurable_const⟩
lemma mb_reg {f} (hf:TestF f) : regular (q.MB B f) := by
  have h : q.MB B f=fun x=> q.Hmat f x-BDiff B f x := by
    funext x; unfold MB BDiff; abel
  rw [h]
  have hh := q.regH hf; have hg := delta_reg B hf
  exact ⟨hh.p.sub hg.p,hh.meas.sub hg.meas⟩

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

lemma mb_ibp (x:Rn m) {f j b:ℝ→ℝ} (hf:TestF f) (_hj:TestF j) (hb:TestF b)
    (hB:∀ x,deriv b x=deriv f x*j x) :
    PJ W (q.MB B f x) (B.eval j x)= trN (W*q.MB B b x) -
      (∫ z,q.betaK B W f j z x) := by
  let l := (PJ W).flip (B.eval j x)
  let k := (PJ W).flip (1:Mat m)
  have he (z:ℝ) : q.betaK B W f j z x= l (q.zE B f z x)- k (q.zE B b z x) := by
    have ht (a b:ℝ) (A C:Mat m) :
        Pj W (a•A) (C-b•(1:Mat m))=PJ W (a•A) C-PJ W ((a*b)•A) 1 := by
      have hj : Pj W (a•A) ((b:ℝ)•(1:Mat m))=PJ W ((a*b)•A) 1 := by
        rw [pJ_eq,pj_scale]
        have he := pj_scale (a*b) 1 W A 1
        simp only [one_smul,one_mul] at he
        rw [he]; ring
      rw [← hj]
      simp_rw [← pJ_eq,_root_.map_sub]
    unfold betaK l k FieldMat.eVal zE scalar
    rw [ht,hB]; rfl
  have he' (A:Mat m) : trN (W*A)= k A := by rw [← pj_I,← pJ_eq]; rfl
  rw [q.mb_eq B hf _,q.mb_eq B hb _]
  rw [he']
  change l (-(∫ z,q.zE B f z x)) = k _ - _
  simp_rw [he]
  have ha := q.zi B hf x; have hc := q.zi B hb x
  rw [integral_sub (l.integrable_comp ha) (k.integrable_comp hc),
    l.integral_comp_comm ha,k.integral_comp_comm hc, _root_.map_neg,_root_.map_neg]; ring

lemma mb_comp {f j b:ℝ→ℝ} (hf:TestF f) (hj:TestF j) (hb:TestF b)
    (hB:∀ x,deriv b x=deriv f x*j x) :
    Pt W (q.MB B f) (B.eval j)=etw W (q.MB B b) - q.be B W f j := by
  unfold Pt etw et be
  simp_rw [← pJ_eq,q.mb_ibp B W _ hf hj hb hB]
  have hi := q.bMS B W hf hj
  rw [integral_sub]
  · exact int_etw _ (q.mb_reg B hb).ig
  exact (mixed_integrable (ν:=normal m) (μ:=volume) hi.1 hi.2.aestronglyMeasurable).integral_prod_right
lemma etw_H {f} (hf:TestF f) :
    etw W (q.Hmat f)=etw W (q.MB B f)+LDel B W f := by
  unfold LDel etw et
  simp_rw [q.mb_plus B,mul_add,trN_add]
  exact integral_add (int_etw _ (q.mb_reg B hf).ig) (int_etw _ (delta_reg B hf).ig)
lemma etw16a {j} (hj:TestF j) :
    etw W (q.Hmat j)= LDel B W j+Pt W (q.MB B (fun x=>x)) (B.eval (deriv j))
      + q.be B W (fun x=>x) (deriv j) := by
  rw [q.mb_comp B W TestF.id hj.der hj (by intro x; simp),q.etw_H B W hj]; ring

omit [NeZero m] in
lemma Delta_sub {f j} (hf:TestF f) (hj:TestF j) :
    LDel B W (fun x=>f x-j x)=LDel B W f-LDel B W j := by
  unfold LDel etw et
  have he (x:Rn m) : BDiff B (fun x=>f x-j x) x= BDiff B f x-BDiff B j x := by
    unfold BDiff; rw [B.eval_sub hf hj,ga_sub hf hj]; unfold scalar; module
  simp_rw [he,mul_sub,trN_sub]
  exact integral_sub (etwReg _ (delta_reg B hf)) (etwReg _ (delta_reg B hj))

lemma f_pair16 {f j w:ℝ→ℝ} (hf:TestF f) (hj:TestF j)
    (he:ga f=0) (hw:TestF w) (h':∀ x,deriv w x=f x*deriv j x) :
    Pt q.covMat (q.Hmat f) (B.eval j) =
      (∫ x,q.layerW x*(f x*j x)) + (LDel B q.covMat w-∫ x,q.dm x*w x) -
        q.be B q.covMat f j := by
  let W := q.covMat
  let g := fun x=>f x*j x
  let b := fun x=>g x-w x
  have hg := hf.mul hj
  have hb := hg.sub hw
  have h (x:ℝ) : deriv b x=deriv f x*j x := by
    have he := ((((hf.diff x).hasDerivAt).fun_mul (hj.diff x).hasDerivAt).fun_sub
      (hw.diff x).hasDerivAt).deriv
    change deriv b x=_ at he; rw [he,h']; ring
  have hi := q.mb_comp B W hf hj hb h
  have hh : Pt W (q.Hmat f) (B.eval j) =
      Pt W (q.MB B f) (B.eval j) + etw W (B.eval g) := by
    unfold Pt etw et
    have he (x) : Pj W (q.Hmat f x) (B.eval j x)=
        Pj W (q.MB B f x) (B.eval j x)+trN (W*B.eval g x) := by
      rw [q.mb_plus B]
      unfold BDiff
      rw [he]; simp only [scalar,zero_smul,sub_zero]
      have he' : jprod (B.eval f x) (B.eval j x)=B.eval g x := by
        unfold jprod g; rw [B.eval_mul hf hj, (B.ccomm x j f).eq]; module
      calc
        _ = Pj W (q.MB B f x) (B.eval j x)+Pj W (B.eval f x) (B.eval j x) := by
          simp_rw [← pJ_eq]; rw [_root_.map_add,_root_.add_apply]
        _ = _ := by unfold Pj; rw [he']
    simp_rw [he]
    rw [integral_add]
    · simp_rw [← pJ_eq]; exact proj_int _ (q.mb_reg B hf) (B.eval_reg hj)
    exact int_etw _ (B.eval_reg hg).ig
  have h₁ : etw W (B.eval g)= LDel B W g+q.s0*ga g := by
    have he (x:Rn m) :
        trN (W*B.eval g x)=trN (W*BDiff B g x)+q.s0*ga g := by
      unfold BDiff s0 scalar W; rw [mul_sub,trN_sub,mul_smul_comm,mul_one,trN_smul]; ring
    unfold etw LDel etw et; simp_rw [he]
    rw [integral_add (int_etw W (delta_reg B hg).ig) (integrable_const _)]
    simp; rfl
  have h₂ := q.etw_H B W hb
  have h₃ := q.h_weighted hb
  change etw W (q.Hmat b)= _ at h₃
  have h₄ : (∫ x,q.dm x*b x)=(∫ x,q.layerW x*g x)-q.s0*ga g-(∫ x,q.dm x*w x) := by
    have he (x) : q.dm x*b x=q.layerW x*g x-q.s0*(phi x*g x)-q.dm x*w x := by
      unfold dm b; ring
    simp_rw [he]; have hi:= ga_i hg; have hh:= q.moment_w.int_test hg
    rw [integral_sub,integral_sub hh (hi.const_mul _),integral_const_mul]; rfl
    · exact hh.sub (hi.const_mul _)
    exact q.dm_m.int_test hw
  have h₅ := Delta_sub B W hg hw
  change Pt W _ _=(∫ x,q.layerW x*g x)+(LDel B W w-_)-_
  linarith
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
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Packet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
lemma k_sq : kk^2=bb-cc := Real.sq_sqrt (by norm_num [bb,cc])
lemma u_eq (x:ℝ) (h:0 ≤ rad x) :
    FF x=d x+(uc x^2+us x^2+qu x^2) := by
  have hh := Real.sin_sq_add_cos_sq (angle x)
  have hi := Real.sq_sqrt h
  unfold rad at hi
  unfold FF qu uc us rad r at *
  nlinarith [k_sq]

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
lemma bar_eq (h:Bwt g) (u:Plane) :
    bInt g u=(u.2-u.1)*bAv g u := by
  let f := fun t=> ∫ z in u.1..t,g (u.1,z)
  have hf : Continuous (fun z=>g (u.1,z)) := h.c.comp (continuous_const.prodMk continuous_id)
  have hd (t:ℝ) : HasDerivAt f (g (u.1,t)) t := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable ..) (hf.stronglyMeasurableAtFilter volume _) hf.continuousAt
  have hi (t:ℝ) : HasDerivAt (f ∘ along u) (g (u.1,along u t)*(u.2-u.1)) t := by
    apply HasDerivAt.comp t (hd (along u t))
    convert ((((hasDerivAt_const t 1).sub (hasDerivAt_id' t)).mul_const u.1).fun_add
      ((hasDerivAt_id' t).mul_const u.2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | ring
  have HH := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> hi t)
    (((hf.comp (by unfold along; fun_prop)).mul continuous_const).intervalIntegrable (0:ℝ) 1)
  rw [intervalIntegral.integral_mul_const] at HH
  simp [along,f] at HH
  unfold bInt bAv; rw [mul_comm]
  convert HH.symm using 1 ; rfl
end Bwt
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Qprimitive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Eq13 mixed derivative kernel, proof via rectangle cumulative
representation of a(min)B(max). -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile
namespace rightLayer
variable (q:rightLayer)

lemma K_c : Continuous q.Km :=
  (cp.comp (by fun_prop)).mul (q.hc.comp (by fun_prop))
lemma K_nn (u) : 0≤q.Km u := mul_nonneg (p_pos _).le (q.hr _)

lemma rcompact (u:Plane) : IsCompact (Rect u) := isCompact_Icc.prod isCompact_Icc
lemma concat_m : MeasurableSet ({p:Plane×Plane| p.2∈Rect p.1}) := by
  let f : Plane × Plane→Plane := Prod.fst
  let g : Plane × Plane→Plane := Prod.snd
  let D : ℕ→Plane × Plane→ℝ := fun i=> if i=0 then Prod.fst ∘ f else if i=1 then Prod.snd ∘ f else if i=2 then Prod.fst ∘ g else Prod.snd ∘ g
  have hi (i j : ℕ) : MeasurableSet {p|D i p ≤ D j p} := by
    unfold D f g; split_ifs <;> exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  exact ((hi 0 2).inter (hi 2 1)).inter ((hi 0 3).inter (hi 3 1))

lemma rect_slice_i (f:Plane→ℝ) (hf:Continuous f) (u:Plane) :
    Integrable fun v=> q.RectF f (u,v) := by
  classical
  have he : (fun v=>q.RectF f (u,v))=(Rect u).indicator (fun v=>q.Km u*f v) := by ext v; rfl
  rw [he]
  exact (integrable_indicator_iff (rcompact u).measurableSet).mpr
    ((continuous_const.mul hf).continuousOn.integrableOn_compact (rcompact u))

lemma Rect_bound (u v:Plane) (h:v∈Rect u) : ‖v‖ ≤ ‖u‖ := by
  have he : (u.1≤v.1 ∧ v.1≤u.2)∧(u.1≤v.2∧v.2≤u.2) := h
  change max ‖v.1‖ ‖v.2‖ ≤ max ‖u.1‖ ‖u.2‖
  simp_rw [Real.norm_eq_abs]; grind
lemma length_rect (u:Plane) :
    volume.real (Rect u) ≤ 4*‖u‖^2 := by
  change ((volume.prod volume) ((Icc u.1 u.2) ×ˢ Icc u.1 u.2)).toReal ≤ _
  rw [prod_prod,ENNReal.toReal_mul]
  change volume.real (Icc u.1 u.2)*volume.real (Icc u.1 u.2) ≤ _
  rw [Real.volume_real_Icc]
  have h : max (u.2-u.1) 0 ≤ 2*‖u‖ := by
    change _≤2*max ‖u.1‖ ‖u.2‖
    simp only [Real.norm_eq_abs]; grind
  nlinarith [norm_nonneg u,le_max_right (u.2-u.1) (0:ℝ)]
lemma Rect_int {f:Plane→ℝ} (hp:PolyBound f) (hf:Continuous f) :
    Integrable (q.RectF f) := by
  classical
  have hm : Measurable (q.RectF f) := Measurable.ite concat_m
    ((q.K_c.measurable.comp measurable_fst).mul (hf.measurable.comp measurable_snd)) measurable_const
  rw [show (volume:Measure (Plane×Plane))=volume.prod volume from rfl]
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (q.rect_slice_i f hf),?_⟩
  obtain ⟨C,n,hc,h⟩ := hp
  let g : Plane→ℝ := fun u=> C*(1+‖u‖)^n
  have hp : PolyBound (fun u:Plane=> (4*‖u‖^2)*g u) :=
    ((PolyBound.const _).mul (PolyBound.id.norm.pow _)).mul
      ((PolyBound.const _).mul (((PolyBound.const _).add PolyBound.id.norm).pow n))
  have hi := q.K_pair hp (by unfold g; fun_prop)
  refine hi.mono' ?_ (ae_of_all _ fun x=>?_ )
  · exact ((hm.stronglyMeasurable.norm).integral_prod_right').aestronglyMeasurable
  · let R := fun u=> ‖q.RectF f (x,u)‖
    change ‖∫ u,R u‖≤_
    rw [Real.norm_of_nonneg (integral_nonneg (fun _=> norm_nonneg _))]
    have he : R=(Rect x).indicator fun u=> q.Km x*‖f u‖ := by
      funext u; unfold R RectF; by_cases h:u∈Rect x
      · simp only [ite_eq_left h,indicator_of_mem h,norm_mul,Real.norm_of_nonneg (q.K_nn x)]
      simp only [ite_eq_right h,indicator_of_notMem h,norm_zero]
    change ∫ u,R u≤ _
    rw [he,integral_indicator (rcompact x).measurableSet]
    have hu : (∫ u in Rect x,q.Km x*‖f u‖) ≤ ∫ u:Plane in Rect x,q.Km x*g x := by
      apply setIntegral_mono_on
        (((continuous_const.mul hf.norm).continuousOn).integrableOn_compact (rcompact x))
        (continuous_const.continuousOn.integrableOn_compact (rcompact x)) (rcompact x).measurableSet
      intro y hy
      apply mul_le_mul_of_nonneg_left _ (q.K_nn _)
      apply (h y).trans
      unfold g; gcongr; exact Rect_bound x y hy
    apply hu.trans
    rw [setIntegral_const,smul_eq_mul]
    have hx : 0 ≤ g x := by unfold g; positivity
    have hi := mul_le_mul_of_nonneg_right (length_rect x) (mul_nonneg (q.K_nn x) hx)
    linarith

lemma slice_rect_a (v:Plane) (f:Plane→ℝ) :
    (∫ u:Plane,q.RectF f (u,v))=q.Kab v*f v := by
  classical
  set x := min v.1 v.2
  set y := max v.1 v.2
  let g := (Iic x).indicator p; let h := (Ici y).indicator q.r
  have he : (fun u=>q.RectF f (u,v))=fun u:Plane=> (g u.1*h u.2)*f v := by
    ext u
    by_cases H:u.1≤x
    · by_cases W:y≤u.2
      · have hh : v∈Rect u := by
          change (u.1≤v.1 ∧ v.1≤u.2)∧(u.1≤v.2 ∧ v.2≤u.2); grind
        have hi : u.1≤u.2 := by grind
        simp [g,h,RectF,hh,Km,H,W,hi]
      have hh : v∉Rect u := by change ¬((u.1≤v.1 ∧ v.1≤u.2)∧(u.1≤v.2 ∧ v.2≤u.2)); grind
      simp [g,h,RectF,hh,W]
    have hh : v∉Rect u := by change ¬((u.1≤v.1 ∧ v.1≤u.2)∧(u.1≤v.2 ∧ v.2≤u.2)); grind
    simp [g,h,RectF,hh,H]
  rw [he,integral_mul_const]
  congr 1
  rw [show (volume:Measure Plane)=volume.prod volume from rfl,integral_prod_mul]
  unfold g h; rw [integral_indicator measurableSet_Iic,integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi,(q.r_slice y).2,(p_slice x).2]; rfl

lemma Kab_I {f:Plane→ℝ} (hf:Continuous f) (h:PolyBound f) :
    Integrable fun u=>q.Kab u*f u := by
  simp_rw [← q.slice_rect_a]
  exact (q.Rect_int h hf).integral_prod_right
lemma R_reverse {f:Plane→ℝ} (hf:Continuous f) (h:PolyBound f) :
    (∫ u,q.Kab u*f u)=∫ u:Plane,q.Km u*∫ v in Rect u,f v := by
  simp_rw [← q.slice_rect_a]
  rw [integral_integral_swap]
  · congr 1; ext u; rw [← integral_const_mul,← integral_indicator (rcompact u).measurableSet]
    rfl
  exact (q.Rect_int h hf).swap

lemma mrgMul {f:ℝ→ℝ} (hf:TestF f) :
    (∫ u:Plane,q.Km u*f u.1)= ∫ x,q.mrg x*f x := by
  rw [show (volume:Measure Plane)=volume.prod volume from rfl,integral_prod]
  · simp_rw [integral_mul_const]
    congr 1; ext x; rw [(q.marg x).2]
  exact q.K_pair (hf.poly.comp PolyBound.fst) (hf.cont.measurable.comp measurable_fst)

lemma R_identity {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    (∫ u:Plane,q.Kab u*(deriv f u.1*deriv g u.2))=
      (∫ x,q.mrg x*(f x*g x)) - q.Q f g := by
  classical
  rw [q.R_reverse (f:=fun u=>deriv f u.1*deriv g u.2) ((hf.der.cont.comp continuous_fst).mul (hg.der.cont.comp continuous_snd))
    ((hf.der.poly.comp PolyBound.fst).mul (hg.der.poly.comp PolyBound.snd))]
  let F := fun u:Plane=>q.Km u*(f u.1*g u.1) - q.Km u*(f u.1*g u.2)
  have hi : Integrable F :=
    (q.K_pair ((hf.poly.mul hg.poly).comp PolyBound.fst)
      ((hf.cont.mul hg.cont).measurable.comp measurable_fst)).sub (q.Q_int hf hg)
  have he : (∫ u:Plane,F u)=(∫ x,q.mrg x*(f x*g x))-q.Q f g := by
    unfold F Q; rw [integral_sub,q.mrgMul (hf.mul hg)]
    all_goals first | exact q.K_pair ((hf.poly.mul hg.poly).comp PolyBound.fst) ((hf.cont.mul hg.cont).measurable.comp measurable_fst) |
      exact q.Q_int hf hg
  rw [← he,split_plane F hi,
    ← integral_add (show Integrable F (volume.restrict Rlo) from hi.integrableOn) (show Integrable (fun u:Plane=>F u.swap) (volume.restrict Rlo) from hi.swap.integrableOn),
    ← integral_indicator Rlo_m]
  apply integral_congr_ae
  filter_upwards [off_diag] with u hu
  rcases lt_or_gt_of_ne hu with h|h
  · have hx:u∈Rlo := h
    rw [indicator_of_mem hx]
    unfold Rect
    rw [show (volume:Measure Plane)=volume.prod volume from rfl,← Measure.prod_restrict,integral_prod_mul]
    have h (f:ℝ→ℝ) (hf:TestF f) :
        (∫ a in Icc u.1 u.2,deriv f a)=f u.2-f u.1 := by
      rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le h.le]
      exact intervalIntegral.integral_deriv_eq_sub (fun a _=>hf.diff a) (hf.der.cont.intervalIntegrable ..)
    rw [h f hf,h g hg]; unfold F
    rw [show q.Km u.swap=q.Km u from by simp [Km,min_comm,max_comm]]
    change _ = q.Km u*_ -_ +(q.Km u*(f u.2*g u.2)-q.Km u*(f u.2*g u.1))
    ring
  have hx:u∉Rlo := not_lt_of_ge h.le
  rw [indicator_of_notMem hx]
  have hh : Rect u=∅ := by unfold Rect; rw [Icc_eq_empty_of_lt h]; simp
  simp [hh]

end rightLayer
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Contact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn _root_.OAI.GeneralMahler.Frm.frame_cmp
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer covariances and scalar contact term. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}
namespace ProjField
variable (q:ProjField m)
lemma ct_pos [NeZero m] (u:Plane) : 0 ≤ q.ct u := by
  unfold ct
  apply div_nonneg _ m_pos.le
  apply integral_nonneg; intro x
  exact mem_posDual.mp (proj_mem ..) (proj_mem ..)

lemma ipt_i {f g:Rn m→Rn m} (hf:regular f) (hg:regular g) :
    Integrable (fun x=>⟪f x,g x⟫) (normal m) :=
  (PolyBound.of_prod_le hf.p hg.p (fun _x=>abs_real_inner_le_norm ..)).gaussian_integrable
    (hf.meas.inner hg.meas)
lemma ipt_sym (f g:Rn m→Rn m) : ipt f g=ipt g f := by
  unfold ipt
  congr 2; ext; exact real_inner_comm ..
lemma regneg {f:Rn m→Rn m} (h:regular f) : regular fun x=> -(f x) :=
  ⟨h.p.neg,h.meas.neg⟩
lemma regsub {f g:Rn m→Rn m} (h:regular f) (hh:regular g) : regular fun x=> f x-g x := by
  simpa only [sub_eq_add_neg] using h.add (regneg hh)
lemma regconst (v:Rn m) : regular (fun _:Rn m=>v) :=
  ⟨PolyBound.const _,aestronglyMeasurable_const⟩
lemma ipt_add {f g h:Rn m→Rn m} (hf:regular f) (hg:regular g) (hh:regular h) :
    ipt (fun x=>f x+g x) h=ipt f h+ipt g h := by
  unfold ipt; simp_rw [inner_add_left,integral_add (ipt_i hf hh) (ipt_i hg hh)]
  ring
lemma ipt_sub {f g h:Rn m→Rn m} (hf:regular f) (hg:regular g) (hh:regular h) :
    ipt (fun x=>f x-g x) h=ipt f h-ipt g h := by
  unfold ipt; simp_rw [inner_sub_left,integral_sub (ipt_i hf hh) (ipt_i hg hh)]
  ring
lemma ipt_smul (f g:Rn m→Rn m) (a:ℝ) :
    ipt (fun x=> a • f x) g=a*ipt f g := by
  unfold ipt; simp_rw [real_inner_smul_left,integral_const_mul]; ring
lemma ipt_const {f:Rn m→Rn m} (hf:regular f) (v:Rn m) :
    ipt (fun _=> v) f=⟪v,∫ x,f x ∂normal m⟫/(m:ℝ) := by
  unfold ipt
  congr 1
  exact (innerSL ℝ v).integral_comp_comm hf.ig

lemma Z_reg : regular q.Z := ⟨PolyBound.clm q.root.toContinuousLinearMap,
  q.root.continuous.aestronglyMeasurable⟩
lemma Z_mean : (∫ x,q.Z x ∂normal m)=0 := by
  have h := affineN_mean q.root 0
  simpa only [affineN,Z,add_zero] using h
lemma X_reg (z:ℝ) : regular (q.XT z) :=
  ⟨poly_sample ..,(q.X_int z).aestronglyMeasurable⟩
lemma Y_reg (z:ℝ) : regular (q.YT z) :=
  ⟨by
    rw [show q.YT z=_ from funext (q.YT_sub z)]
    exact (q.X_reg z).p.sub (q.Z_reg.p.add (PolyBound.const _)),(q.Y_int z).aestronglyMeasurable⟩

lemma zz_cov : ipt q.Z q.Z=q.s0 := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  let l := fun i=> innerSL ℝ (q.Z (b i))
  have he (i) (x:Rn m) : ⟪b i,q.Z x⟫=l i x := by
    unfold l
    change ⟪b i,q.Z x⟫=⟪q.Z _,x⟫; rw [q.Z_def,q.Z_def]; exact (op_iff_hermitian.mp q.pos.1 ..).symm
  have hs (i:Fin m) :
      (∫ x:Rn m, (l i x)^2 ∂normal m)=⟪q.Z (b i),q.Z (b i)⟫ := by
    have h := normal_IBP_lipschitz (l i).lipschitz (q.Z (b i))
    calc
      _ = ∫ x:Rn m,⟪x,q.Z (b i)⟫ • (l i x) ∂normal m := by
        congr 1; ext x; rw [real_inner_comm]
        change ⟪q.Z (b i),x⟫^2= _*⟪q.Z (b i),x⟫; ring
      _ = _ := by rw [← h]; simp_rw [ContinuousLinearMap.fderiv]; simp; exact real_inner_self_eq_norm_sq (q.Z (b i))
  unfold ipt s0 trN
  congr 1
  have hx (x) : ⟪q.Z x,q.Z x⟫=∑ i:Fin m,(l i x)^2 := by
    conv_lhs => arg 2; rw [← b.sum_repr (q.Z x)]
    rw [sum_inner]
    congr 1; ext i
    rw [b.repr_apply_apply,real_inner_smul_left]
    rw [he]; ring
  simp_rw [hx]; rw [integral_finsetSum]
  · simp_rw [hs]
    rw [← mul_one q.covMat,q.trace_SPS]
    simp only [q.Z_def,_root_.map_one]
    rfl
  exact fun i _=> ((PolyBound.clm (l i)).pow 2).gaussian_integrable
    (((l i).continuous.pow _).aestronglyMeasurable)

lemma Xc_reg (z:ℝ) : regular (q.Xcenter z) :=
  regsub (q.X_reg z) (regconst _)
lemma Xc_mean (z:ℝ) : (∫ x,q.Xcenter z x ∂normal m)=0 := by
  unfold Xcenter; rw [integral_sub (q.X_int z) (integrable_const _),q.XT_mean]; simp
lemma xz_cov (z:ℝ) : ipt (q.Xcenter z) q.Z=q.avH z := by
  unfold Xcenter
  rw [ipt_sub (q.X_reg z) (regconst _) q.Z_reg,ipt_const q.Z_reg,q.Z_mean,
    inner_zero_right,zero_div,sub_zero]
  exact (q.avH_as_mean_ip z).symm
lemma xx_cov (z y:ℝ) (hy:z ≤ y) :
    ipt (q.Xcenter z) (q.Xcenter y)=q.avH z-a z*q.Bt y+q.ct (z,y) := by
  have he : q.Xcenter y=fun x=>q.Z x+q.YT y x+(q.shift y - a y • q.U) := by ext x; rw [q.YT_sub]; unfold Xcenter; abel_nf
  rw [ipt_sym,he,ipt_add (q.Z_reg.add (q.Y_reg y)) (regconst _) (q.Xc_reg z),ipt_const (q.Xc_reg z),q.Xc_mean,
    inner_zero_right,zero_div,add_zero,ipt_add q.Z_reg (q.Y_reg y) (q.Xc_reg z),ipt_sym q.Z (q.Xcenter z),q.xz_cov,ipt_sym]
  unfold Xcenter
  rw [ipt_sub (q.X_reg z) (regconst _) (q.Y_reg y),ipt_const (q.Y_reg y),
    real_inner_smul_left]
  have hh : q.ct (z,y) =ipt (q.XT z) (q.YT y) := by unfold ct ipt; simp [hy]
  rw [hh,Bt]; ring

lemma Zs_reg (z:ℝ) : regular fun x:Rn m=>p z • q.Z x :=
  q.Z_reg.smul ⟨PolyBound.const _, aestronglyMeasurable_const⟩
lemma ww_cov0 [NeZero m] (z y:ℝ) (h:z≤y) :
    ipt (q.WW z) (q.WW y) = q.Hcov (z,y)+q.ct (z,y)-q.Lr.Kab (z,y) := by
  have he (z:ℝ) : q.WW z= fun x=>p z • q.Z x-q.Xcenter z x := by
    ext x; unfold WW Xcenter; abel_nf
  rw [he z,he y,ipt_sub (q.Zs_reg z) (q.Xc_reg z) (regsub (q.Zs_reg y) (q.Xc_reg y)),
    ipt_sym (fun x=>p z • q.Z x),ipt_sub (q.Zs_reg y) (q.Xc_reg y) (q.Zs_reg z),
    ipt_sym (q.Xcenter z) (fun x=>_),ipt_sub (q.Zs_reg y) (q.Xc_reg y) (q.Xc_reg z),
    ipt_smul,ipt_sym q.Z (fun x=>_),ipt_smul, q.zz_cov,
    ipt_sym (q.Xcenter y) (fun x=>p z • q.Z x),ipt_smul,
    ipt_smul, ipt_sym q.Z (q.Xcenter z),ipt_sym q.Z (q.Xcenter y), q.xz_cov,q.xz_cov,
    ipt_sym, q.xx_cov z y h]
  unfold Hcov rightLayer.Kab
  simp only [min_eq_left h,max_eq_right h,Lr]; ring

lemma WW_pair_cov [NeZero m] (u:Plane) :
    ipt (q.WW u.1) (q.WW u.2) = q.Hcov u+q.ct u-q.Lr.Kab u := by
  rcases u with ⟨z,y⟩
  rcases le_total z y with h|h
  · exact q.ww_cov0 z y h
  rw [ipt_sym]; convert q.ww_cov0 y z h using 1
  unfold Hcov rightLayer.Kab ct
  simp only [min_comm,max_comm]
  ring

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Eq13
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Eq13 covariance equals Q+Ct on centered tests. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open HMode Layers Profile
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)

omit [NeZero m] in
lemma mixed_contract {f j:ℝ→Rn m→Rn m} (hf:mixed f) (hj:mixed j) :
    mixed fun u:Plane=>fun x=> ⟪f u.1 x,j u.2 x⟫ := by
  intro n
  obtain ⟨C,l,hc,h⟩ := hf n
  obtain ⟨D,k,hd,h'⟩ := hj n
  use C*D,l+k,mul_nonneg hc hd
  intro u y
  have ha : (1+‖u‖)^n ≤ (1+‖u.1‖)^n*(1+‖u.2‖)^n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    change 1+max _ _ ≤ _
    rcases max_choice ‖u.1‖ ‖u.2‖ with h|h <;> rw [h] <;> nlinarith [norm_nonneg u.1,norm_nonneg u.2]
  apply le_trans (mul_le_mul (abs_real_inner_le_norm (f u.1 y) (j u.2 y)) ha (by positivity)
    (by positivity))
  calc
    _ = (‖f u.1 y‖*(1+‖u.1‖)^n)*(‖j u.2 y‖*(1+‖u.2‖)^n) := by ring
    _ ≤ _ := mul_le_mul (h _ _) (h' _ _) (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; ring

lemma ipt_double {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    ipt (q.WH f) (q.WH g) =
      ∫ u:Plane,ipt (q.WW u.1) (q.WW u.2)*(deriv f u.1*deriv g u.2) ∧
    Integrable fun u:Plane=>ipt (q.WW u.1) (q.WW u.2)*(deriv f u.1*deriv g u.2) := by
  let C := fun u:Plane=>fun x=>⟪q.WK f u.1 x,q.WK g u.2 x⟫
  have hC : mixed C := mixed_contract (q.WK_m hf) (q.WK_m hg)
  have hm : StronglyMeasurable C.uncurry :=
    ((q.WK_SM f).comp_measurable
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).inner
        ((q.WK_SM g).comp_measurable
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hi := mixed_integrable (μ:=volume) (ν:=normal m) hC hm.aestronglyMeasurable
  have he (u:Plane) :
      ipt (q.WW u.1) (q.WW u.2)*(deriv f u.1*deriv g u.2) =
        (∫ x,C u x ∂normal m)/(m:ℝ) := by
    have hh (x) : C u x=(deriv f u.1*deriv g u.2)*⟪q.WW u.1 x,q.WW u.2 x⟫ := by
      unfold C WK; rw [real_inner_smul_left,real_inner_smul_right]; ring
    simp_rw [hh]
    rw [integral_const_mul]
    unfold ipt; ring
  simp_rw [he]
  refine ⟨?_,hi.integral_prod_left.div_const _⟩
  rw [integral_div,integral_integral_swap hi]
  have iW (f:ℝ→ℝ) (hf:TestF f) (x) : Integrable (fun z=> q.WK f z x) :=
    mixed_integrable_left (q.WK_m hf) x
      (((q.WK_SM f).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  unfold ipt WH
  congr 2
  ext x
  have hi : Integrable (fun u:Plane=> C u x) := mixed_integrable_left hC x
    ((hm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  exact (integral_prod_bilin (innerSL ℝ) (iW f hf x) (iW g hg x)).symm

lemma Ct_integrable {f g} (hf:TestF f) (hg:TestF g) :
    Integrable fun u:Plane=>q.ct u*(deriv f u.1*deriv g u.2) := by
  let T := fun u:Plane=> deriv f u.1*deriv g u.2
  have hi := (q.ipt_double hf hg).2
  have hh := (q.H_cov_I hf hg).1
  have hu : Integrable fun u:Plane=> q.Lr.Kab u*T u :=
    q.Lr.Kab_I ((hf.der.cont.comp continuous_fst).mul (hg.der.cont.comp continuous_snd))
      ((hf.der.poly.comp PolyBound.fst).mul (hg.der.poly.comp PolyBound.snd))
  convert (hi.add hu).sub hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  change q.ct x*T x = _+_-_
  dsimp only
  rw [show ipt (q.WW x.1) (q.WW x.2)=_ from q.WW_pair_cov x]
  unfold T; ring

lemma eq13 {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (hF:ga f=0) (hG:ga g=0) :
    KP q.covMat (q.Hmat f) (q.Hmat g)=q.Lr.Q f g+q.Ct f g := by
  have hu : Integrable fun u:Plane=> q.Lr.Kab u*(deriv f u.1*deriv g u.2) :=
    q.Lr.Kab_I ((hf.der.cont.comp continuous_fst).mul (hg.der.cont.comp continuous_snd))
      ((hf.der.poly.comp PolyBound.fst).mul (hg.der.poly.comp PolyBound.snd))
  have hi := q.H_cov_I hf hg; rw [hF,hG] at hi
  simp only [sub_zero] at hi
  have he := q.Lr.R_identity hf hg
  rw [← q.pt_k_cov hf hg,show (∫ x, ⟪q.WH f x,q.WH g x⟫ ∂normal m)/(m:ℝ)= _
    from (q.ipt_double hf hg).1]
  simp_rw [q.WW_pair_cov,sub_mul,add_mul]
  have hc := q.Ct_integrable hf hg
  rw [integral_sub,integral_add hi.1 hc,hi.2,he]
  · have hh : q.Lr.mrg=q.layerW := by ext; unfold layerW rightLayer.mrg Lr; ring
    rw [hh]; unfold Ct; ring
  · exact hi.1.add hc
  exact hu
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Variation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

namespace rightLayer

lemma Ileft {f:ℝ→ℝ} (hf:TestF f) (x:ℝ) :
    IntegrableOn (fun t=>p t*f t) (Iic x) := by
  have h : IntegrableOn (fun t=>p t*f t) (Iio 0) := by
    have hi := ((rapid_p.product hf.poly).integrable_real
      ((cp.measurable.sub measurable_st).mul hf.cont.measurable))
    exact hi.integrableOn.congr_fun (fun t ht=>by
      unfold st; simp [not_le_of_gt (mem_Iio.mp ht)]) measurableSet_Iio
  exact ((h.union (cp.mul hf.cont).integrableOn_Icc).mono_set
    (show Iic x ⊆ Iio 0 ∪ Icc 0 x from fun y hy=> by
      rcases lt_or_ge y 0 with h|h
      · exact Or.inl h
      exact Or.inr ⟨h,mem_Iic.mp hy⟩))

lemma pleft {b:ℝ→ℝ} (hb:TestF b) (x:ℝ) :
    (∫ y in Iic x,p y*Nr b y)=a x*b x-p x*deriv b x := by
  let F := fun x=> a x*b x-p x*deriv b x
  have hd (x:ℝ) : HasDerivAt F (p x*Nr b x) x := by
    convert (((d_a x).fun_mul (hb.diff x).hasDerivAt).fun_sub
      ((d_p x).fun_mul (hb.der.diff x).hasDerivAt)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (unfold Nr N a; ring)
  have hl : Tendsto F atBot (𝓝 0) := by
    have h₂ : Tendsto (fun x=>p x*deriv b x) atBot (𝓝 0) := by
      apply Tendsto.congr' _ (rapid_p.product hb.der.poly).tail_limit_bot
      filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx; simp [st,not_le_of_gt hx]
    simpa [F] using ((abot _ hb.poly).sub h₂)
  have hi := integral_Iic_of_hasDerivAt_of_tendsto'
    (fun x _=>hd x) (Ileft (nr_test hb) x) hl
  simpa [F] using hi

lemma right_i {b:ℝ→ℝ} (hb:TestF b) (x:ℝ) :
    IntegrableOn (fun t=> p (-t)*b t) (Ioi x) := by
  let l := (Homeomorph.neg ℝ)
  have h := Ileft hb.ref (-x)
  have hv := ((Measure.measurePreserving_neg volume).integrableOn_comp_preimage
    l.measurableEmbedding).mpr h
  have he : (fun t:ℝ=> -t) ⁻¹' Iic (-x)=Ici x := by ext; simp
  rw [he] at hv
  simp only [Function.comp_def,neg_neg] at hv
  exact hv.mono_set Ioi_subset_Ici_self

lemma pright {b} (hb:TestF b) (x:ℝ) :
    (∫ y in Ioi x,p (-y)*Nr b y)=a (-x)*b x+p (-x)*deriv b x := by
  let F := fun t=> -(a (-t)*b t+p (-t)*deriv b t)
  have hd (x:ℝ) : HasDerivAt F (p (-x)*Nr b x) x := by
    convert (((((d_a (-x)).comp x (hasDerivAt_neg' x)).fun_mul
      (hb.diff x).hasDerivAt).fun_add (((d_p (-x)).comp x (hasDerivAt_neg' x)).fun_mul
        (hb.der.diff x).hasDerivAt)).neg) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (simp only [Function.comp_apply]; unfold Nr N a; ring)
  have hl : Tendsto F atTop (𝓝 0) := by
    have h₁ := (std_hb.product hb.poly).tail_limit
    have h₂ := (rapid_p.product hb.der.ref.poly).tail_limit_bot.comp tendsto_neg_atTop_atBot
    have hh : Tendsto (fun t=> -(a (-t)*st t*b t+(p (-t)-st (-t))*deriv b t)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (h₁.add h₂).neg
    apply Tendsto.congr' _ hh
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; simp [F,st,hx.le,hx]
  simpa [F] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _=>hd x) (right_i (nr_test hb) x) hl

lemma Q0_cov {b f} (hb:TestF b) (hf:TestF f) :
    stdL.Q f (Nr b) = ga (fun x=>f x*b x) := by
  unfold Q
  rw [show (volume:Measure Plane)=volume.prod volume from rfl]
  rw [integral_prod _ (stdL.Q_int hf (nr_test hb))]
  unfold ga; congr 1; ext x
  classical
  let g := (Iic x).indicator fun y=> (p y*Nr b y)*(f x*p (-x))
  let h := (Ioi x).indicator fun y=> (p (-y)*Nr b y)*(f x*p x)
  have he : (fun y=>stdL.Km (x,y)*(f x*Nr b y))=fun y=>g y+h y := by
    ext y; rcases le_or_gt y x with hx|hx
    · simp [g,h,Km,stdL,hx, not_lt_of_ge hx]; ring
    simp [g,h,Km,stdL,hx,hx.le,not_le_of_gt hx]; ring
  rw [he,integral_add]
  · unfold g h; rw [integral_indicator measurableSet_Iic,integral_indicator measurableSet_Ioi,
      integral_mul_const,integral_mul_const,pleft hb,pright hb,← Qpos_id x]; ring
  · exact (integrable_indicator_iff measurableSet_Iic).mpr ((Ileft (nr_test hb) x).mul_const _)
  exact (integrable_indicator_iff measurableSet_Ioi).mpr ((right_i (nr_test hb) x).mul_const _)

variable (q:rightLayer)
lemma arM : MomentF fun x=>a x*q.r x :=
  q.hw.mono (ca.mul q.hc).measurable (fun x=>by
    have he : 0 ≤ q.B x := by rw [← (q.r_slice x).2]; exact integral_nonneg q.hr
    have h : 0 ≤ p x*q.B x := mul_nonneg (p_pos x).le he
    have hh := mul_nonneg (a_pos x).le (q.hr x)
    change ‖a x*q.r x‖≤‖p x*q.B x+a x*q.r x‖
    rw [Real.norm_of_nonneg hh,Real.norm_of_nonneg (by positivity)]; linarith)
lemma prM : MomentF fun x=>p x*q.r x := by
  have h := q.arM.mul ratio_bound (cp.measurable.div ca.measurable)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x; field_simp [ne_of_gt (a_pos x)]

lemma varI {b c r} (hr:MomentF fun x=>a x*r x) (hp:MomentF fun x=>p x*r x)
    (hb:TestF b) (hc:TestF c) :
    Integrable (variationK r b c) :=
  (hr.int_test ((nr_test hb).mul hc)).sub (hp.int_test ((nr_test hb).mul hc.der))
lemma Q_var {b c} (hb:TestF b) (hc:TestF c) :
    q.Q (Nr b) (Nr c)=(∫ x,variationK q.r c b x)+(∫ x,variationK q.r b c x) := by
  rw [q.Q_split (nr_test hb) (nr_test hc)]
  have hi (b c:ℝ→ℝ) (hb:TestF b) :
      (fun x=> q.r x*Nr c x*∫ y in Iio x,p y*Nr b y)=fun x=>variationK q.r c b x := by
    ext x; rw [← integral_Iic_eq_integral_Iio,pleft hb]; unfold variationK; ring
  rw [hi b c hb, hi c b hc]
end rightLayer
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Eq14
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Variation identities. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler
open Profile Layers rightLayer
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)

lemma var_eq {b c:ℝ→ℝ} (hb:TestF b) (hc:TestF c) :
    q.Lr.Q (Nr b) (Nr c) - q.s0*stdL.Q (Nr b) (Nr c)=
    ∫ x,(variationK q.dr b c x+variationK q.dr c b x) := by
  have he (b c) (hb:TestF b) (hc:TestF c) :
      (∫ x,variationK q.dr b c x)= (∫ x,variationK q.Lr.r b c x)-
      q.s0*(∫ x,variationK stdL.r b c x) := by
    rw [← integral_const_mul,← integral_sub]
    · congr 1; ext x; unfold variationK dr
      change _=_-q.s0*(a x*p (-x)*_ - p x*p (-x)*_)
      simp only [Lr,neg_p]; ring
    · exact varI q.Lr.arM q.Lr.prM hb hc
    exact (varI stdL.arM stdL.prM hb hc).const_mul _
  have hi (b c) (hb:TestF b) (hc:TestF c) := varI q.arDelta_moment q.prDelta_moment hb hc
  rw [integral_add (hi _ _ hb hc) (hi _ _ hc hb),q.Lr.Q_var hb hc,stdL.Q_var hb hc,
    he _ _ hb hc,he _ _ hc hb]
  ring

lemma eq14 {b c w} (hb:TestF b) (hc:TestF c) (hw:TestF w)
    (hv:∀ x,deriv w x=deriv (Nr b) x*c x+deriv (Nr c) x*b x) :
    q.Lr.Q (Nr b) (Nr c) - q.s0*stdL.Q (Nr b) (Nr c)=
      (∫ x,q.dm x*w x)+q.delt (fun x=>deriv b x*deriv c x) := by
  let F := fun x=>b x*c x
  let H := fun x=>Nr b x*c x+Nr c x*b x
  let t := fun x=>deriv b x*deriv c x
  let J := fun x=>Nr b x*deriv c x+Nr c x*deriv b x
  have hH : TestF H := ((nr_test hb).mul hc).add ((nr_test hc).mul hb)
  have hF : TestF F := hb.mul hc
  have ht : TestF t := hb.der.mul hc.der
  have he (x:ℝ) : deriv w x=deriv H x-J x := by
    have h := ((((nr_test hb).diff x).hasDerivAt.fun_mul (hc.diff x).hasDerivAt).fun_add
      (((nr_test hc).diff x).hasDerivAt.fun_mul (hb.diff x).hasDerivAt)).deriv
    rw [hv,show deriv H x= _ from h]; unfold J; ring
  have dF (x:ℝ) : deriv F x=deriv b x*c x+b x*deriv c x :=
    ((hb.diff x).hasDerivAt.fun_mul (hc.diff x).hasDerivAt).deriv
  have hh (x:ℝ) : H x=N2 F x+2*t x := by
    have hs : deriv (deriv F) x = deriv (deriv b) x*c x+deriv b x*deriv c x+
        (deriv b x*deriv c x+b x*deriv (deriv c) x) := by
      rw [funext dF]
      exact ((((hb.der.diff x).hasDerivAt.fun_mul (hc.diff x).hasDerivAt)).fun_add
        ((hb.diff x).hasDerivAt.fun_mul (hc.der.diff x).hasDerivAt)).deriv
    unfold H N2 N Nr
    simp only [Profile.N,dF,hs]
    unfold F t; ring
  have hj (x) : J x=deriv F x+shiftD t x := by
    unfold shiftD J; rw [dF,show deriv t x=_ from ((hb.der.diff x).hasDerivAt.fun_mul (hc.der.diff x).hasDerivAt).deriv]
    unfold Nr N t; ring
  let P := fun x=> variationK q.dr b c x+variationK q.dr c b x
  let V := fun x=> q.pb x*N2 F x+q.rk x*deriv F x
  let U := fun x=> 2*(q.pb x*t x)+q.rk x*shiftD t x
  have hp (x:ℝ) : P x+q.hDel x*deriv w x+V x+U x =
      q.dm x*H x+q.hDel x*deriv H x := by
    unfold P V U variationK
    have h := he x
    rw [h,q.dm_eq]
    rw [show N2 F x=H x-2*t x by linarith [hh x],show shiftD t x=J x-deriv F x by linarith [hj x]]
    unfold J H rk
    ring
  have hz := q.eq12 hF
  have hd := q.delta_eq ht
  have hs : TestF (shiftD t) := (((TestF.const _).mul TestF.id).mul ht).sub ht.der
  have hd' : q.delt t= -(∫ x,U x) := by
    rw [hd]; unfold U; rw [integral_add,integral_const_mul]
    · exact (q.pb_m.int_test ht).const_mul _
    exact q.rk_m.int_test hs
  have iP : Integrable P := (varI q.arDelta_moment q.prDelta_moment hb hc).add
    (varI q.arDelta_moment q.prDelta_moment hc hb)
  have iV : Integrable V := (q.pb_m.int_test (N2_test hF)).add (q.rk_m.int_test hF.der)
  have iU : Integrable U := ((q.pb_m.int_test ht).const_mul _).add
    (q.rk_m.int_test hs)
  have ih := q.hd_m.int_test hw.der
  have heq : (∫ x,P x+q.hDel x*deriv w x+V x+U x) = 0 := by
    simp_rw [hp]
    rw [integral_add (q.dm_m.int_test hH) (q.hd_m.int_test hH.der),q.hd_test hH]; ring
  rw [integral_add,integral_add,integral_add iP ih] at heq
  · rw [q.var_eq hb hc,q.hd_test hw]
    change (∫ x,P x)=_+q.delt t
    rw [hd']
    change (∫ x,V x)=0 at hz
    linarith
  all_goals first | exact iP.add ih | exact iV | exact iU | exact (iP.add ih).add iV
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LFun
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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

lemma Bwt.indef {f:Plane→ℝ} (hf:Bwt f) : Bwt (bInt f) := by
  rw [show bInt f=_ from funext hf.bar_eq]
  apply Bwt.mul _ hf.bar
  exact (Bwt.snd TestF.id).sub (Bwt.fst TestF.id)

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

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)

lemma lkMS {f} (hf:Bwt f) :
    mixed (q.lk B W f) ∧ StronglyMeasurable (q.lk B W f).uncurry := by
  have he := pj_M W (q.eM B) (B.p_bmat hf.indef)
  have hh := (pj_cont W).comp_stronglyMeasurable ((q.eSM B).prodMk (B.bsmb hf.indef))
  exact ⟨he,hh⟩
lemma lk_slice_i {f} (hf:Bwt f) (x) : Integrable fun z=>q.lk B W f z x := by
  have he := q.lkMS B W hf
  exact mixed_integrable_left he.1 x
    ((he.2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
lemma Lbar_i {f} (hf:Bwt f) : Integrable (fun x=>∫ z,q.lk B W f z x) (normal m) := by
  have he := q.lkMS B W hf
  exact (mixed_integrable (μ:=volume) (ν:=normal m) he.1 he.2.aestronglyMeasurable).integral_prod_right

omit [NeZero m] in
lemma lk_add {f g} (hf:Bwt f) (hg:Bwt g) (z x) :
    q.lk B W (fun u=>f u+g u) z x=q.lk B W f z x + q.lk B W g z x := by
  unfold lk; simp_rw [← pJ_eq]
  have he (u:Plane) : bInt (fun u=>f u+g u) u=bInt f u+bInt g u :=
    intervalIntegral.integral_add ((hf.c.comp (continuous_const.prodMk continuous_id)).intervalIntegrable ..)
      ((hg.c.comp (continuous_const.prodMk continuous_id)).intervalIntegrable ..)
  have hh : B.bmat (bInt (fun u=>f u+g u)) z x=B.bmat (bInt f) z x+B.bmat (bInt g) z x := by
    apply (B.Fr x).loc_inj; rw [Frm.loc_add,B.bmat_loc,B.bmat_loc,B.bmat_loc]
    ext i j
    by_cases h:i=j
    · subst j; simp [he]
    simp [h]
  rw [hh,_root_.map_add]
lemma Lbar_add {f g} (hf:Bwt f) (hg:Bwt g) :
    q.LLw B W (fun u=>f u+g u)=q.LLw B W f+q.LLw B W g := by
  unfold LLw; simp_rw [q.lk_add B W hf hg, integral_add (q.lk_slice_i B W hf _) (q.lk_slice_i B W hg _)]
  rw [integral_add (q.Lbar_i B W hf) (q.Lbar_i B W hg)]
omit [NeZero m] in
lemma Lbar_scale (f:Plane→ℝ) (a:ℝ) :
    q.LLw B W (fun u=>a*f u)=a*q.LLw B W f := by
  have he (x) : bInt (fun u=>a*f u) x=a*bInt f x := by unfold bInt; rw [intervalIntegral.integral_const_mul]
  have hp (z x) : B.bmat (bInt (fun u=>a*f u)) z x=a • B.bmat (bInt f) z x := by
    apply (B.Fr x).loc_inj; rw [Frm.loc_smul,B.bmat_loc,B.bmat_loc]
    ext i j; by_cases h:i=j
    · subst j; simp [he]
    simp [h]
  unfold LLw lk
  simp_rw [hp,← pJ_eq,_root_.map_smul,smul_eq_mul,integral_const_mul]

lemma Lbar_sub {f g} (hf:Bwt f) (hg:Bwt g) :
    q.LLw B W (fun u=>f u-g u)=q.LLw B W f-q.LLw B W g := by
  have he : f=fun u=>f u-g u+g u := by funext u; ring
  have hh := q.Lbar_add B W (hf.sub hg) hg
  rw [← he] at hh
  linarith

omit [NeZero m] in
lemma Le_id {f j} (_hf:TestF f) (hj:TestF j) :
    q.LLw B W (fun u=>deriv f u.1*deriv j u.2) = q.be B W f j := by
  let h := fun u:Plane=> deriv f u.1*deriv j u.2
  have he (u:Plane) : bInt h u=deriv f u.1*(j u.2-j u.1) := by
    unfold bInt h
    dsimp only; rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_deriv_eq_sub]
    · exact fun x _=>hj.diff x
    exact hj.der.cont.intervalIntegrable ..
  have h₁ (z x) : B.bmat (bInt h) z x = deriv f z • B.eVal j z x := by
    let u:=B.Fr x
    apply u.loc_inj; rw [u.loc_smul, show u.loc (B.bmat (bInt h) z x)=_ from B.bmat_loc ..,
      FieldMat.eVal,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.eval j x)=_ from B.evfrm x j]
    ext i k
    by_cases hh:i=k
    · subst k; simp [he]
    simp [hh]
  unfold LLw be
  change (∫ x,(∫ z,q.lk B W h z x) ∂normal m)= _
  have h₂ (x z) : q.lk B W h z x=q.betaK B W f j z x := by
    unfold lk betaK zE; rw [h₁]
    have hi := pj_scale 1 (deriv f z) W (q.EZ B z x) (B.eVal j z x)
    have hj := pj_scale (deriv f z) 1 W (q.EZ B z x) (B.eVal j z x)
    simp only [one_mul,one_smul] at hi hj
    rw [hi,hj]
  simp_rw [h₂]
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Prim
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
lemma pl_ga {l} (hl:TestF l) : ga (pl l)=0 := by
  rw [show ga (pl l)=_ from ga_sub (p_test hl) (TestF.const _),ga_const,sub_self]

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
lemma fl_ga {l} (hl:TestF l) : ga (fl l)=0 := (Nr_ga (pl_test hl)).trans (pl_ga hl)

lemma ga_N_parts {f g} (hf:TestF f) (hg:TestF g) :
    ga (fun x=> N f x*g x) = ga (fun x=>deriv f x*deriv g x) := ga_pair hf.der hg
lemma ga_nr_parts {f g} (hf:TestF f) (hg:TestF g) :
    ga (fun x=> Nr f x*g x)=ga (fun x=>f x*g x)+ga (fun x=>deriv f x*deriv g x) := by
  unfold Nr; simp_rw [add_mul]
  rw [ga_add (hf.mul hg) ((N_test hf).mul hg),ga_N_parts hf hg]
lemma id_ga : ga (fun x=>x)=0 := by
  simpa [ga] using ga_parts (TestF.const 1)
end GeneralMahler.Profile

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Forms
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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
lemma pj_ss (W A B C D:Mat m) :
    Pj W (A-B) (C-D)= Pj W A C-Pj W A D-Pj W B C+Pj W B D := by
  simp_rw [← pJ_eq]
  simp only [_root_.map_sub,_root_.sub_apply]; ring
lemma pJ_smul_left (W:Mat m) (A C:Mat m) (a:ℝ) :
    Pj W (a•A) C=a*Pj W A C := by simpa using pj_scale a 1 W A C
lemma pJ_smul_right (W:Mat m) (A C:Mat m) (a:ℝ) :
    Pj W A (a•C)=a*Pj W A C := by simpa using pj_scale 1 a W A C

namespace ProjField
variable [NeZero m] (q:ProjField m)
lemma dl_raise {l:ℝ→ℝ} (hl:TestF l) (i:Fin m) (a:MI m) :
    cof (fun x=>q.DLMat l x i) a=sn (a i+1) • cof (q.FL.eval (pl l)) (inc a i) := by
  have hh := pl_test hl
  let f := q.FL.eval (pl l)
  have hi := q.FL.eval_reg hh
  have hf : Differentiable ℝ f := fun x=>(q.hasdl x hh).differentiableAt
  have hv := PLip.fd hf (q.dPoly hh)
  have h := q.LD_reg i hh
  exact coef_raise hi.p hv hf.continuous (ae_of_all _ fun x=>(hf x).hasFDerivAt) i h.p h.meas a

lemma Pt_dir (W:Mat m) {l:ℝ→ℝ} (hl:TestF l) :
    let b := q.FL.eval (pl l)
    HasSum (fun a:MI m=> (deg a:ℝ)* CpPair W b b a) (q.dirF W l) := by
  intro b
  let f := fun (i:Fin m) (a:MI m)=> (a i:ℝ)*CpPair W b b a
  have he (a): (deg a:ℝ)*CpPair W b b a=∑ i,f i a := by
    unfold f deg; rw [← Finset.sum_mul,Nat.cast_sum]
  have hh (i) :
      let c := fun x=>q.DLMat l x i
      HasSum (f i) (Pt W c c) := by
    intro c
    have hi : regular c := q.LD_reg i (pl_test hl)
    have hp := pt_sum (B:=W) hi hi
    have h (a) : CpPair W c c a=f i (inc a i) := by
      unfold CpPair
      rw [show cof c a= _ from q.dl_raise hl i a,pj_scale]
      unfold f CpPair b
      rw [inc_at,← mul_assoc,← pow_two,snsq]
    rw [funext h] at hp
    obtain ⟨he₁,he₂⟩ := inc_sum i (f i) fun a ha=>by simp [ha,f]
    rw [hp.tsum_eq] at he₂
    exact he₂ ▸ (he₁.mpr hp.summable).hasSum
  simp_rw [he]
  exact hasSum_sum fun i _=>hh i

lemma H_K_split {l} (hl:TestF l) :
    let f := q.Hmat (fl l)
    let b := q.FL.eval (pl l)
    let W := q.covMat
    HasSum (q.Dterm l) (KP W f f-2*Pt W f b+Pt W b b+q.dirF W l) := by
  intro f b W
  have hf : regular f:= q.regH (fl_test hl)
  have hb : regular b:=q.FL.eval_reg (pl_test hl)
  have h₁ := (K_sum (B:=W) hf hf).hasSum
  have h₂ := pt_sum (B:=W) hf hb
  have h₃ := pt_sum (B:=W) hb hb
  have h₄ := q.Pt_dir W hl
  have he (a:MI m) :
      q.Dterm l a=CpPair W f f a*kMode a-2*CpPair W f b a+
        CpPair W b b a+(deg a:ℝ)*CpPair W b b a := by
    change (1+_)*Pj W (kMode a • cof f a - cof b a) (kMode a • cof f a - cof b a)=_
    simp only [pj_ss,pJ_smul_left,pJ_smul_right]
    rw [pj_sym W (cof b _)]
    unfold CpPair kMode
    have hi : 0 < 1+(deg a:ℝ) := by positivity
    field_simp; ring
  rw [funext he]
  exact (((h₁.sub (h₂.mul_left 2)).add h₃).add h₄)

lemma R_reg : regular q.RR :=
  ⟨q.A_poly.sub q.L_poly,q.A_SM.aestronglyMeasurable.sub q.L_cont.aestronglyMeasurable⟩
lemma sig_split {l:ℝ→ℝ} (hl:TestF l) :
    let f := q.Hmat (fl l)
    let b := q.FL.eval (pl l)
    let W := q.covMat
    HasSum (q.sigterm l) (KP W q.RR f-Pt W q.RR b) := by
  intro f b W
  have hf : regular f:= q.regH (fl_test hl)
  have hb : regular b:=q.FL.eval_reg (pl_test hl)
  have h₁ := (K_sum (B:=W) q.R_reg hf).hasSum
  have h₂ := pt_sum (B:=W) q.R_reg hb
  have he (a:MI m) : q.sigterm l a=CpPair W q.RR f a*kMode a-CpPair W q.RR b a := by
    unfold sigterm DD CpPair
    have hi (A B C:Mat m) : Pj W A (B-C)= Pj W A B-Pj W A C := by
      simp_rw [← pJ_eq]; rw [_root_.map_sub]
    rw [show q.covMat=W from rfl,hi,pJ_smul_right,mul_comm]
  rw [funext he]
  exact h₁.sub h₂

end ProjField
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

lemma dm_e {f:ℝ→ℝ} (hf:TestF f) : q.Idw f=q.Iw f-q.s0*ga f := by
  unfold Idw dm Iw ga; simp_rw [sub_mul,mul_assoc]
  rw [integral_sub (q.moment_w.int_test hf)
    (show Integrable (fun x=> q.s0*(phi x*f x)) from (ga_i hf).const_mul _),integral_const_mul]
lemma Id_sub {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    q.Idw (fun x=>f x-g x)=q.Idw f-q.Idw g := by
  unfold Idw; simp_rw [mul_sub]
  exact integral_sub (q.dm_m.int_test hf) (q.dm_m.int_test hg)
omit [NeZero m] in
lemma Id_cmul (c:ℝ) (f:ℝ→ℝ) :
    q.Idw (fun x=>c*f x)=c*q.Idw f := by
  unfold Idw; simp_rw [mul_left_comm (dm q _),integral_const_mul]
lemma Id_ext {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (he:deriv f=deriv g) :
    q.Idw f=q.Idw g := by unfold Idw; rw [q.hd_test hf,q.hd_test hg,he]
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
omit [NeZero m] in
lemma delt_scale (f:ℝ→ℝ) (hf:TestF f) (c:ℝ) :
    q.delt (fun x=>c*f x) = c*q.delt f := by
  have he (x) := ((hf.diff x).hasDerivAt.const_mul c).deriv
  unfold delt
  simp_rw [he]
  rw [mul_neg, ← integral_const_mul]; congr 2; ext; ring

lemma ga_prod_comm (f g:ℝ→ℝ) : ga (fun x=>f x*g x)=ga (fun x=>g x*f x) := by
  congr 1; ext; ring
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

lemma Pb_sq {l} (hl:TestF l) (W:Mat m) :
    Pt W (q.FL.eval l) (q.FL.eval l)=etw W (q.FL.eval (fun x=>l x*l x)) := by
  unfold Pt Pj etw et
  have he (A:Mat m): jprod A A=A*A := by unfold jprod; module
  simp_rw [he,FieldMat.eval_mul _ hl hl]

lemma form_sq {l} (hl:TestF l) :
    q.Dnorm l+q.Jtest q.covMat l =
      q.delt (fun z=>l z^2)-LDel q.FL q.covMat (ps (fun z=> l z^2))+
      2*q.be q.FL q.covMat (fl l) (pl l)+q.Ct (fl l) (fl l) := by
  let f := fl l
  let b := pl l
  let h := fun x=>l x^2
  let W := q.covMat
  have hf : TestF f := fl_test hl
  have hb : TestF b := pl_test hl
  have ht : TestF h := by simp_rw [h,pow_two]; exact hl.mul hl
  let w := prim (fun x=>f x*deriv b x)
  let v := prim (fun x=>deriv f x*b x+deriv f x*b x)
  have hw := p_test (hf.mul hb.der)
  have hv := p_test ((hf.der.mul hb).add (hf.der.mul hb))
  have dw (x) : deriv w x=f x*deriv b x := (prim_d (hf.mul hb.der) x).deriv
  have dv (x) : deriv v x=deriv (Nr b) x*b x+deriv (Nr b) x*b x :=
    (prim_d ((hf.der.mul hb).add (hf.der.mul hb)) x).deriv
  let F := fun x=>b x*b x+x*pl h x
  have Ht := pl_test ht
  have HI := TestF.id.mul Ht
  have HB := hb.mul hb
  have FF : TestF F := HB.add HI
  let L := LDel q.FL W

  have hd1 : q.Idw (fun x=>v x-2*(f x*b x)) = q.Idw (fun x=> -(2*w x)) := by
    apply Id_ext _ (hv.sub ((TestF.const _).mul (hf.mul hb))) (((TestF.const _).mul hw).neg)
    funext x
    have hx := ((hf.diff x).hasDerivAt.fun_mul (hb.diff x).hasDerivAt).const_mul 2
    have he := (((hv.diff x).hasDerivAt).fun_sub hx).deriv
    have hh : deriv (fun x=> -(2*w x)) x= -(2*deriv w x) :=
      (((hw.diff x).hasDerivAt.const_mul 2).neg).deriv
    rw [he,hh,dv,dw]
    change _+_-_=_; dsimp only [f,fl,b]; ring
  have IdH : q.Idw v-2*q.Idw (fun x=>f x*b x) = - (2*q.Idw w) := by
    have ha : (fun x=> -(2*w x))=fun x=> -2*w x := by ext; ring
    rw [q.Id_sub hv ((TestF.const _).mul (hf.mul hb)), q.Id_cmul, ha, q.Id_cmul] at hd1
    linarith

  have hd2 : L (fun x=>F x-2*w x)= L (fun x=> - (ps h x)) := by
    apply L_ext _ _ (FF.sub ((TestF.const _).mul hw)) (ps_test ht).neg
    funext x
    have he := (((((hb.diff x).hasDerivAt).fun_mul (hb.diff x).hasDerivAt).fun_add
      ((hasDerivAt_id' x).fun_mul (Ht.diff x).hasDerivAt)).fun_sub
      ((hw.diff x).hasDerivAt.const_mul 2)).deriv
    have HH : deriv (fun x=> -ps h x) x= -deriv (ps h) x :=
      (((ps_test ht).diff x).hasDerivAt.neg).deriv
    change deriv (fun x=>F x-2*w x) x=_ at he
    rw [he,HH,dw,ps_d ht x]
    unfold f fl Nr N b
    simp only [pl_d ht,pl_d hl]
    have hi : deriv h x= deriv l x*l x + l x*deriv l x := by
      unfold h; simp_rw [pow_two]
      exact ((hl.diff x).hasDerivAt.fun_mul (hl.diff x).hasDerivAt).deriv
    rw [hi]
    unfold h; ring
  have LdH : L F-2*L w= -L (ps h) := by
    have he : (fun x=> -ps h x) = fun x=> (-1)*ps h x := by ext; ring
    unfold L at *
    rw [Delta_sub _ _ FF ((TestF.const _).mul hw),L_cmul _ _ _ hw,he,
      L_cmul _ _ _ (ps_test ht)] at hd2
    linarith

  have hgas : ga F=ga (fun x=> f x*b x) := by
    have hh := ga_parts Ht
    rw [pl_d ht] at hh
    unfold F; rw [ga_add HB HI,hh, show f=Nr b from rfl,
      ga_nr_parts hb hb,show deriv b=l from pl_d hl]
    simp_rw [h,pow_two]

  have heq := q.eq14 hb hb hv dv
  rw [rightLayer.Q0_cov hb (nr_test hb)] at heq
  have hu : (fun x=>deriv b x*deriv b x)=h := by simp only [b,pl_d hl,h,pow_two]
  rw [hu] at heq
  change q.Lr.Q f f-q.s0*ga (fun x=>f x*b x)=q.Idw v+q.delt h at heq
  have hi : Pt W (q.FL.eval b) (q.FL.eval b)+
      etw W (fun x=> q.Lmat x*q.FL.eval (pl h) x) = L F + q.s0*ga F := by
    have he (x) : q.Lmat x*q.FL.eval (pl h) x=q.FL.eval (fun x=> x*pl h x) x := by
      rw [FieldMat.eval_mul q.FL TestF.id Ht,q.evId]
    rw [Pb_sq q hb]; simp_rw [he]; rw [L_formula _ W HB,L_formula _ W HI]
    unfold L F; rw [tw_add W HB HI, ga_add HB HI]; change _=_
    rw [show trN W=q.s0 from rfl]; ring
  have hg := fl_ga hl
  have hcov := q.eq13 hf hf hg hg
  have hpa := q.f_pair16 q.FL hf hb hg hw dw
  have hk := q.dm_e (hf.mul hb)
  have h1 := (q.H_K_split hl).tsum_eq
  change q.Dnorm l= _ at h1
  unfold Jtest
  change q.Dnorm _+ (_-q.dirF W l) = q.delt h-L (ps h)+2*q.be q.FL W f b+q.Ct f f
  change Pt W _ _=q.Iw (fun x=>f x*b x)+(L w-q.Idw w)-q.be q.FL W f b at hpa
  rw [hgas] at hi; rw [h1]; dsimp only [W,h,f,b] at *; linarith
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
lemma Mi1 (i:Fin m) (x:Rn m) : MM (inc 0 i) x=x i := by
  rw [inc,factor_upd]; simp [H,sn]

omit [NeZero m] in
lemma cof_subm {f g:Rn m→Mat m} (hf:regular f) (hg:regular g) (a:MI m) :
    cof (fun x=>f x-g x) a=cof f a-cof g a := by
  unfold cof; simp_rw [smul_sub]; rw [integral_sub (i_cof hf.p hf.meas a) (i_cof hg.p hg.meas a)]

omit [NeZero m] in
lemma l_reg : regular q.Lmat := ⟨q.L_poly,q.L_cont.aestronglyMeasurable⟩
lemma a_reg : regular q.Amat := ⟨q.A_poly,q.A_SM.aestronglyMeasurable⟩
omit [NeZero m] in
lemma coL (a:MI m) :
    cof q.Lmat a=∑ i:Fin m,(if a=inc 0 i then (1:ℝ) else 0) • q.M i := by
  classical
  have hi (i:Fin m) : Integrable (fun x:Rn m=> (MM a x*x i) • q.M i) (normal m) := by
    have h := ((M_poly a).mul (PolyBound.clm (coord i)))
    exact ((h.gaussian_integrable (μ:=normal m)
      ((M_cont a).mul (coord i).continuous).aestronglyMeasurable).smul_const _)
  have he (x:Rn m) : MM a x • q.Lmat x=∑ i:Fin m,(MM a x*x i) • q.M i := by
    unfold Lmat; rw [Finset.smul_sum]; simp only [smul_smul]
  unfold cof; simp_rw [he]; rw [integral_finsetSum]
  · simp_rw [integral_smul_const, ← Mi1, M_inner]
  exact fun i _=>hi i

omit [NeZero m] in
lemma coL_o {a:MI m} (h:deg a ≠ 1) : cof q.Lmat a=0 := by
  have he (i:Fin m):a≠ inc 0 i := by
    intro h'; rw [h',deg_inc,dz _ |>.mpr rfl] at h; exact h rfl
  rw [q.coL]; simp [he]
lemma k_l (W:Mat m) {f:Rn m→Mat m} (hf:regular f) :
    2*KP W q.Lmat f=Pt W q.Lmat f := by
  have h := pt_sum (B:=W) q.l_reg hf
  unfold KP
  rw [← tsum_mul_left, ← h.tsum_eq]
  apply tsum_congr; intro a
  by_cases hh:deg a=1
  · rw [kMode,hh]; push_cast; ring
  unfold CpPair; rw [q.coL_o hh]
  simp [Pj,jprod,trN]

lemma kpR (W:Mat m) {f:Rn m→Mat m} (hf:regular f) :
    KP W q.Amat f= KP W q.Lmat f + KP W q.RR f := by
  have he : KP W q.RR f = KP W q.Amat f-KP W q.Lmat f := by
    unfold KP
    rw [← Summable.tsum_sub (K_sum q.a_reg hf) (K_sum q.l_reg hf)]
    apply tsum_congr; intro a
    unfold CpPair RR; rw [cof_subm q.a_reg q.l_reg]
    simp_rw [← pJ_eq]
    simp only [_root_.map_sub,_root_.sub_apply,sub_mul]
  linarith
omit [NeZero m] in
lemma pt_sym (W:Mat m) (f g:Rn m→Mat m) : Pt W f g=Pt W g f := by
  unfold Pt; congr 1; funext x; exact pj_sym ..
lemma MB_id :
    q.MB q.FL (fun x=>x)=q.RR := by
  ext x
  unfold MB RR; rw [q.evId,Profile.id_ga]; simp [scalar,Amat]; rfl

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_FormLin
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Linear profile identity, first part of Eq17. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m)
theorem form_lin {l:ℝ→ℝ} (hl:TestF l) :
    q.delt l=LDel q.FL q.covMat (ps l)+ q.sigma l-
      2*q.be q.FL q.covMat (fun x=>x) (pl l) -q.be q.FL q.covMat (fl l) (fun x=>x)
      -2*q.Ct (fun x=>x) (fl l) := by
  let i := fun x:ℝ=>x
  let k := fun x:ℝ=>(1/2:ℝ)*x
  let b := pl l
  let f := fl l
  let W := q.covMat
  let A := LDel q.FL W
  have hf : TestF f := fl_test hl
  have hb : TestF b := pl_test hl
  have ht := ps_test hl
  have hi : TestF i := TestF.id
  have hk : TestF k := (TestF.const _).mul hi
  have dk : deriv k=fun _=>1/2 := by
    ext x; unfold k; convert (((hasDerivAt_id' x).const_mul (1/2:ℝ)).deriv) using 1 ; ring
  have di : deriv i=fun _=>1 := by ext; simp [i]
  have K : Nr k=i := by
    unfold Nr N; rw [dk]; ext x; unfold k i; simp; ring
  let w := prim f
  let v := prim (fun x=>b x+deriv f x*k x)
  let u := prim b
  have hw := p_test hf
  have hv := p_test (hb.add (hf.der.mul hk))
  have hu := p_test hb
  have du : deriv u=b := funext fun x=> (prim_d hb x).deriv
  have dw : deriv w=f := funext fun x=> (prim_d hf x).deriv
  have dv (x:ℝ) : deriv v x=deriv (Nr k) x*b x+deriv (Nr b) x*k x := by
    rw [K,di]
    have he := (prim_d (hb.add (hf.der.mul hk)) x).deriv
    simp only [one_mul]; exact he

  let I := fun x=> f x*x
  have ih := hf.mul hi
  have h₁ : q.Iw I-2*q.Lr.Q i f=q.Idw (ps l)-q.delt l := by
    have hh := q.eq14 hk hb hv dv
    rw [K,rightLayer.Q0_cov hb hi] at hh
    change q.Lr.Q i f-q.s0*ga (fun x=>i x*b x)=q.Idw v+q.delt _ at hh
    have hz : (fun x=>deriv k x*deriv b x) =fun x=>(1/2:ℝ)*l x := by rw [dk,show deriv b=l from pl_d hl]
    rw [hz,q.delt_scale _ hl] at hh
    have hd := q.dm_e ih
    have he : ga I=2*ga (fun x=>i x*b x) := by
      have HH : ga (fun x=>deriv b x*deriv i x) = ga (deriv b) := by rw [di]; simp
      change ga (fun x=>Nr b x*i x)=_
      rw [ga_nr_parts hb hi,HH, ← ga_parts hb]
      rw [ga_prod_comm b i]
      change ga _+ga (fun x=>i x*b x)=_
      ring
    have ht' : q.Idw (fun x=> I x-2*v x)=q.Idw (ps l) := by
      apply q.Id_ext (ih.sub ((TestF.const _).mul hv)) ht
      ext x
      have hd := ((((hf.diff x).hasDerivAt.fun_mul (hi.diff x).hasDerivAt)).fun_sub
        ((hv.diff x).hasDerivAt.const_mul 2)).deriv
      change deriv (fun x=>f x*i x-2*v x) x=_
      rw [hd,dv,K,ps_d hl,di]
      unfold f b i k fl; ring
    rw [q.Id_sub ih ((TestF.const _).mul hv),q.Id_cmul] at ht'
    change q.Idw I=q.Iw I-q.s0*ga I at hd
    rw [he] at hd; linarith
  have hh : deriv (fun x=>w x-ps l x)=deriv (fun x=>2*u x) := by
    ext x
    rw [((hw.diff x).hasDerivAt.fun_sub (ht.diff x).hasDerivAt).deriv,
      ((hu.diff x).hasDerivAt.const_mul 2).deriv,du,dw,ps_d hl]
    unfold b f; ring
  have he := L_ext q.FL W (hw.sub ht) ((TestF.const _).mul hu) hh
  rw [Delta_sub _ W hw ht,L_cmul q.FL W _ hu] at he
  have hx := q.Id_ext (hw.sub ht) ((TestF.const _).mul hu) hh
  rw [q.Id_sub hw ht,q.Id_cmul] at hx
  have hvu := q.h_weighted hu
  change etw W (q.Hmat u) = q.Idw u at hvu
  rw [q.etw16a q.FL W hu,du,q.MB_id] at hvu

  have hcov := q.eq13 hi hf Profile.id_ga (fl_ga hl)
  change KP W q.Amat (q.Hmat f)=_ at hcov
  have ho : ∀ x,deriv w x=f x*deriv i x := by rw [di,dw]; simp
  have hpa := q.f_pair16 (B:=q.FL) hf hi (fl_ga hl) hw ho
  rw [show q.FL.eval i=q.Lmat from funext q.evId,pt_sym] at hpa
  have hk := q.k_l W (q.regH hf)
  have hq := q.kpR W (q.regH hf)
  have hy := (q.sig_split hl).tsum_eq
  change Pt W q.Lmat (q.Hmat f)=q.Iw I+(A w-q.Idw w)-q.be q.FL W f i at hpa
  unfold sigma; rw [hy]
  linarith
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LinTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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
lemma prim_sub (hf:TestF f) (hg:TestF g) :
    prim (fun x=>f x-g x)=fun x=>prim f x-prim g x := by
  ext x; unfold prim; rw [intervalIntegral.integral_sub]; exact hf.cont.intervalIntegrable ..; exact hg.cont.intervalIntegrable ..
lemma pl_sub (hf:TestF f) (hg:TestF g) :
    pl (fun x=>f x-g x)=fun x=>pl f x-pl g x := by
  unfold pl; rw [prim_sub hf hg,ga_sub (p_test hf) (p_test hg)]; ext; ring
lemma N_sub (hf:TestF f) (hg:TestF g) :
    N (fun x=>f x-g x)=fun x=>N f x-N g x := by
  unfold N; rw [drv_sub hf hg,drv_sub hf.der hg.der]; ext; ring
lemma ps_sub (hf:TestF f) (hg:TestF g) :
    ps (fun x=>f x-g x)=fun x=>ps f x-ps g x := by
  unfold ps
  have hh := pl_test hf
  have hi := pl_test hg
  rw [pl_sub hf hg,N_sub hh hi,← prim_sub ((N_test hh).sub hh) ((N_test hi).sub hi)]
  congr 1; ext; ring
end Profile
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
lemma delt_sub {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    q.delt (fun x=>f x-g x)=q.delt f-q.delt g := by
  rw [q.delta_eq (hf.sub hg),q.delta_eq hf,q.delta_eq hg]
  have h : shiftD (fun x=>f x-g x)=fun x=>shiftD f x-shiftD g x := by
    unfold shiftD; rw [drv_sub hf hg]; ext; ring
  have hi (f:ℝ→ℝ) (hf:TestF f) : TestF (shiftD f) := ((((TestF.const _).mul
    TestF.id).mul hf).sub hf.der)
  rw [h]
  simp_rw [mul_sub]
  rw [integral_sub (q.pb_m.int_test hf) (q.pb_m.int_test hg),
    integral_sub (q.rk_m.int_test (hi f hf)) (q.rk_m.int_test (hi g hg))]
  ring
omit [NeZero m] in
lemma ct_sym (u:Plane) : q.ct u.swap=q.ct u := by unfold ct; simp [min_comm,max_comm]
omit [NeZero m] in
lemma Cts {f g:ℝ→ℝ} : q.Ct f g=q.Ct g f := by
  unfold Ct
  let l := fun u:Plane=> q.ct u*(deriv g u.1*deriv f u.2)
  rw [show (∫ u,l u)=(∫ u:Plane,l u.swap) from (integral_prod_swap _).symm]
  congr 1; ext u; unfold l; rw [q.ct_sym,mul_comm (deriv f u.1)]; rfl
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Eq18
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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

lemma fc_pos (h:LayerOK) :
    0≤2*q.Ct (fun x=>x) (fl FF) -
      q.Ct (fl uc) (fl uc)-q.Ct (fl us) (fl us)-q.Ct (fl qu) (fl qu) := by
  let i := fun x:ℝ=> x
  let l := fun (f j:ℝ→ℝ) (u:Plane)=> q.ct u*(deriv f u.1*deriv j u.2)
  have he : 2*q.Ct i (fl FF)=(∫ u,l i (fl FF) u)+∫ u,l (fl FF) i u := by
    change _=q.Ct _ _+q.Ct _ _
    rw [show q.Ct (fl FF) i=q.Ct i (fl FF) from q.Cts]; ring
  rw [show 2*q.Ct _ _=_ from he]
  have hi {f g} (hf:TestF f) (hg:TestF g) := q.Ct_integrable hf hg
  have ha := fl_test h.c_test
  have hb := fl_test h.s_test
  have hc := fl_test h.q_test
  have hd := fl_test h.f_test
  change 0 ≤ _+_-(∫ u,l (fl uc) (fl uc) u)-(∫ u,l (fl us) (fl us) u)-∫ u,l (fl qu) (fl qu) u
  rw [← integral_add,← integral_sub,← integral_sub,← integral_sub]
  · apply integral_nonneg; intro x
    dsimp only [l,i]
    simp_rw [fl_d h.c_test,fl_d h.s_test,fl_d h.q_test,fl_d h.f_test,h.fN,
      deriv_id'',one_mul,mul_one]
    have hh := h.bh_contact x.1 x.2
    have h' := mul_nonneg (q.ct_pos x) hh.le
    change (0:ℝ) ≤ _
    linarith
  all_goals first | exact hi TestF.id hd | exact hi hd TestF.id | exact hi ha ha |
    exact hi hb hb | exact hi hc hc | exact (hi TestF.id hd).add (hi hd TestF.id) |
    exact ((hi TestF.id hd).add (hi hd TestF.id)).sub (hi ha ha) |
    exact (((hi TestF.id hd).add (hi hd TestF.id)).sub (hi ha ha)).sub (hi hb hb)

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

lemma H_be (W:Mat m) (h:LayerOK) :
    q.LLw q.FL W HH=2*q.be q.FL W (fun x=>x) (pl FF)+q.be q.FL W (fl FF) (fun x=>x)-
      2*q.be q.FL W (fl uc) (pl uc)-2*q.be q.FL W (fl us) (pl us)-
      2*q.be q.FL W (fl qu) (pl qu) := by
  let o := q.LLw q.FL W
  have he (l:ℝ→ℝ) (hl:TestF l) :
      o (Hpart l)=2*q.be q.FL W (fl l) (pl l) := by
    unfold o Hpart
    rw [q.Lbar_scale, q.Le_id q.FL W (fl_test hl) (pl_test hl)]

  rw [H_decomp h,
    q.Lbar_sub q.FL W (((wt_Hp h).sub (wt_part h.c_test)).sub (wt_part h.s_test)) (wt_part h.q_test),
    q.Lbar_sub q.FL W ((wt_Hp h).sub (wt_part h.c_test)) (wt_part h.s_test),
    q.Lbar_sub q.FL W (wt_Hp h) (wt_part h.c_test),show q.LLw q.FL W (Hpart uc)=_ from he uc h.c_test,
    show q.LLw q.FL W (Hpart us)=_ from he us h.s_test,show q.LLw q.FL W (Hpart qu)=_ from he qu h.q_test]
  unfold Hp0
  rw [q.Lbar_add q.FL W ((Bwt.const _).mul (wt_deriv TestF.id (pl_test h.f_test)))
    (wt_deriv (fl_test h.f_test) TestF.id),q.Lbar_scale,
    q.Le_id q.FL W TestF.id (pl_test h.f_test),q.Le_id q.FL W (fl_test h.f_test) TestF.id]

lemma LLw_wt_sum (A B:Mat m) {f} (hf:Bwt f) :
    q.LLw q.FL (A+B) f = q.LLw q.FL A f+q.LLw q.FL B f := by
  unfold LLw
  have he (x z) : q.lk q.FL (A+B) f z x=q.lk q.FL A f z x+q.lk q.FL B f z x := by
    unfold lk Pj; rw [add_mul,trN_add]
  simp_rw [he,integral_add (q.lk_slice_i q.FL A hf _) (q.lk_slice_i q.FL B hf _)]
  rw [integral_add (q.Lbar_i q.FL A hf) (q.Lbar_i q.FL B hf)]

theorem entropy_decomp_oai {T:Mat m} (he:1+T=q.covMat) (h:LayerOK) :
    q.delt d-etw T (q.Hmat v) ≤
      q.DelP T + q.sigma FF-q.DVec-q.JVec q.covMat-Pt T q.RR (q.FL.eval (deriv v))-
        q.LLw q.FL 1 HH -
        q.LLw q.FL T (fun u=> HH u+deriv (deriv v) u.2) := by
  let f := fun z=>uc z^2
  let j := fun z=>us z^2
  let k := fun z=>qu z^2
  let W := q.covMat
  have ha : TestF f := sq_test h.c_test
  have hb : TestF j := sq_test h.s_test
  have hc : TestF k := sq_test h.q_test
  have hh : d=fun z=>FF z-f z-j z-k z := by
    funext z
    have hi := u_eq z (h.rp z).le
    unfold f j k; linarith
  have hu : q.delt d=q.delt FF-q.delt f-q.delt j-q.delt k := by
    conv_lhs=>rw [hh]
    rw [q.delt_sub ((h.f_test.sub ha).sub hb) hc,q.delt_sub (h.f_test.sub ha) hb,
      q.delt_sub h.f_test ha]
  have Lh : LDel q.FL W (ps d)=LDel q.FL W (ps FF) - LDel q.FL W (ps f)-
      LDel q.FL W (ps j)-LDel q.FL W (ps k) := by
    conv_lhs=>rw [hh]
    have i' := h.f_test
    have h1 := i'.sub ha
    have h2 := h1.sub hb
    rw [ps_sub h2 hc,Delta_sub q.FL W (ps_test h2) (ps_test hc),
      ps_sub h1 hb,Delta_sub q.FL W (ps_test h1) (ps_test hb),
      ps_sub i' ha, Delta_sub q.FL W (ps_test i') (ps_test ha)]
  have ht : LDel q.FL W (ps d)-LDel q.FL T v=q.DelP T := by
    unfold W
    unfold DelP; rw [Delta_sub q.FL T (ps_test d_test) v_test]
    unfold LDel; rw [← he, etw_add (delta_reg q.FL (ps_test d_test)).ig]
    ring
  have hi : q.LLw q.FL T (fun u:Plane=> deriv (deriv v) u.2)=
      q.be q.FL T (fun x=>x) (deriv v) := by
    simpa using q.Le_id q.FL T TestF.id v_test.der
  rw [q.etw16a q.FL T v_test,q.MB_id,
    q.Lbar_add q.FL T (H_ok h) (Bwt.snd v_test.der.der),hi]
  have HH := q.H_be W h
  have hew : q.LLw q.FL W Profile.HH= q.LLw q.FL 1 Profile.HH+q.LLw q.FL T Profile.HH := by
    unfold W; rw [← he,q.LLw_wt_sum _ _ (H_ok h)]
  have hf := q.form_lin h.f_test
  have hp := q.fc_pos h
  unfold JVec DVec
  change q.LLw q.FL _ _=_ at HH
  linarith [q.form_sq h.q_test,q.form_sq h.c_test,q.form_sq h.s_test]
end ProjField
end GeneralMahler

end

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.ProjField.entropy_decomp_oai := @OAI.GeneralMahler.ProjField.entropy_decomp_oai

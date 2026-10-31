-- Prove2me | solution 1 for OAI.GeneralMahler.Complete_profile_input
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:41:27.101687+00:00
-- url     : https://prove2.me/submissions/5f3aace7-cfd7-4c15-bb3c-9b3bcd2280a0

import Mathlib
import Definitions.Def_OAIQ026G002
import Theorems.Thm_OAI_GeneralMahler_SCal_Eq04full
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_covered
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_gfalse
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_gtrue

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
lemma d_mj (x:ℝ) : HasDerivAt MillsJ (1-MillsW x) x := by
  rw [sub_eq_add_neg]
  exact (hasDerivAt_id' x).add (d_mc x)

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

lemma ddv (x:ℝ) : HasDerivAt (deriv v) (2-MillsW x-MillsW (-x)) x := by
  simp_rw [funext v_deriv]
  convert ((d_mj x).sub ((d_mj (-x)).comp x (hasDerivAt_neg' x))) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | ring
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

lemma k_pos : 0<kk := by unfold kk; apply Real.sqrt_pos.2; norm_num [bb,cc]
lemma k_sq : kk^2=bb-cc := Real.sq_sqrt (by norm_num [bb,cc])
end GeneralMahler.Profile

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
end Profile
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Parity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Parity of Gaussian fields and coefficient projections. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

lemma map_deriv_odd {f:ℝ→ℝ} (hf:TestF f) (h:Function.Odd f) :
    Function.Even (deriv f) := by
  intro x
  have hh := ((hf.diff (-x)).hasDerivAt.comp x (hasDerivAt_neg' x))
  have he : f ∘ (fun x:ℝ=> -x)= -f := funext h
  rw [he] at hh
  have hi := hh.unique ((hf.diff x).hasDerivAt.neg)
  linarith
lemma map_deriv_even {f:ℝ→ℝ} (hf:TestF f) (h:Function.Even f) :
    Function.Odd (deriv f) := by
  intro x
  have hh := ((hf.diff (-x)).hasDerivAt.comp x (hasDerivAt_neg' x))
  have he : f ∘ (fun x:ℝ=> -x)= f := funext h
  rw [he] at hh
  have hi := hh.unique (hf.diff x).hasDerivAt; linarith

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_FinalR
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
lemma Veven : Function.Even Profile.v := by
  intro x; rw [v_log,v_log,neg_neg]; ring
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Basic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Jet.instZeroIV
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
Fixed-denominator rational interval certificates (§07–08).
Unknown intervals admit all real values.
-/
namespace GeneralMahler.Cert

namespace IV

lemma dpos : 0<den := by decide
lemma rpos : 0<(den:ℝ) := by exact_mod_cast dpos
lemma w_mono : Monotone w := by
  intro a b h; apply div_le_div_of_nonneg_right _ rpos.le; exact_mod_cast h
lemma w_strict : StrictMono w := by
  intro a b h; apply div_lt_div_of_pos_right _ rpos; exact_mod_cast h
lemma w_max (a b:Int) : w (max a b)=max (w a) (w b) := w_mono.map_max
lemma w_min (a b:Int) : w (min a b)=min (w a) (w b) := w_mono.map_min
lemma w_add (a b:Int) : w (a+b)=w a+w b := by unfold w; push_cast; ring
lemma w_neg (a:Int): w (-a)= -w a:= by unfold w; push_cast; ring
lemma w0 : w 0=0 := by simp [w]

lemma mc (a:Int) : (a:ℝ)∈c a := by
  change _≤ _ ∧ _ ≤ _
  unfold w
  push_cast; rw [mul_div_cancel_right₀ _ rpos.ne']; exact ⟨le_rfl,le_rfl⟩
lemma nc (n:ℕ) : (n:ℝ)∈c (n:Int) := by simpa using mc (n:Int)
lemma mz : (0:ℝ) ∈ (0:IV) := by change (0:ℝ) ∈ c (Int.ofNat 0); simpa using mc (Int.ofNat 0)
lemma mo : (1:ℝ)∈(1:IV) := by change (1:ℝ) ∈ c (Int.ofNat 1); simpa using mc (Int.ofNat 1)
variable {u v:ℝ} {A B:IV}
lemma madd (hu:u∈A) (hv:v∈B) :
    u+v∈A+B := by
  cases A <;> cases B <;> first | trivial | skip
  rename_i a b c d
  change w _ ≤ _ ∧ _ ≤ w _
  rw [w_add,w_add]
  exact ⟨add_le_add hu.1 hv.1, add_le_add hu.2 hv.2⟩
lemma mneg (hu:u∈A) : -u∈-A := by
  cases A
  · trivial
  change w _ ≤ _ ∧ _ ≤ w _
  rw [w_neg,w_neg]; exact ⟨neg_le_neg hu.2,neg_le_neg hu.1⟩
lemma msub (hu:u∈A) (hv:v∈B) :
    u-v∈A-B := by rw [sub_eq_add_neg]; exact madd hu (mneg hv)
lemma lower_div (a b:Int) (h:0<b):
    ((a/b:Int):ℝ)≤ (a:ℝ)/(b:ℝ) := by
  apply (le_div_iff₀ (show (0:ℝ)<b from by exact_mod_cast h)).mpr
  exact_mod_cast Int.ediv_mul_le a h.ne'
lemma upper_div (a b:Int) (h:0<b):
    (a:ℝ)/(b:ℝ)≤(ud a b:ℝ) := by
  have he:=lower_div (-a) b h
  push_cast at he
  unfold ud; push_cast; rw [neg_div] at he; linarith

lemma product_box (a b c d:ℝ) (ha:a≤u) (hb:u≤b) (hc:c≤v) (hd:v≤d):
    min (min (a*c) (a*d)) (min (b*c) (b*d))≤ u*v ∧
      u*v≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hi (r:ℝ): min (r*c) (r*d) ≤ r*v ∧ r*v≤ max (r*c) (r*d) := by
    rcases le_total 0 r with h|h
    · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hc h),
        le_trans (mul_le_mul_of_nonneg_left hd h) (le_max_right _ _)⟩
    exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hd h),
      le_trans (mul_le_mul_of_nonpos_left hc h) (le_max_left _ _)⟩
  rcases le_total 0 v with h|h
  · exact ⟨le_trans (min_le_left _ _) ((hi _).1.trans (mul_le_mul_of_nonneg_right ha h)),
      le_trans ((mul_le_mul_of_nonneg_right hb h).trans (hi _).2) (le_max_right _ _)⟩
  exact ⟨le_trans (min_le_right _ _) ((hi _).1.trans (mul_le_mul_of_nonpos_right hb h)),
      le_trans ((mul_le_mul_of_nonpos_right ha h).trans (hi _).2) (le_max_left _ _)⟩

lemma wdn (a:Int): w (a/den) ≤ w a / den :=
  div_le_div_of_nonneg_right (lower_div a den dpos) rpos.le
lemma wup (a:Int): w a / den ≤ w (ud a den) :=
  div_le_div_of_nonneg_right (upper_div a den dpos) rpos.le
lemma wm (a b:Int): w (a*b)/(den:ℝ)=w a*w b := by unfold w; push_cast; ring

lemma mmul (hu:u∈A) (hv:v∈B) : u*v∈ A*B := by
  cases A <;> cases B <;> first| trivial|skip
  rename_i a b c d
  let l := min (min (a*c) (a*d)) (min (b*c) (b*d))
  let h := max (max (a*c) (a*d)) (max (b*c) (b*d))
  change w (l/den)≤_ ∧ _ ≤ w (ud h den)
  have he : Monotone (fun a=>w a/(den:ℝ)) :=
    fun a b ha=> div_le_div_of_nonneg_right (w_mono ha) rpos.le
  have hmin (a b:Int) : w (min a b)/den=min (w a/den) (w b/den) := he.map_min
  have hmax (a b:Int) : w (max a b)/den=max (w a/den) (w b/den) := he.map_max
  have hp:= product_box (w a) (w b) (w c) (w d) hu.1 hu.2 hv.1 hv.2
  refine ⟨(wdn l).trans ?_,le_trans ?_ (wup h)⟩
  · unfold l; simp_rw [hmin,wm]; exact hp.1
  unfold h; simp_rw [hmax,wm]; exact hp.2

lemma mposInv (a b:Int) (h:0<a) (hu:u∈box a b) : u⁻¹∈posInv a b := by
  have ha : 0<w a := w0 ▸ w_strict h
  have hp : 0<u := lt_of_lt_of_le ha hu.1
  have hh : 0<w b := lt_of_lt_of_le hp hu.2
  have hb : 0<b := w_strict.lt_iff_lt.mp (by rwa [w0])
  change w _ ≤ _ ∧ _≤ w _
  have H (a:Int): (((den*den:Int):ℝ)/(a:ℝ))/(den:ℝ)=(w a)⁻¹ := by
    unfold w; push_cast; rw [inv_div]; field_simp
  refine ⟨le_trans ?_ ((inv_le_inv₀ hh hp).mpr hu.2),
    le_trans ((inv_le_inv₀ hp ha).mpr hu.1) ?_⟩
  · rw [← H]; exact div_le_div_of_nonneg_right (lower_div _ _ hb) rpos.le
  rw [← H]; exact div_le_div_of_nonneg_right (upper_div _ _ h) rpos.le

lemma minv (hu:u∈A) : u⁻¹∈A⁻¹ := by
  cases A
  · trivial
  rename_i a b
  change _∈ if a>0 then _ else if b<0 then _ else _
  split
  next h=> exact mposInv a b h hu
  split
  next h=>
    have hi : -u∈box (-b) (-a):=mneg hu
    simpa only [inv_neg,neg_neg] using mneg (mposInv (-b) (-a) (neg_pos.mpr h) hi)
  trivial

lemma mdiv (hu:u∈A) (hv:v∈B): u/v∈A/B := by rw [div_eq_mul_inv]; exact mmul hu (minv hv)
lemma mpow (hu:u∈A) (n:ℕ): u^n∈A^n := by
  induction n with
  | zero=> rw [pow_zero]; exact mo
  | succ n ih=> rw [pow_succ]; exact mmul ih hu

lemma mle (hu:u∈A) (hv:v∈B) (he:LeB A B=true): u≤v := by
  cases A <;> cases B <;> simp only [LeB,Bool.false_eq_true,decide_eq_true_eq] at he
  exact hu.2.trans ((w_mono he).trans hv.1)
lemma mlt (hu:u∈A) (hv:v∈B) (he:Less A B=true): u<v := by
  cases A <;> cases B <;> simp only [Less,Bool.false_eq_true,decide_eq_true_eq] at he
  exact lt_of_le_of_lt hu.2 (lt_of_lt_of_le (w_strict he) hv.1)
lemma subB (hu:u∈A) (he:SubB A B=true): u∈B := by
  cases B
  · trivial
  cases A
  · contradiction
  simp only [SubB,Bool.and_eq_true,decide_eq_true_eq] at he
  exact ⟨(w_mono he.1).trans hu.1,hu.2.trans (w_mono he.2)⟩

lemma mmax (hu:u∈A) (hv:v∈B): max u v∈Zmax A B := by
  cases A <;> cases B <;> first| trivial|skip
  change w _ ≤ _ ∧ _ ≤ w _
  rw [w_max,w_max]
  exact ⟨max_le_max hu.1 hv.1,max_le_max hu.2 hv.2⟩
lemma mclamp (hu:u∈A) (hh:0≤u): u∈clampNN A := by
  cases A
  · trivial
  refine ⟨?_,hu.2⟩
  rw [w_max,w0]; exact max_le hh hu.1
lemma mabs (hu:u∈A): |u|∈Zabs A := mclamp (mmax hu (mneg hu)) (abs_nonneg _)
lemma msq (hu:u∈A) : u^2∈sq A := by
  have h:=mmul (mabs hu) (mabs hu)
  rwa [← pow_two,sq_abs] at h
lemma span_conv {x:ℝ} (hu:u∈A) (hv:v∈B) (he:u≤x) (ht:x≤v): x∈span A B := by
  cases A <;> cases B <;> first| trivial|skip
  refine ⟨?_,?_⟩
  · rw [w_min]; exact (min_le_left _ _).trans (hu.1.trans he)
  rw [w_max]; exact ht.trans (hv.2.trans (le_max_right _ _))

end IV
end GeneralMahler.Cert

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Jet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Real and interval towers of higher derivatives. -/
open Set Filter
open scoped Topology
namespace GeneralMahler.Jet
variable {S T:Set ℝ} {X Y W:RF}

lemma TW.tail (h:TW S X): TW S fun x=>Jet.tail (X x) := fun n x hx=>h (n+1) x hx
lemma TW.add (h:TW S X) (g:TW S Y): TW S fun x=>plusJ (X x) (Y x) :=
  fun n x hx=>(h n x hx).fun_add (g n x hx)
lemma TW.sub (h:TW S X) (g:TW S Y): TW S fun x=>subJ (X x) (Y x) :=
  fun n x hx=>(h n x hx).fun_sub (g n x hx)
lemma TW.neg (h:TW S X): TW S fun x=>negJ (X x) := fun n x hx=>(h n x hx).neg
lemma TW.const (a:ℝ) : TW S fun _=>ray a := by
  intro n x hx; cases n with
  | zero=> exact hasDerivAt_const x a
  | succ n=> exact hasDerivAt_const x (0:ℝ)
lemma TW.mul (h:TW S X) (g:TW S Y): TW S fun x=>mulJ (X x) (Y x) := by
  intro n x hx; induction n generalizing X Y with
  | zero=> exact (h 0 x hx).fun_mul (g 0 x hx)
  | succ n ih=>
    exact (ih h.tail g).fun_add (ih h g.tail)

lemma TW.cp (h:TW S X) (g:TW T W) (hh:TW S Y) (he:∀ x∈S,X x 0∈T):
    TW S fun x n=> cpM n (W (X x 0)) (X x) (Y x) := by
  intro n x hx
  induction n generalizing Y W with
  | zero=>
    have ha := ((g 0 (X x 0) (he x hx)).comp x (h 0 x hx)).fun_mul (hh 0 x hx)
    convert ha using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first|rfl| (simp only [cpM,Jet.tail,mulJ,mulJ0,Function.comp_apply]; ring)
  | succ n ih=>
    exact (ih g.tail (h.tail.mul hh)).fun_add (ih g hh.tail)
lemma TW.comp (h:TW S X) (g:TW T W) (he:∀ x∈S,X x 0∈T):
    TW S fun x=>compJ (W (X x 0)) (X x) := by
  intro n x hx; cases n with
  | zero=> exact (g 0 _ (he x hx)).comp x (h 0 x hx)
  | succ n=> exact TW.cp h g.tail h.tail he n x hx

lemma V_eq (h:TW S X) (hs:IsOpen S) (n:Nat):
    EqOn (dV (fun x=>X x 0) n) (fun x=>X x n) S := by
  induction n with
  | zero=> exact fun _ _=>rfl
  | succ n ih=>
    intro x hx
    change deriv (dV _ n) _ = _
    have he : dV (fun x=>X x 0) n =ᶠ[𝓝 x] (fun x=>X x n) :=
      (show ∀ᶠ y in 𝓝 x,y∈S from hs.mem_nhds hx).mono fun y hy=> ih hy
    exact (he.deriv_eq).trans (h n x hx).deriv

open Cert Cert.IV
variable {U V F:J ℝ} {A B C:J IV}
lemma Fits.ray {x:ℝ} {a:IV} (h:x∈a): Fits (Jet.ray x) (Jet.ray a) := by
  intro n; cases n with
  | zero=>exact h
  | succ n=>exact mz
lemma Fits.drop (h:Fits U A): Fits (tail U) (tail A) := fun n=> h (n+1)
lemma Fits.add (h:Fits U A) (g:Fits V B) : Fits (plusJ U V) (plusJ A B) :=
  fun n=> madd (h n) (g n)
lemma Fits.sub (h:Fits U A) (g:Fits V B) : Fits (subJ U V) (subJ A B) :=
  fun n=> msub (h n) (g n)
lemma Fits.neg (h:Fits U A): Fits (negJ U) (negJ A):= fun n=> mneg (h n)
lemma Fits.mul (h:Fits U A) (g:Fits V B): Fits (mulJ U V) (mulJ A B) := by
  intro n; induction n generalizing U V A B with
  | zero=> exact mmul (h 0) (g 0)
  | succ n ih=> exact madd (ih h.drop g) (ih h g.drop)
lemma Fits.cp (h:Fits U A) (g:Fits V B) (hh:Fits F C) (n:ℕ):
    cpM n F U V∈ cpM n C A B := by
  induction n generalizing F V C B with
  | zero=> exact mmul (hh 0) (g 0)
  | succ n ih=> exact madd (ih (h.drop.mul g) hh.drop) (ih g.drop hh)
lemma Fits.comp (h:Fits U A) (g:Fits F C): Fits (compJ F U) (compJ C A) := by
  intro n; cases n with
  | zero=> exact g 0
  | succ n=> exact Fits.cp h h.drop g.drop n
end GeneralMahler.Jet

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Elem
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Jet.instZeroIV
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interval square root and exponential. -/
namespace GeneralMahler.Cert.IV
lemma mpi : Real.pi ∈ piB := by
  have h₁ := Real.pi_gt_d20; have h₂:=Real.pi_lt_d20
  change w _ ≤ _ ∧ _ ≤ w _
  norm_num [w,den] at *
  constructor <;> linarith

private lemma callSq (q a:Int): w q^2-w a=((q*q-a*den:Int):ℝ)/(den:ℝ)^2 := by
  unfold w; push_cast; field_simp
private lemma Lsq {a q:Int} (h:0< a) (hh:q*q≤a*den): w q ≤ Real.sqrt (w a) := by
  have hi : w q^2≤w a := by
    rw [← sub_nonpos,callSq]
    apply div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    exact_mod_cast (sub_nonpos.mpr hh)
  have hp : 0≤w a := by have h := w_strict h; rw [w0] at h; exact h.le
  nlinarith [Real.sq_sqrt hp,Real.sqrt_nonneg (w a)]
private lemma Usq {a q:Int} (hq:0≤q) (h:0≤a) (hh:a*den≤q*q) :
    Real.sqrt (w a) ≤ w q := by
  have hi : w a≤w q^2 := by
    rw [← sub_nonneg,callSq]
    apply div_nonneg ?_ (sq_nonneg _)
    exact_mod_cast (sub_nonneg.mpr hh)
  have hp (a:Int) (ha:0≤a) : 0≤w a := by have h:=w_mono ha; rwa [w0] at h
  nlinarith [Real.sq_sqrt (hp a h),hp q hq,Real.sqrt_nonneg (w a)]
lemma mrt {x:ℝ} {A:IV} (h:x∈A) : Real.sqrt x ∈ rtB A := by
  cases A
  · trivial
  rename_i a b
  rw [rtB]
  split
  next hh=>
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at hh
    change w _ ≤ _ ∧ _≤ w _
    refine ⟨?_,le_trans (Real.sqrt_le_sqrt (le_trans h.2 (w_mono (le_max_left b 0))))
      (Usq hh.1.1 (le_max_right b 0) hh.1.2)⟩
    unfold rlo at *
    by_cases he: a>0
    · have hj := (hh.2.resolve_left (not_le.mpr he)).2
      rw [ite_eq_left he] at hj ⊢
      exact le_trans (Lsq he hj) (Real.sqrt_le_sqrt h.1)
    rw [ite_eq_right he,w0]; apply Real.sqrt_nonneg
  trivial

open Finset
lemma mSeries {x:ℝ} {A:IV} (h:x∈A) (n:Nat):
    x^n/n.factorial∈(eSeries A n).1∧
      (∑ m∈range n,x^m/m.factorial)∈(eSeries A n).2 := by
  induction n with
  | zero => simpa [eSeries] using (And.intro mo mz)
  | succ n ih =>
    unfold eSeries
    refine ⟨?_,?_⟩
    · have he := mdiv (mmul ih.1 h) (nc (n+1))
      have hi : x^(n+1)/(n+1).factorial=(x^n/n.factorial*x)/(n+1:Nat) := by
        rw [Nat.factorial_succ,pow_succ]; push_cast; field_simp
      rw [hi]
      exact he
    rw [Finset.sum_range_succ]; exact madd ih.2 ih.1

lemma mesmall {x:ℝ} {A:IV} (h:x∈A) (hx:|x|≤1) :
    Real.exp x ∈ IV.esmall A := by
  let v:ℝ:=∑ m∈range 25,x^m/m.factorial
  have hp : Real.exp x-v ∈ terr := by
    have he := Real.exp_bound hx (show 0<25 by decide)
    have hh : |x|^25 ≤1 := pow_le_one₀ (_root_.abs_nonneg x) hx
    change w _ ≤ _ ∧ _ ≤ w _
    have hm : |Real.exp x-v| ≤ _ := he
    have hr : (0:ℝ)< (↑(25+1:ℕ):ℝ) / (((25:ℕ).factorial:ℝ)* ((25:ℕ):ℝ)) := by positivity
    have hi := abs_le.mp hm
    norm_num [w,den,Nat.factorial] at *
    constructor <;> linarith
  apply mclamp _ (Real.exp_pos x).le
  have he := madd (mSeries h 25).2 hp
  rwa [show v+(Real.exp x-v)=Real.exp x by ring] at he

lemma mebox {x:ℝ} (n:ℕ) {A:IV} (h:x∈A): Real.exp x∈ebox n A := by
  induction n generalizing x A with
  | zero=>
    rw [ebox]
    split
    next he=> exact mesmall h (mle (mabs h) mo he)
    trivial
  | succ n ih=>
    rw [ebox]
    split
    next he=> exact mesmall h (mle (mabs h) mo he)
    have htwo : (2:ℝ)∈(2:IV) := mc 2
    have he:=ih (mdiv h htwo)
    apply (show Real.exp (x/2)*Real.exp (x/2)=Real.exp x by rw [← Real.exp_add]; congr 1; ring) ▸ mmul he he
end GeneralMahler.Cert.IV

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Log
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Jet.instZeroIV
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.Cert.IV
open Real Finset

lemma mtwo : (2:ℝ)∈(2:IV) := mc 2
lemma mhalf : (1/2:ℝ)∈(1/2:IV) := mdiv mo mtwo

lemma mseriesL {y:ℝ} {Y:IV} (hy:y∈Y) (n:ℕ) :
    y^(2*n+1)∈(seriesL Y n).1 ∧
      (∑ i∈range n, y^(2*i+1)/(↑(2*i+1:Nat):ℝ))∈(seriesL Y n).2 := by
  induction n with
  | zero=> simpa [seriesL] using (And.intro hy mz)
  | succ n ih=>
    rw [seriesL,sum_range_succ]
    have he:= mmul ih.1 (msq hy)
    refine ⟨?_,madd ih.2 (mdiv ih.1 (nc _))⟩
    rw [show 2*(n+1)+1=(2*n+1)+2 by omega, pow_add]
    exact he
lemma mlbox0 {x:ℝ} {X:IV} (hx:x∈X) (he:lob X=true) :
    Real.log x∈ lbox0 X := by
  let y:=(x-1)/(x+1)
  have hh : y∈logY X := mdiv (msub hx mo) (madd hx mo)
  simp only [lob,Bool.and_eq_true] at he
  obtain ⟨hu,hv⟩ := he
  have hp := mlt mz hx hu
  have ht := mle (mabs hh) mhalf hv
  change |y| ≤1/2 at ht
  have h₁ : (1+y)/(1-y) = x := by unfold y; field_simp; ring
  have h₂ : |y|<1 := by linarith
  let P:=∑ i∈range 32,y^(2*i+1)/(↑(2*i+1:Nat):ℝ)
  have hi : 1/2*Real.log x-P∈errLog := by
    have he:= Real.sum_range_sub_log_div_le h₂ 32
    rw [h₁] at he
    have hi : |1/2*Real.log x-P|≤ |y|^(2*32+1)/(1-y^2) := by
      convert he using 2
      all_goals try with_reducible_and_instances rfl
      unfold P; push_cast; rfl
    have hv : |y|^(2*32+1)/(1-y^2)≤ ((1/2:ℝ)^(2*32+1))/(1-(1/2:ℝ)^2) := by
      have h₁ : y^2≤ (1/2:ℝ)^2 := sq_le_sq.2 (by simpa using ht)
      gcongr
    have hh:=abs_le.mp (le_trans hi hv)
    change w _ ≤ _ ∧ _ ≤ w _
    norm_num [w,den] at *
    constructor <;> linarith
  apply (show 2*(P+(1/2*Real.log x-P))=Real.log x by ring) ▸
    mmul mtwo (madd (mseriesL hh _).2 hi)

lemma mlbox {x:ℝ} {A:IV} (h:x∈A) (n:ℕ) :
    Real.log x∈ lbox n A := by
  induction n generalizing A x with
  | zero=>
    rw [lbox]; split
    next hh=> exact mlbox0 h hh
    trivial
  | succ n ih=>
    rw [lbox]; split
    next he=>
      split
      next hh=> exact mlbox0 h hh
      have hp : 0<x := mlt mz h he
      have hi:=Real.log_sqrt hp.le
      have heq : 2*Real.log (Real.sqrt x) = Real.log x := by linarith
      exact heq ▸ mmul mtwo (ih (mrt h))
    trivial
end GeneralMahler.Cert.IV

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_JCalc
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Tower AD for exp, log, inverse, square root. -/
open Set Real
namespace GeneralMahler.Jet

lemma twInvs : TW {x:ℝ|x≠0} (invJs vn) := by
  intro n x hx; change x≠0 at hx
  induction n with
  | zero=>
    convert (hasDerivAt_id' x).inv hx using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl|skip
    simp [invJs,vn]; ring
  | succ n ih=>
    have he:= ((((hasDerivAt_id' x).inv hx).const_mul (vn (n+1))).fun_mul ih).neg
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first|rfl|skip
    rw [invJs,invJs]
    unfold vn; push_cast
    simp; ring

lemma twRoots : TW {x:ℝ|0<x} (fun x=>rootJs (1/2:ℝ) vn x (Real.sqrt x)) := by
  intro n x hx; change 0<x at hx
  induction n with
  | zero=>
    have hp := Real.sqrt_pos.mpr hx
    convert Real.hasDerivAt_sqrt hx.ne' using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first|rfl|skip
    simp only [rootJs,vn,Nat.cast_zero,sub_zero]
    have hi:= Real.sq_sqrt hx.le
    field_simp
    linarith
  | succ n ih=>
    have he:= ((((hasDerivAt_id' x).inv hx.ne').const_mul ((1/2:ℝ)-vn n)).fun_mul ih)
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first|rfl|skip
    simp only [rootJs]; unfold vn; push_cast; simp; ring
lemma twLogs : TW {x:ℝ|x≠0} (fun x=>logJs vn x (Real.log x)) := by
  intro n x hx; cases n with
  | zero=>exact (by convert Real.hasDerivAt_log hx using 1 <;> rfl)
  | succ n=> exact twInvs n x hx
variable {S:Set ℝ} {X:RF}
lemma TW.inv (h:TW S X) (hx:∀ x∈S, X x 0 ≠ 0): TW S fun x=> invSub vn (X x) := h.comp twInvs hx
lemma TW.root (h:TW S X) (hx:∀ x∈S, 0<X x 0):
    TW S fun x=> rootSub (1/2) vn (X x) (Real.sqrt (X x 0)) := h.comp twRoots hx
lemma TW.log (h:TW S X) (hx:∀ x∈S,X x 0≠ 0): TW S fun x=> logSub vn (X x) (Real.log (X x 0)):=
  h.comp twLogs hx
lemma TW.exp (h:TW S X) :
    TW S fun x=> expSub (X x) (Real.exp (X x 0)) :=
  h.comp (show TW univ fun x _=>Real.exp x from fun _ x _=>Real.hasDerivAt_exp x)
    (fun _ _=> mem_univ _)

open Cert Cert.IV
lemma ubb (n:ℕ):vn n∈ub n := nc n
variable {V:J ℝ} {A:J IV}

lemma fitsInv {x:ℝ} {y:IV} (h:x∈y): Fits (invJs vn x) (invJs ub y) := by
  intro n; induction n with
  | zero=> exact minv h
  | succ n ih=> exact mneg (mmul (mmul (ubb _) (minv h)) ih)
lemma Fits.inv (h:Fits V A):Fits (invSub vn V) (invSub ub A) :=
  Fits.comp h (fitsInv (h 0))
lemma Fits.rt (h:Fits V A){B} (hh:Real.sqrt (V 0)∈B):
    Fits (rootSub (1/2) vn V (Real.sqrt (V 0))) (rootSub (1/2) ub A B) := by
  apply Fits.comp h
  intro n; induction n with
  | zero=> exact hh
  | succ n ih=> exact mmul (mmul (msub mhalf (ubb _)) (minv (h _))) ih
lemma Fits.log (h:Fits V A){B} (hh:Real.log (V 0)∈B):
    Fits (logSub vn V (Real.log (V 0))) (logSub ub A B) :=
  Fits.comp h (by
    intro n; cases n with
    | zero=>exact hh
    | succ n=>exact fitsInv (h 0) n)
lemma Fits.exp (h:Fits V A){B}(hh:Real.exp (V 0)∈B):
    Fits (expSub V (Real.exp (V 0))) (expSub A B) :=
  Fits.comp h fun _=>hh
end GeneralMahler.Jet

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Chord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interpolation/range certificate through second derivatives. -/
open Set Filter Real
namespace GeneralMahler
namespace Jet
variable {f g h:ℝ→ℝ}

lemma convex_err_upper (hf:∀ x,HasDerivAt f (g x) x)
    (hg:∀ x,HasDerivAt g (h x) x) {x y a:ℝ} (hm:x≤y) (ha:a∈Set.Icc (0:ℝ) 1)
    (K:ℝ) (hK:0≤K) (he:∀ z∈Set.Icc x y,-K ≤ h z):
    f (mix x y a)-mix (f x) (f y) a≤K/8*(y-x)^2 := by
  let b := fun x=> K/2*x*x
  let u := fun x=> f x+b x
  let v := fun x=> g x+K*x
  have h₁(x:ℝ): HasDerivAt u (v x) x := by
    apply (hf x).fun_add
    convert ((((hasDerivAt_id' x).const_mul (K/2)).mul (hasDerivAt_id' x))) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first|rfl|ring
  have h₂(x:ℝ): HasDerivAt v (h x+K) x := by
    apply (hg x).fun_add
    convert ((hasDerivAt_id' x).const_mul K) using 1 <;> first|rfl|ring
  have hu := convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc x y)
    (f:=u) (f':=v) (f'':=fun x=>h x+K) (fun x _=> (h₁ x).continuousAt.continuousWithinAt)
    (fun x _=> (h₁ x).hasDerivWithinAt) (fun x _=> (h₂ x).hasDerivWithinAt)
    (fun z hz=> by linarith [he z (interior_subset hz)])
  have ht:= hu.2 (show x∈Set.Icc x y from ⟨le_rfl,hm⟩) (show y∈Set.Icc x y from ⟨hm,le_rfl⟩)
    (sub_nonneg.mpr ha.2) ha.1 (sub_add_cancel 1 a)
  change u (mix x y a) ≤ mix (u x) (u y) a at ht
  have hv : mix (u x) (u y) a = mix (f x) (f y) a+mix (b x) (b y) a := by unfold mix u;ring
  rw [hv] at ht
  have hh : mix (b x) (b y) a-b (mix x y a)=K/2*(y-x)^2*(a*(1-a)):=by unfold mix b; ring
  have hp:= mul_le_mul_of_nonneg_left (show a*(1-a) ≤ 1/4 from by nlinarith [sq_nonneg (a-1/2)])
    (show 0≤ K/2*(y-x)^2 from by positivity)
  change f (mix x y a)+ _≤ _ at ht
  linarith

lemma chord_error (hf:∀ x,HasDerivAt f (g x) x)
    (hg:∀ x,HasDerivAt g (h x) x) {x y a:ℝ} (hm:x≤y) (ha:a∈Set.Icc (0:ℝ) 1)
    (K:ℝ) (hK:0≤K) (he:∀ z∈Set.Icc x y,|h z| ≤ K):
    |f (mix x y a)-mix (f x) (f y) a|≤K/8*(y-x)^2 := by
  have h:= convex_err_upper hf hg hm ha K hK fun z hz=> (abs_le.mp (he z hz)).1
  have h₁:= convex_err_upper (fun x=>(hf x).neg) (fun x=>(hg x).neg) hm ha K hK (fun z hz=> neg_le_neg (le_of_abs_le (he z hz)))
  apply abs_le.mpr
  refine ⟨?_,h⟩
  change -f _-mix (-f x) (-f y) _≤_ at h₁; unfold mix at *; linarith
lemma mix_exists {x y z:ℝ} (h:x≤z) (he:z≤y) :
    ∃ a∈Set.Icc (0:ℝ) 1,z=mix x y a := by
  rcases lt_or_eq_of_le (h.trans he) with ht|ht
  · refine ⟨(z-x)/(y-x),⟨div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith)⟩,?_⟩
    unfold mix; field_simp; ring
  have hz:= le_antisymm h (he.trans ht.symm.le)
  exact ⟨0,⟨le_rfl,zero_le_one⟩,by simp [mix,hz]⟩
end Jet
namespace Cert.IV
open Jet

lemma box_mix {A B:IV} {x y:ℝ} (h:x∈A) (hh:y∈B) {c:ℝ} (hc:c∈Set.Icc (0:ℝ) 1):
    mix x y c∈ IV.span A B := by
  rcases le_total x y with he|he
  · apply span_conv h hh
    all_goals unfold mix; nlinarith [hc.1,hc.2]
  have hx : IV.span A B= IV.span B A := by cases A <;> cases B <;> simp [IV.span,max_comm,min_comm]
  rw [hx]
  apply span_conv hh h
  all_goals unfold mix; nlinarith [hc.1,hc.2]

private lemma lk_pos (a b:Int) : 0≤ w (max (-a) (max 0 b)) :=
  w0 ▸ (w_mono ((le_max_left ..).trans (le_max_right ..)))
private lemma lk_e (a b:Int) {x:ℝ} (ha:x∈box a b): |x|≤ w (max (-a) (max 0 b)) := by
  rw [w_max,w_max,w_neg,w0]
  rw [abs_le]; constructor
  · have hx:w a≤ x:=ha.1
    have hi: -w a ≤ max (-w a) (max 0 (w b)) := le_max_left ..
    linarith
  exact ha.2.trans ((le_max_right ..).trans (le_max_right ..))

lemma mcChord (X:RF) (h:TW univ X) (n:ℕ) (x y z:ℝ) (hx:x ≤ z)
    (hy:z≤y) (A B D F:IV)
    (ha:X x n∈A) (hb:X y n∈B) (hd:y-x∈D)
    (hf:∀ z∈Set.Icc x y,X z (n+2) ∈ F):
    X z n∈ bcChord D A B F := by
  cases F
  · cases D <;> cases A <;> cases B <;> trivial -- IV.mul on sq etc defeq maybe
  rename_i a b
  let K:= w (max (-a) (max 0 b))
  have hm : K∈limK (box a b):= ⟨le_rfl,le_rfl⟩
  have he8: (8:ℝ)∈ IV.c 8 := mc 8
  have hr:=mmul (mdiv hm he8) (msq hd)
  let r:= Radius D (box a b)
  obtain ⟨c,hc,hcx⟩:= mix_exists hx hy
  have he:= chord_error (fun t=>h n t (mem_univ _)) (fun t=>h (n+1) t (mem_univ _)) (hx.trans hy)
    hc K (lk_pos _ _) (fun t ht=> lk_e a b (hf t ht))
  change |X _ n-_| ≤ _ at he
  rw [← hcx] at he
  have hi:= abs_le.mp he
  have hh:= madd (box_mix ha hb hc) (span_conv (mneg hr) hr hi.1 hi.2)
  exact (show mix (X x n) (X y n) c + (X z n - mix (X x n) (X y n) c) = X z n by ring) ▸ hh
end Cert.IV
end GeneralMahler

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Trig
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Jet.instZeroIV
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.Cert.IV
open Complex Finset

lemma misum {x:ℝ} {X:IV} (hx:x∈X) (n):
    let t : ℕ→ℂ:=fun k=>(↑x*I)^k/k.factorial
    covers (isum X n).1 (t n) ∧ covers (isum X n).2 (∑ i∈range n,t i) := by
  intro t; induction n with
  | zero=>
    simp only [isum,t,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,sum_range_zero]
    exact ⟨⟨mo,mz⟩,⟨mz,mz⟩⟩
  | succ n ih=>
    let a:ℝ:=x/((n+1:Nat):ℝ)
    have ha:a∈ (X / c (Int.ofNat (n+1))) := mdiv hx (nc (n+1))
    have he : t (n+1)= t n*a*I := by unfold t a; rw [pow_succ,Nat.factorial_succ]; push_cast; field_simp
    have h1 : (t (n+1)).re= -((t n).im*a) := by rw [he]; simp
    have h2 : (t (n+1)).im=(t n).re*a := by rw [he]; simp
    constructor
    · refine ⟨?_,?_⟩
      · rw [h1]; exact mneg (mmul ih.1.2 ha)
      rw [h2]; exact mmul ih.1.1 ha
    rw [sum_range_succ]
    exact ⟨madd ih.2.1 ih.1.1,madd ih.2.2 ih.1.2⟩

lemma msmallsc {x:ℝ} {X:IV} (hx:x∈X) (h:|x|≤1) :
    Real.cos x∈(smallsc X).1∧Real.sin x∈(smallsc X).2 := by
  let y := (x:ℂ)* I
  have he : ‖y‖=|x| := by simp [y]
  let v:ℂ:=∑ i∈range 25,y^i/i.factorial
  let R:= Complex.exp y-v
  have hp := Complex.exp_bound (x:=y) (by rwa [he]) (show 0<25 by decide)
  have hw : ‖R‖ ≤_ := hp
  have hr {x:ℝ} (hx:|x| ≤ ‖R‖):x∈terr := by
    have h1:= abs_le.mp hx
    have h2 := pow_le_one₀ (_root_.abs_nonneg _) h (n:=25)
    change w _ ≤ _ ∧ _ ≤ w _
    rw [he] at hw
    norm_num [w,den,Nat.factorial] at *
    constructor <;> linarith
  have hv:= misum hx 25
  change _ ∧ covers _ v at hv
  have hi : covers (smallsc X) (Complex.exp y) := by
    rw [show Complex.exp y=v+R from by unfold R; ring]
    exact ⟨madd hv.2.1 (hr (abs_re_le_norm R)),madd hv.2.2 (hr (abs_im_le_norm R))⟩
  unfold y covers at hi
  simpa using hi

lemma mtrbox {x:ℝ} {X:IV} (hx:x∈X) (n:ℕ) :
    Real.cos x∈(trbox n X).1 ∧ Real.sin x∈(trbox n X).2 := by
  induction n generalizing x X with
  | zero=>
    rw [trbox]; split
    next he=> exact msmallsc hx (mle (mabs hx) mo he)
    exact ⟨trivial,trivial⟩
  | succ n ih=>
    rw [trbox]; split
    next he=> exact msmallsc hx (mle (mabs hx) mo he)
    obtain ⟨H,G⟩:= ih (mdiv hx mtwo)
    have ha : Real.cos x=Real.cos (x/2)^2-Real.sin (x/2)^2 := by
      conv_lhs=> rw [show x=x/2+x/2 from by ring,Real.cos_add]
      ring
    have hb : Real.sin x=2*Real.cos (x/2)*Real.sin (x/2) := by
      conv_lhs=> rw [show x=x/2+x/2 from by ring,Real.sin_add]
      ring
    rw [ha,hb]; exact ⟨msub (msq H) (msq G),mmul (mmul mtwo H) G⟩
end GeneralMahler.Cert.IV

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Powers
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

end Profile
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_HSeries
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 log-series h in stable formulas. Remainders and smooth positive coefficients. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Finset
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal

lemma hpden {u t:ℝ} (ht:t∈Icc (0:ℝ) 1) (h:u<1) : 0<hden u t := by
  unfold hden; have h1 : 0 ≤ t := ht.1; have h2 : t ≤ 1 := ht.2
  rcases h1.eq_or_lt with hx|hx
  · rw [← hx]; simp
  have he := mul_lt_mul_of_pos_right h hx; linarith
lemma intH (n:Nat) {u:ℝ} (h:u<1): IntervalIntegrable (Qhv n u) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  unfold Qhv; apply ContinuousOn.pow
  exact continuousOn_id.div ((by unfold hden; fun_prop : Continuous _).continuousOn)
    fun x hx=>(hpden hx h).ne'
lemma hdv (n:Nat) {u t:ℝ} (ht:t∈Icc (0:ℝ) 1) (h:u<1) :
    HasDerivAt (fun x=> Qhv n x t) (((n+1:Nat):ℝ)* Qhv (n+1) u t) u := by
  have he: HasDerivAt (fun u=> hden u t) (-t) u := by
    convert ((hasDerivAt_const u 1).sub ((hasDerivAt_id' u).mul_const t)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first|rfl|ring
  have hh:= ((hasDerivAt_const u t).div he (hpden ht h).ne').pow (n+1)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first| rfl | skip
  unfold Qhv; push_cast; simp [pow_succ]; ring

lemma hdQ (n:Nat) {u:ℝ} (h:u<1):
    HasDerivAt (Qh n) (((n+1:Nat):ℝ)* Qh (n+1) u) u := by
  let c:ℝ:= max 0 ((1+u)/2)
  let F:= Qhv n
  let G:= fun (x t:ℝ)=> ((n+1:Nat):ℝ)*Qhv (n+1) x t
  let A:= ((n+1:Nat):ℝ)*(1/(1-c))^(n+2)
  have hc : u < c := lt_of_lt_of_le (by linarith) (le_max_right ..)
  have hh : c<1 := max_lt (by linarith) (by linarith)
  have he (m:Nat) (u:ℝ): Measurable (Qhv m u) := by unfold Qhv hden; fun_prop
  have hm (t) (ht:t ∈ Ι (0:ℝ) 1) : t∈Icc (0:ℝ) 1 := by rw [uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le,ht.2⟩
  have hd (x:ℝ) (hx:x∈Iio c) (t) (ht:t∈Icc (0:ℝ) 1):
      ‖G x t‖ ≤ A := by
    have hv:=hpden ht (lt_trans hx hh)
    have hℓ : 1-c ≤ hden x t := by
      unfold hden
      have hc : 0≤ c:=le_max_left ..
      have h' : x*t ≤ c*1 := le_trans (mul_le_mul_of_nonneg_right hx.le ht.1)
        (mul_le_mul_of_nonneg_left ht.2 hc)
      linarith
    have htp : 0≤t/hden x t:= div_nonneg ht.1 hv.le
    unfold G A Qhv
    rw [Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ htp
    apply div_le_div₀ (by positivity) ht.2 (sub_pos.mpr hh) hℓ
  have hi := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=volume) (F:=F)
    (F':=G) (x₀:=u) (bound:=fun _=> A) (s:=Iio c) (Iio_mem_nhds hc)
    (Eventually.of_forall fun x=> (he _ x).aestronglyMeasurable) (intH n h)
    ((measurable_const.mul (he _ u)).aestronglyMeasurable)
    (ae_of_all _ fun t ht x hx=> hd x hx _ (hm t ht)) (continuous_const.intervalIntegrable 0 1)
    (ae_of_all _ fun t ht x hx=> hdv n (hm t ht) (lt_trans hx hh))
  obtain ⟨_,hi⟩:=hi
  unfold G at hi; rw [intervalIntegral.integral_const_mul] at hi; exact hi
lemma hlog {u:ℝ} (hu:0<u) (h:u<1): u^2*Qh 0 u= -Real.log (1-u)-u := by
  let f:= fun t=> -Real.log (hden u t)-u*t
  let g:= fun t=> u^2*Qhv 0 u t
  have hd (x:ℝ) (hx:x∈Set.uIcc (0:ℝ) 1): HasDerivAt f (g x) x := by
    rw [Set.uIcc_of_le zero_le_one] at hx
    have he : HasDerivAt (hden u) (-u) x := by
      convert ((hasDerivAt_const x 1).sub ((hasDerivAt_id' x).const_mul u)) using 1
      all_goals try with_reducible_and_instances rfl
      all_goals first|rfl|ring
    convert ((he.log (hpden hx h).ne').neg.sub ((hasDerivAt_id' x).const_mul u)) using 1
    all_goals try with_reducible_and_instances rfl
    unfold g Qhv
    have hh:=hpden hx h
    unfold hden at *
    simp only [Nat.zero_add,pow_one]; field_simp; ring
  have hi:= intervalIntegral.integral_eq_sub_of_hasDerivAt hd (show IntervalIntegrable g volume 0 1 from
    (intH 0 h).const_mul _)
  unfold g f at hi; rw [intervalIntegral.integral_const_mul] at hi
  simpa only [hden,mul_zero,mul_one,sub_zero,Real.log_one,neg_zero,Qh] using hi

lemma comb (i n:Nat):
    hCoef (i+1) (n+1) = hCoef i (n+1)+ hCoef (i+1) n := by
  unfold hCoef
  rw [show i+1+(n+1)=i+n+1+1 from by omega,Nat.choose]
  push_cast; rw [show i+1+n=i+n+1 from by omega, show i+(n+1)=i+n+1 from by omega]
  ring

lemma RecPoly (i n:Nat) (x:ℝ):
    Rpoly (i+1) (n+1) x= Rpoly i (n+1) x + x* Rpoly (i+1) n x := by
  induction n with
  | zero=> simp [Rpoly,hCoef]
  | succ n ih=>
    have he (i n:Nat):Rpoly i (n+1) x=Rpoly i n x+hCoef i n*x^n :=
      sum_range_succ ..
    rw [he,he i (n+1),comb,pow_succ]
    have ht := he (i+1) n
    linear_combination ih - x * ht
lemma PowRec (i:Nat) (x:ℝ): Rpow (i+1) x= Rpow i x+x*Rpow (i+1) x := by
  by_cases h:x=1
  · subst x; simp [Rpow]
  unfold Rpow
  rw [pow_succ _ (i+1)]
  field_simp; ring

lemma r_est (i n:Nat) {x:ℝ} (hx:0≤x) (he:x<1):
    let u:= Rpow i x-Rpoly i n x
    0 ≤ u ∧ u ≤ hCoef i n*x^n*Rpow i x := by
  dsimp only
  have hr (i n:Nat): 0 ≤ hCoef i n := by unfold hCoef; positivity
  have hp : 1 ≤1/(1-x) := by rw [le_div_iff₀ (by linarith)]; linarith
  induction i generalizing n with
  | zero=>
    have hj : Rpow 0 x-Rpoly 0 n x=hCoef 0 n*x^n*Rpow 0 x := by
      simp only [Rpow,Rpoly,hCoef,Nat.zero_add,Nat.choose_self,Nat.cast_one,one_mul,pow_one]
      rw [geom_sum_eq (ne_of_lt he)]
      have h1:=sub_ne_zero.mpr (ne_of_lt he)
      have h2:=sub_ne_zero.mpr (ne_of_gt he)
      field_simp
      ring
    rw [hj]; unfold Rpow; exact ⟨mul_nonneg (mul_nonneg (hr ..) (pow_nonneg hx _)) (pow_nonneg (by linarith) _),le_rfl⟩
  | succ i ih=>
    induction n with
    | zero=>
      have ht : 0≤Rpow (i+1) x := by unfold Rpow; positivity
      simpa [Rpoly,hCoef] using ht
    | succ n H=>
      have hz (n:Nat): Rpow (i+1) x-Rpoly (i+1) (n+1) x =
          Rpow i x-Rpoly i (n+1) x + x*(Rpow (i+1) x-Rpoly (i+1) n x) := by
        rw [RecPoly]; linarith [PowRec i x]
      have ht := H.2
      have hh := ih (n+1)
      rw [hz]
      refine ⟨add_nonneg hh.1 (mul_nonneg hx H.1),?_⟩
      have he' : Rpow i x ≤ Rpow (i+1) x := by unfold Rpow; gcongr; omega
      rw [comb]
      have hj:= mul_le_mul_of_nonneg_left he' (show 0≤ hCoef i (n+1)*x^(n+1) from
        mul_nonneg (hr ..) (pow_nonneg hx _))
      apply le_trans (add_le_add hh.2 (mul_le_mul_of_nonneg_left H.2 hx))
      rw [add_mul, add_mul]
      apply add_le_add hj (le_of_eq ?_)
      rw [pow_succ]; ring
end GeneralMahler.SCal

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_HBox
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Jet.instZeroIV
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
open Cert Cert.IV Finset
lemma Qh_est (i n:ℕ) (u:ℝ) (hu:0≤u) (h:u<1):
    Qpol i n u≤Qh i u ∧ Qh i u ≤ Qpol i n u+
      hCoef i n*u^n*(1/(1-u))^(i+1) := by
  let f := fun t=> t^(i+1)*Rpoly i n (u*t)
  let C:=hCoef i n*u^n*(1/(1-u))^(i+1)
  have hm (t:ℝ) (ht:t∈Set.Icc (0:ℝ) 1) : f t ≤ Qhv i u t ∧ Qhv i u t ≤ f t+C := by
    have ht' : 0≤t:=ht.1
    have ht₁ : t≤1:=ht.2
    have he : u*t ≤ u := mul_le_of_le_one_right hu ht₁
    obtain ⟨ha,hb⟩:= r_est i n (mul_nonneg hu ht') (lt_of_le_of_lt he h)
    have hg : Qhv i u t = t^(i+1)*Rpow i (u*t) := by unfold Qhv Rpow hden; ring
    rw [hg]; unfold f
    rw [sub_nonneg] at ha
    refine ⟨mul_le_mul_of_nonneg_left ha (by positivity),?_⟩
    have hs : 0≤hCoef i n:= by unfold hCoef; positivity
    have hp := pow_le_one₀ ht' ht₁ (n:=i+1)
    have hq : 0<1-u:= by linarith
    have hv := mul_le_mul_of_nonneg_left hb (show 0 ≤ t^(i+1) by positivity)
    have hd : 0 < 1-u*t:= by linarith
    have hh : t^(i+1)*(hCoef i n*(u*t)^n*Rpow i (u*t))≤ C := by
      apply le_trans (mul_le_of_le_one_left (show 0 ≤ hCoef i n*(u*t)^n*Rpow i (u*t) by unfold Rpow; positivity) hp)
      unfold Rpow C
      gcongr
    linarith
  have he : (∫ t in (0:ℝ)..1,f t) = Qpol i n u := by
    have he (t): f t=∑ j∈Finset.range n,(hCoef i j*u^j)*t^(i+j+1) := by
      unfold f Rpoly; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      simp_rw [pow_add,mul_pow]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_finsetSum]
    · unfold Qpol
      apply Finset.sum_congr rfl; intro j _
      rw [intervalIntegral.integral_const_mul, integral_pow]; push_cast; norm_num; ring
    exact fun i _=> Continuous.intervalIntegrable (by fun_prop) ..
  have hc : Continuous f := by unfold f Rpoly; fun_prop
  have hi:= hc.intervalIntegrable (μ:=volume) 0 1
  have HH:=intH i h
  rw [← he]
  constructor
  · apply intervalIntegral.integral_mono_on zero_le_one hi HH
    exact fun t h=> (hm t h).1
  have hv:= intervalIntegral.integral_mono_on zero_le_one HH (g:=fun t=> f t+C)
    (hi.add (intervalIntegrable_const ..)) (fun t h=> (hm t h).2)
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,intervalIntegral.integral_const] at hv
  simpa only [Qh,C,sub_zero,one_smul] using hv

lemma mcb (i j:Nat): hCoef i j ∈ cB i j:= nc ((i+j).choose j)

lemma mbsumH (U:IV) (i:Nat) (u:ℝ) (h:u∈U) (n:ℕ):
    u^n∈(bsumH U i n).1 ∧ Qpol i n u∈(bsumH U i n).2 := by
  induction n with
  | zero=> simpa [Qpol,bsumH] using And.intro mo mz
  | succ n ih=>
    rw [bsumH,pow_succ,Qpol,Finset.sum_range_succ]
    exact ⟨mmul ih.1 h,madd ih.2 (mdiv (mmul (mcb _ _) ih.1) (nc (i+n+2)))⟩
lemma mhBox {U:IV} (i n:Nat) {u:ℝ} (hu:0≤u) (h:u<1) (hx:u∈U):
    Qh i u∈hBox U i n := by
  obtain ⟨hp,hq⟩:=Qh_est i n u hu h
  obtain ⟨ha,hb⟩:=mbsumH U i u hx n
  let k:= Qh i u-Qpol i n u
  have h₁: 0≤k:=sub_nonneg.mpr hp
  have h₂: k≤hCoef i n*u^n*(1/(1-u))^(i+1) := by unfold k; linarith
  have he := mmul (mmul (mcb i n) ha) (mpow (mdiv mo (msub mo hx)) (i+1))
  exact (show Qpol i n u+k=Qh i u from by unfold k; ring) ▸ madd hb (span_conv mz he h₁ h₂)
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Moments
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 stable Laplace moments. Define using the translated Gaussian variable
on (x,∞). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal
namespace GeneralMahler.SCal
open Profile Layers
lemma lp_r (n:Nat) (x:ℝ): rapid (Lpn n x) := by
  have h : PolyBound (fun y:ℝ=>(y-x)^n/phi x) := by
    simp only [div_eq_mul_inv]; exact ((PolyBound.id.sub (PolyBound.const _)).pow n).mul (PolyBound.const _)
  exact rapid_phi.product h
lemma lp_i (n:Nat) (x:ℝ) : Integrable (Lpn n x) := by
  have h : Continuous (Lpn n x) := by
    unfold Lpn; exact c_phi.mul (Continuous.div_const (by fun_prop) _)
  exact (lp_r n x).integrable_real h.measurable
lemma Ymp (n:Nat) (x:ℝ): 0 < Ymk n x := by
  have hh (y) (hy:x<y) : 0< Lpn n x y := mul_pos (phi_pos _)
    (div_pos (pow_pos (sub_pos.mpr hy) n) (phi_pos x))
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ (lp_i n x).integrableOn).mpr
  · apply lt_of_lt_of_le (isOpen_Ioi.measure_pos volume (Set.nonempty_Ioi (a:=x)))
    apply measure_mono
    exact fun y hy=> ⟨(hh y hy).ne',hy⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy; exact (hh y hy).le
lemma Ym0 : Ymk 0=Y := by
  ext x; unfold Ymk Lpn Y
  simp_rw [pow_zero, mul_one_div,integral_div,int_Ioi]
lemma Hd0 (x y:ℝ) : HasDerivAt (Lpn 0 x) (-x*Lpn 0 x y-Lpn 1 x y) y := by
  have he : Lpn 0 x=fun y=> phi y/phi x := by unfold Lpn; ext y; ring
  rw [he]
  convert (d_phi y).div_const (phi x) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first| rfl| (unfold Lpn; dsimp only; ring)
lemma Hdn (x y:ℝ) (n:Nat) : HasDerivAt (Lpn (n+1) x)
    (((n+1:Nat):ℝ)*Lpn n x y - x*Lpn (n+1) x y-Lpn (n+2) x y) y := by
  have h:= (d_phi y).mul ((((hasDerivAt_id' y).sub_const x).pow (n+1)).div_const (phi x))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | skip
  unfold Lpn
  push_cast; simp [pow_succ]; ring
lemma R0 (x:ℝ) : x*Ymk 0 x+Ymk 1 x=1 := by
  let f:=Lpn 0 x
  have hi : Integrable (fun y=> -x*f y-Lpn 1 x y):=
    ((lp_i 0 x).const_mul _).sub (lp_i 1 x)
  have he:= integral_Ioi_of_hasDerivAt_of_tendsto'
    (a:=x) (fun y _=>Hd0 x y) hi.integrableOn (lp_r 0 x).tail_limit
  rw [integral_sub (((lp_i 0 x).integrableOn).const_mul _) (lp_i 1 x).integrableOn,
    integral_const_mul] at he
  rw [show Lpn 0 x x=1 from by unfold Lpn; field_simp [(phi_pos x).ne']] at he
  unfold Ymk; linarith
lemma Rn (x:ℝ) (n:Nat) : x*Ymk (n+1) x+Ymk (n+2) x = ((n+1:Nat):ℝ)*Ymk n x := by
  have hi : Integrable (fun y=> ((n+1:Nat):ℝ)*Lpn n x y-x*Lpn (n+1) x y) :=
    ((lp_i _ x).const_mul _).sub ((lp_i _ x).const_mul _)
  have he:= integral_Ioi_of_hasDerivAt_of_tendsto'
    (a:=x) (fun y _=>Hdn x y n) (hi.sub (lp_i _ x)).integrableOn (lp_r _ x).tail_limit
  rw [integral_sub hi.integrableOn (lp_i _ x).integrableOn,integral_sub (((lp_i _ x).integrableOn).const_mul _)
    (((lp_i _ x).integrableOn).const_mul _),integral_const_mul, integral_const_mul] at he
  rw [show Lpn (n+1) x x=0 from by simp [Lpn]] at he
  unfold Ymk; linarith
lemma DYmk0 (x:ℝ) : HasDerivAt (Ymk 0) (-(Ymk 1 x)) x := by
  have hh:=R0 x
  rw [Ym0] at *
  convert dY x using 1 <;> first | (with_reducible_and_instances rfl) | (unfold Yd; linarith)
lemma DYmk (x:ℝ) (n:Nat): HasDerivAt (Ymk n) (-(Ymk (n+1) x)) x := by
  have h0:=DYmk0 x
  have he :∀ n:Nat, HasDerivAt (Ymk n) (-(Ymk (n+1) x)) x ∧
      HasDerivAt (Ymk (n+1)) (-(Ymk (n+2) x)) x := by
    intro n; induction n with
    | zero=>
      have hh : Ymk 1=fun x=> 1-x*Ymk 0 x:= funext fun x=>by linarith [R0 x]
      refine ⟨h0,?_⟩
      change HasDerivAt (Ymk 1) _ x; rw [hh]
      convert (hasDerivAt_const x 1).sub ((hasDerivAt_id' x).mul h0) using 1
      all_goals try with_reducible_and_instances rfl
      have hi:=Rn x 0; norm_num at *; linarith
    | succ n ih=>
      refine ⟨ih.2,?_⟩
      have hh : Ymk (n+2)=fun x=> ((n+1:Nat):ℝ)*Ymk n x-x*Ymk (n+1) x :=
        funext fun x=>by linarith [Rn x n]
      change HasDerivAt (Ymk (n+2)) _ x
      rw [hh]
      convert (ih.1.const_mul ((n+1:Nat):ℝ)).sub ((hasDerivAt_id' x).mul ih.2) using 1
      all_goals try with_reducible_and_instances rfl
      have hi:=Rn x (n+1)
      push_cast at *; linarith
  exact (he n).1
lemma Yanti (n:Nat): StrictAnti (Ymk n) :=
  strictAnti_of_deriv_neg fun x=> by rw [(DYmk x n).deriv]; linarith [Ymp (n+1) x]

lemma cRp (n:Nat) (x:ℝ): 0 < cRat n x := div_pos (Ymp ..) (Ymp ..)
lemma cfBase (x:ℝ) : (x+cRat 0 x)* Ymk 0 x=1 := by
  unfold cRat; rw [add_mul,div_mul_cancel₀ _ (Ymp 0 x).ne']; apply R0
lemma cfIter (n:Nat) (x:ℝ): cRat n x * (x+cRat (n+1) x)=((n+1:Nat):ℝ) := by
  unfold cRat
  have h1:=(Ymp n x).ne'
  have h2:=(Ymp (n+1) x).ne'
  field_simp
  have he:=Rn x n; push_cast at *; nlinarith

end GeneralMahler.SCal

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_LapBox
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Jet.instZeroIV
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 interval enclosures for the Ymk via Taylor and CF. -/
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal
open Profile Layers Cert Cert.IV
lemma mphi0: phi 0∈ phi0B := by
  have h : phi 0= (√(2*π))⁻¹ := by simp [phi_apply]
  rw [h]; exact minv (mrt (mmul mtwo mpi))
lemma mcx {x:ℝ} {X:IV} (hx:x∈X): -(x^2)/2∈cxB X := mdiv (mneg (msq hx)) mtwo
lemma mphi {x:ℝ} {X:IV} (hx:x∈X) : phi x∈phiB X := by
  have he : phi x=phi 0*Real.exp (-(x^2)/2) := by simp [phi_apply]
  rw [he]; exact mmul mphi0 (mebox _ (mcx hx))

open Finset
lemma mpSeries {c:ℝ} {C:IV} (hc:c∈C) (n:ℕ) :
    c^n/n.factorial ∈(pSeries C n).1∧
      (∑ i∈range n,c^i/i.factorial / ((2*i+1:Nat):ℝ)) ∈ (pSeries C n).2 := by
  induction n with
  | zero=> simpa [pSeries] using (And.intro mo mz)
  | succ n ih=>
    rw [pSeries,sum_range_succ]
    refine ⟨?_,madd ih.2 (mdiv ih.1 (nc _))⟩
    have he : c^(n+1)/(n+1).factorial = c^n/n.factorial*c/((n+1:Nat):ℝ) := by
      rw [Nat.factorial_succ,pow_succ]; push_cast; field_simp
    rw [he]; exact mdiv (mmul ih.1 hc) (nc _)

lemma p_int_beta (x:ℝ):
    p x=1/2+x*phi 0*(∫ t in (0:ℝ)..1, Real.exp ((-(x^2)/2)*t^2)) := by
  let F:=fun t:ℝ=> p (t*x)
  let A:= fun t:ℝ=> Real.exp ((-(x^2)/2)*t^2)
  have hd (t): HasDerivAt F ((x*phi 0)*A t) t := by
    have h: HasDerivAt F (phi (t*x)*(1*x)) t :=
      by change HasDerivAt (p ∘ (fun y=>y*x)) _ t; exact (d_p (t*x)).comp t ((hasDerivAt_id' t).mul_const x)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    unfold A; simp [phi_apply]; ring_nf
  have hi:= intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> hd t)
    ((continuous_const.mul (by unfold A; fun_prop : Continuous A)).intervalIntegrable (0:ℝ) 1)
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [F,one_mul,zero_mul,p_half] at hi
  change p x=1/2+x*phi 0*(∫ t in (0:ℝ)..1,A t)
  linarith

lemma pT_bound (c:ℝ) (hc:|c|≤1) :
    (∫ t in (0:ℝ)..1,Real.exp (c*t^2)) - (∑ i∈range 25,c^i/i.factorial / ((2*i+1:Nat):ℝ)) ∈terr := by
  let S:=fun i:ℕ=> fun t:ℝ=> (c*t^2)^i/i.factorial
  let f:=fun t=> ∑ i∈range 25,S i t
  let g:= fun t:ℝ=> Real.exp (c*t^2)
  have he : (∑ i∈range 25,c^i/i.factorial / ((2*i+1:Nat):ℝ)) =
      ∫ t in (0:ℝ)..1,f t := by
    unfold f; rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro i _
      have hi : S i=fun t=> (c^i/i.factorial)*t^(2*i) := by
        ext; unfold S; rw [pow_mul,mul_pow]; ring
      rw [hi,intervalIntegral.integral_const_mul,integral_pow]; push_cast; norm_num; ring
    exact fun i _=> (by unfold S; fun_prop : Continuous (S i)).intervalIntegrable ..
  rw [he]
  let v:ℝ := 1/10^24
  have hu (x:ℝ) (hx:x∈Ι (0:ℝ) 1): ‖g x-f x‖≤ v := by
    have hh : 0≤ x ∧ x≤1 := by rw [uIoc_of_le zero_le_one] at hx; exact ⟨hx.1.le,hx.2⟩
    have hx' : |c*x^2| ≤1 := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg x)]
      exact (mul_le_of_le_one_left (sq_nonneg x) hc).trans (by nlinarith [hh.1,hh.2])
    have h:=Real.exp_bound hx' (show 0<25 by decide)
    have hi : ‖g x-f x‖≤ _ := h
    have hp : |c*x^2|^25 ≤1 := pow_le_one₀ (_root_.abs_nonneg _) hx'
    unfold v
    norm_num [Nat.factorial] at *
    linarith
  have ht:=intervalIntegral.norm_integral_le_of_norm_le_const hu
  have hg : Continuous g := by unfold g; fun_prop
  have hf : Continuous f := by unfold f S; fun_prop
  rw [intervalIntegral.integral_sub (hg.intervalIntegrable ..) (hf.intervalIntegrable ..),
    Real.norm_eq_abs] at ht
  have hp:= abs_le.mp ht
  change w _ ≤ (∫ t in (0:ℝ)..1,g t)-_ ∧ _ ≤ w _
  unfold v at *
  norm_num [w,den] at *
  exact hp

lemma mpTaylor {x:ℝ} {X:IV} (hx:x∈X) (he:|-(x^2)/2|≤1):
    p x∈ pTaylor X := by
  let c:ℝ:=-(x^2)/2
  have h:= madd (mpSeries (mcx hx) 25).2 (pT_bound c he)
  change (∑ i∈range 25,c^i/i.factorial/((2*i+1:Nat):ℝ))+((∫ t in (0:ℝ)..1,Real.exp (c*t^2))-_ )∈_ at h
  have hh : (∫ t in (0:ℝ)..1,Real.exp (c*t^2)) ∈ (pSeries (cxB X) 25).2+terr := by
    rw [add_sub_cancel ..] at h
    exact h
  rw [p_int_beta]
  exact madd mhalf (mmul (mmul hx mphi0) hh)

lemma mcEncl {x:ℝ} {X:IV} (hx:x∈X) (hr:0<x) (i n:ℕ) :
    cRat n x∈ cEncl X i n := by
  induction i generalizing n with
  | zero=>
    apply span_conv mz (mdiv (nc _) hx) (cRp n x).le
    have he:= cfIter n x
    rw [le_div_iff₀ hr]
    nlinarith [cRp n x,cRp (n+1) x]
  | succ i ih=>
    have he:=cfIter n x
    rw [show cRat n x = ((n+1:Nat):ℝ)/(x+cRat (n+1) x) from (eq_div_iff (add_pos hr (cRp (n+1) x)).ne').mpr he]
    exact mdiv (nc _) (madd hx (ih _))

lemma mforward {x:ℝ} {X Y:IV} (hx:x∈X) (h:Ymk 0 x∈Y): ∀ n,Ymk n x∈forward X Y n
  | 0=>h
  | 1=>by
    have he : Ymk 1 x = 1-x*Ymk 0 x := by linarith [R0 x]
    rw [he]; exact msub mo (mmul hx h)
  | n+2=>by
    rw [show Ymk (n+2) x = ((n+1:Nat):ℝ)*Ymk n x-x*Ymk (n+1) x from by linarith [Rn x n] ]
    exact msub (mmul (nc _) (mforward hx h n)) (mmul hx (mforward hx h (n+1)))

lemma mprodCF {x:ℝ} {X:IV} (hx:x∈X) (hr:0<x) (e n:ℕ):
    Ymk n x∈prodCF X e n := by
  induction n with
  | zero=>
    have he:=cfBase x
    have hv:=add_pos hr (cRp 0 x)
    have heq : Ymk 0 x=(x+cRat 0 x)⁻¹ := by rw [← one_div,eq_div_iff hv.ne',mul_comm]; exact he
    rw [heq]; exact minv (madd hx (mcEncl hx hr _ _))
  | succ n ih=>
    have he : Ymk (n+1) x=cRat n x*Ymk n x := by unfold cRat; rw [div_mul_cancel₀ _ (Ymp n x).ne']
    rw [he]; exact mmul (mcEncl hx hr _ _) ih

lemma myBox {x:ℝ} {X:IV} (hx:x∈X) (n:ℕ): Ymk n x∈ ymBox n X := by
  unfold ymBox; split
  next he=>
    apply mforward hx
    rw [Ym0]
    exact mdiv (msub mo (mpTaylor hx (mle (mabs (mcx hx)) mo he))) (mphi hx)
  split
  next he=> exact mprodCF hx (mlt mz hx he) _ _
  trivial
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Stable
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 stable algebra shared by finite and infinite estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal
open Profile Layers
lemma u_eq' (x:ℝ) : sU x=1-p x := by
  unfold sU sY; rw [Ym0]; unfold Y; rw [div_mul_cancel₀ _ (phi_pos x).ne']
lemma u_pos (x:ℝ):0 < sU x := by rw [u_eq']; linarith [p_lt_one x]
lemma u_le (x:ℝ):sU x<1 := by rw [u_eq']; linarith [p_pos x]
lemma sPe (x): sP x=p x := by rw [sP,u_eq']; ring
lemma h_f (x:ℝ): f x=sU x^2*sH x := by
  have h:= hlog (u_pos x) (u_le x)
  unfold f sH; rw [h,u_eq']; simp; ring
lemma lp_st (x:ℝ): sJ x=j x := by
  unfold sJ j
  rw [sPe,← u_eq',sU,Real.log_mul (show sY x≠0 from (Ymp _ _).ne') (phi_pos _).ne',phi_apply,
    Real.log_mul (by positivity) (by positivity),Real.log_inv,Real.log_exp]
  ring
lemma B_st (x): sB x=1-x*sY x := by unfold sB sY; linarith [R0 x]
lemma Xu (x): X x*sU x=sP x*sY x := by
  rw [sU,sPe]; unfold X; field_simp [(phi_pos x).ne']
lemma X1u (x): Xd x*sU x=sW x := by
  unfold Xd sW
  rw [add_mul,mul_assoc,Xu,B_st]; unfold sP; ring
lemma YDst (x): Yd x= -sB x := by unfold Yd; rw [B_st]; unfold sY; rw [Ym0]; ring
lemma d_stable (x:ℝ) : sd x=d x := by
  unfold sd d; rw [lp_st,← X1u,YDst,h_f]; ring
lemma k_stable (x:ℝ) : sK x=Kp x := by
  unfold Kp g sK; rw [d_stable,lp_st,h_f]
  have hh (x):sY x=Y x:=by unfold sY; rw [Ym0]
  have he : X x^2*(sU x^2*sH x)=(sP x*sY x)^2*sH x := by rw [← Xu]; ring
  rw [he,hh]; ring
lemma g_stable (x:ℝ): sg1 x=deriv g x := by
  unfold sg1; rw [(dg x).deriv,lp_st]
  unfold gd; rw [h_f,YDst]
  have he : X x*Xd x*(sU x^2*sH x)=(sP x*sY x)*sW x*sH x := by rw [← Xu,← X1u]; ring
  rw [he]; unfold sY; rw [Ym0]; ring
lemma c_stable (x:ℝ): sC x=Cp x := by
  rw [sC,d_stable,g_stable,k_stable,Cp,(ddg x).deriv,Kp]; ring
lemma sY_ident (x) : sY x* MillsC (-x)=1 := by
  unfold sY; rw [Ym0]; unfold Y MillsC
  rw [neg_phi,neg_p]; have h:=(q_pos x).ne'; field_simp [(phi_pos x).ne']
lemma sJneg (x): MillsJ (-x) = sB x/sY x := by
  have hh:=sY_ident x
  rw [B_st,eq_div_iff (show sY x≠0 from (Ymp _ _).ne')]
  unfold MillsJ; linarith
lemma rv_stable (x:ℝ): sRv x=deriv v x-x := by
  rw [sRv,sPe,v_deriv,← sJneg]; unfold MillsJ MillsC; ring
lemma v2_stable (x:ℝ): sV2 x=deriv (deriv v) x:= by
  have he : MillsC (-x) =1/sY x := by
    rw [eq_div_iff (show sY x≠0 from (Ymp _ _).ne'),mul_comm]; apply sY_ident
  rw [(ddv x).deriv,MillsW,MillsW,sJneg,he]
  unfold sV2 MillsJ MillsC; rw [sPe]; dsimp only; ring

lemma hsb : 0 < sb := by norm_num [sb]
lemma xD (t:ℝ): HasDerivAt xs (ast t) t := (Real.hasDerivAt_sinh t).const_mul sb
lemma aD (t:ℝ): HasDerivAt ast (xs t) t := (Real.hasDerivAt_cosh t).const_mul sb
lemma ap (t):0<ast t:= mul_pos hsb (Real.cosh_pos _)
lemma x_mono : StrictMono xs := strictMono_of_deriv_pos fun x=>by rw [(xD x).deriv]; apply ap
lemma x_ang (t): angle (xs t)=omegaP*t := by
  unfold angle xs; rw [mul_comm sb,mul_div_cancel_right₀ _ hsb.ne',Real.arsinh_sinh]
lemma ontoX (x:ℝ): ∃ t:ℝ,xs t=x := by
  refine ⟨Real.arsinh (x/sb),?_⟩
  unfold xs; rw [Real.sinh_arsinh,mul_div_cancel₀ _ hsb.ne']
end GeneralMahler.SCal

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_RealJ
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Finite-real-variable towers in t coordinate. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal
open Profile Layers Jet
lemma xj0 (x): xj x 0=xs x:=by simp [xj]
lemma aj0 (x): aj x 0=ast x:=by simp [xj,aj,tail]
lemma Ix : TW univ xj := by
  intro n x _
  by_cases h:Even n
  · have he : ¬Even (n+1) := by grind
    simpa only [xj,ite_eq_left h,ite_eq_right he] using xD x
  have he: Even (n+1):= by grind
  simpa only [xj,ite_eq_left he,ite_eq_right h] using aD x
lemma Ia: TW univ aj := Ix.tail

lemma Imom (i): TW univ (momRF i) := by
  intro n x _
  convert ((DYmk x (i+n)).const_mul ((-1:ℝ)^n)) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl |(unfold momRF; rw [← Nat.add_assoc,pow_succ]; ring)
lemma Ihf: TW (Iio 1) hfRF := by
  intro n x hx
  convert ((hdQ n hx).const_mul ((n.factorial:ℝ))) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl |(unfold hfRF; rw [Nat.factorial_succ]; push_cast; ring)

namespace CJet

lemma hs0 (x): halfS x 0= xs x *xs x /2 := by
  change 1/2*(xj x 0*xj x 0)=_; rw [xj0]; ring
lemma ph0 (x): ph x 0=phi (xs x) := by
  change phi 0*Real.exp (-halfS x 0)=_
  rw [hs0]; simp only [phi_apply]; ring_nf; simp
lemma ym0 (i x): ym i x 0=Ymk i (xs x):=by
  change (-1:ℝ)^0*_ =_
  rw [xj0]; ring_nf
lemma Y0 (x): Y x 0=sY (xs x):=ym0 0 _
lemma B0 (x): B x 0=sB (xs x):=ym0 1 _
lemma u0 (x): u x 0=sU (xs x):= by
  change Y x 0*ph x 0=_;rw [Y0,ph0]; rfl
lemma p0v (x): p0 x 0=sP (xs x):=by change 1-u x 0=_; rw [u0]; rfl
lemma h0 (x): h x 0=sH (xs x):= by
  change Nat.factorial 0* Qh 0 (u x 0)=_
  rw [u0]; simp [sH]
lemma j0 (x): j x 0=sJ (xs x):=by
  change halfS x 0+ _-Real.log (Y x 0)-p0 x 0=_
  rw [hs0,Y0,p0v]; rfl
lemma wst (x):w x 0=sW (xs x) := by change 1-p0 x 0 * B x 0=_; rw [p0v,B0]; rfl
lemma d0s (x):dj x 0=sd (xs x):=by
  change B x 0*B x 0*j x 0+w x 0*w x 0*h x 0=_
  rw [B0,j0,wst,h0]; rfl
lemma k0s (x):kj x 0=sK (xs x):=by
  change dj x 0+ Y x 0* Y x 0* (j x 0+p0 x 0*p0 x 0*h x 0)-1=_
  rw [d0s,Y0,j0,p0v,h0]; rfl
lemma c0s (x):cj x 0=sC (xs x):=by
  change -(dj x 0)+(ar-1)*(xj x 0*(Y x 0* (B x 0*j x 0-w x 0*p0 x 0*h x 0))-kj x 0)=_
  rw [xj0,Y0,j0,p0v,h0,B0,wst,d0s,k0s]; rfl
lemma krv (x):rv x 0=sRv (xs x):=by
  change ph x 0*(p0 x 0)⁻¹-B x 0*(Y x 0)⁻¹=_
  rw [ph0,p0v,B0,Y0]; unfold sRv; ring
lemma kvv (x):vv x 0=sV2 (xs x):=by
  change 2-ph x 0*(p0 x 0)⁻¹ * (xj x 0+ph x 0*(p0 x 0)⁻¹)-B x 0*(Y x 0)⁻¹*(Y x 0)⁻¹=_
  rw [ph0,p0v,xj0,B0,Y0]; unfold sV2; dsimp only; ring

lemma Ih : TW univ halfS := (TW.const _).mul (Ix.mul Ix)
lemma Iph : TW univ ph := (TW.const _).mul (Ih.neg.exp)
lemma IY (i): TW univ (ym i) := Ix.comp (Imom i) (fun _ _=>mem_univ _)
lemma Iu: TW univ u:=(IY 0).mul Iph
lemma Ip: TW univ p0:=(TW.const _).sub Iu
lemma ypJ (x): 0 < Y x 0 := Y0 x ▸ Ymp 0 _
lemma ppJ (x): 0 < p0 x 0 := p0v x ▸ (sPe (xs x)).symm ▸ p_pos _
lemma IhJ: TW univ h:= Iu.comp Ihf (fun x _=> by rw [u0]; exact u_le _)
lemma Ij: TW univ j:= ((Ih.add (TW.const _)).sub ((IY 0).log (fun x _=> (ypJ x).ne'))).sub Ip
lemma Iw: TW univ w := (TW.const _).sub (Ip.mul (IY 1))
lemma Id: TW univ dj:= (((IY 1).mul (IY 1)).mul Ij).add ((Iw.mul Iw).mul IhJ)
lemma Ig: TW univ gp:= (IY 0).mul (((IY 1).mul Ij).sub ((Iw.mul Ip).mul IhJ))
lemma IK: TW univ kj:= (Id.add (((IY 0).mul (IY 0)).mul (Ij.add ((Ip.mul Ip).mul IhJ)))).sub (TW.const _)
lemma IC: TW univ cj:= Id.neg.add ((TW.const _).mul ((Ix.mul Ig).sub IK))
lemma Ijy: TW univ jy:= (IY 0).inv (fun x _=> (ypJ x).ne')
lemma Imc: TW univ mc:= Iph.mul (Ip.inv (fun x _=> (ppJ x).ne'))
lemma Irv: TW univ rv:= Imc.sub ((IY 1).mul Ijy)
lemma Ivv: TW univ vv:= ((TW.const _).sub (Imc.mul (Ix.add Imc))).sub (((IY 1).mul Ijy).mul Ijy)
end CJet
end GeneralMahler.SCal

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_BoxJ
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interval enclosures for profile derivative towers from hyperbolic coordinates
and bounds for the Laplace moments `Ymk`. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Profile Layers Jet Cert Cert.IV

namespace Row0
lemma msbB : sb∈sbB := by
  have hh:=mdiv (mc 36) (mc 10)
  norm_num [sb] at *; exact hh
lemma marB : ar∈arB := by
  have hh:=mdiv (mc 75) (mc 10)
  norm_num [ar] at *; exact hh
lemma mHyp {U:IV} {x:ℝ} (hx:x∈U): Real.sinh x∈bSinh U ∧ Real.cosh x∈bCosh U := by
  rw [Real.sinh_eq,Real.cosh_eq, Real.exp_neg]
  have he:= mebox 5 hx
  exact ⟨mdiv (msub he (minv he)) mtwo,mdiv (madd he (minv he)) mtwo⟩
lemma at_point {x:ℝ} {B:IV} (hx:x∈B): At x (point B) := by
  have hi:=mHyp hx
  have hs : xs x∈sbB*bSinh B := mmul msbB hi.1
  exact ⟨hs,mmul msbB hi.2,fun i=>myBox hs i⟩
lemma at_segment {x y z:ℝ} {A B:Row0} (ha:At x A) (hb:At y B)
    (he:0≤x) (h:x≤z) (hh:z≤y): At z (around A B) := by
  have hz:= x_mono.monotone h
  have ht:= x_mono.monotone hh
  have hc : MonotoneOn ast (Ici 0) := by
    intro x hx y hy h
    unfold ast
    apply mul_le_mul_of_nonneg_left _ hsb.le
    apply Real.cosh_le_cosh.mpr; rw [abs_of_nonneg hx,abs_of_nonneg hy]; exact h
  have hv:=he.trans h
  have hp:=hv.trans hh
  exact ⟨span_conv ha.X hb.X hz ht,
    span_conv ha.T hb.T (hc he hv h) (hc hv hp hh),
    fun i=>span_conv (hb.mm i) (ha.mm i) ((Yanti i).antitone ht) ((Yanti i).antitone hz)⟩
variable (w:Row0)

namespace At
open CJet
variable {w:Row0} {x:ℝ} (h:At x w)
include h
lemma mXj : Fits (xj x) w.Xj := by
  unfold xj Xj
  intro n
  by_cases he:n%2=0
  · simpa only [Nat.even_iff,ite_eq_left he] using h.X
  simpa only [Nat.even_iff,ite_eq_right he] using h.T
lemma ms : Fits (halfS x) w.hsS :=
  (Fits.ray mhalf).mul (h.mXj.mul h.mXj)
lemma mP : Fits (ph x) w.Ph := by
  have hi := h.ms.neg
  exact (Fits.ray mphi0).mul (hi.exp (mebox 14 (hi 0)))
lemma mY (i:ℕ): Fits (ym i x) (w.Ym i) := by
  apply h.mXj.comp
  intro n
  unfold momRF; rw [xj0]
  exact mmul (mpow (mneg mo) _) (h.mm _)
lemma mU : Fits (u x) w.U := (h.mY 0).mul h.mP
lemma mP0: Fits (p0 x) w.P0:=(Fits.ray mo).sub h.mU
lemma mW: Fits (CJet.w x) w.W0 := (Fits.ray mo).sub (h.mP0.mul (h.mY 1))
lemma mH: Fits (CJet.h x) w.Hj := by
  unfold CJet.h Hj; dsimp only
  apply h.mU.comp
  intro n
  have he : 0 < sU (xs x) := u_pos _
  have hp := u_le (xs x)
  have hh:=u0 x
  rw [← hh] at he hp
  exact mmul (nc _) (mhBox _ _ he.le hp (h.mU 0))
lemma mJ: Fits (CJet.j x) w.J0 :=
  ((h.ms.add (Fits.ray (mlbox (mrt (mmul mtwo mpi)) _))).sub
    ((h.mY 0).log (mlbox (h.mY 0 0) _))).sub h.mP0
lemma mD: Fits (CJet.dj x) w.Dj :=
  ((((h.mY 1).mul (h.mY 1)).mul h.mJ).add ((h.mW.mul h.mW).mul h.mH))
lemma mK: Fits (CJet.kj x) w.Kj := (h.mD.add (((h.mY 0).mul (h.mY 0)).mul
    (h.mJ.add ((h.mP0.mul h.mP0).mul h.mH)))).sub (Fits.ray mo)
lemma mC: Fits (CJet.cj x) w.Cj := by
  have ih : Fits (CJet.gp x) w.Gp := (h.mY 0).mul (((h.mY 1).mul h.mJ).sub ((h.mW.mul h.mP0).mul h.mH))
  exact h.mD.neg.add ((Fits.ray (msub marB mo)).mul ((h.mXj.mul ih).sub h.mK))
lemma mMc: Fits (CJet.mc x) w.Mc:=h.mP.mul h.mP0.inv
lemma mJy: Fits (CJet.jy x) w.JY:=(h.mY 0).inv
lemma mRv: Fits (CJet.rv x) w.Rv:=h.mMc.sub ((h.mY 1).mul h.mJy)
lemma mVv: Fits (CJet.vv x) w.Vv:=
  ((Fits.ray mtwo).sub (h.mMc.mul (h.mXj.add h.mMc))).sub (((h.mY 1).mul h.mJy).mul h.mJy)
end At
end Row0
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_QuantJ
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Towers for q, N profiles and field composition identities. -/
open Set Filter MeasureTheory MeasureTheory.Measure Real
namespace GeneralMahler.SCal
open Profile Layers Jet
noncomputable section
lemma th_eq (x): thR x=Real.tanh x := by
  unfold thR xs ast; rw [Real.tanh_eq_sinh_div_cosh]; field_simp [hsb.ne']
lemma d_lift {f:ℝ→ℝ} (hf:TestF f) (x:ℝ):
    HasDerivAt (liftF f) (ast x*deriv f (xs x)) x := by
  rw [mul_comm]; exact (hf.diff _).hasDerivAt.comp x (xD x)
lemma dd_lift {f:ℝ→ℝ} (hf:TestF f) (x):
    HasDerivAt (DotF f)
      (xs x * deriv f (xs x) + ast x * (ast x*deriv (deriv f) (xs x))) x := by
  have hh : DotF f=fun x=> ast x*deriv f (xs x):=funext fun x=> (d_lift hf x).deriv
  rw [hh]
  exact (aD x).mul (d_lift hf.der x)
lemma SCov (f:ℝ→ℝ) (hf:TestF f) (x):
    NNf f x = ast x^2*deriv (deriv f) (xs x) ∧
    N2 f (xs x) = 2*f (xs x)+ thR x*DotF f x-
      (ast x)⁻¹ *((ast x)⁻¹)* NNf f x := by
  have hh : DotF f x=_:= (d_lift hf x).deriv
  unfold NNf; rw [DDot,(dd_lift hf x).deriv,hh]; unfold N2 N thR
  have hp := (ap x)
  constructor <;> field_simp <;> ring

namespace CJet
lemma rje (x): rj x 0=rad (xs x) := by change radK - dj x 0=_; rw [d0s,d_stable,rad,pow_two];rfl
lemma qje (x): qj x 0 = qu (xs x) := by change kk-√(rj x 0)=_; rw [rje]; rfl
lemma Ir: TW univ rj:= (TW.const _).sub Id
lemma Ie (h:RadH): TW univ el := Ir.root (fun x _=> by rw [rje]; exact h _)
lemma IQ (h:RadH): TW univ qj:= (TW.const _).sub (Ie h)
lemma It: TW univ it := Ia.inv (fun x _=> by rw [aj0]; exact (ap x).ne')
lemma IT: TW univ tj:=Ix.mul It
lemma IN (X:RF) (h:TW univ X): TW univ (NJ X):= h.tail.tail.sub (IT.mul h.tail)
lemma IS (X:RF) (h:TW univ X): TW univ (Sf X):=
  (((TW.const _).mul h).add (IT.mul h.tail)).sub ((It.mul It).mul (IN X h))

lemma nj0 (X:RF) (f:ℝ→ℝ) (h:TW univ X) (he:(fun x=>X x 0)=liftF f) (x:ℝ):
    X x 1=DotF f x ∧ X x 2=DDot f x ∧ NJ X x 0= NNf f x := by
  have hh (i:Nat): X x i=dV (liftF f) i x := by rw [← he]; exact (V_eq h isOpen_univ i (mem_univ x)).symm
  have hx : X x 1=DotF f x := hh 1
  have hy : X x 2= DDot f x:= hh 2
  refine ⟨hx,hy,?_⟩
  change X x 2-xj x 0*(aj x 0)⁻¹*X x 1= _
  rw [hx,hy,xj0,aj0]
  unfold NNf thR; ring
lemma sj0 (X:RF) (f:ℝ→ℝ) (h:TW univ X) (he:(fun x=>X x 0)=liftF f) (hf:TestF f) (x):
    Sf X x 0= N2 f (xs x) := by
  obtain ⟨ha,hb,hc⟩:= nj0 X f h he x
  change 2*X x 0+xj x 0*(aj x 0)⁻¹*X x 1-((aj x 0)⁻¹*(aj x 0)⁻¹)*NJ X x 0=_
  have he' : X x 0=f (xs x):= congrFun he x
  rw [he',ha,xj0,aj0,hc,(SCov f hf x).2]
  unfold thR; ring
end CJet
end

open Cert Cert.IV
namespace Row0
variable (w:Row0)

lemma mbb: bb∈bbB := by have hh:=mdiv (mc 602) (mc 1000);norm_num [bb] at *; exact hh
lemma mcc: cc∈ccB := by have hh:=mdiv (mc 365) (mc 1000);norm_num [cc] at *; exact hh
lemma mrB : Profile.r∈rB := by have hh:=mdiv (mc 22) (mc 100);norm_num [Profile.r] at *; exact hh
lemma mradB: CJet.radK∈ radB := msub mbb (mmul mrB mrB)
lemma mkkB:kk∈ kkB := mrt (msub mbb mcc)
namespace At
open CJet
variable {w:Row0}{x:ℝ}(h:At x w)
include h
lemma mRJ: Fits (rj x) w.Rj := (Fits.ray mradB).sub h.mD
lemma mQJ: Fits (qj x) w.Qj := (Fits.ray mkkB).sub (h.mRJ.rt (mrt (h.mRJ 0)))
lemma mit: Fits (it x) w.itB := h.mXj.drop.inv
lemma mtj: Fits (tj x) w.tjB := h.mXj.mul h.mit
lemma mNJ {X:RF} {A:J IV} (he:Fits (X x) A): Fits (NJ X x) (w.NB A) :=
  he.drop.drop.sub (h.mtj.mul he.drop)
lemma mSf {X:RF} {A:J IV} (he:Fits (X x) A): Fits (Sf X x) (w.SF A):=
  (((Fits.ray mtwo).mul he).add (h.mtj.mul he.drop)).sub ((h.mit.mul h.mit).mul (h.mNJ he))
end At
end Row0
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Grid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Finite interval cells of appendix §07. Actual tagged values. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Profile Jet CJet
namespace Tag

open Cert Cert.IV

lemma tower (i:Tag) (h:CJet.RadH) : TW univ (Fld i) := by
  have ha:=IK; have hb:=IC; have he:=IQ h
  cases i
  · exact Ir
  · exact ha
  · exact hb
  · exact he
  · exact ha.tail
  · exact hb.tail
  · exact he.tail
  · exact ha.tail.tail
  · exact hb.tail.tail
  · exact he.tail.tail
  · exact IN kj ha
  · exact IN cj hb
  · exact IN qj he
  · exact Irv
  · exact Ivv
  · exact IS qj he
lemma FldK (x): Fld K x 0=Kp (xs x):= (k0s x).trans (k_stable _)
lemma FldC (x): Fld C x 0=Cp (xs x):= (c0s x).trans (c_stable _)
lemma field_val (h:CJet.RadH) (hQ:TestF qu) (i:Tag) (x:ℝ) :
    Fld i x 0=act i x := by
  have heq : (fun x=>qj x 0)=liftF qu:= funext qje
  obtain ⟨ha,hb,hc⟩:= nj0 kj Kp IK (funext FldK) x
  obtain ⟨hh,hi,hj⟩:= nj0 cj Cp IC (funext FldC) x
  obtain ⟨hf,hg,hq⟩:= nj0 qj qu (IQ h) heq x
  cases i
  · exact rje x
  · exact FldK x
  · exact FldC x
  · exact qje x
  · exact ha
  · exact hh
  · exact hf
  · exact hb
  · exact hi
  · exact hg
  · exact hc
  · exact hj
  · exact hq
  · exact (krv x).trans (rv_stable _)
  · exact (kvv x).trans (v2_stable _)
  · exact sj0 qj qu (IQ h) heq hQ x
lemma fit {w:Row0} {x:ℝ} (h:Row0.At x w) (i:Tag) : Fits (Fld i x) (Jt i w) := by
  have ha := h.mK; have hb:= h.mC; have hc:= h.mQJ
  cases i
  · exact h.mRJ
  · exact ha
  · exact hb
  · exact hc
  · exact ha.drop
  · exact hb.drop
  · exact hc.drop
  · exact ha.drop.drop
  · exact hb.drop.drop
  · exact hc.drop.drop
  · exact h.mNJ (X:=kj) ha
  · exact h.mNJ (X:=cj) hb
  · exact h.mNJ (X:=qj) hc
  · exact h.mRv
  · exact h.mVv
  · exact h.mSf (X:=qj) hc
end Tag

namespace Grid
open Tag Cert Cert.IV
lemma mgrid (n:ℕ):nd n∈nbox n := mdiv (nc n) (mc 200)
lemma n_nn (n:ℕ):0≤nd n := by unfold nd; positivity
lemma dcell (n:ℕ): nd (n+1)-nd n∈deltG := by
  rw [show nd (n+1)-nd n=1/200 from by unfold nd; push_cast; ring]
  exact mdiv mo (mc 200)

lemma pGa (n:ℕ):Row0.At (nd n) (pG n) := Row0.at_point (mgrid n)
lemma pca (n:ℕ) (x) (hx:x∈Icc (nd n) (nd (n+1))):
    Row0.At x (pc n) := Row0.at_segment (pGa _) (pGa _) (n_nn _) hx.1 hx.2

lemma hcb0 (n:ℕ) (t:Tag) (i:ℕ) (F:IV) (ht:TW univ (Fld t))
    (he:∀ x∈Icc (nd n) (nd (n+1)),t.Fld x (i+2)∈F)
    (x:ℝ) (hx:x∈Icc (nd n) (nd (n+1))) :
    t.Fld x i ∈ cb0 n t i F :=
  mcChord _ ht i (nd n) (nd (n+1)) x hx.1 hx.2 _ _ _ _
    (fit (pGa _) t _) (fit (pGa _) t _) (dcell n) he

lemma hcb (n:ℕ) (t:Tag) (i:ℕ) (ht:TW univ (Fld t))
    (x:ℝ) (hx:x∈Icc (nd n) (nd (n+1))) :
    t.Fld x i ∈ cb n t i :=
  hcb0 n t i _ ht (fun x hx=>fit (pca n x hx) t _) x hx

lemma htot (n:ℕ) (t:Tag) (ht:TW univ (Fld t))
    (x:ℝ) (hx:x∈Icc (nd n) (nd (n+1))) :
    t.Fld x 0∈tot n t := by
  unfold tot; split
  · exact hcb0 n t _ _ ht (hcb n t 2 ht) x hx
  exact hcb n t _ ht x hx
end Grid
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Pass
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Range assertions and combined first derivative assertion for §07.
Integers in tables denote exact multiples 1/10000. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Profile Layers Jet Tag Cert Cert.IV

namespace Grid
lemma w_bd (a:Int): w (a*bandD) = (a:ℝ)/10000 := by unfold w; norm_num [bandD,den]; ring
lemma mem_band (x:ℝ) (l u:Int): x∈band l u ↔ (l:ℝ)/10000 ≤ x ∧ x ≤ (u:ℝ)/10000 := by
  change (w _ ≤ _ ∧ _ ≤w _)↔_
  rw [w_bd,w_bd]
lemma mbd (a:Int): (a:ℝ)/10000∈ bd a:= by apply (mem_band _ a a).mpr; simp

lemma SIn_check {b:Tag→IV} {a:Tag→ℝ} (ha:∀ i,a i∈b i) {k:Panel} (hh:checkSR b k=true): SIn a k := by
  simp only [checkSR,Bool.and_eq_true] at hh
  exact ⟨subB (ha Q) hh.1.1,subB (ha S) hh.1.2,subB (ha V) hh.2⟩

lemma mUcost (b:Tag→IV) (f:Tag→ℝ) (he:∀ i,f i∈b i): Ucost f∈ Ubox b := by
  have h1:= mmul (mbd 15070) (mmax mz (mneg (he NK)))
  have h2:=mdiv (mbd 96000) (msq (mbd 3520))
  have h3:= mmul (mbd 12500) (msq (madd (he dK) (mmul (mbd 210) (he dC))))
  have h4:= mmul (mmul (mc 5) (msq (mbd 430))) (msq (he dC))
  have hi:=madd h1 (mmul h2 (madd h3 h4))
  unfold Ucost
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl| (unfold mstar tc Profile.tr; norm_num)
lemma mUr: Ur∈UrB := by
  have hi:= mmul (mmul (mbd 5400) (msq (mbd 2200))) (msq (mbd 46000))
  unfold Ur
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl| (unfold r omegaP; norm_num)
lemma mCor {x y z:ℝ} {a b c:IV} (hx:x∈a) (hy:y∈b) (hz:z∈c): Cor x y z∈ CorB a b c := by
  have hi:= madd (madd (mmul (mbd 6500) (msq hz)) (mmul hz hy)) hx
  unfold Cor
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl| (unfold lam; norm_num)
lemma mTa {x y:ℝ}{a b:IV} (hx:x∈a) (hy:y∈b): Ta x y∈ TaB a b := by
  have hi:=msub (msub (mmul (mbd (-7400)) hy) (msq (mbd 3700))) (mmul (mbd 26000) hx)
  unfold Ta
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl| (unfold ell0 lam; norm_num)
lemma c_check {a:Tag→ℝ} {b:Tag→IV} (h:∀ i,a i∈b i) (he:joint b=true): Corr a := by
  simp only [joint,Bool.and_eq_true] at he
  have hi : tmin ∈ bd (-220) := by convert mbd (-220); norm_num [tmin]
  have hp : tmax ∈ bd 640 := by convert mbd 640; norm_num [tmax]
  have hh : mstar∈ bd 3520 := by convert mbd 3520; norm_num [mstar]
  exact ⟨mlt mz (mCor (h K) (h C) hi) he.1.1.1, mlt (mCor (h K) (h C) hp) mz he.1.1.2,
    mlt (msq hh) (mTa (h K) (h C)) he.1.2, mle (mUcost b a h) mUr he.2⟩

lemma allT_mem (a:Tag):a∈allT := by cases a <;> decide
lemma hasSub {a b:Tag→IV} (h:checkIn a b=true) (i:Tag): SubB (a i) (b i)=true :=
  List.all_eq_true.mp h i (allT_mem i)

lemma passes {n:ℕ} {b:Tag→IV} {a:Tag→ℝ} (ha:∀ i,a i∈b i) (he:pass0 n b=true):
    passR n a := by
  simp only [pass0,Bool.and_eq_true] at he
  refine
    ⟨fun i=> subB (ha i) (hasSub he.1.1.1.1 i), c_check ha he.1.1.1.2,
      fun hi i=>subB (ha i) (hasSub ?_ i), SIn_check ha he.1.2,
      fun hi=>subB (ha Q) ?_⟩
  · have h:=he.1.1.2
    simpa only [ite_eq_left hi] using h
  have h:=he.2; simpa only [ite_eq_left hi] using h
lemma cell_R {n} (hp:pass n) {x:ℝ} (hx:x∈Icc (nd n) (nd (n+1))) :
    (Tag.R.act x) ∈ rng R := by
  have he := htot n R CJet.Ir x hx
  have hv : R.Fld x 0=R.act x:= CJet.rje x
  rw [hv] at he
  simp only [pass,pass0,Bool.and_eq_true] at hp
  apply subB he (hasSub hp.1.1.1.1 R)
lemma cell_pass {n} (hp:pass n) (h:CJet.RadH) (hQ:TestF qu) {x:ℝ} (hx:x∈Icc (nd n) (nd (n+1))) :
    passR n (fun t=>t.act x) := by
  apply passes _ hp
  intro i; rw [← i.field_val h hQ]
  apply htot n i (tower i h) x hx
end Grid
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Regular
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Smooth growth and reflection for all profiles. -/
open Set Filter Real
noncomputable section
namespace GeneralMahler.SCal
open Profile Jet Tag Layers
variable {f:ℝ→ℝ}
lemma root_reg (h:TestF f) (d:ℝ) (he:0<d) (hh:∀ x,d≤f x) :
    TestF (fun x=> (√(f x))⁻¹) ∧ TestF (fun x=> √(f x)) := by
  let g:=fun x=> (√(f x))⁻¹
  have hp(x:ℝ):0<f x := lt_of_lt_of_le he (hh x)
  have hq(x:ℝ):0<√(f x):=Real.sqrt_pos.mpr (hp x)
  let F:=fun x=> √(f x)
  have hd (x): HasDerivAt F ((1/2*deriv f x)*g x) x := by
    convert (Real.hasDerivAt_sqrt (hp x).ne').comp x (h.diff x).hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl| (unfold g; ring)
  have hj (x): HasDerivAt g (((-(1/2)*deriv f x*g x)*g x)*g x) x := by
    convert (hd x).inv (hq x).ne' using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first| rfl|(unfold g F; ring)
  have ht : TestF g:= by
    intro n; induction n with
    | zero=>
      have he : PolyBound g:= PolyBound.of_bound (√d)⁻¹ fun x=>by
        unfold g; rw [Real.norm_of_nonneg (inv_pos.mpr (hq _)).le]
        exact (inv_le_inv₀ (hq _) (Real.sqrt_pos.mpr he)).mpr (Real.sqrt_le_sqrt (hh _))
      exact ⟨he,continuous_iff_continuousAt.mpr fun x=>(hj x).continuousAt⟩
    | succ n ih=>
      exact Moderate.mk' hj (((((Moderate.const _ n).mul (h.der n)).mul ih).mul ih).mul ih)
  exact ⟨ht, TestF.of_d hd (((TestF.const _).mul h.der).mul ht)⟩
lemma q_reg (h:∀ x,(5:ℝ)/100 ≤ rad x): TestF qu := by
  have hi: TestF rad := (TestF.const _).sub d_test
  exact (TestF.const _).sub (root_reg hi (5/100) (by norm_num) h).2

lemma ua_reg: TestF angle := by
  let f:=fun x:ℝ=> 1+x^2
  have he: TestF f := (TestF.const _).add (sq_test TestF.id)
  let v:=fun x=> (√(1+(x/sb)^2))⁻¹
  have hv: TestF v:= by
    have hp : TestF (fun x:ℝ=>x/sb) := by
      simp only [div_eq_mul_inv]; apply TestF.id.mul (TestF.const _)
    apply (root_reg ((TestF.const _).add (sq_test hp)) 1 zero_lt_one _).1
    intro x; nlinarith
  apply TestF.of_d (g:= fun x=> omegaP*(v x*sb⁻¹)) _ ((TestF.const _).mul (hv.mul (TestF.const _)))
  intro x
  convert (((Real.hasDerivAt_arsinh (x/sb)).comp x ((hasDerivAt_id' x).div_const sb)).const_mul omegaP)
    using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl|(unfold v;ring)
lemma ucs_reg: TestF uc ∧ TestF us := by
  let c:=fun x=>Real.cos (angle x)
  let s:=fun x=>Real.sin (angle x)
  have hc (x:ℝ):HasDerivAt c (-(s x*deriv angle x)) x:= by
    convert (Real.hasDerivAt_cos _).comp x (ua_reg.diff x).hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first|rfl|(unfold s;ring)
  have hs (x): HasDerivAt s (c x*deriv angle x) x :=
    (Real.hasDerivAt_sin _).comp x (ua_reg.diff x).hasDerivAt
  have hi (n:Nat): Moderate n c ∧ Moderate n s:= by
    induction n with
    | zero=> exact ⟨⟨PolyBound.of_bound 1 (fun x=>Real.abs_cos_le_one _),continuous_cos.comp ua_reg.cont⟩,
        ⟨PolyBound.of_bound 1 (fun x=>Real.abs_sin_le_one _),continuous_sin.comp ua_reg.cont⟩⟩
    | succ n ih=> exact ⟨Moderate.mk' hc (ih.2.mul (ua_reg.der n)).neg, Moderate.mk' hs (ih.1.mul (ua_reg.der n))⟩
  exact ⟨(TestF.const _).mul (fun n=>(hi n).1),(TestF.const _).mul (fun n=>(hi n).2)⟩

lemma Geven : Function.Even Profile.g := by
  intro x
  unfold Profile.g
  have hh:=Y_ref x; have he : X (-x)=Y x:=by rw [← Y_ref,neg_neg]
  rw [hh,he,j_ref,← j_ref,neg_neg]; ring
lemma Deven : Function.Even Profile.d := by
  intro x; unfold Profile.d Xd Yd
  have he : X (-x)=Y x:=by rw [← Y_ref,neg_neg]
  rw [he,Y_ref,j_ref,← j_ref,neg_neg]; ring
lemma Reven : Function.Even rad:= by intro x; unfold rad; rw [Deven]
lemma Keven : Function.Even Kp:=by intro x; unfold Kp; rw [Geven,Deven]
lemma Ceven : Function.Even Cp:=by
  intro x; unfold Cp; rw [Deven, map_deriv_odd g_test.der (map_deriv_even g_test Geven)]
lemma Qeven : Function.Even qu:=by intro x; unfold qu;rw [Reven]
lemma N_ref (hf:TestF f) (h:Function.Even f):Function.Even (N2 f):=by
  have hi:=map_deriv_even hf h
  intro x; unfold N2 N; rw [hi,h,map_deriv_odd hf.der hi]; ring
lemma lift_ref (h:Function.Even f) : Function.Even (liftF f) := by
  intro x; unfold liftF xs; rw [Real.sinh_neg,mul_neg,h]
lemma x_neg (x):xs (-x) = -(xs x):=by simp [xs]
lemma a_neg (x):ast (-x)=ast x:=by simp [ast]
lemma t_ref (h:TestF f) (hh:Function.Even f):
    Function.Odd (DotF f) ∧ Function.Even (DDot f)∧ Function.Even (NNf f) := by
  have hi (x:ℝ) := (d_lift h x).deriv
  have hv (x:ℝ) := (dd_lift h x).deriv
  have hj:= map_deriv_even h hh
  have ha : Function.Odd (DotF f):= by
    intro x; unfold DotF; rw [hi,hi,x_neg,a_neg,hj]; ring
  have hb : Function.Even (DDot f):= by
    intro x; unfold DDot; rw [hv,hv,x_neg,a_neg,hj,map_deriv_odd h.der hj]; ring
  exact ⟨ha,hb,fun x=> by unfold NNf thR; rw [ha,hb,x_neg,a_neg]; ring⟩
namespace Tag
lemma TvEv {i:Tag}(hf:TestF qu) (he:i.odd=false):Function.Even i.act:= by
  cases i <;> simp only [odd,Bool.true_eq_false] at he
  · exact lift_ref Reven
  · exact lift_ref Keven
  · exact lift_ref Ceven
  · exact lift_ref Qeven
  · exact (t_ref testK Keven).2.1
  · exact (t_ref testC Ceven).2.1
  · exact (t_ref hf Qeven).2.1
  · exact (t_ref testK Keven).2.2
  · exact (t_ref testC Ceven).2.2
  · exact (t_ref hf Qeven).2.2
  · exact lift_ref (map_deriv_odd v_test.der (map_deriv_even v_test Veven))
  exact lift_ref (N_ref hf Qeven)
lemma TvOd {i:Tag} (hf:TestF qu) (he:i.odd=true):Function.Odd i.act:=by
  cases i <;> simp only [odd,Bool.false_eq_true] at he
  · exact (t_ref testK Keven).1
  · exact (t_ref testC Ceven).1
  · exact (t_ref hf Qeven).1
  intro x
  change deriv Profile.v (xs (-x))-xs (-x)=-(deriv Profile.v (xs x)-xs x)
  rw [x_neg, map_deriv_even v_test Veven]; ring
end Tag
end GeneralMahler.SCal

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Circle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Circular profile and layer bound envelopes. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Tag Grid Jet Profile Layers Cert Cert.IV
noncomputable section
lemma lc_e (x) : lc x= r * Real.cos (omegaP*x):= by unfold lc liftF uc; rw [x_ang]
lemma ls_e (x) : ls x= r * Real.sin (omegaP*x):= by unfold ls liftF us; rw [x_ang]
lemma lcsq (x): lc x^2+ ls x^2 = r^2 := by
  rw [lc_e,ls_e]; have h:= Real.sin_sq_add_cos_sq (omegaP*x)
  linear_combination r^2*h
lemma dlc (x:ℝ): HasDerivAt lc (-omegaP*ls x) x:= by
  rw [funext lc_e,ls_e]
  convert ((Real.hasDerivAt_cos _).comp x ((hasDerivAt_id' x).const_mul omegaP)).const_mul r using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl|ring
lemma dls (x:ℝ):HasDerivAt ls (omegaP*lc x) x:=by
  rw [funext ls_e,lc_e]
  convert ((Real.hasDerivAt_sin _).comp x ((hasDerivAt_id' x).const_mul omegaP)).const_mul r using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl|ring
lemma NC_c (x:ℝ): N2 uc (xs x)=ca x*lc x-cb1 x*ls x := by
  have he := (SCov uc ucs_reg.1 x).2
  have hd : DotF uc = fun x=> -omegaP*ls x := funext fun x=> (dlc x).deriv
  have hh : DDot uc x = -omegaP*(omegaP*lc x):= by rw [DDot, hd]; exact ((dls x).const_mul _).deriv
  rw [he,NNf,hh,hd]
  change 2*lc x+_ - _=_
  unfold ca cb1; ring
lemma NC_s (x:ℝ): N2 us (xs x)=ca x*ls x+cb1 x*lc x := by
  have he := (SCov us ucs_reg.2 x).2
  have hd : DotF us = fun x=> omegaP*lc x:= funext fun x=>(dls x).deriv
  have hh : DDot us x= omegaP*(-omegaP*ls x):= by rw [DDot,hd]; exact ((dlc x).const_mul _).deriv
  rw [he,NNf,hh,hd]
  change 2*ls x+_ - _=_
  unfold ca cb1; ring

lemma nr2 (x): ro2 x=N2 uc (xs x)^2+ N2 us (xs x)^2:= by
  rw [NC_c,NC_s,ro2, ← lcsq x]; ring
lemma uA (x:ℝ): (ast x)⁻¹^2=aY (thR x^2) := by
  have hi : ast x ^2= xs x^2+sb^2 := by
    unfold ast xs; linear_combination sb^2*Real.cosh_sq_sub_sinh_sq x
  unfold aY thR
  have hp:=ap x
  field_simp [hsb.ne']
  linarith
lemma rx_eq (x:ℝ): ro2 x=rPoly (thR x^2):=by unfold ro2 ca cb1; rw [uA]; unfold rPoly; ring
lemma ri0 (x:ℝ): thR x^2∈Icc (0:ℝ) 1 := by
  have hi:= uA x; unfold aY at hi
  refine ⟨sq_nonneg _,?_⟩
  have hh:0≤ (1-thR x^2)/sb^2:=hi ▸ sq_nonneg _
  rw [le_div_iff₀ (sq_pos_of_pos hsb)] at hh; linarith
lemma rPolyMono : MonotoneOn rPoly (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  unfold rPoly
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  set a:=aY x
  set b:=aY y
  have he : a-b=(y-x)/sb^2:=by dsimp [a,b,aY];ring
  have hah (x:ℝ) (hx:x∈Icc (0:ℝ) 1): 0≤aY x ∧ aY x≤1/sb^2 := by
    have H₁ : 0 ≤ x:=hx.1;have H₂:x≤1:=hx.2
    unfold aY; exact ⟨div_nonneg (by linarith) (by positivity), div_le_div_of_nonneg_right (by linarith) (by positivity)⟩
  obtain ⟨ha,hb⟩:=hah x hx; obtain ⟨hc,hd⟩:=hah y hy
  change 0≤a at ha;change a ≤ _ at hb
  change 0≤b at hc;change b ≤ _ at hd
  have hh : 0 ≤ (1+b)^2- x*(2+a+b)/sb^2- (4+omegaP^2*(a+b))/sb^2 := by
    have hh1:0≤x:= hx.1; have hh2:x≤1:= hx.2
    unfold sb omegaP at *
    have hi:= mul_nonneg (show 0≤(1-x) by linarith) (show 0≤2+a+b by linarith)
    norm_num at *
    nlinarith
  have H:=mul_nonneg (mul_nonneg (show 0≤y-x by linarith) (sq_nonneg omegaP)) hh
  rw [← sub_nonneg]
  apply H.trans_eq
  rw [show y = x + sb^2*(a-b) from by field_simp [hsb.ne'] at he; linarith]
  field_simp [hsb.ne']; ring
lemma th_m: Monotone thR:= by
  intro x y h
  unfold thR xs ast
  have hp (y:ℝ):0 < sb*cosh y:= ap y
  rw [div_le_div_iff₀ (hp _) (hp _)]
  have he : 0 ≤ sinh (y-x):=Real.sinh_nonneg_iff.mpr (by linarith)
  rw [Real.sinh_sub] at he
  apply sub_nonneg.mp
  have hi:=mul_nonneg (sq_nonneg sb) he
  linarith
lemma r_monoP : MonotoneOn ro2 (Ici 0):= by
  intro x hx y hy h
  rw [rx_eq,rx_eq]; apply rPolyMono (ri0 _) (ri0 _); gcongr
  · apply le_trans _ (th_m hx); simp [thR,xs]
  apply th_m h
lemma ro2_neg (x):ro2 (-x)=ro2 x:=by rw [rx_eq,rx_eq,th_eq,th_eq];simp

end
lemma mroB {t:ℝ}{A:Row0} (h:Row0.At t A): ro2 t∈rBox A:=by
  have hp:omegaP∈omegaB := by unfold omegaB; convert mbd 46000; norm_num [omegaP]
  have hv:Profile.r∈bd 2200:=by convert mbd 2200; norm_num [r]
  have h₁:=msq (minv h.T)
  exact mmul (msq hv)
    (madd (msq (madd mtwo (mmul (msq hp) h₁))) (msq (mmul (mmul (madd mo h₁) hp)
      (mdiv h.X h.T))))
lemma pnT : (List.range 9).all testPn=true := by decide +kernel
lemma rp_pos (k:Nat) (h:k≤8):0 ≤ rPanel k:=by
  interval_cases k <;> norm_num [rPanel,panel,pan]
lemma rp_val (k:Nat) (h:k≤8) (x:ℝ) (hx:(panel k).hi < 720→ |x|≤nd (panel k).hi):
    ro2 x ≤ rPanel k^2 := by
  have he :ro2 x=ro2 |x|:=by rcases le_total 0 x with h|h; rw [abs_of_nonneg h]; rw [abs_of_nonpos h,ro2_neg]
  rw [he]
  by_cases hh:(panel k).hi<720
  · have hq:=List.all_eq_true.mp pnT k (List.mem_range.mpr (by omega))
    rw [testPn,ite_eq_left hh] at hq
    have hj:= r_monoP (abs_nonneg x) (n_nn _) (hx hh)
    exact hj.trans (mle (mroB (pGa _)) (msq (mbd _)) hq)
  have hu:k=8 := by interval_cases k <;> norm_num [panel,pan] at *
  rw [rx_eq]
  have hr:=ri0 |x|
  apply (rPolyMono hr (show 1∈Icc (0:ℝ) 1 from ⟨by norm_num,le_rfl⟩) hr.2).trans
  subst k; norm_num [rPoly,rPanel,r,omegaP,aY,panel,pan]
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_LayerAlg
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 layer rectangles. Evaluate only 4 vertices in H and V2. -/
open Set Filter Real
namespace GeneralMahler.SCal.PA
open Tag Grid Jet Profile Cert Cert.IV
lemma ek (k:Bool)(A:IV): eR k A∈eB k A:= ⟨le_rfl,le_rfl⟩
lemma orderE {x:ℝ}{A:IV}(h:x∈A) (he:A≠ unk) :
    eR false A ≤ x ∧ x≤ eR true A := by cases A; contradiction; exact h

-- Rational interval enclosures for the layer constants.
lemma mnums :
    Profile.tc∈bd 210∧ kar∈bd 11600 ∧ Profile.tr∈bd 430 ∧ h₀ ∈ bd 5000 ∧
      alpha∈ bd 22600 ∧ tmin∈bd (-220) ∧ eta∈bd 220 ∧ e₀∈bd 2560 := by
  have h:=mbd
  unfold Profile.tc Profile.tr kar h₀ alpha tmin eta e₀
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals change w _ ≤ _ ∧ _ ≤ w _; norm_num [w,bandD,den]
lemma mDef {x v:ℝ} {A B:IV}(h:x∈A) (hv:v∈B): Ldef x v ∈ defB A B := by
  obtain ⟨hc,hk,ht,hh,hb,_⟩:=mnums
  have hj:= msub (madd h hv) (mmul mtwo hk)
  exact msub (madd h (mmul hc hj)) (mmul (madd (mdiv ht (mmul mtwo hh)) (mdiv mo hb)) (msq hj))

lemma mBBc : bb∈bd 6020∧cc∈bd 3650∧ tmax∈bd 640 := by
  unfold bb cc tmax
  refine ⟨?_,?_,?_⟩
  all_goals change w _ ≤ _ ∧ _ ≤ w _; norm_num [w,bandD,den]
lemma mthree:(3:ℝ)∈(3:IV):= mc 3
lemma mfour:(4:ℝ)∈(4:IV):= mc 4
lemma mbMc : bm∈bmb := by
  obtain ⟨hb,hc,ht⟩:=mBBc
  obtain ⟨_,_,_,_,_,_,he,_⟩:=mnums
  exact mdiv (mmul (madd mo ht) (msub hb (mmul mthree he))) (mmul mthree
    (msub (mmul mthree (madd hb he)) (mmul mfour hc)))
lemma mCost {x v:ℝ} {A B:IV}(h:x∈A) (he:v∈B): Lcost x v ∈ costB A B := by
  obtain ⟨_,hk,hr,hj,_,ht,ha,hb⟩:=mnums
  have hi:= madd mBBc.1 ha
  exact madd (madd (madd (mmul mtwo (madd hi (mmul (msub hi hk) ht)))
    (mmul (mmul (mmul mtwo mbMc) h) he)) (mmul (mmul mtwo hb) (msq (mmul mtwo hr))))
    (mdiv (mmul hr hj) mtwo)
lemma mHV {x v:ℝ} {A B:IV}(h:x∈A) (he:v∈B): HV x v∈ hvB A B :=
  madd (madd (mmul mfour mBBc.2.1) (mmul (mmul mfour Row0.mkkB) h)) (mmul (mmul mtwo (msub Row0.mkkB h)) he)

lemma hBm (k:Bool)(x z:Nat):Hbnd k x z∈hbB k x z := by
  have h : Profile.r∈bd 2200 := by convert mbd 2200; norm_num [r]
  have he:=mmul (mmul mtwo h) (mbd (panel z).rh)
  unfold Hbnd hbB
  refine madd (mHV (ek ..) (ek ..)) ?_
  cases k
  · exact mneg he
  exact he
lemma passC (x:Nat) (hx:x≤8): allCn x=true := by
  interval_cases x <;> decide +kernel
lemma corner_pos {x z:Nat}(h:x≤8)(he:z≤8)(a b:Bool):
    Lcost (eR true (panel x).sr) (eR true (panel z).sr) <
      Ldef (Hbnd a x z) (eR b (panel x).vR):= by
  apply mlt (mCost (ek ..) (ek ..)) (mDef (hBm a x z) (ek ..))
  have hp := List.all_eq_true.mp (passC x h) z (List.mem_range.mpr (by omega))
  suffices hh:cond x z a b=true from hh
  simp only [corners,Bool.and_eq_true] at hp; cases a <;> cases b
  · exact hp.2
  · exact hp.1.2
  · exact hp.1.1.2
  exact hp.1.1.1

lemma lpos {x y a b c T:ℝ} (hc:c∈Icc (0:ℝ) 1) (hx:T<Ldef x a) (hy:T<Ldef y b):
    T<Ldef (mix x y c) (mix a b c) := by
  have he : T < mix (Ldef x a) (Ldef y b) c := by
    unfold mix; have h1:=hc.1; have h2:=hc.2
    rcases le_or_gt 1 c with h|h
    · have hh:c=1:=le_antisymm h2 h; rw [hh]; linarith
    have hi:= mul_lt_mul_of_pos_left hx (show 0<1-c by linarith)
    have hh:= mul_le_mul_of_nonneg_left hy.le h1
    linarith
  apply lt_of_lt_of_le he
  let r:=Profile.tr/(2*h₀)+1/alpha
  have hr:0 ≤ r:=by unfold r Profile.tr h₀ alpha; norm_num
  have hh : Ldef (mix x y c) (mix a b c) - mix (Ldef x a) (Ldef y b) c=
      r*(1-c)*c*((x+a)-(y+b))^2:= by unfold mix Ldef r; ring
  rw [← sub_nonneg,hh]; have hp:=hc.1; have hz:0≤1-c:=sub_nonneg.mpr hc.2
  positivity
lemma whole {x z:Nat} (hx:x≤8) (hz:z≤8) (t v:ℝ)
    (ht:t∈Icc (Hbnd false x z) (Hbnd true x z))
    (hv:v∈Icc (eR false (panel x).vR) (eR true (panel x).vR)):
    Lcost (eR true (panel x).sr) (eR true (panel z).sr)< Ldef t v := by
  obtain ⟨a,ha,he⟩:= mix_exists ht.1 ht.2
  obtain ⟨b,hb,hg⟩:= mix_exists hv.1 hv.2
  let c:=Lcost (eR true (panel x).sr) (eR true (panel z).sr)
  have h (p t:ℝ):mix t t p=t:=by unfold mix; ring
  have hh (k:Bool):c<Ldef (Hbnd k x z) v := by
    have hi:=lpos hb (corner_pos hx hz k false) (corner_pos hx hz k true)
    rwa [h, ← hg] at hi
  have hi:=lpos ha (hh false) (hh true)
  rwa [← he,h] at hi
end GeneralMahler.SCal.PA

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Data
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Compact certificate for §07 and table for later quadrature. -/
open Set Filter Real
namespace GeneralMahler.SCal.Grid
open Tag CJet Jet Profile Cert Cert.IV

lemma mGP (a:Int): gv a∈ GP a := by
  change IV.w _≤_ ∧ _≤ IV.w _
  rw [show IV.w (a*dn8)=gv a from by unfold gv IV.w; norm_num [dn8,den]; ring]
  exact ⟨le_rfl,le_rfl⟩

lemma nodeC (n:ℕ) (L:Line) (h:inData n L=true): NodeTrue n L := by
  let p:=pGa n
  have hk:=p.mK 0; have hc:=p.mC 0; have hq:=p.mQJ 0
  have hm: omegaP∈ bd 46000 := by convert mbd 46000; norm_num [omegaP]
  have hr: Profile.r∈ bd 2200 := by convert mbd 2200; norm_num [r]
  obtain ⟨ha,hb⟩:= mtrbox (mmul hm (mgrid n)) 8
  simp only [inData,Bool.and_eq_true] at h
  rw [k0s,k_stable] at hk;rw [c0s,c_stable] at hc;rw [qje] at hq
  refine ⟨subB p.X h.1.1.1.1.1,subB hk h.1.1.1.1.2,subB hc h.1.1.1.2,subB hq h.1.1.2,?_,?_⟩
  · unfold uc; rw [x_ang]; exact subB (mmul hr ha) h.1.2
  unfold us; rw [x_ang]; exact subB (mmul hr hb) h.2

lemma line_good (n:ℕ) (L:Line) (h:checkL n L=true) :
    NodeTrue n L∧(n<720 → pass n=true ∧ ∀ x∈Icc (nd n) (nd (n+1)), K.act x ≤ gv L.mx) := by
  simp only [checkL,Bool.and_eq_true] at h
  refine ⟨nodeC n L h.1,fun hn=>?_⟩
  have hh:=h.2; rw [ite_eq_left hn] at hh; simp only [Bool.and_eq_true] at hh
  refine ⟨hh.1,fun x hx=>?_⟩
  have hp:=htot n K IK x hx
  have he : K.Fld x 0=K.act x:=FldK x
  rw [he] at hp
  exact mle hp (mGP _) hh.2

lemma byRun (p:ℕ→Bool) (n m k:ℕ) (he:n+m=k) (h:runB p n m=true): By p n k := by
  subst k
  induction m with
  | zero=> intro i h1 h2; omega
  | succ m ih=>
    simp only [runB,Bool.and_eq_true] at h
    intro i h1 h2; by_cases H:i=n+m
    · exact H.symm ▸ h.1
    apply ih h.2 _ h1; omega
lemma byJoin {p:ℕ→Bool} {x y z:ℕ} (h:By p x y) (hh:By p y z):
    By p x z := by intro i he hz; rcases lt_or_ge i y with h'|h'; exact h i he h'; exact hh i h' hz
end GeneralMahler.SCal.Grid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Base
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Tail jets use log coordinate t, denoted y here. This implements D=x∂_x. -/
open Set Filter Real
noncomputable section
namespace GeneralMahler.SCal.Tail
open Profile Layers Jet
lemma xP (y):0<XX y:=Real.exp_pos _
lemma vP (y):0 < iv y:= inv_pos.mpr (xP y)
lemma iP (y):0 < ev y:= sq_pos_of_pos (vP y)
lemma Xd0 (y): HasDerivAt XX (XX y) y:= Real.hasDerivAt_exp _
lemma vd0 (y): HasDerivAt iv (-iv y) y:= by
  have hp:=xP y
  convert (Xd0 y).inv hp.ne' using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl|(unfold iv; field_simp)
lemma id0 (y): HasDerivAt ev (-2*ev y) y:= by
  convert (vd0 y).pow 2 using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl|(unfold ev; norm_num;ring)
lemma MkP (n:Nat) (y):0 < Mk n y:=mul_pos (pow_pos (xP y) _) (Ymp ..)
lemma M0e (y): Mk 0 y=1-ev y* Mk 1 y:= by
  unfold Mk ev iv; have hp:=xP y
  have he: (XX y)⁻¹^2*((XX y)^(1+1)*Ymk 1 (XX y))=Ymk 1 (XX y):=by field_simp
  rw [he]; norm_num
  linarith [R0 (XX y)]
lemma Mke (i:Nat) (y):
    Mk (i+1) y+ev y*Mk (i+2) y=((i+1:Nat):ℝ)*Mk i y := by
  unfold Mk ev iv; have hp:=xP y; let x:= XX y
  have he:= SCal.Rn x i
  have hh : x⁻¹^2*(x^(i+2+1)*Ymk (i+2) x) = x^(i+1)*Ymk (i+2) x := by
    change 0<x at hp; simp only [pow_succ]; field_simp
  change x^(i+1+1)*Ymk _ x+_ = _; rw [hh,pow_succ _ (i+1)]
  change _+x^(i+1)*Ymk _ x= ((i+1:Nat):ℝ)*(x^(i+1)*Ymk i x)
  linear_combination x^(i+1)*he
lemma Mk_hi (i:Nat) (y): Mk i y ≤ i.factorial:=by
  induction i with
  | zero=>
    rw [M0e]; have hp:=iP y; have h:=MkP 1 y
    norm_num; nlinarith
  | succ i ih=>
    have he:=Mke i y
    have hp:=iP y; have h:=MkP (i+2) y
    rw [Nat.factorial_succ]
    push_cast at *; nlinarith [show (0:ℝ) ≤ i by positivity]

lemma Dmk (n:Nat) (y): HasDerivAt (Mk n) (ev y*Mk (n+2) y) y := by
  let x:= XX y
  have hi:= ((Xd0 y).pow (n+1)).fun_mul ((DYmk x n).comp y (Xd0 y))
  have hh : HasDerivAt (Mk n) (((n+1:Nat):ℝ)*Mk n y-Mk (n+1) y) y := by
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first|rfl | skip
    unfold Mk x; simp only [Nat.add_sub_cancel,pow_succ,Function.comp_apply,Pi.pow_apply]
    ring
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  linarith [Mke n y]

lemma Dqp (n:Nat) (y): HasDerivAt (Qp n) ((n:ℝ)*Qp n y-Qp (n+2) y) y:= by
  have h:= ((Xd0 y).pow n).fun_mul ((d_phi (XX y)).comp y (Xd0 y))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first| rfl|skip
  unfold Qp
  cases n <;> simp only [Nat.add_sub_cancel,pow_succ,Function.comp_apply] <;> norm_num <;> ring
lemma Wd0 (y):HasDerivAt Wv (-2*Wv y+ev y) y:= by
  convert (id0 y).mul ((hasDerivAt_id' y).add_const Z0) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl|(unfold Wv Lv; ring)

namespace JT

lemma Ti : TW univ IJ:= by
  intro n x _
  convert (id0 x).const_mul ((-2:ℝ)^n) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first|rfl|(unfold IJ;rw [pow_succ];ring)
lemma IJ0 (x):IJ x 0=ev x:=by unfold IJ; ring
lemma Tw: TW univ WW:=by
  intro n x _
  induction n with
  | zero=>
    convert Wd0 x using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first|rfl| simp only [WW,Wrec,IJ0,ray]
  | succ n ih=>
    exact ((ih.const_mul (-2:ℝ)).fun_add (Ti n x (mem_univ _)))
lemma Tp (i): TW univ (TP i):= by
  intro n x _
  induction n generalizing i with
  | zero=>exact Dqp i x
  | succ n ih=>exact ((ih i).const_mul (i:ℝ)).fun_sub (ih (i+2))
lemma TM0 (x m): TM m 0 x 0=Mk m x:=by simp [TM,Mrec]
lemma Tm (m i): TW univ (TM m i):= by
  intro n x _
  induction n generalizing m i with
  | zero=>
    convert ((id0 x).pow i).mul (Dmk m x) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first|rfl|skip
    unfold TM; simp only [Mrec]
    cases i <;> simp only [Nat.add_sub_cancel,pow_succ,Pi.mul_apply] <;> norm_num
    ring
  | succ n ih=>
    exact (((ih m i).const_mul (-2*(i:ℝ))).fun_add (ih (m+2) (i+1)))
end JT
end GeneralMahler.SCal.Tail

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Limit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 log domain elementary envelope values. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail
open JT Grid Profile Tag Cert Cert.IV Jet Layers
noncomputable section
lemma ey0 : XX y0=64:=Real.exp_log (by norm_num)
lemma ro_lim :
    (4158/1000:ℝ)≤ y0 ∧ y0≤416/100 ∧ 4/10≤ Z0 ∧ Z0≤42/100 := by
  have h64 : (64:ℝ)∈ c 64 := mc 64
  have hi:= mlbox h64 6
  have hh:=(mrt (mmul mtwo mpi))
  have hp:= msub (mlbox hh 6) mhalf
  have h₁:=subB hi (B:=band 41580 41600) (by decide +kernel)
  have h₂:=subB hp (B:=band 4000 4200) (by decide +kernel)
  rw [mem_band] at h₁ h₂
  unfold Z0 y0; norm_num at *
  exact ⟨by linarith [h₁.1],by linarith [h₁.2],by linarith [h₂.1],by linarith [h₂.2]⟩

lemma vsmall {y:ℝ} (h:y0≤ y): 64 ≤ XX y ∧ iv y ≤1/64 ∧ ev y≤1/4096 := by
  have hh:=exp_le_exp.mpr h
  change XX y0 ≤ XX y at hh
  rw [ey0] at hh
  have hi:iv y≤1/64:=by
    unfold iv; rw [one_div]
    exact (inv_le_inv₀ (xP _) (by norm_num)).mpr hh
  have he:=vP y
  refine ⟨hh,hi,?_⟩
  unfold ev; nlinarith
lemma econ {y:ℝ} (h:y0≤y):
    45/10≤ Lv y ∧ Wv y ≤112/100000+ 1/100000 ∧
      ev y*(Lv y-3/2)≤ 76/100000 := by
  have he (x:ℝ) (hx:y0≤x):45/10≤ Lv x := by
    obtain ⟨hh,_,hj,_⟩:=ro_lim
    unfold Lv; linarith
  have hv (a:ℝ) (ha:a≤3/2) :
      Wv y-ev y*a ≤ Wv y0-ev y0*a := by
    let f:=fun y=> Wv y-ev y*a
    have hd (x) : HasDerivAt f ((-2*Wv x+ev x)-(-2*ev x)*a) x :=
      (Wd0 x).fun_sub ((id0 x).mul_const a)
    apply antitoneOn_of_deriv_nonpos (f:=f) (convex_Ici y0)
      (fun x _=> (hd x).continuousAt.continuousWithinAt)
      (fun x _=> (hd x).differentiableAt.differentiableWithinAt)
      _ (mem_Ici.mpr le_rfl) h h
    intro x hx
    rw [(hd _).deriv]
    have hh:=he x (interior_subset hx)
    have hi:=iP x
    unfold Wv; nlinarith
  have hi:=hv 0 (by norm_num)
  have hj:=hv (3/2) le_rfl
  have hk:=ro_lim
  have h0: ev y0=1/4096:=by unfold ev iv; rw [ey0]; norm_num
  refine ⟨he y h,?_,?_⟩
  · unfold Wv Lv at *; rw [h0] at hi; linarith [hk.2.1,hk.2.2.2]
  unfold Wv at *
  rw [h0] at hj; unfold Lv at *; linarith [hk.2.1,hk.2.2.2]

lemma Q_limit {y:ℝ} (h:y0≤y) (i:Nat) (hi:i≤10):
    0≤ Qp i y ∧ Qp i y ≤1/10^9 := by
  have hp (x:ℝ) (i:ℕ): 0 < Qp i x:=mul_pos (pow_pos (xP x) _) (phi_pos _)
  have he : Qp 10 y ≤ Qp 10 y0 := by
    apply antitoneOn_of_deriv_nonpos (f:=Qp 10) (convex_Ici y0)
      (fun x _=> (Dqp 10 x).continuousAt.continuousWithinAt)
      (fun x _=> (Dqp 10 x).differentiableAt.differentiableWithinAt)
      _ (mem_Ici.mpr le_rfl) h h
    intro x hx
    rw [(Dqp _ _).deriv]
    have hh : Qp (10+2) x=(XX x)^2 * Qp 10 x := by unfold Qp; ring
    rw [hh]; rw [sub_nonpos]; apply mul_le_mul_of_nonneg_right _ (hp x 10).le; norm_num; nlinarith [(vsmall (show y0≤ x from interior_subset hx)).1]
  refine ⟨(hp y i).le, le_trans ?_ (he.trans ?_)⟩
  · unfold Qp; apply mul_le_mul_of_nonneg_right _ (phi_pos _).le
    apply pow_le_pow_right₀ _ hi
    linarith [(vsmall h).1]
  unfold Qp; rw [ey0,phi_apply,show (-(64^2)/2:ℝ)= -2048 by norm_num, Real.exp_neg]
  have hv : (√(2*π))⁻¹ ≤ 1 := by
    have hp : 1 ≤ √(2*π) := by
      have h := Real.pi_gt_three
      rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith
    rwa [inv_le_one₀ (by positivity)]
  have he : (2:ℝ)^100 ≤ Real.exp 2048 := by
    have H := Real.add_one_le_exp 1
    have hi : (2:ℝ)^100 ≤ (Real.exp 1)^100 := by gcongr; linarith
    apply hi.trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr; norm_num
  have hs : (Real.exp 2048)⁻¹ ≤ ((2:ℝ)^100)⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr he
  apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul hv hs (by positivity) (by norm_num)) (by norm_num))
  norm_num
end

variable {x:ℝ} (hv:y0≤ x)
include hv
lemma lXI: ev x∈ XI :=
  span_conv mz (mdiv mo (show (4096:ℝ)∈ c 4096 from mc 4096)) (iP _).le (vsmall hv).2.2
lemma lBI: Fits (IJ x) BI := fun _=> mmul (mpow (mneg mtwo) _) (lXI hv)
lemma lwb : Wv x∈ wb := by
  have he:= econ hv
  unfold wb
  apply span_conv mz (mdiv (mc 113) (mc 100000))
  · unfold Wv; nlinarith [he.1,iP x]
  norm_num; linarith [he.2.1]
lemma lwr: Fits (WW x) wr := by
  intro n; induction n with
  | zero=>exact lwb hv
  | succ n ih=> exact madd (mmul (mneg mtwo) ih) (lBI hv n)
lemma lpF (m:Nat): Fits (TP m x) fun n=> pr n m := by
  intro n; induction n generalizing m with
  | zero=>
    change _∈ pr 0 m; rw [pr]; split
    next h=>
      have hh:=Q_limit hv m h
      have ha : (1/10^9:ℝ) ∈ (1/IV.c 1000000000) := by
        convert mdiv mo (mc 1000000000) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
      exact span_conv mz ha hh.1 hh.2
    trivial
  | succ n ih=> exact msub (mmul (ubb m) (ih m)) (ih _)
lemma lTm0 (m:Nat): Mk m x∈m0B m := by
  have h:= (vsmall hv).2.2
  have hQ:1/4096 ∈xiMax := mdiv mo (show (4096:ℝ) ∈ c 4096 from mc 4096)
  have h0:Mk 0 x ≤ 1 := by simpa using Mk_hi 0 x
  have h1:Mk 1 x ≤ 1 := by simpa using Mk_hi 1 x
  have hL : 1- 1/4096 ≤ Mk 0 x:= by rw [M0e]; nlinarith [iP x]
  unfold m0B
  split
  next hh=> subst m; exact span_conv (msub mo hQ) mo hL h0
  split
  next hh=>
    subst m
    refine span_conv (msub mo (mmul (mc 3) hQ)) mo ?_ h1
    have hh:= Mke 0 x
    have hi: Mk 2 x ≤ 2:=by convert Mk_hi 2 x; norm_num [Nat.factorial]
    norm_num at *; nlinarith [iP x]
  exact span_conv mz (ubb _) (MkP m x).le (Mk_hi m x)
lemma lTm (m i:Nat): Fits (TM m i x) (fun n=>mr n m i):= by
  intro n; induction n generalizing m i with
  | zero=>exact mmul (mpow (lXI hv) _) (lTm0 hv m)
  | succ n ih=>exact madd (mmul (mmul (mneg mtwo) (ubb _)) (ih m i)) (ih _ _)
end GeneralMahler.SCal.Tail

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Tower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 tail profile identities using normalized log towers. -/
open Set Filter Real
open scoped Topology
noncomputable section
namespace GeneralMahler.SCal.Tail.JT
open Profile Layers Jet
variable (x:ℝ) -- logarithmic point

lemma ym_id : sY (XX x) * XX x=MJ x 0 := by rw [MJ,TM0]; unfold sY Mk; ring
lemma n_id : ev x * NJ x 0=sB (XX x) := by
  rw [NJ,TM0]; unfold ev iv sB Mk; have he:=xP x; field_simp
lemma pt0 : Pt x 0=XX x*phi (XX x)*MJ x 0:=by
  change (XX x ^1*phi (XX x))*_=_
  rw [pow_one]
lemma U0 : U x 0=sU (XX x):=by
  change IJ x 0*Pt x 0=_
  rw [IJ0,pt0, ← ym_id]
  have he:=xP x; unfold ev iv sU; field_simp
lemma MPv : 0 < MJ x 0:= by rw [MJ,TM0]; apply MkP
lemma mi_id : ev x * mi x 0= 1 - (MJ x 0)^2 := by
  change ev x * (NJ x 0 *(1+MJ x 0))=_
  rw [NJ,MJ,TM0,TM0,M0e]; ring
lemma P0 : PP x 0=sP (XX x):= by change 1-U x 0=_; rw [U0];rfl
lemma H0 : HH x 0=sH (XX x):= by
  change Nat.factorial 0*Qh 0 (U x 0)=_
  rw [U0]; unfold sH; simp

lemma ht1 (u:ℝ) (hu:0<u) (hv:u<1):
    Qh 0 u-1/2=u/2*((1-u)⁻¹-Qh 1 u) := by
  let f:=fun u:ℝ=>u^2*Qh 0 u
  have he:= ((hasDerivAt_id' u).pow 2).fun_mul (hdQ 0 hv)
  let g:= fun u:ℝ=> -Real.log (1-u)-u
  have h:= ((((hasDerivAt_id' u).const_sub 1).log (sub_pos.mpr hv).ne').neg.sub (hasDerivAt_id' u))
  have he' : f =ᶠ[𝓝 u] g := by
    filter_upwards [Ioo_mem_nhds hu hv] with x hx
    exact hlog hx.1 hx.2
  have hf : HasDerivAt f _ u := he
  have hg : HasDerivAt g _ u := h
  have hj:= hf.unique (hg.congr_of_eventuallyEq he')
  norm_num at hj
  have hp : 0<1-u := by linarith
  field_simp at hj ⊢
  nlinarith

lemma DH0 : ev x*DH x 0 = HH x 0-1/2 := by
  let y:=sU (XX x)
  change ev x*((1/2*Pt x 0)*((PP x 0)⁻¹-_))=_
  have h : HH x 0=Qh 0 y := H0 x
  have he : PP x 0=1-y:= P0 x
  have hz : H1 x 0=Qh 1 y := by
    change (Nat.factorial _ : ℝ)*Qh 1 (U x 0)= _
    rw [U0]; unfold y; norm_num
  rw [h,he,hz,ht1 y (u_pos _) (u_le _)]
  have hp : ev x *Pt x 0=y := by rw [← IJ0]; exact U0 x
  rw [← hp]; ring
lemma WZ0 :
    wZ x 0= ev x*(sJ (XX x) -(XX x *XX x)/2+(PP x 0)^2*(HH x 0)) := by
  have hm : Real.log (MJ x 0)=Real.log (sY (XX x))+x := by
    rw [← ym_id, Real.log_mul (show sY (XX x)≠0 from (Ymp _ _).ne') (xP _).ne']
    unfold XX; simp
  change Wv x+ IJ x 0*((-Real.log (MJ x 0)-(PP x 0-1))+
    (PP x 0*PP x 0*HH x 0-1/2))=_
  rw [hm,IJ0,P0]; unfold Wv Lv Z0 sJ; ring

lemma dF0 : dF x 0 = d (XX x) := by
  change 1/2+IJ x 0*(DH x 0+(1/2*(NJ x 0*NJ x 0)-2*PP x 0*HH x 0*NJ x 0)+
    NJ x 0*NJ x 0*wZ x 0)=_
  have hi : ev x*(XX x*XX x)=1:= by unfold ev iv; have hp:=xP x; field_simp
  rw [IJ0, mul_add,mul_add,DH0,WZ0,← d_stable]
  unfold sd sW
  rw [← H0,← n_id, ← P0]
  linear_combination (ev x*(NJ x 0 ^2)/(-2))*hi

lemma gF0 : gF x 0=g (XX x) := by
  change 1/4*IJ x 0 * mi x 0- (1/2*(MJ x 0*MJ x 0)*wZ x 0)+1/4=_
  rw [IJ0,mul_assoc (1/4:ℝ),mi_id,WZ0]
  have he (x:ℝ) : g x= (1 - (sY x)^2*(j x+(sP x)^2*sH x))/2 := by
    unfold g; rw [h_f]
    have hh : X x ^ 2*(sU x ^ 2*sH x)=(sP x*sY x)^2*sH x:=by rw [← Xu]; ring
    rw [hh]; unfold sY; rw [Ym0]; ring
  rw [he,H0,P0,lp_st, ← ym_id]
  have hp := xP x; unfold ev iv; field_simp; ring

lemma kF0 : kF x 0=Kp (XX x) := by
  rw [Kp,← gF0,← dF0]
  let t:=IJ x 0; let z:=mi x 0; let m:= M2 x 0; let n:= NJ x 0
  have he : NN x 0=n*n := rfl
  have hf : t*z=1-m := by unfold t m; rw [IJ0,mi_id]; change 1-_=1-MJ x 0*MJ x 0;rw [pow_two]
  have hh : z = n*(2-t*n) := by
    have hi : MJ x 0=1-t*n := by unfold t n; rw [MJ,NJ,TM0,TM0,IJ0,M0e]
    change n*(1+MJ x 0)=_; rw [hi]; ring
  let a:= A x 0; let b:= DH x 0; let w:= Wv x; let d:= del x 0
  change w+t*((b+a-n+1/2*(t*NN x 0)+3/2+(m+t*NN x 0)*d+(NN x 0-z)*w)-3/2)=
    1/2+t*(b+a+NN x 0*(w+t*d))-2*(1/4*t*z-1/2*m*(w+t*d)+1/4)
  rw [he]; rw [show m=1-t*z from by linarith]; rw [hh];ring

lemma TeM:TW univ MJ:=Tm 0 0
lemma TeN:TW univ NJ:=Tm 1 0
lemma TeP:TW univ Pt:=(Tp _).mul TeM
lemma TeU:TW univ U:=Ti.mul TeP
lemma TePP:TW univ PP:=(TW.const _).sub TeU
lemma huJ : ∀ x:ℝ,U x 0∈Iio 1:=fun x=>by rw [U0]; exact u_le _
lemma ppj (x):0 < PP x 0:=by rw [P0,sPe]; apply p_pos
lemma TeH: TW univ HH:=TeU.comp Ihf fun x _=> huJ x
lemma TeH1: TW univ H1:=TeU.comp Ihf.tail fun x _=> huJ x
lemma Ted: TW univ del:=
  (((TeM.log (fun x _=> (MPv x).ne')).neg.sub (TePP.sub (TW.const _))).add
    (((TePP.mul TePP).mul TeH).sub (TW.const _)))
lemma TeZ: TW univ wZ:= Tw.add (Ti.mul Ted)
lemma Tem2:TW univ M2:=TeM.mul TeM
lemma Ten2:TW univ NN:=TeN.mul TeN
lemma Temi:TW univ mi:=TeN.mul ((TW.const _).add TeM)
lemma TeG:TW univ G0:=
  (((TW.const _).mul Ti).mul Temi).sub (((TW.const _).mul Tem2).mul TeZ)
lemma TeA:TW univ A:= ((TW.const _).mul Ten2).sub ((((TW.const _).mul TePP).mul TeH).mul TeN)
lemma TeDH : TW univ DH:=
  ((TW.const _).mul TeP).mul ((TePP.inv (fun x _=>(ppj x).ne')).sub TeH1)
lemma TeDD : TW univ DD:= (TeDH.add TeA).add (Ten2.mul TeZ)
lemma TeN1:TW univ N1:=Ti.mul Ten2
lemma TeKR:TW univ KR:=
  ((((((TeDH.add TeA).sub TeN).add ((TW.const _).mul TeN1)).add (TW.const _)).add
    ((Tem2.add TeN1).mul Ted)).add ((Ten2.sub Temi).mul Tw))
lemma TeCQ:TW univ CQ:= ((TW.const _).mul (TeG.tail.tail.sub TeG.tail)).sub TeDD
lemma TdF:TW univ dF:= (TW.const _).add (Ti.mul TeDD)
lemma TkF:TW univ kF:=Tw.add (Ti.mul (TeKR.sub (TW.const _)))
lemma TgF:TW univ gF:=TeG.add (TW.const _)
lemma TcF:TW univ cF:=(Ti.mul TeCQ).sub (TW.const _)

lemma path (f:ℝ→ℝ) (hf:TestF f) (F:RF) (he:TW univ F) (hh:∀ x,F x 0=f (XX x)):
    F x 1=XX x*deriv f (XX x)∧
      F x 2=F x 1+ XX x*XX x*deriv (deriv f) (XX x) := by
  have hi (g:ℝ→ℝ) (hg:TestF g) (x:ℝ): HasDerivAt (fun x=>g (XX x)) (deriv g (XX x)* XX x) x :=
    (hg.diff _).hasDerivAt.comp x (Xd0 x)
  have h₁ (x:ℝ) : F x 1=XX x *deriv f (XX x) := by
    have he := he 0 x (mem_univ _)
    simp_rw [hh] at he
    rw [show F x 1=_ from he.unique (hi f hf x)]
    ring
  refine ⟨h₁ x,?_⟩
  have ht := he 1 x (mem_univ _)
  simp_rw [h₁] at ht
  rw [show F x 2=_ from ht.unique ((Xd0 x).fun_mul (hi (deriv f) hf.der x)),h₁]
  ring

lemma cF0 : cF x 0=Cp (XX x) := by
  obtain ⟨h,h₁⟩:=path x g g_test gF TgF gF0
  have hp := xP x
  have he : ev x*(gF x 2-gF x 1)=deriv (deriv g) (XX x) := by rw [h₁]; unfold ev iv; field_simp; ring
  have hi : ev x*(G0 x 2-G0 x 1)=deriv (deriv g) (XX x) := by
    change ev x*((G0 x 2+0)-(G0 x 1+0))=_ at he; simpa using he
  rw [Cp,← dF0,← hi]
  change IJ x 0*((ar-1)*(G0 x 2-G0 x 1)-DD x 0)-1/2= -(1/2+IJ x 0*DD x 0)+_
  rw [IJ0]; ring
end GeneralMahler.SCal.Tail.JT

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Enclose
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interval AD bounding envelopes DD, CQ, KR. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail.JTB
open JT Grid Profile Tag Cert Cert.IV Jet Layers

lemma mquarter : (1/4:ℝ)∈(1/4:IV) :=
  mdiv mo (mc 4)
lemma m32: (3/2:ℝ)∈(3/2:IV):=
  mdiv (mc 3) mtwo

variable {x:ℝ} (h:y0≤x)
include h
lemma fmJ: Fits (MJ x) bmJ:=lTm h 0 0
lemma fnJ:Fits (NJ x) bnJ:= lTm h 1 0
lemma fPt: Fits (JT.Pt x) bPt:= (lpF h 1).mul (fmJ h)
lemma fU: Fits (U x) bU:= (lBI h).mul (fPt h)
lemma fPP: Fits (PP x) bPP:= (Fits.ray mo).sub (fU h)
lemma fhf0: Fits (hfRF (U x 0)) hf0:= by
  have hi:= fU h 0
  have he: 0<U x 0:=by rw [U0]; apply u_pos
  have hh: U x 0<1:= huJ x
  intro n; exact mmul (nc _) (mhBox n _ he.le hh hi)
lemma fbH: Fits (JT.HH x) bHH:= (fU h).comp (fhf0 h)
lemma fbH1: Fits (JT.H1 x) bH1:= (fU h).comp (fhf0 h).drop
lemma fbDH: Fits (DH x) bDH :=
  ((Fits.ray mhalf).mul (fPt h)).mul ((fPP h).inv.sub (fbH1 h))
lemma fbM: Fits (M2 x) bM:= (fmJ h).mul (fmJ h)
lemma fbN: Fits (NN x) bN:= (fnJ h).mul (fnJ h)
lemma fbD: Fits (del x) bDel:=
  ((((fmJ h).log (mlbox (fmJ h 0) _)).neg.sub ((fPP h).sub (Fits.ray mo))).add
    ((((fPP h).mul (fPP h)).mul (fbH h)).sub (Fits.ray mhalf)))
lemma fbZ: Fits (wZ x) bZ := (lwr h).add ((lBI h).mul (fbD h))
lemma fbA: Fits (JT.A x) bA:= ((Fits.ray mhalf).mul (fbN h)).sub
  ((((Fits.ray mtwo).mul (fPP h)).mul (fbH h)).mul (fnJ h))
lemma fbMi: Fits (mi x) bMi:=(fnJ h).mul ((Fits.ray mo).add (fmJ h))
lemma fDD: Fits (DD x) bDD:=((fbDH h).add (fbA h)).add ((fbN h).mul (fbZ h))
lemma fbG: Fits (G0 x) bG:=
  (((Fits.ray mquarter).mul (lBI h)).mul (fbMi h)).sub (((Fits.ray mhalf).mul (fbM h)).mul (fbZ h))
lemma fbN1: Fits (N1 x) bN1:=(lBI h).mul (fbN h)
lemma fKR: Fits (KR x) bKR:=
  (((((((fbDH h).add (fbA h)).sub (fnJ h)).add ((Fits.ray mhalf).mul (fbN1 h))).add
    (Fits.ray m32)).add (((fbM h).add (fbN1 h)).mul (fbD h))).add
    (((fbN h).sub (fbMi h)).mul (lwr h)))
lemma fCQ: Fits (CQ x) bCQ:=
  ((Fits.ray (msub Row0.marB mo)).mul ((fbG h).drop.drop.sub (fbG h).drop)).sub (fDD h)
lemma fdF: Fits (dF x) bdF:= (Fits.ray mhalf).add ((lBI h).mul (fDD h))
lemma fcF: Fits (cF x) bcF:= ((lBI h).mul (fCQ h)).sub (Fits.ray mhalf)
lemma fkF: Fits (kF x) bkF:=
  (lwr h).add ((lBI h).mul ((fKR h).sub (Fits.ray m32)))
end GeneralMahler.SCal.Tail.JTB

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Coords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Convert tail jets into coordinate and number operator bounds. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail
open JT JTB Grid Jet Tag Cert Cert.IV Profile Layers
noncomputable section
lemma rre0 (x:ℝ):rrF x 0=rad (XX x):=by change CJet.radK - dF x 0=_;rw [dF0,rad,pow_two];rfl
lemma qe0 (x:ℝ):ql x 0=qu (XX x):= by change kk-√(rrF x 0)=_;rw [rre0];rfl
lemma Twq (h:CJet.RadH):TW univ ql := (TW.const _).sub
  (((TW.const _).sub TdF).root (fun x _ =>by change 0< rrF x 0; rw [rre0]; exact h _))

lemma dots_log {x y:ℝ} (hh:xs x=XX y) {F:RF} (h:TW univ F) {f:ℝ→ℝ} (hf:TestF f)
    (he:∀ t,F t 0=f (XX t)) :
    let G:=bt x y
    DotF f x=G*F y 1 ∧ NNf f x = G^2*(F y 2-F y 1) ∧
      DDot f x=G^2*(F y 2-F y 1)+F y 1 ∧
      N2 f (xs x)=2*F y 0+F y 1-ev y*(F y 2-F y 1) := by
  intro G
  obtain ⟨hp,hv⟩:=path y f hf F h he
  have h₁:= (d_lift hf x).deriv
  have ha:=SCov f hf x
  have h₂:= (dd_lift hf x).deriv
  rw [hh] at h₁ h₂ ha
  have hQ:=xP y
  refine ⟨?_,?_,?_,?_⟩
  · unfold DotF; rw [h₁,hp]; unfold G bt iv; field_simp
  · rw [ha.1,hv]; unfold G bt iv; field_simp; ring
  · unfold DDot
    rw [h₂,hv,hp]; unfold G bt iv; field_simp; ring
  rw [hh,N2,N,hv,hp,he]; unfold ev iv; field_simp; ring
lemma bt_bound {x y:ℝ} (hh:xs x=XX y) (h:y0 ≤ y): 0 ≤ bt x y ∧ bt x y ≤1002/1000 := by
  have hp:=xP y
  have ha := ap x
  have hu:= (vsmall h).1
  unfold bt iv
  have he : ast x ^2 = xs x ^2+ sb^2 := by
    unfold ast xs
    have hi:= Real.cosh_sq_sub_sinh_sq x
    linear_combination sb^2*hi
  refine ⟨mul_nonneg ha.le (by positivity),?_⟩
  rw [← div_eq_mul_inv,div_le_iff₀ hp]
  rw [hh] at he; unfold sb at *
  nlinarith
end

lemma mRj {x:ℝ} (hv:y0 ≤ x): Fits (rrF x) bRj:=
  (Fits.ray Row0.mradB).sub (fdF hv)
private lemma mqReduce {X:J ℝ} {A:J IV} (h:Fits X A):
    Fits (subJ (ray kk) (rootSub (1/2) vn X (√(X 0))))
      (subJ (ray Row0.kkB) (rootSub (1/2) ub A (rtB (A 0)))) :=
  (Fits.ray Row0.mkkB).sub (h.rt (mrt (h 0)))
lemma mQl {x:ℝ} (hv:y0 ≤ x): Fits (ql x) bQj:= mqReduce (mRj hv)
lemma mDots {x y:ℝ} (hh:xs x=XX y) (he:y0 ≤ y) {F:RF}{A:J IV} (h:TW univ F)
    {f:ℝ→ℝ} (hf:TestF f) (hv:∀ t,F t 0=f (XX t)) (hj:Fits (F y) A):
    DotF f x∈ba A ∧ NNf f x∈bbN A∧ DDot f x∈ bdN A∧
      N2 f (xs x)∈bS2 A := by
  have hi:=bt_bound hh he
  have hu:bt x y ∈bRat := by
    apply span_conv mz (mdiv (mc 1002) (mc 1000)) hi.1
    exact hi.2
  obtain ⟨h₁,h₂,h₃,h₄⟩:=dots_log hh h hf hv
  rw [h₁,h₂,h₃,h₄]
  have hp:= msub (hj 2) (hj 1)
  have hq:= mmul (msq hu) hp
  exact ⟨mmul hu (hj 1),hq,madd hq (hj 1),
    msub (madd (mmul mtwo (hj 0)) (hj 1)) (mmul (lXI he) hp)⟩
end GeneralMahler.SCal.Tail

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_PassTail
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Uniform global (after 64) certificates of value and Euler derivative bounds. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail
open JT JTB Grid Jet Tag Cert Cert.IV Profile Layers
-- K needs individual scaled-error bounds because tends to zero
private lemma checkKR: SubB (bKR 0) (band (-500) 500) &&
    SubB (bKR 1) (band (-5000) 5000) &&
    SubB (bKR 2) (band (-15000) 15000) := by decide +kernel

lemma kTail {y:ℝ} (h:y0≤ y) :
    Kp (XX y) ∈ band 0 8 ∧ Kp (XX y) ≤ ev y*y ∧ 0≤ kF y 2-kF y 1 := by
  have hk:Kp (XX y)=ev y*(Lv y+KR y 0-3/2) := by
    rw [← kF0]
    change Wv y +IJ y 0* _= _
    rw [IJ0]; unfold Wv; dsimp [Jet.subJ,Jet.ray]; ring
  have hi := checkKR
  simp only [Bool.and_eq_true] at hi
  have he:= subB (fKR h 0) hi.1.1; have hp:=subB (fKR h 1) hi.1.2
  have hj:=subB (fKR h 2) hi.2
  rw [mem_band] at he hp hj
  norm_num at he hp hj
  have hv:= iP y
  have hl:= econ h
  have hs:= (vsmall h).2.2
  refine ⟨?_,?_,?_⟩
  · rw [mem_band,hk]
    norm_num
    constructor
    · exact mul_nonneg hv.le (by linarith [he.1,hl.1])
    nlinarith [he.2,hl.2.2]
  · rw [hk]
    apply mul_le_mul_of_nonneg_left _ hv.le
    unfold Lv; linarith [he.2,ro_lim.2.2.2]
  have hz : kF y 2-kF y 1 = ev y * (6* (Lv y+KR y 0-3/2)-5-5*KR y 1+KR y 2) := by
    -- use WW coeff recurrence at k
    simp only [kF,plusJ,WW,Wrec,mulJ,mulJ0,IJ,subJ,tail,ray,Wv]; ring
  rw [hz]
  apply mul_nonneg hv.le; linarith [hl.1,he.1,hp.2,hj.1]

lemma vTail {y:ℝ}(h:y0≤y): deriv Profile.v (XX y)-XX y∈rvb ∧
    deriv (deriv Profile.v) (XX y)∈vvb := by
  let v:=MJ y 0; let n:=NJ y 0; let x:=XX y
  have he:=ym_id y
  have hi:sY x=iv y*v := by unfold x v iv; rw [← ym_id]; have ht:=xP y; field_simp
  have hp:sB x= (iv y)^2*n:= (n_id y).symm
  have hX:=xP y; have hY:= vP y; have hV:0 < v:=MPv _
  let A:=sP x
  have hP:A ∈ bPP 0 := by rw [show A=PP y 0 from (P0 y).symm];apply fPP h
  have hh:phi x∈pf0 := by
    have he := lpF h 0 0
    change Qp 0 y∈pr 0 0 at he
    simpa only [Qp,pow_zero,one_mul,pr, show 0≤(10:ℕ) from by decide, ite_eq_left] using he
  have hz:x*phi x∈pf0 := by
    have he:=lpF h 1 0
    change Qp 1 y ∈ pr 0 1 at he
    simpa only [Qp,pow_one,pr, show (1:ℕ)≤10 from by decide,ite_eq_left] using he
  have hv:v∈bmJ 0:=fmJ h _
  have hn:n∈ bnJ 0:=fnJ h _
  have hb:iv y∈ivb := span_conv mz (mdiv mo (show (64:ℝ)∈ c 64 from mc 64))
    hY.le (vsmall h).2.1
  have hx:=mdiv hh hP
  change deriv _ x-x∈_∧ deriv _ x∈_
  rw [← rv_stable, ← v2_stable]
  unfold sRv sV2; rw [hp,hi]
  change phi x/A-(iv y)^2*n/(iv y*v)∈_∧2-phi x/A*(x+phi x/A)-
    _∈_
  rw [show (iv y)^2*n/(iv y*v)=iv y*n/v from by field_simp,
    show phi x/A*(x+phi x/A)=x*phi x/A+phi x/A*(phi x/A) by ring]
  refine ⟨msub hx (mdiv (mmul hb hn) hv),?_⟩
  rw [show iv y ^2*n/(iv y*v*(iv y*v))=n/v^2 from by field_simp,sub_add_eq_sub_sub]
  exact msub (msub (msub mtwo (mdiv hz hP)) (mmul hx hx)) (mdiv hn (msq hv))

lemma tag_tail {x y:ℝ} (h:y0 ≤ y) (he:xs x=XX y) (hR:CJet.RadH) (hf:TestF qu)
    (t:Tag) : t.act x∈tabT t := by
  unfold tabT
  generalize hQ : bQj = A
  have hmQ : Fits (ql y) A := hQ ▸ mQl h
  obtain ⟨ha,hb,hc,_⟩:=mDots he h TkF Profile.testK kF0 (fkF h)
  obtain ⟨hK,hK',hN⟩:=kTail h
  have hN':0 ≤ NNf Kp x := by
    have hh:= (dots_log he TkF Profile.testK kF0).2.1
    rw [hh]; exact mul_nonneg (sq_nonneg _) hN
  obtain ⟨hd,hi,hj,_⟩:=mDots he h TcF Profile.testC cF0 (fcF h)
  obtain ⟨hp,hq,hu,ht⟩:=mDots he h (Twq hR) hf qe0 hmQ
  have hr:=mRj h 0
  have hcv:=fcF h 0
  have hqv:=hmQ 0
  obtain ⟨hx,hv⟩:=vTail h
  rw [rre0] at hr; rw [cF0] at hcv; rw [qe0] at hqv
  rw [← he] at hK hcv hqv hx hv hr
  cases t
  · exact hr
  · exact hK
  · exact hcv
  · exact hqv
  · exact ha
  · exact hd
  · exact hp
  · exact hc
  · exact hj
  · exact hu
  · exact mclamp hb hN'
  · exact hi
  · exact hq
  · exact hx
  · exact hv
  · exact ht

theorem tailCheck: pass0 719 tabT=true := by decide +kernel

lemma rad_tail {x y:ℝ} (h:y0≤y) (he:xs x=XX y): Tag.R.act x∈rng R := by
  have hi : rrF y 0∈bRj 0:= mRj h 0
  have hu : R.act x=rrF y 0:= by
    rw [rre0, ← he]
    rfl
  have hh := tailCheck
  simp only [pass0,Bool.and_eq_true] at hh
  rw [hu]
  apply subB hi (hasSub hh.1.1.1.1 R)
end GeneralMahler.SCal.Tail

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Universal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Propagate and combine the finite/infinite and reflected ranges. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Grid Tag Profile CJet Cert Cert.IV
variable {X:ℕ}

lemma NG.good (h:NG) (n:ℕ) (hi:n ≤ 720): NodeTrue n (Nodes.A n)∧(n<720 → pass n=true ∧ ∀ x∈Icc (nd n) (nd (n+1)), K.act x ≤ gv (Nodes.A n).mx) := line_good n (Nodes.A n) (h n (by omega) (by omega))

lemma nd0: nd 0=0:=by norm_num [nd]
lemma nd_m:StrictMono nd := by intro i j h; unfold nd; gcongr
lemma find_cell (n i:ℕ) (h:i<n) {x:ℝ} (hx:x∈Icc (nd i) (nd n)):
    ∃ j:ℕ,i ≤ j∧ j<n ∧ x∈Icc (nd j) (nd (j+1)) := by
  induction n with
  | zero=> omega
  | succ n ih=>
    by_cases hj:nd n≤ x
    · exact ⟨n,by omega,by omega,hj,hx.2⟩
    have hi:i<n := by
      have hv: nd i < nd n := lt_of_le_of_lt hx.1 (lt_of_not_ge hj)
      exact nd_m.lt_iff_lt.mp hv
    obtain ⟨j,hj,hz,hg⟩:=ih hi ⟨hx.1,(lt_of_not_ge hj).le⟩
    exact ⟨j,hj,by omega,hg⟩

lemma x720 : (658/10:ℝ) ≤ xs (nd 720) := by
  have hi:=mle (mbd 658000) (pGa 720).X (by decide +kernel)
  convert hi using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

lemma find_tail {x:ℝ} (hh:nd 720 ≤ x): ∃ y, Tail.y0≤ y∧ xs x=Tail.XX y := by
  have hi:= x_mono.monotone hh
  have hp : 64≤xs x := by linarith [x720]
  exact ⟨Real.log (xs x), Real.log_le_log (by norm_num) hp, (Real.exp_log (by linarith)).symm⟩

lemma rp_th (h:NG) {x:ℝ} (hx:0≤ x):R.act x∈rng R := by
  rcases le_total x (nd 720) with he|he
  · obtain ⟨n,_,hn,hu⟩:=find_cell 720 0 (by decide) ⟨nd0.symm ▸ hx,he⟩
    exact cell_R (((h.good n hn.le).2 hn).1) hu
  obtain ⟨y,hy,hi⟩:=find_tail he
  exact Tail.rad_tail hy hi
lemma rp_bound (h:NG) (x:ℝ):5/100≤ rad x := by
  obtain ⟨t,ht⟩:=ontoX x
  rw [← ht]
  have hh:= rp_th h (abs_nonneg t)
  have he : R.act |t| = rad (xs t) := by
    rcases le_total t 0 with he|he
    · rw [abs_of_nonpos he]; exact lift_ref Reven _
    rw [abs_of_nonneg he]; rfl
  rw [he] at hh
  have hv:=(mem_band _ _ _).mp hh
  norm_num at hv; linarith [hv.1]
lemma hrq (h:NG): RadH:=fun x=>by linarith [rp_bound h x]
lemma hqt (h:NG):TestF qu:=q_reg (rp_bound h)

lemma stage_size (n:ℕ) (h:n<720): stage n≤8∧(panel (stage n)).lo≤n∧ n<(panel (stage n)).hi := by
  unfold stage; split_ifs <;> norm_num [panel,pan] <;> omega

-- whenever past lower index r. returns cell n and panel contains x
lemma Propagate (h:NG) {x:ℝ} {r:ℕ} (hr:r<720) (hu:nd r ≤ x) :
    ∃ n:ℕ,r ≤ n∧ n<720∧
      nd (panel (stage n)).lo ≤ x∧ ((panel (stage n)).hi<720 → x ≤ nd (panel (stage n)).hi) ∧
      passR n (fun t=>t.act x) := by
  rcases le_total x (nd 720) with he|he
  · obtain ⟨n,hn,hx,hc⟩:= find_cell 720 r hr ⟨hu,he⟩
    have hs:= stage_size n hx
    exact ⟨n,hn,hx,(nd_m.monotone hs.2.1).trans hc.1,
      fun _=> hc.2.trans (nd_m.monotone (by omega)),
      cell_pass (((h.good n hx.le).2 hx).1) (hrq h) (hqt h) hc⟩
  obtain ⟨y,hy,hd⟩:= find_tail he
  refine ⟨719,by omega,by decide,(nd_m.monotone (by decide)).trans he,fun h=>?_,
    passes (fun i=>Tail.tag_tail hy hd (hrq h) (hqt h) i) Tail.tailCheck⟩
  norm_num [stage,panel,pan] at h

-- per-real argument assertion
lemma Sym_b (i:Tag)(h:i.odd=true): SubB (-(rng i)) (rng i) &&
    SubB (-(roff i)) (roff i) := by cases i <;> first| decide|simp [Tag.odd] at h
lemma mRange (h:NG) (x:ℝ) (i:Tag):i.act x∈rng i := by
  have hh:= abs_nonneg x
  obtain ⟨n,_,_,_,_,hg⟩:= Propagate h (r:=0) (by decide) (show nd 0≤|x| from nd0.symm ▸ hh)
  have he:=hg.gr i
  rcases le_total 0 x with hz|hz
  · simpa only [abs_of_nonneg hz] using he
  rw [abs_of_nonpos hz] at he
  rcases hb:i.odd with _|_
  · rw [Tag.TvEv (hqt h) hb] at he; exact he
  rw [Tag.TvOd (hqt h) hb] at he
  have ht:=Sym_b i hb; simp only [Bool.and_eq_true] at ht
  simpa only [neg_neg] using subB (mneg he) ht.1

lemma GlobalCorr (h:NG) (x:ℝ): Corr (fun i=>i.act x):= by
  have hh:=abs_nonneg x
  obtain ⟨n,_,_,_,_,hg⟩:= Propagate h (r:=0) (by decide) (show nd 0≤ |x| from nd0.symm ▸ hh)
  have hv:= hg.uu
  rcases le_total 0 x with hz|hz
  · simpa only [abs_of_nonneg hz] using hv
  have he (i:Tag)(he:i.odd=false):i.act (-x)=i.act x:= Tag.TvEv (hqt h) he x
  have ho (i:Tag)(he:i.odd=true):i.act (-x)= -i.act x:=Tag.TvOd (hqt h) he x
  rw [abs_of_nonpos hz] at hv
  unfold Corr Ucost at *
  dsimp only at *
  rw [he K (by rfl),he C (by rfl),he NK (by rfl),ho dK (by rfl),ho dC (by rfl)] at hv
  simp only [mul_neg,← neg_add, Even.neg_pow (show Even 2 by decide)] at hv
  exact hv
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_LayerProof
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Pointwise scalar covariance and layer inequalities. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Grid Tag Profile Cert Cert.IV Jet
variable (h:NG)
lemma SQrange (h:NG) (x:ℝ):113/1000≤ N2 qu x ∧ N2 qu x≤514/1000 := by
  obtain ⟨t,ht⟩:=ontoX x
  have hi:=mRange h t S
  rw [rng,mem_band] at hi
  simp only [Tag.act,liftF] at hi; rw [ht] at hi
  norm_num at *; exact hi

-- choose one rectangle for each parameter
lemma onPanels (h:NG) (t:ℝ) :
    ∃ k:ℕ,k≤8 ∧ SIn (fun i=>i.act t) (panel k) ∧
      ro2 t≤ rPanel k^2 := by
  obtain ⟨n,_,hn,_,hb,hc⟩:= Propagate h (r:=0) (by decide)
    (show nd 0≤ |t| from nd0.symm ▸ abs_nonneg t)
  have hk:= (stage_size n hn).1
  refine ⟨stage n,hk,?_,rp_val _ hk _ hb⟩
  have he:=hc.pn
  rcases le_total 0 t with ht|ht
  · simpa only [abs_of_nonneg ht] using he
  rw [abs_of_nonpos ht] at he
  have hh (i:Tag)(he:i.odd=false):i.act (-t)=i.act t:=Tag.TvEv (hqt h) he t
  unfold SIn at *; dsimp only at *
  rwa [hh S (by rfl),hh Q (by rfl),hh V (by rfl)] at he

lemma Sp_upper (h:NG) (x:ℝ):N2 uc x^2+N2 us x^2 ≤ (1104/1000:ℝ)^2:=by
  obtain ⟨t,ht⟩:=ontoX x
  obtain ⟨k,hk,_,hr⟩:=onPanels h t
  rw [← ht,← nr2]
  apply hr.trans
  interval_cases k <;> norm_num [rPanel,panel,pan]
lemma CSr (a b x y c d:ℝ) (h:0≤ c)(he:0≤ d)(hh:a^2+b^2 ≤ c^2)(hj:x^2+y^2≤d^2):
    |a*x+b*y| ≤ c*d:= by
  have hh': (a*x+b*y)^2≤(c*d)^2:= by
    rw [mul_pow]; apply le_trans _ (mul_le_mul hh hj (by positivity) (by positivity))
    nlinarith [sq_nonneg (a*y-b*x)]
  have hi:=sq_le_sq.mp hh'; rwa [abs_of_nonneg (mul_nonneg h he)] at hi
lemma kk_bd: 48/100 ≤ kk ∧ kk ≤ 49/100:= by
  have hp:=k_pos; have hh:=k_sq; unfold bb cc at hh; constructor <;> nlinarith
lemma h_contact (h:NG) (x y:ℝ): 0<4*cc+2*kk*(N2 qu x+N2 qu y)- N2 qu x*N2 qu y -
    (N2 uc x*N2 uc y+N2 us x*N2 us y) := by
  obtain ⟨ha,hb⟩:=SQrange h x; obtain ⟨hc,hd⟩:=SQrange h y
  have he:= le_of_abs_le (CSr _ _ _ _ _ _ (by norm_num) (by norm_num)
    (Sp_upper h x) (Sp_upper h y))
  have hi : 0≤ N2 qu x:= by linarith
  have hj : 0≤ N2 qu y:= by linarith
  have hf := mul_le_mul hb hd hj (show (0:ℝ)≤514/1000 by norm_num)
  have hu:= kk_bd.1
  unfold cc at *
  nlinarith

namespace PA
lemma kstats (k:Nat)(h:k≤8) : (panel k).sr ≠ unk ∧
    (panel k).qR≠ unk∧(panel k).vR≠ unk ∧
    eR true (panel k).sr ≤514/1000∧eR true (panel k).qR ≤256/1000 := by
  interval_cases k <;> norm_num [panel,pan,eR,w,endp,band,bandD,den] <;> exact ⟨nofun, nofun, nofun⟩

lemma hMono {a b c d:ℝ} (ha:a ≤ b)(hb:c ≤ d)(he:d ≤514/1000)
    (hh:b ≤ 256/1000): HV a c≤HV b d:= by
  have hi:=kk_bd.1
  unfold HV
  have hp:= mul_nonneg (sub_nonneg.mpr ha) (show 0≤ 4*kk-2*c by linarith)
  have hv:=mul_nonneg (sub_nonneg.mpr hb) (show 0≤kk-b by linarith)
  nlinarith
end PA

open PA
lemma layer_line (h:NG) (t u:ℝ) :
    let v := (xs t,xs u)
    HH v + tc*Hh v-1/2*Profile.tr*(h₀+Hh v^2/h₀)>
      2*(bb+eta+(bb+eta-kar)*tmin)+2*bm*N2 qu v.1*N2 qu v.2+2*e₀*(2*Profile.tr)^2+Hh v^2/alpha := by
  intro v
  obtain ⟨kx,hkx,ha,hax⟩:=onPanels h u
  obtain ⟨kz,hkz,hb,hbx⟩:=onPanels h t
  let c := N2 qu (xs t)
  let d := N2 qu (xs u)
  let a:= qu (xs u)
  let w:= deriv (deriv Profile.v) (xs u)
  have hp (k) (h:k≤8): 0 ≤ rPanel k:= rp_pos k h
  have kkx := kstats kx hkx; have kkz:= kstats kz hkz
  obtain ⟨hxq,hxs,hxv⟩:=ha
  obtain ⟨hzq,hzs,hzv⟩:=hb
  have Hxq:=orderE hxq kkx.2.1;have Hxs:= orderE hxs kkx.1
  have Hz:= orderE hzs kkz.1; have HV':= orderE hxv kkx.2.2.1
  change eR _ _≤ a ∧ a≤ _ at Hxq
  change eR _ _≤ c ∧ c≤ _ at Hz
  change eR _ _≤ d ∧ d≤ _ at Hxs
  let sd:= N2 uc (xs t)*uc (xs u)+N2 us (xs t)*us (xs u)
  have hR : 0 ≤ Profile.r:=by norm_num [r]
  have hj : |sd| ≤ rPanel kz*r := CSr _ _ _ _ _ _ (hp _ hkz) hR
    (by rw [← nr2];exact hbx)
    (le_of_eq (lcsq u))
  have heq : HH v= HV a c -2*sd := by unfold HH HV; rfl
  have hd : HH v∈Icc (Hbnd false kx kz) (Hbnd true kx kz):=by
    rw [heq]
    have hi := hMono Hxq.1 Hz.1 (Hz.2.trans kkz.2.2.2.1) (Hxq.2.trans kkx.2.2.2.2)
    have hv:= hMono Hxq.2 Hz.2 kkz.2.2.2.1 kkx.2.2.2.2
    unfold Hbnd; simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
    have hg:=abs_le.mp hj; constructor <;> nlinarith [hg.1,hg.2]
  have hc : 0≤ c:= by have hj:=SQrange h (xs t);unfold c;linarith [hj.1]
  have H : 0≤ d := by have hj:=SQrange h (xs u);unfold d;linarith [hj.1]
  have h' := mul_le_mul Hxs.2 Hz.2 hc (H.trans Hxs.2)
  have hh:= whole hkx hkz (HH v) w hd HV'
  have hi : Lcost c d ≤ Lcost (eR true (panel kx).sr) (eR true (panel kz).sr):= by
    unfold Lcost
    have hp : 0≤2*bm := by norm_num [bm,bb,tmin,tmax,cc,eta]
    nlinarith
  have hv:=hi.trans_lt hh
  unfold Lcost Ldef at hv
  have he : Hh v= HH v+w-2*kar:=rfl
  change HH v + tc*_ -_ > _+2*bm*c*d+_+_
  rw [he]; unfold tc kar Profile.tr alpha h₀ at *; norm_num at *; linarith

theorem hSeg01 (h:NG): LayerOK := by
  refine ⟨hrq h,hqt h,ucs_reg.1,ucs_reg.2,Qeven,
    fun x=> ?_,fun x=>?_,h_contact h,?_⟩
  · linarith [(SQrange h x).1]
  · obtain ⟨t,ht⟩:=ontoX x
    have hi:= mRange h t RV
    rw [rng,mem_band] at hi
    simp only [Tag.act,liftF] at hi
    rw [ht] at hi
    norm_num at hi; apply abs_le.mpr; constructor <;> linarith [hi.1,hi.2]
  rintro ⟨x,z⟩
  obtain ⟨t,rfl⟩:=ontoX x; obtain ⟨u,rfl⟩:=ontoX z
  exact layer_line h t u

theorem upd_ok (h:NG): UpdatesOK Cp Kp := by
  refine ⟨testC.poly,testK.poly,testC.cont,testK.cont,?_,?_,?_,?_⟩
  all_goals intro x; obtain ⟨t,rfl⟩:=ontoX x; obtain ⟨ha,hb,hc,-⟩:= GlobalCorr h t
  · exact ha.le
  · exact hb.le
  · simp only [Tag.act,liftF,Ta] at hc; linarith
  have hi:= mRange h t C
  rw [rng,mem_band] at hi; simp only [Tag.act,liftF] at hi
  unfold cupper; norm_num at *; exact hi.2
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Tiles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Arithmetic verification of compact region. -/
open Set Filter Real
namespace GeneralMahler.SCal.Mid
open Grid Jet Profile Segment SE Cert Cert.IV
lemma chk_every (p:Ft→Bool)(h:everyF p=true)(t:Ft):p t=true:=
  List.all_eq_true.mp h t (by cases t <;> decide)
variable (B:PrefixC)
lemma cWorks (h:initC B=true) (he:By (ctStep B) 0 720):Works B:=
  ⟨chk_every _ h,fun n hn=>chk_every _ (he n (by omega) hn)⟩

end GeneralMahler.SCal.Mid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Verified
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma CK0_11 : By (ctStep Cn) 0 11 := by
  apply byRun (ctStep Cn) 0 11 11
  · rfl
  decide +kernel
lemma CK11_22 : By (ctStep Cn) 11 22 := by
  apply byRun (ctStep Cn) 11 11 22
  · rfl
  decide +kernel
lemma CK0_22 : By (ctStep Cn) 0 22 := byJoin CK0_11 CK11_22
lemma CK22_33 : By (ctStep Cn) 22 33 := by
  apply byRun (ctStep Cn) 22 11 33
  · rfl
  decide +kernel
lemma CK33_45 : By (ctStep Cn) 33 45 := by
  apply byRun (ctStep Cn) 33 12 45
  · rfl
  decide +kernel
lemma CK22_45 : By (ctStep Cn) 22 45 := byJoin CK22_33 CK33_45
lemma CK0_45 : By (ctStep Cn) 0 45 := byJoin CK0_22 CK22_45
lemma CK45_56 : By (ctStep Cn) 45 56 := by
  apply byRun (ctStep Cn) 45 11 56
  · rfl
  decide +kernel
lemma CK56_67 : By (ctStep Cn) 56 67 := by
  apply byRun (ctStep Cn) 56 11 67
  · rfl
  decide +kernel
lemma CK45_67 : By (ctStep Cn) 45 67 := byJoin CK45_56 CK56_67
lemma CK67_78 : By (ctStep Cn) 67 78 := by
  apply byRun (ctStep Cn) 67 11 78
  · rfl
  decide +kernel
lemma CK78_90 : By (ctStep Cn) 78 90 := by
  apply byRun (ctStep Cn) 78 12 90
  · rfl
  decide +kernel
lemma CK67_90 : By (ctStep Cn) 67 90 := byJoin CK67_78 CK78_90
lemma CK45_90 : By (ctStep Cn) 45 90 := byJoin CK45_67 CK67_90
lemma CK0_90 : By (ctStep Cn) 0 90 := byJoin CK0_45 CK45_90
lemma CK90_101 : By (ctStep Cn) 90 101 := by
  apply byRun (ctStep Cn) 90 11 101
  · rfl
  decide +kernel
lemma CK101_112 : By (ctStep Cn) 101 112 := by
  apply byRun (ctStep Cn) 101 11 112
  · rfl
  decide +kernel
lemma CK90_112 : By (ctStep Cn) 90 112 := byJoin CK90_101 CK101_112
lemma CK112_123 : By (ctStep Cn) 112 123 := by
  apply byRun (ctStep Cn) 112 11 123
  · rfl
  decide +kernel
lemma CK123_135 : By (ctStep Cn) 123 135 := by
  apply byRun (ctStep Cn) 123 12 135
  · rfl
  decide +kernel
lemma CK112_135 : By (ctStep Cn) 112 135 := byJoin CK112_123 CK123_135
lemma CK90_135 : By (ctStep Cn) 90 135 := byJoin CK90_112 CK112_135
lemma CK135_146 : By (ctStep Cn) 135 146 := by
  apply byRun (ctStep Cn) 135 11 146
  · rfl
  decide +kernel
lemma CK146_157 : By (ctStep Cn) 146 157 := by
  apply byRun (ctStep Cn) 146 11 157
  · rfl
  decide +kernel
lemma CK135_157 : By (ctStep Cn) 135 157 := byJoin CK135_146 CK146_157
lemma CK157_168 : By (ctStep Cn) 157 168 := by
  apply byRun (ctStep Cn) 157 11 168
  · rfl
  decide +kernel
lemma CK168_180 : By (ctStep Cn) 168 180 := by
  apply byRun (ctStep Cn) 168 12 180
  · rfl
  decide +kernel
lemma CK157_180 : By (ctStep Cn) 157 180 := byJoin CK157_168 CK168_180
lemma CK135_180 : By (ctStep Cn) 135 180 := byJoin CK135_157 CK157_180
lemma CK90_180 : By (ctStep Cn) 90 180 := byJoin CK90_135 CK135_180
lemma CK0_180 : By (ctStep Cn) 0 180 := byJoin CK0_90 CK90_180
lemma CK180_191 : By (ctStep Cn) 180 191 := by
  apply byRun (ctStep Cn) 180 11 191
  · rfl
  decide +kernel
lemma CK191_202 : By (ctStep Cn) 191 202 := by
  apply byRun (ctStep Cn) 191 11 202
  · rfl
  decide +kernel
lemma CK180_202 : By (ctStep Cn) 180 202 := byJoin CK180_191 CK191_202
lemma CK202_213 : By (ctStep Cn) 202 213 := by
  apply byRun (ctStep Cn) 202 11 213
  · rfl
  decide +kernel
lemma CK213_225 : By (ctStep Cn) 213 225 := by
  apply byRun (ctStep Cn) 213 12 225
  · rfl
  decide +kernel
lemma CK202_225 : By (ctStep Cn) 202 225 := byJoin CK202_213 CK213_225
lemma CK180_225 : By (ctStep Cn) 180 225 := byJoin CK180_202 CK202_225
lemma CK225_236 : By (ctStep Cn) 225 236 := by
  apply byRun (ctStep Cn) 225 11 236
  · rfl
  decide +kernel
lemma CK236_247 : By (ctStep Cn) 236 247 := by
  apply byRun (ctStep Cn) 236 11 247
  · rfl
  decide +kernel
lemma CK225_247 : By (ctStep Cn) 225 247 := byJoin CK225_236 CK236_247
lemma CK247_258 : By (ctStep Cn) 247 258 := by
  apply byRun (ctStep Cn) 247 11 258
  · rfl
  decide +kernel
lemma CK258_270 : By (ctStep Cn) 258 270 := by
  apply byRun (ctStep Cn) 258 12 270
  · rfl
  decide +kernel
lemma CK247_270 : By (ctStep Cn) 247 270 := byJoin CK247_258 CK258_270
lemma CK225_270 : By (ctStep Cn) 225 270 := byJoin CK225_247 CK247_270
lemma CK180_270 : By (ctStep Cn) 180 270 := byJoin CK180_225 CK225_270
lemma CK270_281 : By (ctStep Cn) 270 281 := by
  apply byRun (ctStep Cn) 270 11 281
  · rfl
  decide +kernel
lemma CK281_292 : By (ctStep Cn) 281 292 := by
  apply byRun (ctStep Cn) 281 11 292
  · rfl
  decide +kernel
lemma CK270_292 : By (ctStep Cn) 270 292 := byJoin CK270_281 CK281_292
lemma CK292_303 : By (ctStep Cn) 292 303 := by
  apply byRun (ctStep Cn) 292 11 303
  · rfl
  decide +kernel
lemma CK303_315 : By (ctStep Cn) 303 315 := by
  apply byRun (ctStep Cn) 303 12 315
  · rfl
  decide +kernel
lemma CK292_315 : By (ctStep Cn) 292 315 := byJoin CK292_303 CK303_315
lemma CK270_315 : By (ctStep Cn) 270 315 := byJoin CK270_292 CK292_315
lemma CK315_326 : By (ctStep Cn) 315 326 := by
  apply byRun (ctStep Cn) 315 11 326
  · rfl
  decide +kernel
lemma CK326_337 : By (ctStep Cn) 326 337 := by
  apply byRun (ctStep Cn) 326 11 337
  · rfl
  decide +kernel
lemma CK315_337 : By (ctStep Cn) 315 337 := byJoin CK315_326 CK326_337
lemma CK337_348 : By (ctStep Cn) 337 348 := by
  apply byRun (ctStep Cn) 337 11 348
  · rfl
  decide +kernel
lemma CK348_360 : By (ctStep Cn) 348 360 := by
  apply byRun (ctStep Cn) 348 12 360
  · rfl
  decide +kernel
lemma CK337_360 : By (ctStep Cn) 337 360 := byJoin CK337_348 CK348_360
lemma CK315_360 : By (ctStep Cn) 315 360 := byJoin CK315_337 CK337_360
lemma CK270_360 : By (ctStep Cn) 270 360 := byJoin CK270_315 CK315_360
lemma CK180_360 : By (ctStep Cn) 180 360 := byJoin CK180_270 CK270_360
lemma CK0_360 : By (ctStep Cn) 0 360 := byJoin CK0_180 CK180_360
lemma CK360_371 : By (ctStep Cn) 360 371 := by
  apply byRun (ctStep Cn) 360 11 371
  · rfl
  decide +kernel
lemma CK371_382 : By (ctStep Cn) 371 382 := by
  apply byRun (ctStep Cn) 371 11 382
  · rfl
  decide +kernel
lemma CK360_382 : By (ctStep Cn) 360 382 := byJoin CK360_371 CK371_382
lemma CK382_393 : By (ctStep Cn) 382 393 := by
  apply byRun (ctStep Cn) 382 11 393
  · rfl
  decide +kernel
lemma CK393_405 : By (ctStep Cn) 393 405 := by
  apply byRun (ctStep Cn) 393 12 405
  · rfl
  decide +kernel
lemma CK382_405 : By (ctStep Cn) 382 405 := byJoin CK382_393 CK393_405
lemma CK360_405 : By (ctStep Cn) 360 405 := byJoin CK360_382 CK382_405
lemma CK405_416 : By (ctStep Cn) 405 416 := by
  apply byRun (ctStep Cn) 405 11 416
  · rfl
  decide +kernel
lemma CK416_427 : By (ctStep Cn) 416 427 := by
  apply byRun (ctStep Cn) 416 11 427
  · rfl
  decide +kernel
lemma CK405_427 : By (ctStep Cn) 405 427 := byJoin CK405_416 CK416_427
lemma CK427_438 : By (ctStep Cn) 427 438 := by
  apply byRun (ctStep Cn) 427 11 438
  · rfl
  decide +kernel
lemma CK438_450 : By (ctStep Cn) 438 450 := by
  apply byRun (ctStep Cn) 438 12 450
  · rfl
  decide +kernel
lemma CK427_450 : By (ctStep Cn) 427 450 := byJoin CK427_438 CK438_450
lemma CK405_450 : By (ctStep Cn) 405 450 := byJoin CK405_427 CK427_450
lemma CK360_450 : By (ctStep Cn) 360 450 := byJoin CK360_405 CK405_450
lemma CK450_461 : By (ctStep Cn) 450 461 := by
  apply byRun (ctStep Cn) 450 11 461
  · rfl
  decide +kernel
lemma CK461_472 : By (ctStep Cn) 461 472 := by
  apply byRun (ctStep Cn) 461 11 472
  · rfl
  decide +kernel
lemma CK450_472 : By (ctStep Cn) 450 472 := byJoin CK450_461 CK461_472
lemma CK472_483 : By (ctStep Cn) 472 483 := by
  apply byRun (ctStep Cn) 472 11 483
  · rfl
  decide +kernel
lemma CK483_495 : By (ctStep Cn) 483 495 := by
  apply byRun (ctStep Cn) 483 12 495
  · rfl
  decide +kernel
lemma CK472_495 : By (ctStep Cn) 472 495 := byJoin CK472_483 CK483_495
lemma CK450_495 : By (ctStep Cn) 450 495 := byJoin CK450_472 CK472_495
lemma CK495_506 : By (ctStep Cn) 495 506 := by
  apply byRun (ctStep Cn) 495 11 506
  · rfl
  decide +kernel
lemma CK506_517 : By (ctStep Cn) 506 517 := by
  apply byRun (ctStep Cn) 506 11 517
  · rfl
  decide +kernel
lemma CK495_517 : By (ctStep Cn) 495 517 := byJoin CK495_506 CK506_517
lemma CK517_528 : By (ctStep Cn) 517 528 := by
  apply byRun (ctStep Cn) 517 11 528
  · rfl
  decide +kernel
lemma CK528_540 : By (ctStep Cn) 528 540 := by
  apply byRun (ctStep Cn) 528 12 540
  · rfl
  decide +kernel
lemma CK517_540 : By (ctStep Cn) 517 540 := byJoin CK517_528 CK528_540
lemma CK495_540 : By (ctStep Cn) 495 540 := byJoin CK495_517 CK517_540
lemma CK450_540 : By (ctStep Cn) 450 540 := byJoin CK450_495 CK495_540
lemma CK360_540 : By (ctStep Cn) 360 540 := byJoin CK360_450 CK450_540
lemma CK540_551 : By (ctStep Cn) 540 551 := by
  apply byRun (ctStep Cn) 540 11 551
  · rfl
  decide +kernel
lemma CK551_562 : By (ctStep Cn) 551 562 := by
  apply byRun (ctStep Cn) 551 11 562
  · rfl
  decide +kernel
lemma CK540_562 : By (ctStep Cn) 540 562 := byJoin CK540_551 CK551_562
lemma CK562_573 : By (ctStep Cn) 562 573 := by
  apply byRun (ctStep Cn) 562 11 573
  · rfl
  decide +kernel
lemma CK573_585 : By (ctStep Cn) 573 585 := by
  apply byRun (ctStep Cn) 573 12 585
  · rfl
  decide +kernel
lemma CK562_585 : By (ctStep Cn) 562 585 := byJoin CK562_573 CK573_585
lemma CK540_585 : By (ctStep Cn) 540 585 := byJoin CK540_562 CK562_585
lemma CK585_596 : By (ctStep Cn) 585 596 := by
  apply byRun (ctStep Cn) 585 11 596
  · rfl
  decide +kernel
lemma CK596_607 : By (ctStep Cn) 596 607 := by
  apply byRun (ctStep Cn) 596 11 607
  · rfl
  decide +kernel
lemma CK585_607 : By (ctStep Cn) 585 607 := byJoin CK585_596 CK596_607
lemma CK607_618 : By (ctStep Cn) 607 618 := by
  apply byRun (ctStep Cn) 607 11 618
  · rfl
  decide +kernel
lemma CK618_630 : By (ctStep Cn) 618 630 := by
  apply byRun (ctStep Cn) 618 12 630
  · rfl
  decide +kernel
lemma CK607_630 : By (ctStep Cn) 607 630 := byJoin CK607_618 CK618_630
lemma CK585_630 : By (ctStep Cn) 585 630 := byJoin CK585_607 CK607_630
lemma CK540_630 : By (ctStep Cn) 540 630 := byJoin CK540_585 CK585_630
lemma CK630_641 : By (ctStep Cn) 630 641 := by
  apply byRun (ctStep Cn) 630 11 641
  · rfl
  decide +kernel
lemma CK641_652 : By (ctStep Cn) 641 652 := by
  apply byRun (ctStep Cn) 641 11 652
  · rfl
  decide +kernel
lemma CK630_652 : By (ctStep Cn) 630 652 := byJoin CK630_641 CK641_652
lemma CK652_663 : By (ctStep Cn) 652 663 := by
  apply byRun (ctStep Cn) 652 11 663
  · rfl
  decide +kernel
lemma CK663_675 : By (ctStep Cn) 663 675 := by
  apply byRun (ctStep Cn) 663 12 675
  · rfl
  decide +kernel
lemma CK652_675 : By (ctStep Cn) 652 675 := byJoin CK652_663 CK663_675
lemma CK630_675 : By (ctStep Cn) 630 675 := byJoin CK630_652 CK652_675
lemma CK675_686 : By (ctStep Cn) 675 686 := by
  apply byRun (ctStep Cn) 675 11 686
  · rfl
  decide +kernel
lemma CK686_697 : By (ctStep Cn) 686 697 := by
  apply byRun (ctStep Cn) 686 11 697
  · rfl
  decide +kernel
lemma CK675_697 : By (ctStep Cn) 675 697 := byJoin CK675_686 CK686_697
lemma CK697_708 : By (ctStep Cn) 697 708 := by
  apply byRun (ctStep Cn) 697 11 708
  · rfl
  decide +kernel
lemma CK708_720 : By (ctStep Cn) 708 720 := by
  apply byRun (ctStep Cn) 708 12 720
  · rfl
  decide +kernel
lemma CK697_720 : By (ctStep Cn) 697 720 := byJoin CK697_708 CK708_720
lemma CK675_720 : By (ctStep Cn) 675 720 := byJoin CK675_697 CK697_720
lemma CK630_720 : By (ctStep Cn) 630 720 := byJoin CK630_675 CK675_720
lemma CK540_720 : By (ctStep Cn) 540 720 := byJoin CK540_630 CK630_720
lemma CK360_720 : By (ctStep Cn) 360 720 := byJoin CK360_540 CK540_720
lemma CK0_720 : By (ctStep Cn) 0 720 := byJoin CK0_360 CK360_720
lemma checkedP : Works Cn := cWorks _ (by decide +kernel) CK0_720
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general Mahler inequality, equality characterization, and Santaló minimum. -/

namespace GeneralMahler

open SCal SCal.Grid SCal.Mid Set MeasureTheory

lemma Complete_profile_input_oai : Input091 :=
  let h : NG := Nodes.covered
  ⟨hSeg01 h, upd_ok h, Eq04full h Tab.Cn Tab.checkedP ⟨Tab.gtrue, Tab.gfalse⟩⟩

end GeneralMahler

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.Complete_profile_input_oai := @OAI.GeneralMahler.Complete_profile_input_oai

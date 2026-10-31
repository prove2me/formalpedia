-- Prove2me | solution 1 for OAI.GeneralMahler.ProjField.budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:41:30.540615+00:00
-- url     : https://prove2.me/submissions/6a4e6797-f19f-4ecc-b859-66e6aa175b54

import Mathlib
import Definitions.Def_GeneralMahler
import Definitions.Def_OAIQ026G002
import Theorems.Thm_OAI_GeneralMahler_ProjField_entropy_decomp
import Theorems.Thm_OAI_GeneralMahler_ProjField_reserve

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
end Layers
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Profiles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma v_log (x:ℝ) : v x= -LC x-LC (-x) := by
  have he : X x=(MillsC x)⁻¹ := by unfold X MillsC; rw [inv_div]
  have hh : Y x=(MillsC (-x))⁻¹ := by unfold Y MillsC; rw [neg_p,neg_phi,inv_div]
  rw [v,Real.log_mul (xp x).ne' (yp x).ne',he,hh,LC,LC,Real.log_inv,Real.log_inv]; ring
lemma dV (x:ℝ) : HasDerivAt v (MillsJ x-MillsJ (-x)) x := by
  rw [funext v_log]
  convert ((d_lc x).neg.sub ((d_lc (-x)).comp x (hasDerivAt_neg' x))) using 1
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

lemma v_test : TestF v := TestF.of_d dV (mj_test.sub mj_test.ref)
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

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Update
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp _root_.OAI.GeneralMahler.mat_borel _root_.OAI.GeneralMahler.mat_meas
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

lemma jordan_sym {A B : Mat m} (ha:A.IsHermitian) (hb:B.IsHermitian) :
    (jprod A B).IsHermitian := by
  apply Matrix.IsHermitian.smul _ (show IsSelfAdjoint (1/2:ℝ) from rfl)
  change star (A*B+B*A) = _
  rw [star_add,star_mul,star_mul, (show star A=A from ha),(show star B=B from hb),add_comm]
lemma sqPSD {A : Mat m} (ha:A.IsHermitian) : 0 ≤ A*A := by
  change IsSelfAdjoint A at ha
  conv_lhs => skip
  simpa only [ha.star_eq] using star_mul_self_nonneg A
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

lemma logD_sum {A:Mat m} (ha:A.PosDef) :
    logD A=(∑ i,Real.log (ha.1.eigenvalues i))/(m:ℝ) := by
  rw [logD,ha.1.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [Real.log_prod (fun i _=>?_)]
  exact ne_of_gt (ha.eigenvalues_pos i)

-- trace comparison for final connection
lemma trN_logD_eq {A:Mat m} (ha:A.PosDef) :
    trN (cfc Real.log A)=logD A := by
  rw [trN,logD_sum ha]
  open Unitary in
    rw [Matrix.IsHermitian.cfc_eq ha.1,Matrix.IsHermitian.cfc,conjStarAlgAut_apply,
      Matrix.trace_mul_comm,← mul_assoc]
    simp

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_DefectIBP
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
lemma N2_test {f:ℝ→ℝ} (hf:TestF f) : TestF (N2 f) :=
  ((TestF.id.mul hf.der).sub hf.der.der).add ((TestF.const 2).mul hf)
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

end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Entropy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Frm.frame_cmp
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

end GeneralMahler.HMode

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

lemma loc_mul (A B:Mat m) : u.loc (A*B)=u.loc A*u.loc B := by
  unfold loc; simp only [mul_assoc]
  rw [show u.val*(star u.val*(B*u.val))=B*u.val from by rw [← mul_assoc,u.m₂,one_mul]]

lemma loc_star (A:Mat m) : u.loc (star A)=star (u.loc A) := by
  unfold loc; rw [star_mul,star_mul,star_star,mul_assoc]
lemma loc_trace (A:Mat m) : trace (u.loc A) = trace A := by
  unfold loc; rw [trace_mul_comm,← mul_assoc,u.m₂,one_mul]

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

lemma off_diag : ∀ᵐ u:Plane,u.1≠u.2 := by
  apply (ae_prod_iff_ae_ae (((isClosed_eq continuous_fst continuous_snd).measurableSet.compl))).mpr
  filter_upwards with x
  rw [ae_iff]; simp []
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
lemma reg : regular B.A := ⟨B.poly,B.hM.aestronglyMeasurable⟩

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
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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

lemma mixed_proj {X Y E F:Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f:X→Y→E} (hf:mixed f) (l:E→L[ℝ]F) :
    mixed fun x y=> l (f x y) := by
  apply hf.product (g:=fun _ _=>‖l‖)
    (show PolyBound (fun _:X×Y=>‖l‖) from PolyBound.const _)
  intro x y
  calc
    _ ≤ ‖l‖*‖f x y‖ := l.le_opNorm _
    _ = _ := by rw [Real.norm_of_nonneg (norm_nonneg l),mul_comm]

namespace FieldMat
variable (B:FieldMat m)
lemma pEval {f} (hf:TestF f) : PolyBound (B.eVal f).uncurry :=
  (((B.eval_reg hf).p).comp PolyBound.snd).sub
    ((hf.poly.comp PolyBound.fst).smul (PolyBound.const _))
lemma smEval {f} (hf:TestF f) : StronglyMeasurable (B.eVal f).uncurry :=
  ((B.theta_gen_meas (f:=fun _ y=>f y) (hf.cont.measurable.comp measurable_snd)).stronglyMeasurable).sub
    (((hf.cont.comp continuous_fst).stronglyMeasurable).smul stronglyMeasurable_const)

lemma Em : StronglyMeasurable B.EC.uncurry :=
  ((jump_m.comp (measurable_swap.comp measurable_fst)).stronglyMeasurable.smul stronglyMeasurable_const).sub
    (B.thetaM.comp_measurable ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
lemma Ep : PolyBound B.EC.uncurry :=
  ((PolyBound.of_bound (f:=fun v:Plane × Rn m=>jump v.1.2 v.1.1) 1
    (fun v=>by unfold jump; split_ifs <;> simp)).smul (PolyBound.const _)).sub
    (PolyBound.of_bound (f:=fun v:Plane × Rn m=>B.Θ v.1.2 v.2) 1 (fun v=>B.theta_norm ..))

lemma vanishEC (x:Rn m) (u:Plane) (h: max ‖u.1‖ ‖B.A x‖ < ‖u.2‖) :
    B.EC u x=0 := by
  unfold EC
  obtain ⟨hv,hx⟩ := max_lt_iff.mp h
  have he := B.theta_exact u.2 x hx
  unfold QP at he; rw [sub_eq_zero.mp he]
  have ht : jump u.2 u.1=st u.2 := by
    simp only [Real.norm_eq_abs] at hv
    unfold jump st; split_ifs <;> grind
  rw [ht,scalar,sub_self]

lemma gapM (x:Rn m) (z:ℝ) {f:ℝ→ℝ} (hf:TestF f) :
    Integrable fun y:ℝ=> deriv f y • B.EC (z,y) x := by
  let g := fun y (_:ℝ)=> deriv f y • B.EC (z,y) x
  have hi : mixed g := by
    have hh : PolyBound (fun v:ℝ×ℝ=>B.EC (z,v.1) x) :=
      PolyBound.of_bound 2 fun v=> by
        have h := norm_sub_le (scalar m (jump v.1 z)) (B.Θ v.1 x)
        have hh : ‖scalar m (jump v.1 z)‖≤1 := by
          rcases subsingleton_or_nontrivial (Mat m) with h | h
          · have h0 : scalar m (jump v.1 z) = 0 := @Subsingleton.elim _ h _ 0
            rw [h0, norm_zero]
            exact zero_le_one
          · let : Nontrivial (Mat m) := h
            unfold jump scalar
            split <;> simp
        apply h.trans
        linarith [B.theta_norm v.1 x]
    apply mixed.of_cutoff (show PolyBound g.uncurry from (hf.der.poly.comp PolyBound.fst).smul hh)
      (PolyBound.const (X:=ℝ) (max ‖z‖ ‖B.A x‖))
    intro y w h; unfold g; rw [B.vanishEC _ _ h,smul_zero]
  apply mixed_integrable_left hi 0
  exact ((hf.der.cont.stronglyMeasurable).smul (B.Em.comp_measurable
    ((measurable_const.prodMk measurable_id).prodMk measurable_const))).aestronglyMeasurable

lemma gap (x:Rn m) (z:ℝ) {f:ℝ→ℝ} (hf:TestF f) :
    B.eVal f z x= ∫ y,deriv f y • B.EC (z,y) x := by
  let u := B.Fr x
  let l := LL u
  let g := fun y=> deriv f y • B.EC (z,y) x
  have hi := B.gapM x z hf
  apply u.loc_inj
  rw [eVal,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.eval f x)= _ from B.evfrm x f]
  change _=l (∫ y,g y)
  rw [← l.integral_comp_comm hi]
  ext i j
  rw [show (∫ y,l (g y)) i j=∫ y,l (g y) i j from
    ((coeffMap i j).integral_comp_comm (l.integrable_comp hi)).symm]
  have he (y) : l (g y) = deriv f y • (scalar m (jump y z)-Matrix.diagonal (fun i=>jump y (B.ev x i))) := by
    change u.loc (deriv f y • (scalar m (jump y z)-B.Θ y x))=_
    rw [u.loc_smul,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.Θ y x)=_ from B.evfrm x (jump y)]
  simp_rw [he]
  by_cases h:i=j
  · subst j
    have ht (y) : (deriv f y • (scalar m (jump y z)-Matrix.diagonal (fun i=>jump y (B.ev x i)))) i i =
        ss f y (B.ev x i)-ss f y z := by
      simp [ss,score,scalar]; ring
    have hh (x) := centered_s hf x
    have hp (x:ℝ) : Integrable fun y=>ss f y x :=
      mixed_integrable_left (ss_m hf) x ((ss_sm f).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    simp_rw [ht]; rw [integral_sub (hp _) (hp _),hh,hh]; simp
  simp [scalar,h]

lemma nest (x:Rn m) (z y:ℝ) (hz:z≤y) :
    B.Θ z x* B.Θ y x=B.Θ z x ∧ B.Θ y x*B.Θ z x=B.Θ z x := by
  let u := B.Fr x
  have hi (t:ℝ) : u.loc (B.Θ t x)= Matrix.diagonal (fun i=>jump t (B.ev x i)) := B.evfrm x (jump t)
  constructor <;> apply u.loc_inj <;> rw [u.loc_mul] <;>
    simp only [hi,Matrix.diagonal_mul_diagonal] <;> congr 1 <;> funext i <;>
    unfold jump <;> split_ifs <;> grind
end FieldMat
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Beta
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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

lemma nMS {f j} (hf:TestF f) (hj:TestF j) : mixed (q.nTK W f j) ∧
    StronglyMeasurable (q.nTK W f j).uncurry := by
  let h := fun u:Plane=>deriv f u.1*deriv j u.2
  let l := etL W
  have hm : mixed fun u x=> l (q.edge.NTm u x) := mixed_proj q.edge.nt_mixed l
  have hu : Continuous h := (hf.der.cont.comp continuous_fst).mul (hj.der.cont.comp continuous_snd)
  have hh : PolyBound h := (hf.der.poly.comp PolyBound.fst).mul (hj.der.poly.comp PolyBound.snd)
  have he : q.nTK W f j = fun u x=>h u*l (q.edge.NTm u x) := by
    ext; unfold h l nTK; rw [etL_apply]
  rw [he]
  exact ⟨hm.product (g:=fun u _=>h u) (hh.comp PolyBound.fst) (fun u x=>by rw [norm_mul,mul_comm]),
    (hu.comp continuous_fst).stronglyMeasurable.mul
      ((l.continuous.measurable.comp q.edge.nt_meas).stronglyMeasurable)⟩

lemma ER_P : PolyBound (q.RadiusE B) := q.edge.r_poly.add B.poly.norm
lemma ER_hi (x) :
    q.edge.radius x ≤ q.RadiusE B x ∧ ‖B.A x‖ ≤ q.RadiusE B x :=
  ⟨le_add_of_nonneg_right (norm_nonneg _),le_add_of_nonneg_left (q.edge.r_pos _).le⟩
lemma beyond (x) {z:ℝ} (h:q.RadiusE B x < ‖z‖) : q.EZ B z x=0 := by
  have he := (q.ER_hi B x).1.trans_lt h
  have hf := B.theta_exact z x ((q.ER_hi B x).2.trans_lt h)
  have hi : q.edge.P z x=scalar m (st z) := by
    rw [Real.norm_eq_abs] at he; unfold st; split_ifs with hx
    · rw [abs_of_nonneg hx] at he; rw [q.edge.tend_pos z x he,scalar,one_smul]
    rw [abs_of_neg (lt_of_not_ge hx)] at he; rw [q.edge.tend_neg z x he,scalar,zero_smul]
  change q.edge.P z x-B.Θ z x=_
  rw [hi,sub_eq_zero.mp (show B.Θ z x-scalar m (st z)=0 from hf),sub_self]

lemma crossMS {f j} (hf:TestF f) (hj:TestF j) :
    mixed (q.crossK B W f j) ∧ StronglyMeasurable (q.crossK B W f j).uncurry := by
  let c := fun u:Plane × Rn m=> (u.1.1,u.2)
  let h := fun u:Plane × Rn m=> u.1.2
  have hc : PolyBound c := ((PolyBound.fst.comp PolyBound.fst).prodMk PolyBound.snd)
  have hh : PolyBound h := PolyBound.snd.comp PolyBound.fst
  have he := pj_p (((q.zm B hf).poly).comp hc)
    (((hj.der.poly).comp hh).smul B.Ep) W
  have hm : mixed (q.crossK B W f j) := by
    apply mixed.of_cutoff (f:=q.crossK B W f j) he (q.ER_P B)
    intro u x hx
    by_cases hu : q.RadiusE B x < ‖u.1‖
    · unfold crossK; rw [zE,q.beyond B x hu,smul_zero,← pJ_eq,_root_.map_zero]; rfl
    change _ < max _ _ at hx
    have ht : max ‖u.1‖ ‖B.A x‖ < ‖u.2‖ := by
      have hh := q.ER_hi B x; grind
    unfold crossK; rw [B.vanishEC x u ht,smul_zero,← pJ_eq,_root_.map_zero]
  have h₁ : Measurable c := by unfold c; fun_prop
  have h₂ : Continuous h := by unfold h; fun_prop
  have hi := (pj_cont W).comp_stronglyMeasurable (((q.zSM B f).comp_measurable h₁).prodMk
    (((hj.der.cont.comp h₂).stronglyMeasurable).smul B.Em))
  exact ⟨hm,hi⟩

lemma point_expand_f (x) (f:ℝ→ℝ) (u:Plane) (hu:u.1<u.2) :
    q.nTK W f f u x+Pj W (q.zE B f u.1 x) (q.zE B f u.2 x)=
    q.crossK B W f f u x+q.crossK B W f f u.swap x := by
  set y := u.1; set z:=u.2
  have hh := B.nest x y z hu.le
  unfold nTK Edge.NTm crossK zE
  rw [min_eq_left hu.le,max_eq_right hu.le,pj_scale,pj_scale,pj_scale]
  have HH : u.1<u.2:=hu
  have ha : B.EC u x=1-B.Θ z x := by simp [FieldMat.EC,jump,HH.le,z,scalar]
  have hb : B.EC u.swap x= -B.Θ y x := by simp [FieldMat.EC,jump,not_le_of_gt HH,y,scalar]
  rw [ha,hb]
  let a := q.Pmat y x; let b := q.Pmat z x
  let t := B.Θ y x; let w := B.Θ z x
  have h :
      Pj W a (1-b)+Pj W (a-t) (b-w)=Pj W (a-t) (1-w)+Pj W (b-w) (-t) := by
    unfold Pj jprod
    have hh₁ : t*w=t := hh.1
    have hh₂ : w*t=t := hh.2
    rw [← trN_add, ← trN_add,← mul_add,← mul_add,← smul_add,← smul_add]
    congr 3
    simp only [sub_mul,mul_sub,mul_one,one_mul,neg_mul,mul_neg,hh₁,hh₂]; abel
  change deriv f y*deriv f z*Pj W a (1-b)+ _= _
  change deriv f y*deriv f z*_+deriv f y*(deriv f z*Pj W (a-t) (b-w))=
    deriv f y*(deriv f z*Pj W (a-t) (1-w))+deriv f z*(deriv f y*Pj W (b-w) (-t))
  linear_combination deriv f y*deriv f z*h

lemma point_expand (x) (f:ℝ→ℝ) :
    ∀ᵐ u:Plane,q.nTK W f f u x+Pj W (q.zE B f u.1 x) (q.zE B f u.2 x)=
    q.crossK B W f f u x+q.crossK B W f f u.swap x := by
  filter_upwards [off_diag] with u hu
  rcases lt_or_gt_of_ne hu with h|h; exact q.point_expand_f B W x f u h
  have he := q.point_expand_f B W x f u.swap h
  rw [pj_sym] at he
  simpa [nTK, Edge.NTm, min_comm,max_comm,mul_comm,add_comm] using he

lemma square_pt {f:ℝ→ℝ} (hf:TestF f) (x:Rn m) :
    Pj W (q.MB B f x) (q.MB B f x)+ (∫ u:Plane,q.nTK W f f u x) =
      2*∫ z,q.betaK B W f f z x := by
  let U := fun z=> q.zE B f z x
  let g := fun u:Plane=> q.crossK B W f f u x
  let h := fun u:Plane=> q.nTK W f f u x
  let s := fun u:Plane=> PJ W (U u.1) (U u.2)
  have ig : Integrable g := mixed_integrable_left (q.crossMS B W hf hf).1 x
    (((q.crossMS B W hf hf).2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  have ih : Integrable h := mixed_integrable_left (q.nMS W hf hf).1 x
    (((q.nMS W hf hf).2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  have iu : Integrable U := q.zi B hf x
  have ih' : Integrable s :=
    by
      have he := iu.op_fst_snd (pj_cont W) ⟨‖etL W‖,(fun x y=> pj_norm)⟩ iu
      unfold s; simp_rw [pJ_eq]; exact he
  have he : (∫ u:Plane,(h u+s u))= ∫ u:Plane,(g u+g u.swap) := by
    apply integral_congr_ae
    filter_upwards [q.point_expand B W x f] with u hu
    simpa only [h,s,g,U,pJ_eq] using hu
  have hs : (∫ u,s u)=Pj W (q.MB B f x) (q.MB B f x) := by
    rw [q.mb_eq B hf,← pJ_eq]
    simp only [_root_.map_neg,_root_.neg_apply,neg_neg]
    exact integral_prod_bilin (PJ W) iu iu
  have ha : (∫ u,g u)=∫ z,q.betaK B W f f z x := by
    rw [show (volume:Measure Plane)=volume.prod volume from rfl,integral_prod _ ig]
    congr 1
    ext z
    unfold betaK g crossK
    simp_rw [← pJ_eq]
    rw [B.gap x z hf]; exact (PJ W _).integral_comp_comm (B.gapM x z hf)
  rw [integral_add ih ih',integral_add ig (show Integrable (fun u:Plane=>g u.swap) volume from ig.swap),
    show (∫ u:Plane,g u.swap)=∫ u,g u from integral_prod_swap _,hs,ha] at he
  linarith
lemma eq15 {f:ℝ→ℝ} (hf:TestF f) :
    Pt W (q.MB B f) (q.MB B f)= 2*q.be B W f f-q.Nt W f f := by
  have he (x) : Pj W (q.MB B f x) (q.MB B f x)=
      2*(∫ z,q.betaK B W f f z x)-(∫ u:Plane,q.nTK W f f u x) :=
    eq_sub_of_add_eq (q.square_pt B W hf x)
  unfold Pt be Nt; simp_rw [he]
  have ih := q.bMS B W hf hf
  have hf := q.nMS W hf hf
  rw [integral_sub,integral_const_mul]
  · exact ((mixed_integrable (μ:=volume) (ν:=normal m) ih.1 ih.2.aestronglyMeasurable).integral_prod_right).const_mul _
  exact (mixed_integrable (μ:=volume) (ν:=normal m) hf.1 hf.2.aestronglyMeasurable).integral_prod_right
end ProjField
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

namespace FieldMat
variable (B:FieldMat m)
omit [NeZero m] in
lemma eval_scale {f:ℝ→ℝ} (hf:TestF f) (a:ℝ) (x) :
    B.eval (fun z=>a*f z) x=a•B.eval f x := cfc_const_mul a f _ hf.cont.continuousOn
omit [NeZero m] in
lemma eval_sub {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (x) :
    B.eval (fun z=>f z-g z) x=B.eval f x-B.eval g x :=
  cfc_sub f g _ hf.cont.continuousOn hg.cont.continuousOn
end FieldMat
namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Roots
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Exterior square-root kernel integrals in §05. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Roots

lemma u_pos {t:ℝ} (h:0≤t) : 0<u t := by unfold u; apply sub_pos.mpr; apply Real.sqrt_lt_sqrt h; linarith
lemma u_add {t:ℝ} (h:0≤t) : u t*(√(1+t)+√t)=1 := by
  unfold u
  nlinarith [Real.sq_sqrt h,Real.sq_sqrt (show 0≤1+t by linarith)]
lemma sqrt_top {t:ℝ} (h:0≤t) : √(1+t)=(1+p t)/(2*u t) := by
  have he := u_pos h
  have hh := u_add h
  field_simp
  unfold p; unfold u at *; nlinarith
lemma sqrt_bot {t:ℝ} (h:0≤t) : √t=(1-p t)/(2*u t) := by
  have he := u_pos h; have hh:= u_add h; field_simp
  unfold p; unfold u at *; nlinarith
lemma t_p {t:ℝ} (h:0≤t) : t=(1-p t)^2/(4*p t) := by
  have hp : 0<p t := pow_pos (u_pos h) _
  have he := Real.sq_sqrt h
  rw [sqrt_bot h,div_pow] at he
  calc
    t = _ := he.symm
    _ = _ := by unfold p; ring
lemma p_lt {t:ℝ} (h:0<t) : p t<1 := by
  have he := sqrt_bot h.le
  have hv := Real.sqrt_pos.2 h
  have hu := u_pos h.le
  field_simp at he
  nlinarith
lemma dp {t:ℝ} (h:0<t) :
    HasDerivAt p (-(4*p t^2)/(1-p t^2)) t := by
  have hp : 0<p t := pow_pos (u_pos h.le) _
  have hu := u_pos h.le
  have hl := p_lt h
  have ht : 0 <1+t := by linarith
  have he : HasDerivAt u ((1/(2*√(1+t)))-(1/(2*√t))) t :=
    by
      convert ((((hasDerivAt_id' t).const_add 1).sqrt ht.ne').sub ((hasDerivAt_id' t).sqrt h.ne')) using 1
      all_goals try with_reducible_and_instances rfl
      all_goals rfl
  convert he.pow 2 using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | skip
  rw [sqrt_top h.le,sqrt_bot h.le]
  have hs : 1-p t^2≠0 := by nlinarith
  have hv : 1-p t≠0 := by linarith
  norm_num
  field_simp
  unfold p; ring

lemma y_formula {t:ℝ} (h:0<t) :
    yk t=(1/(1+p t) - p t/2)/2*(4*p t^2/(1-p t^2)) := by
  have hp : 0<p t := pow_pos (u_pos h.le) _
  have hu := u_pos h.le; have hx:= p_lt h
  have hz : 1-p t^2≠0 := by nlinarith
  unfold yk
  rw [sqrt_top h.le,sqrt_bot h.le]
  conv_lhs =>
    rhs; lhs; rhs; rw [t_p h.le]
  field_simp
  unfold p; ring

lemma pu_limit : Tendsto p atTop (𝓝 0) := by
  let g := fun t:ℝ=> √(1+t)+√t
  have ht : Tendsto g atTop atTop := by
    apply tendsto_atTop_mono (g:=g) _ Real.tendsto_sqrt_atTop
    intro x; change √x ≤ √(1+x)+√x; linarith [Real.sqrt_nonneg (1+x)]
  have he : Tendsto u atTop (𝓝 0) := by
    apply Tendsto.congr' _ (tendsto_inv_atTop_zero.comp ht)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t h
    have ha := u_pos h; have hh := u_add h
    have hs : g t≠0 := by
      unfold g; positivity
    change (g t)⁻¹=u t
    field_simp
    linarith
  have h := he.pow 2; norm_num at h; exact h
lemma cu : Continuous p := by unfold p u; fun_prop

lemma dfy {t:ℝ} (h:0<t) : HasDerivAt fy (yk t) t := by
  have hp : 0<p t := pow_pos (u_pos h.le) _
  convert ((((((dp h).const_add 1).log (by positivity)).div_const 2).sub
    (((dp h).pow 2).div_const 8)).neg) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | skip
  rw [y_formula h]; norm_num; ring
lemma area_template {f g:ℝ→ℝ} (hf:ContinuousAt f 0) (h:Tendsto f atTop (𝓝 0))
    (hp:∀ t,0<t→ 0≤g t) (hd:∀ t,0<t→HasDerivAt f (g t) t) :
    IntegrableOn g (Ioi 0) ∧ (∫ t in Ioi 0,g t)=-f 0 := by
  have he := integrableOn_Ioi_deriv_of_nonneg hf.continuousWithinAt hd hp h
  refine ⟨he,?_⟩
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto hf.continuousWithinAt hd he h

lemma puc (f:ℝ→ℝ) (hf:ContinuousOn f (Ici 0)) :
    Continuous (fun x=>f (p x)) := hf.comp_continuous cu (fun x=> mem_Ici.mpr (show 0 ≤ p x from sq_nonneg _))

lemma y_area :
    IntegrableOn yk (Ioi 0) ∧ (∫ t in Ioi 0,yk t)=Real.log 2/2 -1/8 := by
  let f := fun x:ℝ=> -(Real.log (1+x)/2-x^2/8)
  have hf : ContinuousOn f (Ici 0) := by
    unfold f; fun_prop (disch:= first | (intro x hx; change 0≤x at hx; positivity) | positivity)
  have hp : Continuous fy := puc f hf
  have hC : ContinuousAt f 0 := by unfold f; fun_prop (disch:=norm_num)
  have ht : Tendsto fy atTop (𝓝 0)  := by
    have h := hC.tendsto.comp pu_limit
    change Tendsto fy atTop (𝓝 (f 0)) at h
    norm_num [f] at h; exact h
  have hh := area_template hp.continuousAt ht (fun t h=> show 0≤ yk t by unfold yk; positivity)
    (fun t h=>dfy h)
  norm_num [fy,p,u] at hh ⊢
  exact hh
end GeneralMahler.Roots

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Major
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Piecewise kernel square estimates will use these scaled integrable
majorants. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Roots
open Classical

lemma slab_int (f g:ℝ→ℝ) (hf:IntegrableOn f (Ioi 0))
    (hg:Continuous g) :
    Integrable (slab f g) ∧ (∫ x,slab f g x)=(2*∫ x in Ioi 0,f x)+∫ x in Icc 0 1,g x := by
  let l := (Ioi 0).indicator f
  let k := (Icc 0 1).indicator g
  have hl : Integrable l := (integrable_indicator_iff measurableSet_Ioi).mpr hf
  have hk : Integrable k := (integrable_indicator_iff measurableSet_Icc).mpr hg.integrableOn_Icc
  have hi : Integrable (fun x=>l (-x)) :=
    ((measurePreserving_neg volume).integrable_comp_emb (Homeomorph.neg _).measurableEmbedding).mpr hl
  have hh : Integrable (fun x=>l (x-1)) := by
    simpa [sub_eq_add_neg] using hl.comp_add_right (-1)
  have he : slab f g=fun x=> l (-x)+k x+l (x-1) := by
    ext x
    unfold l k slab
    by_cases h:x<0
    · simp [h,indicator,show ¬0≤x by linarith,show ¬0<x-1 by linarith]
    by_cases ht:x≤1
    · simp [h,ht, indicator, show 0≤x by linarith, show ¬0<x-1 by linarith]
    simp [h,ht,indicator,show 0<x-1 by linarith]
  rw [he]
  refine ⟨(hi.add hk).add hh,?_⟩
  rw [integral_add,integral_add hi hk, integral_neg_eq_self, integral_sub_right_eq_self]
  · unfold l k
    simp_rw [integral_indicator measurableSet_Ioi,integral_indicator measurableSet_Icc]; ring
  all_goals first | exact hi.add hk | exact hh

lemma secU (f:ℝ→ℝ) (q:ℝ) {a:ℝ} (ha:0<a) (hf:Integrable f) :
    Integrable (fun z=>a*f ((z-q)/a)) ∧ (∫ z:ℝ,a*f ((z-q)/a))=a^2*∫ x,f x := by
  have h : Integrable (fun z=> f (z/a)) :=
    by simp_rw [div_eq_mul_inv]; exact (integrable_comp_mul_right_iff f (inv_pos.mpr ha).ne').2 hf
  let l := fun z:ℝ=>f (z/a)
  have hi : Integrable (fun z=>l (z-q)) := by simpa [l,sub_eq_add_neg] using h.comp_add_right (-q)
  constructor
  · exact hi.const_mul _
  rw [integral_const_mul]
  have ht : (∫ z:ℝ,l (z-q))=∫ z,l z := integral_sub_right_eq_self l q
  change a*(∫ z,l (z-q))=_
  rw [ht]
  unfold l
  rw [Measure.integral_comp_div]
  simp [abs_of_pos ha]; ring
lemma U_area (f g:ℝ→ℝ) (hf:IntegrableOn f (Ioi 0)) (hg:Continuous g) (x y:ℝ) :
    Integrable (U f g x y) ∧ (∫ z,U f g x y z)=(x-y)^2*((2*∫ t in Ioi 0,f t)+∫ t in Icc 0 1,g t) := by
  by_cases h:x=y
  · subst y; rw [show U f g x x=(fun _ => (0:ℝ)) from by ext; simp [U] ]; simp
  have hu := secU (slab f g) (min x y) (show 0< |y-x| from abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))) (slab_int f g hf hg).1
  unfold U; convert hu using 1
  rw [sq_abs, (slab_int f g hf hg).2]; ring_nf

lemma Uy_area (x y:ℝ) :
    Integrable (Uy x y) ∧ (∫ z,Uy x y z)=(Real.log 2+1/4)*(x-y)^2 := by
  have h := U_area _ (fun _=>1/2) y_area.1 continuous_const x y
  rw [y_area.2,setIntegral_const] at h; refine ⟨h.1,h.2.trans ?_⟩
  norm_num; ring
lemma U_swap (f g) (x y z) : U f g x y z=U f g y x z := by rw [U,U,abs_sub_comm,min_comm]
lemma U_outHi (f g) {x y z:ℝ} (hx:x<y) (hy:y<z) :
    U f g x y z=(y-x)*f ((z-y)/(y-x)) := by
  have h:= sub_pos.mpr hx
  have he : 1<(z-x)/(y-x) := by rw [lt_div_iff₀ h]; linarith
  rw [U,abs_of_pos h,min_eq_left hx.le,slab,ite_eq_right (by linarith),ite_eq_right (by linarith)]
  congr 2; field_simp; ring
lemma U_outLo (f g) {x y z:ℝ} (hx:x<y) (hy:z<x) :
    U f g x y z=(y-x)*f ((x-z)/(y-x)) := by
  have h:= sub_pos.mpr hx
  rw [U,abs_of_pos h,min_eq_left hx.le,slab,ite_eq_left (div_neg_of_neg_of_pos (sub_neg.mpr hy) h)]
  congr 2; ring
lemma U_mid (f g) {x y z:ℝ} (hx:x<z) (hy:z<y) :
    U f g x y z=(y-x)*g ((z-x)/(y-x)) := by
  have h:= sub_pos.mpr (hx.trans hy)
  rw [U,abs_of_pos h,min_eq_left (by linarith),slab,
    ite_eq_right (not_lt_of_ge (div_nonneg (by linarith) h.le)),ite_eq_left]; rw [div_le_iff₀ h]; linarith
end GeneralMahler.Roots

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

lemma r_swap (x y z) : rcoef x y z=rcoef y x z := by
  unfold rcoef
  by_cases h:signE x z=signE y z
  · simp only [h,↓reduceIte]; ring
  simp [h,Ne.symm h]
lemma K_swap (f) (x y z) : kz f x y z=kz f y x z := by
  unfold kz; rw [r_swap]; ring
lemma O_swap (f) (x y z) : Om f x y z=Om f y x z := by unfold Om; ring
lemma bar_const (x:Plane) : bAv (fun _=>1) x=1 := by unfold bAv; simp

lemma middle (f:Plane→ℝ) (hf:Bwt f) {x y z:ℝ} (hx:x<z) (hy:z<y) :
    kz f x y z ^2≤Om (fun u=>f u^2) x y z* Uy x y z ∧
    (2*kz (fun _=>1) x y z)^2≤Om (fun _=>1) x y z* Ux x y z := by
  have ha : x≤ z := hx.le
  have he : rcoef x y z=0 := by unfold rcoef signE; norm_num [not_lt_of_ge ha,hy]
  let a := z-x
  let b := y-z
  let V := fun t => bAv f (z,t)
  let W := fun t => bAv (fun u=>f u^2) (z,t)
  have hp : 0<a := sub_pos.mpr hx
  have hh : 0<b := sub_pos.mpr hy
  have hu : y-x=a+b := by unfold a b; ring
  unfold kz Om Uy Ux
  rw [he,U_mid xk gx hx hy,U_mid yk _ hx hy,abs_of_neg (sub_neg.mpr hx),abs_of_pos (sub_pos.mpr hy)]
  have hh₁ : x-z= -a := by unfold a; ring
  rw [hh₁,neg_neg]
  constructor
  · change ((-a*V x+b*V y-0*_)/2)^2 ≤ (a*W x+b*W y)/2*((y-x)*(1/2))
    have hv : (a*V x-b*V y)^2 ≤ (a+b)*(a*W x+b*W y) :=
      calc
        _ ≤ (a+b)*(a*V x^2+b*V y^2) := by nlinarith [mul_nonneg (mul_nonneg hp.le hh.le) (sq_nonneg (V x+V y))]
        _ ≤ _ := by
          have hX : V x^2≤W x := bar_sq f hf _
          have hY : V y^2≤W y := bar_sq f hf _
          gcongr
    rw [hu]; nlinarith
  simp_rw [bar_const]
  unfold gx; rw [hu]
  have hh₂ : z-x=a := rfl
  rw [hh₂]; apply le_of_eq; field_simp; ring

-- parameterized ray ε, near z+ε*b, far z+ε*a.
lemma av_dist (f:Plane→ℝ) (z sig b:ℝ) (_hb:0<b) :
    bAv f (z,z+sig*b)*b = ∫ t in 0..b,f (z,z+sig*t) := by
  let g := fun t=>f (z,z+sig*t)
  have hh := intervalIntegral.smul_integral_comp_mul_left g (a:=0) (b:=1) b
  unfold bAv
  have he (t:ℝ) : f ((z,z+sig*b).1,along (z,z+sig*b) t) = g (b*t) := by
    unfold along g; dsimp; congr 2; ring
  simp_rw [he]
  simpa only [mul_zero,mul_one,smul_eq_mul,mul_comm b,zero_mul,one_mul,g] using hh

lemma ext_shape {a b:ℝ} (ha:0<b) (h:b<a) :
    let l:=a-b
    l*xk (b/l)=(√a-√b)^4/( (a+b)/2) ∧
      l*yk (b/l)=(√a-√b)^2/2*((a-b)/a+(1-√b/√a)^2/2) := by
  intro l
  have hl : 0<l:= sub_pos.mpr h
  have hp : 0<a:=ha.trans h
  have ht : 1+b/l=a/l := by field_simp; unfold l; ring
  unfold xk yk u
  rw [ht,Real.sqrt_div ha.le,Real.sqrt_div hp.le]
  have hk:= Real.sq_sqrt hl.le
  have he:= Real.sqrt_pos.mpr hp; have hh:=Real.sqrt_pos.mpr hl
  have hb : 1+2*(b/l)>0 := by positivity
  constructor
  all_goals field_simp
  · rw [show √l^4=l^2 by rw [show (4:ℕ)=2*2 from rfl,pow_mul,hk] ]
    unfold l; ring
  rw [hk]; unfold l; ring

-- exterior, parameterized orientation. U replaced analytic RHS.
lemma K_ext (f:Plane→ℝ) (hf:Bwt f) (z s a b:ℝ) (hs:s=1 ∨ s= -1)
    (hp:0<b) (h:b<a) :
    let x:=z+s*b
    let y:=z+s*a
    let l:=a-b
    kz f x y z ^2 ≤ Om (fun u=>f u^2) x y z*(l*yk (b/l)) ∧
    (2*kz (fun _=>1) x y z)^2 ≤ Om (fun _=>1) x y z*(l*xk (b/l)) := by
  intro x y l
  have ha : 0<a:=hp.trans h
  set A:=√a; set B:=√b
  have hA : 0<A:= Real.sqrt_pos.mpr ha
  have hB : 0<B:= Real.sqrt_pos.mpr hp
  have HB : B^2=b := Real.sq_sqrt hp.le
  have HA : A^2=a := Real.sq_sqrt ha.le
  let g := fun t=>f (z,z+s*t)
  have hg : Continuous g := hf.c.comp (by fun_prop)
  let R := fun t=> bAv f (z,z+s*t)
  let P := fun t=> bAv (fun u=> f u^2) (z,z+s*t)
  let x₁:=∫ t in b..a,g t
  let x₂:=∫ t in 0..b,g t
  let y₁:=∫ t in b..a,g t^2
  let y₂:=∫ t in 0..b,g t^2
  have hi : R b*b=x₂ ∧ R a*a=x₂+x₁ ∧ P b*b=y₂ ∧ P a*a=y₂+y₁ := by
    have he := hg.intervalIntegrable (μ:=volume)
    have hh := (hg.pow 2).intervalIntegrable (μ:=volume)
    exact ⟨av_dist f z s b hp,(av_dist f z s a ha).trans
      (intervalIntegral.integral_add_adjacent_intervals (he ..) (he ..)).symm,
      av_dist _ z s b hp,(av_dist _ z s a ha).trans
        (intervalIntegral.integral_add_adjacent_intervals (hh ..) (hh ..)).symm⟩
  obtain ⟨hx,hx',hy,hy'⟩:=hi
  have he : (A*R a-B*R b)^2 ≤ (a*P a+b*P b)*((a-b)/a+(1-B/A)^2/2) := by
    have h₁:= integral_sq_le g hg b a h.le
    have h₂:= integral_sq_le g hg 0 b hp.le; rw [sub_zero] at h₂
    change x₁^2≤l*y₁ at h₁
    change x₂^2≤b*y₂ at h₂
    have hl : 0<l:= sub_pos.mpr h
    let d:=1/A; let c:=1/A-1/B
    have hh : (d*x₁+c*x₂)^2 ≤ (d^2*l+c^2*b/2)*(y₁+2*y₂) := by
      have he := add_le_add ((div_le_iff₀ hl).mpr (h₁.trans_eq (mul_comm ..))) (mul_le_mul_of_nonneg_left ((div_le_iff₀ hp).mpr (h₂.trans_eq (mul_comm ..)))
        (show (0:ℝ)≤2 by norm_num))
      apply le_trans _ (mul_le_mul_of_nonneg_left he (by positivity))
      field_simp
      nlinarith [sq_nonneg (2*d*l*x₂-c*b*x₁)]
    have hz : d*x₁+c*x₂=A*R a-B*R b := by
      unfold d c
      rw [show x₁=R a*a-R b*b by linarith,← hx,← HA,← HB]
      field_simp; ring
    have hq : d^2*l+c^2*b/2=(a-b)/a+(1-B/A)^2/2 := by
      unfold d c l; rw [← HA,← HB]; field_simp; ring
    rw [hz,hq] at hh
    have hi : y₁+2*y₂=a*P a+b*P b := by linarith
    rw [hi] at hh; linarith
  have ht : |x-z|=b ∧ |y-z|=a ∧ x-z=s*b ∧ y-z=s*a ∧ rcoef x y z=s*B*A := by
    unfold x y rcoef signE
    rcases hs with h|h <;> subst s <;> simp [A,B,hp,ha,not_lt_of_ge hp.le,not_lt_of_ge ha.le,abs_of_pos]
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := ht
  obtain ⟨h₆,h₇⟩ := ext_shape hp h
  have hs' : s^2=1 := by rcases hs with rfl|rfl<;>ring
  unfold kz Om
  rw [h₅,h₁,h₂,h₃,h₄]
  constructor
  · change ((s*b*R b+s*a*R a-s*B*A*(R b+R a))/2)^2 ≤ (b*P b+a*P a)/2*(l*yk (b/l))
    rw [h₇]
    change _≤(b*P b+a*P a)/2*((A-B)^2/2*((a-b)/a+(1-B/A)^2/2))
    apply le_trans _ (by
      have h := mul_le_mul_of_nonneg_left he (show 0 ≤ (A-B)^2/4 by positivity)
      exact h.trans_eq (by ring))
    apply le_of_eq
    calc
      _ = s^2*((A-B)^2/4)*(A*R a-B*R b)^2 := by rw [← HA,← HB]; ring
      _ = _ := by rw [hs',one_mul]
  simp_rw [bar_const]
  rw [h₆]
  apply le_of_eq
  change _= _*((A-B)^4 / _)
  field_simp
  rw [← HA,← HB]
  rcases hs with h|h <;> rw [h] <;> ring

lemma k_same (f) (z x:ℝ) :
    kz f x x z=0 := by
  unfold kz rcoef
  rw [ite_eq_left rfl, mul_assoc (signE x z) (√|x-z|) (√|x-z|),← pow_two, Real.sq_sqrt (abs_nonneg _)]
  unfold signE; split_ifs with h
  · rw [abs_of_pos (sub_pos.mpr h)]; ring
  rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))]; ring

lemma pairOrd (f:Plane→ℝ) (hf:Bwt f) {x y z:ℝ} (hx:x<y) (hy:z≠x) (hz:z≠y) :
    kz f x y z ^2 ≤ Om (fun u=>f u^2) x y z* Uy x y z ∧
    (2*kz (fun _=>1) x y z)^2 ≤ Om (fun _=>1) x y z* Ux x y z := by
  unfold Uy Ux
  rcases lt_or_gt_of_ne hy with h|h
  · rw [U_outLo _ _ hx h,U_outLo _ _ hx h]
    have hh := K_ext f hf z 1 (y-z) (x-z) (Or.inl rfl) (sub_pos.mpr h)
      (show x-z<y-z by linarith)
    simpa only [one_mul,add_sub_cancel,sub_sub_sub_cancel_right] using hh
  rcases lt_or_gt_of_ne hz with h'|h'
  · exact middle f hf h h'
  rw [U_outHi _ _ hx h',U_outHi _ _ hx h',K_swap,O_swap,K_swap (fun _=>1),O_swap (fun _=>1)]
  have hh := K_ext f hf z (-1) (z-x) (z-y) (Or.inr rfl) (sub_pos.mpr h')
    (show z-y<z-x by linarith)
  simpa only [neg_one_mul,← sub_eq_add_neg,sub_sub_cancel,sub_sub_sub_cancel_left] using hh

lemma pairEst (f:Plane→ℝ) (hf:Bwt f) {x y z:ℝ} (hy:z≠x) (hz:z≠y) :
    kz f x y z ^2 ≤ Om (fun u=>f u^2) x y z* Uy x y z ∧
    (2*kz (fun _=>1) x y z)^2 ≤ Om (fun _=>1) x y z* Ux x y z := by
  rcases lt_trichotomy x y with h|rfl|h
  · exact pairOrd f hf h hy hz
  · simp only [k_same,Ux,Uy,U,sub_self,abs_zero]; norm_num
  rw [K_swap,O_swap,K_swap (fun _=>1),O_swap (fun _=>1),Ux,U_swap,Uy,U_swap]
  exact pairOrd f hf h hz hy
end GeneralMahler.Seg

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

lemma tr_blk (w:Fin m→ℝ) (hw:∀ i,0≤w i) :
    mats (fun i=> ∑ j,(b.a i*w i+b.a j*w j)/2*b.E i j^2) ≤
    mats (fun i=>b.S i i*w i) := by
  have he :
      (∑ i,∑ j,(b.a i*w i+b.a j*w j)/2*b.E i j^2)=
      ∑ i,b.a i*w i*∑ j,b.E i j^2 := by
    have h (i j) :
        (b.a i*w i+b.a j*w j)/2*b.E i j^2=
        (b.a i*w i*b.E i j^2+b.a j*w j*b.E j i^2)/2 := by rw [symm_entry b.Her i j]; ring
    let F := fun i j=> b.a i*w i*b.E i j^2
    simp_rw [h,← Finset.sum_div,Finset.sum_add_distrib, Finset.mul_sum]
    change ((∑ i,∑ j,F i j)+(∑ j,∑ i,F i j))/2=∑ i,∑ j,F i j
    rw [Finset.sum_comm]; ring
  unfold mats
  rw [he]
  gcongr
  change _ ≤ b.S i i*w i
  rw [b.Sdiag]
  apply le_trans (mul_le_mul_of_nonneg_left (b.Ed2 _) (mul_nonneg (abs_nonneg _) (hw _)))
  apply le_of_eq; unfold a; ring

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
lemma fl_d {l} (hl:TestF l) : deriv (fl l)=N2 l := by
  unfold fl Nr N
  rw [pl_d hl]
  ext x
  have he := (((pl_test hl).diff x).hasDerivAt.fun_add (((hasDerivAt_id' x).fun_mul
    (hl.diff x).hasDerivAt).fun_sub (hl.der.diff x).hasDerivAt)).deriv
  simp only [pl_d hl] at he
  unfold N2 N; rw [he]; ring
lemma Nr_ga {b} (hb:TestF b) : ga (Nr b)=ga b := by
  unfold Nr
  rw [ga_add hb (N_test hb)]; unfold N
  rw [ga_sub (TestF.id.mul hb.der) hb.der.der,
    ga_parts hb.der]; ring
lemma fl_ga {l} (hl:TestF l) : ga (fl l)=0 := (Nr_ga (pl_test hl)).trans (pl_ga hl)

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

lemma pj_poly_part {f: Rn m→Mat m} (hf:regular f) (W:Mat m) :
    Integrable (fun x=>Pj W (f x) (f x)) (normal m) := by
  simp_rw [← pJ_eq]
  exact ProjField.proj_int W hf hf

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Parity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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

lemma pl_odd (f:ℝ→ℝ) (hf:TestF f) (hh:Function.Even f) :
    Function.Odd (pl f) := by
  have h : Function.Odd (prim f) := by
    intro x
    let g := fun y=>prim f (-y)+prim f y
    have he (t:ℝ) : HasDerivAt g 0 t := by
      convert (((prim_d hf (-t)).comp t (hasDerivAt_neg' t)).add (prim_d hf t)) using 1
      all_goals try with_reducible_and_instances rfl
      all_goals first | rfl | (rw [hh]; ring)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => he z)
      (continuous_const.intervalIntegrable 0 x)
    simp only [intervalIntegral.integral_zero,g,neg_zero,show prim f 0=0 from by simp [prim] ] at h
    linarith
  have he : ga (prim f)=0 := by
    let g := fun x=>phi x*prim f x
    have ht : (fun x:ℝ=>g (-x))=fun x=> -g x := by ext x; unfold g; rw [h,neg_phi]; ring
    have hi := integral_neg_eq_self g volume
    rw [ht,integral_neg] at hi; change (∫ x,g x)=0; linarith
  intro x; rw [pl,pl,h,he]; ring
lemma fl_odd (f:ℝ→ℝ) (hf:TestF f) (h:Function.Even f) :
    Function.Odd (fl f) := by
  let b:= pl f
  have h' := pl_test hf
  have hh := pl_odd f hf h
  have hv := map_deriv_odd h' hh
  intro x; unfold fl Nr N
  rw [hh,hv,map_deriv_even h'.der hv]; ring
lemma Hneg (n:ℕ) : ∀ x,H n (-x)=(-1)^n*H n x := by
  induction n with
  | zero=> simp [H]
  | succ n ih=>
    intro x
    have he : H n ∘ (fun x:ℝ=> -x)=fun x=> (-1)^n*H n x := funext ih
    have h := ((ht n).diff (-x)).hasDerivAt.comp x (hasDerivAt_neg' x)
    rw [he] at h
    have hh := h.unique (((ht n).diff x).hasDerivAt.const_mul ((-1)^n))
    simp only [H,ih,pow_succ]
    have hb : deriv (H n) (-x)= -((-1)^n*deriv (H n) x) := by linarith
    rw [hb]; ring
lemma MMneg (a:MI m) (x:Rn m) : MM a (-x)=(-1)^(deg a)*MM a x := by
  unfold MM
  simp only [show ∀ i:Fin m,(-x) i= -(x i) from fun _=>rfl,Hneg,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,deg]

namespace ProjField
variable (q:ProjField m)
lemma Lneg (x:Rn m) : q.Lmat (-x) = -q.Lmat x := by simp_rw [← q.ell_eq,_root_.map_neg]

section
variable [NeZero m]

lemma BoEval {f:ℝ→ℝ} (hf:Function.Odd f) :
    Function.Odd (q.FL.eval f) := by
  intro x
  let B:=q.FL
  let u:= B.Fr x
  have he : B.A (-x)= -B.A x := q.Lneg x
  have hu : u.loc (B.A (-x))= -u.loc (B.A x) := by
    rw [he]; simp [Frm.loc]
  have h (i): u.eig (B.A (-x)) i= -u.eig (B.A x) i := by unfold Frm.eig; rw [hu]; rfl
  have ht : u.Dgn (B.A (-x)) := by
    unfold Frm.Dgn
    rw [hu,show u.loc (B.A x)=_ from B.Fr_D x]
    ext i j; by_cases hh:i=j
    · subst j; simp [h]; rfl
    simp [hh]
  apply u.loc_inj
  change u.loc (cfc f (B.A (-x)))=u.loc (-cfc f (B.A x))
  rw [show u.loc (-cfc f (B.A x)) = -u.loc (cfc f (B.A x)) from by simp [Frm.loc],
    u.loc_cfc (B.sym x) (B.Fr_D x),u.loc_cfc (B.sym (-x)) ht]
  ext i j
  by_cases hi:i=j
  · subst j; simp [h]; apply hf
  simp [hi]

end

lemma cf_ref (f:Rn m→Mat m) (a:MI m) :
    cof (fun x=>f (-x)) a=(-1:ℝ)^(deg a) • cof f a := by
  unfold cof
  rw [← integral_smul,normal_integral,normal_integral]; rw [← integral_neg_eq_self (fun x=> nDensity x • MM a x • f (-x)) volume]; simp_rw [MMneg,mul_smul,neg_neg,nDensity,norm_neg]
lemma cf_s (f:Rn m→Mat m) (a:MI m) (c:ℝ) :
    cof (fun x=>c • f x) a=c • cof f a := by
  unfold cof; rw [← integral_smul]; congr 1; funext x; rw [smul_comm]
lemma cof_odd_zero (f:Rn m→Mat m) (a:MI m) (he:Even (deg a)) (hh:Function.Odd f) :
    cof f a=0 := by
  have hi : (fun x=>f (-x))= fun x=> (-1:ℝ) • f x := funext fun x=>by rw [hh];simp
  have ht := cf_ref f a
  rw [hi,cf_s, he.neg_one_pow] at ht
  simp only [neg_smul,one_smul] at ht
  ext i j
  have hi := congrFun (congrFun ht i) j
  change - (cof f a i j)=_ at hi; change _=0
  linarith
variable [NeZero m]

lemma re_ref : regular fun x=>q.RR (-x) := ⟨q.R_reg.p.comp PolyBound.id.neg,by
  have he : StronglyMeasurable q.RR := q.A_SM.sub q.L_cont.stronglyMeasurable
  exact (he.comp_measurable measurable_neg).aestronglyMeasurable⟩
lemma Ro_reg : regular q.Ro :=
  (show regular (fun x=>q.RR x-q.RR (-x)) from ⟨q.R_reg.p.sub q.re_ref.p,
    q.R_reg.meas.sub q.re_ref.meas⟩).smul ⟨PolyBound.const _,aestronglyMeasurable_const⟩
lemma coRo (a:MI m) :
    cof q.Ro a= if Even (deg a) then 0 else cof q.RR a := by
  change cof (fun x=>(_ : ℝ) • _) a=_
  rw [cf_s,cof_subm q.R_reg q.re_ref,cf_ref]
  split_ifs with hh
  · simp [hh.neg_one_pow]
  have he : Odd (deg a) := Nat.not_even_iff_odd.mp hh
  rw [he.neg_one_pow]; module

lemma bal_cf (h:q.avgA=0) (a:MI m) (hd:deg a < 2) : cof q.RR a=0 := by
  unfold RR
  rw [cof_subm q.a_reg q.l_reg]
  by_cases hh:a=0
  · subst a; rw [q.coL_o (by simp [deg])]
    unfold cof; simp_rw [Mzero]; simp only [one_smul,sub_zero]; exact h
  obtain ⟨i,hi⟩ : ∃ i,a i≠0 := by by_contra! hb; exact hh (funext hb)
  set b := decM a i
  have he : a=inc b i := (inc_dec a i hi).symm
  have hb : b=0 := by
    rw [he,deg_inc] at hd
    apply (dz b).mp; omega
  rw [hb] at he
  rw [he,q.coL]
  have ht : cof q.Amat (inc 0 i)=q.M i := by
    unfold cof; simp_rw [Mi1]; rfl
  rw [ht,Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp
  intro j hj hj'
  have hh : inc (0:MI m) i≠ inc 0 j := by
    intro hi
    have he := congrFun hi i
    simp [inc, Ne.symm hj'] at he
  simp [hh]
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Degree
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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
omit [NeZero m] in
lemma pj_positive {W A:Mat m} (h:0≤W) (hh:A.IsHermitian) : 0≤ Pj W A A := by
  rw [Pj,j_same]
  exact trN_mul_nonneg h (sqPSD hh)
omit [NeZero m] in
lemma p_le_p {W T A:Mat m} (h:W≤T) (hh:A.IsHermitian) :
    Pj W A A≤ Pj T A A := by simp only [Pj,j_same]; apply trN_mul_mono h (sqPSD hh)
omit [NeZero m] in
lemma p_ladd (W A B C:Mat m) : Pj W A (B+C)= Pj W A B+Pj W A C := by
  simp_rw [← pJ_eq]; rw [_root_.map_add]
omit [NeZero m] in
lemma p_square_diff (W A B:Mat m) (c:ℝ) :
    Pj W (A-c•B) (A-c•B)=Pj W A A-2*c*Pj W A B+c^2*Pj W B B := by
  simp_rw [pj_ss,pJ_smul_left,pJ_smul_right]; rw [pj_sym W B A]; ring

omit [NeZero m] in
lemma pos_cov {q:ProjField m} : 0≤q.covMat := sqPSD q.pos.isHermitian
omit [NeZero m] in
lemma Cf_sym {A:Rn m→Mat m} (ha:regular A) (hh:∀ x,(A x).IsHermitian) (a:MI m) :
    (cof A a).IsHermitian := hermitian_integral (i_cof ha.p ha.meas a)
      (ae_of_all _ fun x=> (hh x).smul (show IsSelfAdjoint (_:ℝ) from rfl))

omit [NeZero m] in
lemma rho_pos (a:MI m) : 0<kMode a := by unfold kMode; positivity
omit [NeZero m] in
lemma rho_inv (a:MI m) : (kMode a)⁻¹=1+(deg a:ℝ) := by unfold kMode; rw [inv_inv]
namespace ProjField
variable (q:ProjField m)
lemma DD_sym {l:ℝ→ℝ} (hl:TestF l) (a:MI m) :
    (q.DD l a).IsHermitian := by
  unfold DD
  refine ((q.cfH_sym (fl_test hl) _).smul (by simp [IsSelfAdjoint])).sub
    (Cf_sym (q.FL.eval_reg (pl_test hl)) (fun _=> cfc_herm ..) _)
lemma r_sym (x) : (q.RR x).IsHermitian :=
  (q.H_hermitian poly_id_der x).sub (q.L_sym x)

lemma P_mb_sym {l} (hl:TestF l) (x) : (q.MB q.FL l x).IsHermitian :=
  ((q.H_hermitian hl.der.poly x).sub (cfc_herm ..)).add (scalar_sym ..)
lemma D_pos {l} (hl:TestF l) : 0 ≤ q.Dnorm l :=
  tsum_nonneg (fun a=> mul_nonneg (by positivity) (pj_positive pos_cov (q.DD_sym hl _)))

-- linearity of D in test l
lemma pl_scale {l} (_hl:TestF l) (a:ℝ) :
    pl (fun t=>a*l t)=fun t=>a*pl l t := by
  have h : prim (fun t=>a*l t)=fun t=>a*prim l t := by
    funext x; unfold prim; rw [intervalIntegral.integral_const_mul]
  unfold pl; rw [h,ga_mul]; ext; ring
lemma d_cmul (l:ℝ→ℝ) (hl:TestF l) (a:ℝ) :
    deriv (fun t=>a*l t) =fun t=>a*deriv l t :=
  funext fun x=> ((hl.diff x).hasDerivAt.const_mul a).deriv
lemma fl_s {l} (hl:TestF l) (a:ℝ) :
    fl (fun t=>a*l t)=fun t=>a*fl l t := by
  unfold fl; rw [pl_scale hl]; unfold Nr N
  rw [d_cmul _ (pl_test hl),d_cmul _ (pl_test hl).der]
  ext; ring
lemma D_s (l:ℝ→ℝ) (hl:TestF l) (a:ℝ) (x:MI m) :
    q.DD (fun t=>a*l t) x=a•q.DD l x := by
  unfold DD; rw [fl_s hl,pl_scale hl,show q.FL.eval (fun t=>a*pl l t) =_ from funext
    (fun x=>q.FL.eval_scale (pl_test hl) a x)]
  have he : q.Hmat (fun t=>a*fl l t)=fun t=>a•q.Hmat (fl l) t := by
    funext t; unfold Hmat kerH; rw [d_cmul _ (fl_test hl)]
    simp_rw [mul_smul,integral_smul]
  rw [he,cf_s,cf_s]; module
lemma Hd_sub (l j:ℝ→ℝ) (hl:TestF l) (hj:TestF j) :
    q.Hmat (fun x=>l x-j x)=fun x=> q.Hmat l x-q.Hmat j x := by
  funext x
  have he (z) : q.kerH (fun x=>l x-j x) z x=q.kerH l z x-q.kerH j z x := by
    unfold kerH; rw [drv_sub hl hj,sub_smul]
  unfold Hmat; simp_rw [he]; rw [integral_sub (q.H_left_int hl.der.poly x) (q.H_left_int hj.der.poly x)]
lemma D_sub {l j} (hl:TestF l) (hj:TestF j) (a:MI m) :
    q.DD (fun x=>l x-j x) a=q.DD l a-q.DD j a := by
  unfold DD
  have he : fl (fun x=>l x-j x) = fun x=>fl l x-fl j x := by
    unfold fl; rw [pl_sub hl hj]; unfold Nr; rw [N_sub (pl_test hl) (pl_test hj)]
    funext x; ring
  rw [he,pl_sub hl hj,q.Hd_sub _ _ (fl_test hl) (fl_test hj),cof_subm (q.regH
    (fl_test hl)) (q.regH (fl_test hj))]
  simp_rw [show q.FL.eval (fun x=>_ - _) = _ from (funext fun x=> q.FL.eval_sub (pl_test hl) (pl_test hj) x)]
  rw [cof_subm (q.FL.eval_reg (pl_test hl)) (q.FL.eval_reg (pl_test hj))]; module

lemma D_c1 (a:MI m) :
    q.DD (fun _=>1) a=(2*kMode a) • cof q.RR a := by
  let k := fun _:ℝ=> (1:ℝ)
  let i := fun x:ℝ=>x
  have he : prim k=i := by funext x; unfold prim k i; simp
  have hh : pl k=i := by unfold pl; rw [he,id_ga]; funext x; ring
  have hh' : fl k=fun x=>2*x := by unfold fl; rw [hh]; funext x; unfold i Nr N; simp; ring
  have hp : q.Hmat (fl k)=fun x=> (2:ℝ)•q.Amat x := by
    funext t
    unfold Amat Hmat kerH; rw [hh']
    have he : deriv (fun x:ℝ=>2*x) =fun x=>2 := by ext; simp
    simp_rw [he,deriv_id, one_smul, integral_smul]
  change q.DD k a=_
  unfold DD
  rw [hh,show q.FL.eval i=q.Lmat from funext q.evId,hp,cf_s]
  unfold RR; rw [cof_subm q.a_reg q.l_reg]
  by_cases h:deg a=1
  · rw [kMode,h]; push_cast; module
  rw [q.coL_o h]; module

lemma D_F (h:LayerOK) (a:MI m) :
    q.DD FF a=(2*cc*kMode a) • cof q.RR a+(2*kk)• q.DD qu a := by
  let f := fun _:ℝ=>(1:ℝ)
  have hh : FF=fun x=> cc*f x - (-2*kk)*qu x := by funext x; unfold FF f; ring
  rw [hh,q.D_sub ((TestF.const _).mul (TestF.const _)) ((TestF.const _).mul h.q_test),
    q.D_s f (TestF.const _),q.D_s qu h.q_test,q.D_c1]; module
lemma D_e (h:LayerOK) (a:MI m) (he:Even (deg a)) :
    q.DD qu a=kMode a • cof (q.MB q.FL (fl qu)) a := by
  have hh := h.q_test
  have he' : q.MB q.FL (fl qu)=fun x=> q.Hmat (fl qu) x-q.FL.eval (fl qu) x := by
    funext x; rw [MB,fl_ga hh]; simp [scalar]
  unfold DD
  rw [he',cof_subm (q.regH (fl_test hh)) (q.FL.eval_reg (fl_test hh))]
  have hf := cof_odd_zero _ a he (q.BoEval (fl_odd _ hh h.q_even))
  have hg := cof_odd_zero _ a he (q.BoEval (pl_odd _ hh h.q_even))
  rw [hf,hg]; module
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Eq19
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Budgets on remainder by Hermite degree. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers HMode Profile
variable {m:ℕ} [NeZero m]

lemma sigEQ {q:ProjField m} (h:LayerOK) (a:MI m) :
    2*q.sigterm FF a =
      4*cc*kMode a*Pj q.covMat (cof q.RR a) (cof q.RR a)+
      4*kk*Pj q.covMat (cof q.RR a) (q.DD qu a) := by
  rw [ProjField.sigterm,q.D_F h,p_ladd,pJ_smul_right,pJ_smul_right]
  ring

omit [NeZero m] in
lemma odd_budget (W X Y:Mat m) (hw:0≤W) (hx:X.IsHermitian) (hy:Y.IsHermitian)
    (k:ℝ) (hk:0<k) (hr:k≤1/4) :
    4*cc*k*Pj W X X+4*kk*Pj W X Y-k⁻¹*Pj W Y Y ≤ bb*Pj W X X := by
  have he := pj_positive hw (hy.sub (hx.smul (show IsSelfAdjoint (2*kk*k) from rfl)))
  rw [p_square_diff,pj_sym W Y X] at he
  calc
    _ ≤ (4*cc*k+4*kk^2*k)*Pj W X X := by
      field_simp; nlinarith
    _ = 4*bb*k*Pj W X X := by rw [k_sq]; ring
    _ ≤ _ := by
      have hh := pj_positive hw hx
      have h₁ : 4*bb*k ≤ bb := by unfold bb; linarith
      exact mul_le_mul_of_nonneg_right h₁ hh

lemma bmp_pos : 0<bmp := by unfold bmp bm bb cc eta tmax; norm_num
lemma bm_pos : 0<bm := by unfold bm bb cc eta tmax; norm_num

omit [NeZero m] in
lemma even_budget (W X Y:Mat m) (hw:0≤W) (hx:X.IsHermitian) (hy:Y.IsHermitian)
    (k:ℝ) (hk:0<k) (hr:k≤1/3) :
    4*cc*k*Pj W X X+4*kk*k*Pj W X Y-k*Pj W Y Y ≤ (bb+eta)*Pj W X X+bmp*Pj W Y Y := by
  let a := bb+eta-4*cc*k
  have ha : 0<a := by unfold a bb eta cc; linarith
  let m := 2*kk*k
  have he := pj_positive hw (hx.sub (hy.smul (show IsSelfAdjoint (m/a) from rfl)))
  rw [p_square_diff] at he
  have H : m^2≤a*(bmp+k) := by
    have h₁ : a*(bmp+k)-m^2=(1-3*k)*((bb+eta)*bmp+4*bb/3*k) := by
      unfold a m
      rw [mul_pow,mul_pow,k_sq]
      unfold bmp bm bb cc eta tmax
      ring
    rw [← sub_nonneg,h₁]
    have h := bmp_pos
    have hv : 0≤1-3*k:=by linarith
    exact mul_nonneg hv (by unfold bb eta; positivity)
  have hh : 2*m*Pj W X Y≤ a*Pj W X X + m^2/a*Pj W Y Y := by
    field_simp at he ⊢
    nlinarith
  have ht := mul_le_mul_of_nonneg_right ((div_le_iff₀ ha).mpr (H.trans_eq (mul_comm ..)))
    (pj_positive hw hy)
  unfold a m at *
  linarith

namespace ProjField
variable (q:ProjField m)
omit [NeZero m] in
lemma cov_bound {T:Mat m} (ht:T ∈ specBox m tmin tmax) (he:1+T=q.covMat) :
    q.covMat ≤ scalar m (1+tmax) := by
  rw [← he,scalar, add_smul,one_smul]
  exact add_le_add le_rfl ht.2.2
lemma sig_one_degree (hs:LayerOK) (hh:q.avgA=0)
    {T:Mat m} (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat) (a:MI m) :
    let W := q.covMat
    2*q.sigterm FF a - q.Dterm qu a ≤
      (bb+eta)*CpPair W q.RR q.RR a-eta*CpPair W q.Ro q.Ro a+
      bm*CpPair 1 (q.MB q.FL (fl qu)) (q.MB q.FL (fl qu)) a := by
  intro W
  let X := cof q.RR a
  let Y := q.DD qu a
  let Q := cof (q.MB q.FL (fl qu)) a
  set k := kMode a
  have hk := rho_pos a
  have hw : 0≤W := pos_cov
  have hf := fl_test hs.q_test
  have hx : X.IsHermitian := Cf_sym q.R_reg q.r_sym a
  have hy : Y.IsHermitian := q.DD_sym hs.q_test a
  have hQ : Q.IsHermitian := Cf_sym (q.mb_reg q.FL hf) (fun x=> q.P_mb_sym hf x) a
  rw [sigEQ hs]
  unfold CpPair Dterm
  rw [← rho_inv]
  have hz := pj_positive (show 0 ≤ (1:Mat m) from (Matrix.PosSemidef.one).nonneg) hQ
  change 4*cc*k*Pj W X X+4*kk*Pj W X Y-k⁻¹*Pj W Y Y ≤
    (bb+eta)*Pj W X X-eta*Pj W (cof q.Ro a) (cof q.Ro a)+bm*Pj 1 Q Q
  rw [q.coRo]
  by_cases h:deg a<2
  · have he : X=0 := q.bal_cf hh a h
    have hu : cof q.RR a=0 := he
    rw [he,hu]
    have h₀ (B:Mat m) : Pj W 0 B=0 := by simp [Pj,jprod,trN]
    simp_rw [ite_self,h₀,mul_zero,add_zero]
    have hy' := pj_positive hw hy
    have hb := bm_pos; have hi : 0 ≤ k⁻¹ := by exact (inv_pos.mpr hk).le
    nlinarith
  have hh : k≤1/3 := by
    unfold k kMode
    rw [← one_div, div_le_iff₀ (by positivity)]
    have hi : 2 ≤ deg a := by omega
    have h₂ : (2:ℝ) ≤ deg a := by exact_mod_cast hi
    linarith
  split_ifs with ha
  · have hu : Y=k• Q := q.D_e hs a ha
    rw [hu,pJ_smul_right,pJ_smul_right,pJ_smul_left,show Pj W 0 0=0 from by simp [Pj,jprod,trN] ]
    have hb := even_budget W X Q hw hx hQ k hk hh
    have hl := p_le_p (q.cov_bound ht he) hQ
    have hl' : Pj (scalar m (1+tmax)) Q Q = (1+tmax)*Pj 1 Q Q := by
      simp only [scalar,Pj,smul_mul_assoc,trN_smul]
    rw [hl'] at hl
    have heq : bmp*(1+tmax)=bm := by unfold bmp tmax; field_simp
    have hi := mul_le_mul_of_nonneg_left hl bmp_pos.le
    have hu : k⁻¹*(k*(k*Pj W Q Q))=k*Pj W Q Q := by field_simp
    rw [hu]
    rw [← mul_assoc,heq] at hi
    linarith
  change _≤ (bb+eta)*Pj W X X-eta*Pj W X X+ _
  have h' : 3≤deg a := by
    obtain ⟨n,hn⟩ := Nat.not_even_iff_odd.mp ha
    omega
  have hx' : k ≤ 1/4 := by
    unfold k kMode
    rw [← one_div, div_le_iff₀ (by positivity)]
    have h : (3:ℝ)≤deg a := by exact_mod_cast h'
    linarith
  have h := odd_budget W X Y hw hx hy k hk hx'
  linarith [mul_nonneg bm_pos.le hz]

lemma degree19 (hs:LayerOK) (hh:q.avgA=0)
    {T:Mat m} (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat) :
    q.sigma FF-q.DVec ≤
      (bb+eta)*Pt q.covMat q.RR q.RR-eta*Pt q.covMat q.Ro q.Ro +
      bm*Pt 1 (q.MB q.FL (fl qu)) (q.MB q.FL (fl qu)) := by
  let W := q.covMat
  have hu := (pt_sum (B:=W) q.R_reg q.R_reg).mul_left (bb+eta)
  have hv := (pt_sum (B:=W) q.Ro_reg q.Ro_reg).mul_left eta
  have hp := q.mb_reg q.FL (fl_test hs.q_test)
  have hx := ((hu.sub hv).add ((pt_sum (B:=1) hp hp).mul_left bm))
  have h := ((q.sig_split hs.f_test).mul_left 2).sub (q.H_K_split hs.q_test)
  have hb := hasSum_le (fun a=> q.sig_one_degree hs hh ht he a) h hx
  have hi := (q.sig_split hs.f_test).tsum_eq
  have hj := (q.H_K_split hs.q_test).tsum_eq
  unfold sigma DVec Dnorm
  rw [hi,hj]
  have hc := q.D_pos hs.c_test; have hd := q.D_pos hs.s_test
  unfold Dnorm at hc hd
  linarith

lemma NTpos19 (hs:LayerOK) :
    Pt 1 (q.MB q.FL (fl qu)) (q.MB q.FL (fl qu)) ≤
      2*q.LLw q.FL 1 (fun u=>N2 qu u.1*N2 qu u.2) := by
  have h := hs.q_test; have hp := fl_test h; let f := fl qu
  have ht : 0≤q.Nt 1 f f := by
    apply integral_nonneg; intro x; apply integral_nonneg; intro u
    dsimp only [nTK,f,Pi.zero_apply]; rw [fl_d h,one_mul]
    exact mul_nonneg (mul_nonneg (hs.sq_p _).le (hs.sq_p _).le) (q.edge.nt_pos ..)
  rw [q.eq15 _ _ hp,← q.Le_id q.FL 1 hp hp,fl_d h]
  linarith
end ProjField
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
lemma bjdiag (b:Fin m→ℝ) (A C:Mat m) :
    trN (A*jprod C (diagonal b)) =
      mats (fun i=>∑ j,A i j*C j i*((b i+b j)/2)) := by
  rw [trace_pair]
  unfold jprod
  congr 1; ext i
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply,Matrix.add_apply, Matrix.mul_diagonal,Matrix.diagonal_mul,smul_eq_mul]
  ring
lemma bjdiag' (b:Fin m→ℝ) (A C:Mat m) (ha:A.IsHermitian) (hc:C.IsHermitian) :
    trN (A*jprod C (diagonal b)) =
      mats (fun i=>∑ j,C i j*A j i*((b i+b j)/2)) := by
  rw [bjdiag]; congr 1
  ext i; apply Finset.sum_congr rfl
  intro j _; rw [symm_entry ha,symm_entry hc]; ring
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

lemma LL_Bw (x z) {f:Plane→ℝ} (hf:Bwt f) :
    q.lk B 1 f z x=q.bmZ B (bAv f) z x := by
  unfold lk bmZ
  congr 2
  funext u
  exact hf.bar_eq u

lemma pairing_layer (x z) {f:Plane→ℝ} (hf:Bwt f) (ht:T.IsHermitian) :
    let b:=q.BL B x z
    let u:=B.Fr x
    let t:=u.loc T
    q.lk B T f z x =
      trN (b.S*jprod t (diagonal (fun i=> bAv f (z,b.x i)))) +
        mats (fun i=>∑ j,b.E i j*t j i*kz f (b.x i) (b.x j) z) := by
  intro b u t
  rw [bjdiag,lk,← u.pjL,← q.BLe,B.bmat_loc,Pj,bjdiag']
  · rw [← mats_add]
    congr 1; ext i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    change b.E i j*t j i*((bInt f (z,b.x i)+bInt f (z,b.x j))/2)=_
    unfold kz
    have he : b.S i j=rcoef (b.x i) (b.x j) z*b.E i j := rfl
    rw [he,hf.bar_eq,hf.bar_eq]
    dsimp only []; ring
  · exact u.HL ht
  exact b.Her
lemma bm_add (x z) (f g:Plane→ℝ) :
    q.bmZ B (fun w=>f w+g w) z x=q.bmZ B f z x+q.bmZ B g z x := by
  simp_rw [bm_trace]; rw [← mats_add]
  congr 1; ext; ring
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Klimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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
lemma mats_int (f:ℝ→Fin m→Fin m→ℝ) (hi:∀ i j,Integrable (fun x=> f x i j)) :
    Integrable (fun x=>mats (fun i=>∑ j,f x i j)) ∧
    (∫ x,mats (fun i=>∑ j,f x i j))=mats (fun i=>∑ j,∫ x,f x i j) := by
  unfold mats
  have hk (i:Fin m) : Integrable fun x:ℝ=>∑ j,f x i j :=
    integrable_finsetSum _ (fun j _=> hi i j)
  refine ⟨(integrable_finsetSum _ (fun i _=>hk i)).div_const _,?_⟩
  rw [integral_div,integral_finsetSum _ (fun i _=>hk i)]
  congr 1; apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ (fun j _=>hi i j)]
lemma w_Young {a b c:ℝ} (hc:a^2≤b*c) (hb:0≤b) (he:0 ≤ c) {klm:ℝ}
    (h:0<klm) (x y:ℝ) : -(x*y*a) ≤ klm*(x^2*b) + (4*klm)⁻¹*(y^2*c) := by
  by_cases hi:b=0
  · have hv : a=0 := by rw [hi] at hc; nlinarith
    rw [hi,hv]; simp; positivity
  have hk : 0<b := lt_of_le_of_ne hb (Ne.symm hi)
  field_simp
  have HH := sq_nonneg (2*klm*b*x+y*a)
  have hp := mul_le_mul_of_nonneg_left hc (sq_nonneg y)
  nlinarith

omit [NeZero m] in
lemma Frm.loc_s (u:Frm m) (t:ℝ) : u.loc (scalar m t)=scalar m t := by
  simp only [scalar,u.loc_smul,u.loc_one]
omit [NeZero m] in
lemma ctR_box {T:Mat m} (h:T∈specBox m tmin tmax) (u:Frm m) :
    u.loc T∈specBox m tmin tmax := by
  exact ⟨u.HL h.1,by simpa only [u.loc_s] using u.loc_le h.2.1,
    by simpa only [u.loc_s] using u.loc_le h.2.2⟩
omit [NeZero m] in
lemma ck_i {A:Rn m→Mat m} (h:regular A) (T:Mat m) :
    Integrable (fun x=>hsN (cmu (A x) T)) (normal m) := by
  let g := fun x=>cmu (A x) T
  have hg : regular g := ⟨(h.p.mul (PolyBound.const _)).sub ((PolyBound.const _).mul h.p),
    (h.meas.mul aestronglyMeasurable_const).sub (aestronglyMeasurable_const.mul h.meas)⟩
  have hs : regular (fun x=>star (g x)) := by
    refine ⟨hg.p.mono (fun x=>by rw [norm_star]),?_⟩
    exact continuous_star.comp_aestronglyMeasurable hg.meas
  have hl : regular (fun x=>g x*star (g x)) := ⟨hg.p.mul hs.p,hg.meas.mul hs.meas⟩
  have hi := hl.lin (trL)
  have he : (fun x=>hsN (g x)) = fun x=> trL (g x*star (g x)) := by funext x; rw [trL_apply];rfl
  change Integrable (fun x=> hsN (g x)) _
  rw [he]
  exact hi.ig

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)

-- f,b profiles in k; R profile for diagonal gain; bAv f gives matrix subtracted pairing.
-- κ₀ scales both f and U choice exposed
lemma Klimit (ht:T∈specBox m tmin tmax)
    {f w R:Plane→ℝ} (hf:Bwt f) (hw:Bwt w) (hR:Bwt R)
    (hp:∀ v:Plane,0≤w v)
    (c:ℝ) (_hc:0 ≤ c)
    (hmat:∀ (z:ℝ) (l:Fin m→ℝ) (t:Mat m), t∈specBox m tmin tmax →
      Matrix.diagonal (fun i=>R (z,l i)) ≤
        c • jprod t (diagonal (fun i=> bAv f (z,l i))))
    (U:ℝ→ℝ→ℝ→ℝ) (b₀:ℝ)
    (hU:∀ x y,Integrable (U x y) ∧ (∫ z,U x y z)=b₀*(x-y)^2)
    (hu:∀ x y z,z≠x→z≠y→0≤U x y z)
    (hK:∀ x y z,z≠x→z≠y→ (c*kz f x y z)^2≤
      ((|x-z| * w (z,x)+|y-z| * w (z,y))/2)*U x y z)
    {klm:ℝ} (h:0<klm) :
    q.BB B R - c*q.LLw B T f ≤ klm*q.BB B w + b₀/(4*klm)*Hcomm B.A T := by
  have he (x:Rn m) :
      (∫ z,q.bmZ B R z x)- c*(∫ z,q.lk B T f z x) ≤
      klm*(∫ z,q.bmZ B w z x)+ b₀/(4*klm)*hsN (cmu (B.A x) T) := by
    let u := B.Fr x
    let t := u.loc T
    let y := B.ev x
    let g := fun z:ℝ=> mats (fun i:Fin m=>∑ j:Fin m, (t j i)^2* U (y i) (y j) z)
    have hm (i j:Fin m) := hU (y i) (y j)
    have ha := mats_int (fun z i j=> (t j i)^2 * U (y i) (y j) z) (fun i j=>(hm i j).1.const_mul _)
    have hh : (∫ z,g z)=b₀*hsN (cmu (B.A x) T) := by
      unfold g
      rw [ha.2,cmu_eig (B.A x) T u (B.Fr_D x)]
      simp_rw [integral_const_mul]
      rw [← mats_s]
      congr 1; ext i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [(hm _ _).2,symm_entry (u.HL ht.1)]
      change _ = b₀*((y i-y j)^2 * (t j i)^2)
      ring
    have ha' : Integrable g := ha.1
    let m₁ := fun z=>q.bmZ B R z x - c*q.lk B T f z x
    let m₂ := fun z=>klm*q.bmZ B w z x +(4*klm)⁻¹*g z
    have hi₁ := q.bmh B hR x; have hi₂ := q.lk_slice_i B T hf x
    have hi₃ := q.bmh B hw x
    have he : ∀ᵐ z:ℝ, m₁ z≤ m₂ z := by
      have he : ∀ᵐ z:ℝ,∀ i:Fin m,z≠y i :=
        ae_all_iff.2 fun i=>by rw [ae_iff]; simp
      filter_upwards [he] with z hz
      let b := q.BL B x z
      let V := Matrix.diagonal fun i=> bAv f (z,y i)
      have hs := trN_mul_mono (hmat z y t (ctR_box ht u)) b.Spar
      rw [trN_cyclic _ b.S,trN_cyclic _ b.S,traceDiag,mul_smul_comm,trN_smul] at hs
      let J := fun i j:Fin m=> b.E i j*t j i*kz f (y i) (y j) z
      let d := fun i j:Fin m=>(|y i-z| * w (z,y i)+ |y j-z| * w (z,y j))/2
      let k:=fun i=>∑ j,b.E i j^2*d i j
      have hJ (i j) : (-c)*J i j ≤ klm*(b.E i j^2*d i j)+(4*klm)⁻¹*(t j i^2*U (y i) (y j) z) := by
        have hh := hp (z,y i); have hhh := hp (z,y j)
        have ht := hK (y i) (y j) z (hz _) (hz _)
        change _ ≤ d i j*_ at ht
        apply le_trans _ (w_Young ht (by unfold d; positivity) (hu _ _ _ (hz _) (hz _)) h (b.E i j) (t j i))
        unfold J; apply le_of_eq; ring
      have hi :
          (-c)*mats (fun i=> ∑ j,J i j)≤ klm*mats k+(4*klm)⁻¹*g z := by
        unfold g k; rw [mats_s2,mats_s2,mats_s2,← mats_add]
        apply mats_le; intro i; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun j _=>hJ _ _
      have he : mats k≤ q.bmZ B w z x := by
        have ht:= b.tr_blk (fun i=> w (z,y i)) (fun i=> hp _)
        rw [q.bm_trace]
        change _ ≤ mats (fun i=>b.S i i*w (z,y i))
        apply le_trans _ ht
        unfold k d
        apply le_of_eq; congr 1; funext i
        apply Finset.sum_congr rfl; intro j _
        exact mul_comm ..
      unfold m₁ m₂
      rw [q.pairing_layer B T x z hf ht.1,q.bm_trace B x z R]
      change mats (fun i=> b.S i i*R (z,y i))-c*(trN (b.S*jprod t V)+mats (fun i=>∑ j,J i j))
        ≤ klm*q.bmZ B w z x+(4*klm)⁻¹*g z
      change mats _≤ c*trN (b.S*jprod t V) at hs
      linarith [mul_le_mul_of_nonneg_left he h.le]
    have hp := integral_mono_ae (show Integrable m₁ volume from hi₁.sub (hi₂.const_mul c))
      (show Integrable m₂ volume from (hi₃.const_mul _).add (ha'.const_mul _)) he
    unfold m₁ m₂ at hp
    rw [integral_sub hi₁ (hi₂.const_mul _),integral_add (hi₃.const_mul _) (ha'.const_mul _)] at hp
    simp_rw [integral_const_mul,hh] at hp
    rw [div_eq_mul_inv]; linarith
  unfold BB LLw Hcomm
  have hi := q.bmah B hR; have hh := q.Lbar_i B T hf
  have hg := q.bmah B hw
  rw [← integral_const_mul,← integral_const_mul,← integral_const_mul]
  have hx := ck_i B.reg T
  rw [← integral_sub hi (hh.const_mul _), ← integral_add (hg.const_mul _) (hx.const_mul _)]
  exact integral_mono (hi.sub (hh.const_mul _)) ((hg.const_mul _).add (hx.const_mul _)) he
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Tbound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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
lemma uy_nn {x y z:ℝ} : 0 ≤ Uy x y z := by
  unfold Uy U slab
  apply mul_nonneg (abs_nonneg _)
  generalize (z-min x y)/ |y-x|=t
  split_ifs with h h'
  · unfold yk; have hp : 0 < -t := by linarith
    positivity
  · norm_num
  have hh : 0<t-1 := by linarith
  unfold yk; positivity
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
lemma trp : 0<Profile.tr := by norm_num [Profile.tr]
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

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)

section
variable [NeZero m]

lemma BB_add {f g} (hf:Bwt f) (hg:Bwt g) :
    q.BB B (fun x=>f x+g x)=q.BB B f+q.BB B g := by
  unfold BB; simp_rw [q.bm_add B,integral_add (q.bmh B hf _) (q.bmh B hg _)]
  rw [integral_add (q.bmah B hf) (q.bmah B hg)]
lemma BB_sub {f g} (hf:Bwt f) (hg:Bwt g) :
    q.BB B (fun x=>f x-g x)=q.BB B f-q.BB B g := by
  have h := q.BB_add B (hf.sub hg) hg
  rw [show (fun x=>f x-g x+g x)=f from by ext; ring] at h
  linarith
end

lemma BB_bar {f} (hf:Bwt f) : q.LLw B 1 f=q.BB B (bAv f) := by
  unfold LLw BB; simp_rw [q.LL_Bw B _ _ hf]

lemma block_boxJ {T:Mat m} (ht:T∈specBox m tmin tmax) {V:Mat m} (hv:V.IsHermitian) :
    tc•V-(tr/2:ℝ)•(scalar m h₀+h₀⁻¹•(V*V)) ≤ jprod T V := by
  have hd : ‖T-scalar m tc‖ ≤ tr := by
    apply spectrum_norm_box trp.le (ht.1.sub (scalar_sym ..)) _ _
    · have hi : scalar m (-tr)+scalar m tc=scalar m tmin := by unfold scalar; rw [← add_smul]; norm_num [tmin,tr,tc]
      rw [le_sub_iff_add_le,hi]; exact ht.2.1
    have hi : scalar m tr+scalar m tc=scalar m tmax := by unfold scalar; rw [← add_smul]; norm_num [tmax,tr,tc]
    rw [_root_.sub_le_iff_le_add,hi]; exact ht.2.2
  have he : (tc•V-(tr/2:ℝ)•(scalar m h₀+h₀⁻¹•(V*V))).IsHermitian :=
    (hv.smul (by simp [IsSelfAdjoint])).sub (((scalar_sym ..).add
      ((sqPSD hv).posSemidef.1.smul (by simp [IsSelfAdjoint]))).smul (by simp [IsSelfAdjoint]))
  apply (op_order_iff he (jordan_sym ht.1 hv)).mpr
  intro x
  let y := op V x
  have h₁ : ⟪x,op (jprod T V) x⟫=⟪op T x,y⟫ := by
    simp only [jprod,_root_.map_add,_root_.map_mul,_root_.map_smul,
      _root_.smul_apply,_root_.mul_apply_eq_comp,_root_.add_apply,
      real_inner_smul_right,inner_add_right]
    rw [← op_iff_hermitian.mp ht.1,← op_iff_hermitian.mp hv]
    rw [real_inner_comm x]; ring
  let z := op T x-tc • x
  have h₂ : ‖z‖ ≤ tr*‖x‖ := by
    have hz : z=op (T-scalar m tc) x := by
      rw [_root_.map_sub,_root_.sub_apply,op_scalar]
    rw [hz]
    exact ((op (T-scalar m tc)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  have h := neg_le_of_abs_le (abs_real_inner_le_norm z y)
  unfold z at h h₂
  rw [inner_sub_left,real_inner_smul_left] at h
  rw [h₁]
  simp only [_root_.map_sub,_root_.map_smul,_root_.map_add,_root_.map_mul,
    _root_.sub_apply,_root_.smul_apply,_root_.add_apply,
    _root_.mul_apply_eq_comp,inner_sub_right,inner_add_right,real_inner_smul_right]
  rw [show op (1:Mat m) x=x from by rw [_root_.map_one]; rfl,← op_iff_hermitian.mp hv x (op V x),
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  change tc*⟪x,y⟫-tr/2*(h₀*_+h₀⁻¹*‖y‖^2)≤ _
  have heq := mul_le_mul_of_nonneg_right h₂ (norm_nonneg y)
  norm_num [h₀,Profile.tr] at *
  nlinarith [sq_nonneg (‖x‖-2*‖y‖)]

variable [NeZero m]

lemma limitB (ht:T∈specBox m tmin tmax) (hs:LayerOK) :
    -(q.LLw q.FL 1 (fun u=>HH u-P0 u))-q.LLw q.FL T Hh ≤
      (alpha*(Real.log 2 +1/4)/4)*Hcomm q.Lmat T -
        q.BB q.FL (fun u=> ww u-ww0 u) := by
  have hf := bhj hs
  have hm (z:ℝ) (l:Fin m→ℝ) (t:Mat m) (he:t∈specBox m tmin tmax) :
      Matrix.diagonal (fun i=> wwR (z,l i)) ≤ (1:ℝ) •
        jprod t (diagonal (fun i=> bAv Hh (z,l i))) := by
    rw [one_smul]
    let V := diagonal fun i=> bAv Hh (z,l i)
    apply le_trans _ (block_boxJ he (V:=V) (Matrix.isHermitian_diagonal_iff.mpr fun i=>rfl))
    apply le_of_eq
    unfold wwR V scalar
    rw [Matrix.diagonal_mul_diagonal]
    ext i j; by_cases h:i=j
    · subst j; simp; ring
    simp [h]
  have h := q.Klimit q.FL T ht hf (w0t hs) (Rwt hs) (fun _=>(wpos hs _).2)
    1 zero_le_one hm (fun x y z=>alpha*Uy x y z) (alpha*(Real.log 2+1/4))
    (fun x y=> by
      have h:= Uy_area x y
      refine ⟨h.1.const_mul _,?_⟩; rw [integral_const_mul,h.2]; ring)
    (fun _ _ _ _ _=>mul_nonneg alpha_p.le uy_nn)
    (fun x y z hx hy=> by
      rw [one_mul]; have h := (pairEst Hh hf hx hy).1
      unfold ww0
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      unfold Om; field_simp [alpha]) (klm:=(1:ℝ)) zero_lt_one
  rw [q.BB_bar q.FL ((ProjField.H_ok hs).sub (P0_wt hs)), q.BB_sub q.FL (wwt hs) (w0t hs)]
  unfold ww; rw [q.BB_add q.FL (((H_ok hs).sub (P0_wt hs)).bar) (Rwt hs)]
  change q.BB _ _-_≤ 1*q.BB _ _+ _* Hcomm q.Lmat T at h
  linarith
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_FinalR
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.Body.mem_off _root_.OAI.GeneralMahler.Body.pair_mem_cone _root_.OAI.GeneralMahler.hgtL_apply _root_.OAI.GeneralMahler.hgt_add _root_.OAI.GeneralMahler.hgt_smul _root_.OAI.GeneralMahler.horizL_apply _root_.OAI.GeneralMahler.horiz_add _root_.OAI.GeneralMahler.horiz_smul _root_.OAI.GeneralMahler.pair_hgt _root_.OAI.GeneralMahler.pair_horiz _root_.OAI.GeneralMahler.pair_inner _root_.OAI.GeneralMahler.pair_zero
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
lemma hsN_mul_bdd (T V:Mat m) (ht:T.IsHermitian) (hv:V.IsHermitian)
    (c:ℝ) (he:‖V‖ ≤ c) : hsN (T*V) ≤ c^2 * trN (T*T) := by
  have hi : 0 ≤ c := (norm_nonneg _).trans he
  have hh : V*V ≤ scalar m (c^2) := by
    apply (op_order_iff (sqPSD hv).posSemidef.1 (scalar_sym ..)).mpr; intro x
    rw [_root_.map_mul,_root_.mul_apply_eq_comp,← op_iff_hermitian.mp hv,
      real_inner_self_eq_norm_sq, op_scalar,real_inner_smul_right,real_inner_self_eq_norm_sq]
    rw [← mul_pow]
    have he' := ((op V).le_opNorm x).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
    gcongr
  have h := trN_mul_mono hh (sqPSD ht)
  unfold hsN
  rw [star_mul,(show star T=T from ht),(show star V=V from hv)]
  calc
    _ = trN ((V*V)*(T*T)) := by
      rw [mul_assoc,trN_cyclic T]
      simp only [mul_assoc]
    _ ≤ _ := h
    _ = _ := by simp only [scalar,smul_mul_assoc,one_mul,trN_smul]

-- logarithm bound by derivative sign
lemma log_low (x:ℝ) (hx:tmin≤x):
    x- Real.log (1+x) ≤ x^2/(2*(1+tmin)) := by
  have hp : 0<1+tmin := by norm_num [tmin]
  let f := fun x:ℝ=> x-Real.log (1+x)-x^2/(2*(1+tmin))
  have hd (y:ℝ) (hy:tmin≤y) :
      HasDerivAt f (y*(tmin-y)/((1+tmin)*(1+y))) y := by
    have hi : 0<1+y := by linarith
    convert (((hasDerivAt_id' y).sub (((hasDerivAt_id' y).const_add 1).log hi.ne')).sub
      (((hasDerivAt_id' y).pow 2).div_const (2*(1+tmin)))) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (norm_num; field_simp; ring)
  have ht : tmin≤0 := by norm_num [tmin]
  have he : f 0=0 := by simp [f]
  suffices h:f x≤f 0 by rw [he] at h; exact sub_nonpos.mp h
  rcases le_total x 0 with hr|h
  · have h (y:ℝ) (hy:y∈Icc tmin 0) := hd y hy.1
    apply monotoneOn_of_deriv_nonneg (convex_Icc tmin 0)
      (fun x hx => (h x hx).continuousAt.continuousWithinAt) _ _ (show x∈Icc tmin 0 from ⟨hx,hr⟩)
      (show 0∈Icc tmin 0 from ⟨ht,le_rfl⟩)
    all_goals first | assumption | skip
    all_goals intro y hy; have hv : y∈Icc tmin 0 := interior_subset hy
    · exact (h y hv).differentiableAt.differentiableWithinAt
    rw [(h _ hv).deriv]
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos hv.2 (sub_nonpos.mpr hv.1)) (by
      have hh : 0 < 1+y := by linarith [hv.1]
      positivity)
  have ih (y:ℝ) (hy:y∈Ici 0) := hd y (ht.trans hy)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun y hy=>(ih y hy).continuousAt.continuousWithinAt) _ _ (show (0:ℝ)∈Ici 0 from mem_Ici.mpr le_rfl) h h
  all_goals intro y hy; have hv : y∈Ici 0 := interior_subset hy
  · exact (ih y hv).differentiableAt.differentiableWithinAt
  rw [(ih y hv).deriv]; change 0≤y at hv
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hv (by linarith)) (by positivity)
lemma logSigma {T:Mat m} (h:T∈specBox m tmin tmax):
    trN T-logD (1+T) ≤ trN (T*T)/(2*(1+tmin)) := by
  have he := form_posDef (by norm_num) (add_cov_box h)
  rw [← trN_logD_eq he]
  let u:= Frm.eu h.1
  let l := u.eig T
  let A := diagonal l
  have ha : u.loc T=A := Frm.eu_d h.1
  have h₁ : u.loc (1+T)=diagonal (fun i=>1+l i) := by
    rw [Frm.loc_add,Frm.loc_one,ha]; unfold A; ext i j
    by_cases ht:i=j
    · subst j; simp
    simp [ht]
  have hd : u.Dgn (1+T) := by rw [Frm.Dgn,Frm.eig,h₁,Matrix.diag_diagonal]
  rw [← Frm.trNL u T,← Frm.trNL u (cfc Real.log _),← Frm.trNL u (T*T), Frm.loc_cfc
    _ he.1 hd, Frm.eig, h₁,Matrix.diag_diagonal,Frm.loc_mul,ha]
  unfold A trN trace
  simp only [Matrix.diagonal_mul_diagonal,Matrix.diag_diagonal,← sub_div,
    ← Finset.sum_sub_distrib]
  have hp (i:Fin m): tmin≤l i := by
    apply (spectrum_order T h.1 (l:=tmin) (r:=tmax)).1.mp h.2.1
    rw [h.1.spectrum_real_eq_range_eigenvalues]; unfold l u; rw [Frm.eu_eig]; exact ⟨_,rfl⟩
  rw [div_right_comm]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (g:=fun i=> l i^2/(2*(1+tmin))) (f:=fun i=>l i-Real.log (1+l i))
    (fun i _=> log_low (l i) (hp i))
  rw [← Finset.sum_div] at hh
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa [pow_two] using hh

namespace ProjField
variable [NeZero m] (q:ProjField m)
lemma residual_odd (T:Mat m) (hh:q.avgA=0) :
    Pt T q.RR (q.FL.eval (deriv v)) =
      Pt T q.Ro (q.FL.eval (fun x=>deriv v x-x)) := by
  let f := fun x:ℝ=>deriv v x-x
  let g := deriv v
  let W := q.FL
  have hg := v_test.der
  have hf := hg.sub TestF.id
  have he : W.eval f = fun x=> W.eval g x-q.Lmat x := by ext x; rw [W.eval_sub hg TestF.id,q.evId]
  have ha : HasSum (CpPair T q.RR (W.eval g)) _ := pt_sum q.R_reg (W.eval_reg hg)
  have hb := pt_sum (B:=T) q.Ro_reg (W.eval_reg hf)
  apply HasSum.unique ha
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  unfold CpPair; rw [q.coRo,he,
    cof_subm (W.eval_reg hg) q.l_reg]
  split_ifs with ht
  · have hi := cof_odd_zero _ a ht (q.BoEval (map_deriv_even v_test Veven))
    rw [show cof (W.eval g) a=0 from hi]
    simp [Pj,jprod,trN]
  by_cases hx:deg a=1
  · rw [q.bal_cf hh a (by omega)]; simp [Pj,jprod,trN]
  rw [q.coL_o hx,sub_zero]

lemma RoH (x) : (q.Ro x).IsHermitian :=
  ((q.r_sym x).sub (q.r_sym (-x))).smul (by simp [IsSelfAdjoint])
lemma end_cost (T:Mat m) (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat)
    (hs:LayerOK) (h:q.avgA=0) :
    -eta*Pt q.covMat q.Ro q.Ro -Pt T q.RR (q.FL.eval (deriv v)) + (trN T-logD q.covMat) ≤
      18/10*trN (T*T) := by
  let b:ℝ:=319/1000
  let f := fun x=>deriv v x-x
  let g := q.FL.eval f
  let d:= eta*(1+tmin)
  have hf := q.FL.eval_reg (v_test.der.sub TestF.id)
  have hd : 0<d := by norm_num [d,eta,tmin]
  have hh(x) :
      -eta*Pj q.covMat (q.Ro x) (q.Ro x)-Pj T (q.Ro x) (g x) ≤
        (4*d)⁻¹*b^2 * trN (T*T) := by
    let V := g x
    let A := q.Ro x
    have hv : V.IsHermitian := cfc_herm ..
    have hA:= q.RoH x
    have ht' := ht.1
    have hi : ‖V‖≤ b := by
      have hi : IsSelfAdjoint (q.FL.A x):=q.FL.sym x
      apply norm_cfc_le (show 0≤b by norm_num [b])
      exact fun x _=> hs.v_bound x
    have hz : Pj T A V=ipN A (T*V) := by
      unfold ipN; rw [pj_cyc3 ht' hA hv,star_mul,show star V=_ from hv, show star T=_ from ht',mul_assoc]
    have hu : scalar m (1+tmin)≤q.covMat := by rw [← he,scalar, add_smul,one_smul]; exact add_le_add le_rfl ht.2.1
    have he := p_le_p hu hA
    have he' : Pj (scalar m (1+tmin)) A A=(1+tmin)*hsN A := by
      rw [Pj,j_same,scalar,smul_mul_assoc,one_mul,trN_smul,hsN,show star A=A from hA]
    rw [he'] at he
    have hp := hsN_mul_bdd T V ht' hv b hi
    change -eta*_ -Pj T A V ≤ _
    rw [hz]; have hh := young_H A (T*V) hd
    unfold d eta tmin at *; norm_num at *; linarith
  have HP := q.Ro_reg
  have hi := integral_mono (μ:=normal m)
    (show Integrable (fun x=> -eta*Pj q.covMat (q.Ro x) (q.Ro x)-Pj T (q.Ro x) (g x)) (normal m) from
      (((pj_poly_part HP _).const_mul _).sub (by
        simp_rw [← pJ_eq]; exact proj_int _ HP hf))) (integrable_const _) hh
  rw [integral_sub,integral_const_mul] at hi
  · rw [q.residual_odd T h,← he]
    have hv := logSigma ht
    have hq := (trN_mono (sqPSD ht.1))
    simp only [trN,trace_zero,zero_div] at hq
    simp only [integral_const,probReal_univ,one_smul] at hi
    change -eta*Pt q.covMat _ _-Pt T q.Ro g≤_ at hi
    rw [he] at *
    unfold b d eta tmin at *; norm_num at *
    change 0 ≤ trN (T*T) at hq; unfold g f at hi; linarith
  · exact (pj_poly_part HP _).const_mul _
  simp_rw [← pJ_eq]; exact proj_int _ HP hf
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Eq23
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §05 reduction to matrix functionals on linear field. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (T:Mat m)

lemma P0_layer (h:LayerOK) :
    q.LLw q.FL 1 P0 =
      (2*ap+2*e₀*(2*tr)^2)*q.LLw q.FL 1 (fun _=>1) +
      (2*bm)*q.LLw q.FL 1 (fun u=> N2 qu u.1*N2 qu u.2) := by
  let g := fun u:Plane=> N2 qu u.1*N2 qu u.2
  let K := (2*ap+2*e₀*(2*tr)^2)
  have H : P0=fun x=> (K*1)+(2*bm)*g x := by funext x; unfold K P0 g; ring
  rw [H, q.Lbar_add q.FL 1 (Bwt.const _) ((Bwt.const _).mul
    ((Bwt.fst (N2_test h.q_test)).mul (Bwt.snd (N2_test h.q_test))))]
  rw [q.Lbar_scale,q.Lbar_scale]

lemma H0_layer (h:LayerOK) :
    q.LLw q.FL T (fun u=> HH u+deriv (deriv v) u.2)=2*kar*q.LLw q.FL T (fun _=>1)+
      q.LLw q.FL T Hh := by
  have H : (fun u:Plane=>HH u+deriv (deriv v) u.2)=fun u=>2*kar*1+Hh u :=
    by funext x; unfold Hh; ring
  rw [H,q.Lbar_add q.FL T (Bwt.const _) (bhj h)]
  rw [show q.LLw q.FL T (fun _=>2*kar*1)=2*kar*q.LLw q.FL T (fun _=>1) from
    q.Lbar_scale _ _ (fun _=>1) _]

theorem budget_oai (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat)
    (hs:LayerOK) (hh:q.avgA=0) :
    q.scoreE T ≤ q.DelP T-q.JVec q.covMat+(80/100)*Hcomm q.Lmat T+
      (18/10)*trN (T*T)-q.BB q.FL (fun u=> ww u-ww0 u) := by
  have h := q.entropy_decomp he hs
  have h₁ := q.degree19 hs hh ht he
  have h₂ := q.NTpos19 hs
  have hu := q.end_cost T ht he hs hh
  have hv := q.reserve T ht he hh
  have hx := q.limitB T ht hs
  rw [q.Lbar_sub q.FL 1 (H_ok hs) (P0_wt hs),q.P0_layer hs] at hx
  rw [q.H0_layer T hs] at h
  have hsum : e₀+alpha*(Real.log 2+1/4)/4 ≤ 80/100 := by
    unfold e₀ alpha; linarith [Real.log_two_lt_d9]
  have he' : 0 ≤ Hcomm q.Lmat T := integral_nonneg fun _=>hsN_pos _
  have he := mul_le_mul_of_nonneg_left h₂ GeneralMahler.bm_pos.le
  unfold scoreE
  linarith [mul_le_mul_of_nonneg_right hsum he']
end ProjField
end GeneralMahler

end

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.ProjField.budget_oai := @OAI.GeneralMahler.ProjField.budget_oai

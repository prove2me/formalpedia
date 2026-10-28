-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_sectionLength_corrected
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:46:56.720597+00:00
-- url     : https://prove2.me/submissions/381a77fc-984c-45de-bbf1-d43eebe08ead

import Mathlib
import Definitions.Def_OAIQ079A001
import Definitions.Def_OAIQ079A002

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma rho_spec {k : ℝ} (hk : 0 ≤ k) :
    0 ≤ rho k ∧ rho k < 1 ∧ (rho k) ^ 2 = Real.pi * k ^ 2 * (1 - rho k) := by
  let x := Real.sqrt Real.pi * k
  let z := Real.sqrt (1 + (Real.pi / 4) * k ^ 2)
  have hx : 0 ≤ x := by positivity
  have hx2 : x ^ 2 = Real.pi * k ^ 2 := by
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
  have hz : 0 ≤ z := by positivity
  have hz2 : z ^ 2 = 1 + x ^ 2 / 4 := by
    dsimp [z]
    rw [Real.sq_sqrt (by positivity), hx2]
    ring
  have hzx : x / 2 < z := by nlinarith
  have heq : rho k = x * z - x ^ 2 / 2 := by
    dsimp [rho, x, z]
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
    ring
  have hr : 0 ≤ rho k := by rw [heq]; nlinarith
  have hs : (rho k) ^ 2 = Real.pi * k ^ 2 * (1 - rho k) := by
    rw [heq, ← hx2]
    linear_combination x ^ 2 * hz2
  refine ⟨hr, ?_, hs⟩
  by_contra! hn
  have hm := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ Real.pi * k ^ 2) (by linarith : 1 - rho k ≤ 0)
  nlinarith

lemma rho_zero : rho 0 = 0 := by simp [rho]

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

lemma rhoRoot_pos (k : ℝ) : 0 < rhoRoot k := by unfold rhoRoot; positivity
lemma rhoRoot_sq (k : ℝ) : rhoRoot k ^ 2 = Real.pi * k ^ 2 + 4 := by
  exact Real.sq_sqrt (by positivity)
lemma rhoDen_pos (k : ℝ) : 0 < rhoDen k := by
  have hs := rhoRoot_pos k
  have hs2 := rhoRoot_sq k
  have ha : (Real.sqrt Real.pi * k) ^ 2 = Real.pi * k ^ 2 := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
  by_contra! hn
  change rhoRoot k + Real.sqrt Real.pi * k ≤ 0 at hn
  have hk : 0 ≤ -(Real.sqrt Real.pi * k) := by linarith
  have hsq := (sq_le_sq₀ hs.le hk).2 (show rhoRoot k ≤ -(Real.sqrt Real.pi * k) by linarith)
  rw [neg_sq, ha, hs2] at hsq
  linarith

end CubicTorus.Scalar
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar
open Set MeasureTheory Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

lemma rho_rational (k : ℝ) : rho k = 2 * Real.sqrt Real.pi * k / rhoDen k := by
  have hs : rhoRoot k = 2 * Real.sqrt (1 + Real.pi * k ^ 2 / 4) := by
    have h1 := rhoRoot_sq k
    have h2 := Real.sq_sqrt (show 0 ≤ 1 + Real.pi * k ^ 2 / 4 by positivity)
    have h3 := rhoRoot_pos k
    have h4 := Real.sqrt_nonneg (1 + Real.pi * k ^ 2 / 4)
    nlinarith
  have ha := Real.sq_sqrt Real.pi_pos.le
  have hd := ne_of_gt (rhoDen_pos k)
  apply (eq_div_iff hd).2
  unfold rho rhoDen
  rw [hs, show Real.pi / 4 * k ^ 2 = Real.pi * k ^ 2 / 4 by ring]
  have hz := Real.sq_sqrt (show 0 ≤ 1 + Real.pi * k ^ 2 / 4 by positivity)
  linear_combination Real.sqrt Real.pi * k * 2 * hz +
    k ^ 2 * Real.sqrt (1 + Real.pi * k ^ 2 / 4) * ha

lemma hasDerivAt_rhoRoot (k : ℝ) :
    HasDerivAt rhoRoot (Real.pi * k / rhoRoot k) k := by
  convert ((((hasDerivAt_id k).pow 2).const_mul Real.pi).add_const 4).sqrt
    (by positivity : Real.pi * k ^ 2 + 4 ≠ 0) using 1 <;> try rfl
  dsimp [rhoRoot]
  ring

lemma hasDerivAt_rho (k : ℝ) : HasDerivAt rho (rhoSlope k) k := by
  have heq : rho = fun k ↦ 2 * Real.sqrt Real.pi * k / rhoDen k := funext rho_rational
  rw [heq]
  have hh := ((hasDerivAt_id k).const_mul (2 * Real.sqrt Real.pi)).div
    ((hasDerivAt_rhoRoot k).add ((hasDerivAt_id k).const_mul (Real.sqrt Real.pi)))
    (ne_of_gt (rhoDen_pos k))
  convert hh using 1 <;> try rfl
  dsimp [rhoSlope, rhoDen]
  have hs := ne_of_gt (rhoRoot_pos k)
  have hd : rhoRoot k + Real.sqrt Real.pi * k ≠ 0 := ne_of_gt (rhoDen_pos k)
  field_simp
  linear_combination -2 * rhoRoot_sq k

lemma continuous_rho : Continuous rho :=
  continuous_iff_continuousAt.2 (fun k ↦ (hasDerivAt_rho k).continuousAt)

lemma contDiff_rho {n : WithTop ℕ∞} : ContDiff ℝ n rho := by
  unfold rho
  have hs : ContDiff ℝ n (fun k : ℝ ↦ Real.sqrt (1 + Real.pi / 4 * k ^ 2)) :=
    (by fun_prop : ContDiff ℝ n (fun k : ℝ ↦ 1 + Real.pi / 4 * k ^ 2)).sqrt
      (fun k ↦ by positivity)
  exact ((contDiff_const.mul contDiff_id).mul hs).sub
    (contDiff_const.mul (contDiff_id.pow 2))

lemma antitoneOn_rhoSlope : AntitoneOn rhoSlope (Ici 0) := by
  intro k hk K hK hkK
  change 0 ≤ k at hk
  change 0 ≤ K at hK
  have hroot : rhoRoot k ≤ rhoRoot K := Real.sqrt_le_sqrt
    (add_le_add (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hk hK).2 hkK) Real.pi_pos.le) le_rfl)
  have hden : rhoDen k ≤ rhoDen K := add_le_add hroot
    (mul_le_mul_of_nonneg_left hkK (Real.sqrt_nonneg _))
  have hprod : rhoRoot k * rhoDen k ^ 2 ≤ rhoRoot K * rhoDen K ^ 2 :=
    mul_le_mul hroot (pow_le_pow_left₀ (rhoDen_pos k).le hden 2)
      (sq_nonneg _) (rhoRoot_pos K).le
  exact div_le_div_of_nonneg_left (by positivity) (mul_pos (rhoRoot_pos k) (sq_pos_of_pos (rhoDen_pos k))) hprod

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

lemma deriv_rho_eq : deriv rho = rhoSlope := funext (fun k ↦ (hasDerivAt_rho k).deriv)

lemma concaveOn_rho : ConcaveOn ℝ (Ici 0) rho := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) continuous_rho.continuousOn
    (fun k _ ↦ (hasDerivAt_rho k).differentiableAt.differentiableWithinAt)
  rw [deriv_rho_eq]
  exact antitoneOn_rhoSlope.mono interior_subset

lemma mul_rhoSlope_le {k : ℝ} (hk : 0 ≤ k) : k * rhoSlope k ≤ rho k := by
  rcases eq_or_lt_of_le hk with hzero | hpos
  · rw [← hzero, rho_zero, zero_mul]
  · have hs := concaveOn_rho.deriv_le_slope (show 0 ∈ Ici (0 : ℝ) by simp)
      hk hpos (hasDerivAt_rho k).differentiableAt
    rw [slope_def_field, rho_zero, sub_zero, sub_zero, deriv_rho_eq] at hs
    simpa only [mul_comm] using (le_div_iff₀ hpos).1 hs

lemma second_deriv_rho_nonpos {k : ℝ} (hk : 0 < k) : deriv (deriv rho) k ≤ 0 := by
  rw [deriv_rho_eq]
  have hh := antitoneOn_rhoSlope.derivWithin_nonpos (x := k)
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hk)] at hh
  exact hh

lemma hasDerivAt_divParam (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    HasDerivAt (fun h ↦ X / h) (-X / h ^ 2) h := by
  convert (hasDerivAt_const h X).div (hasDerivAt_id h) hh using 1 <;> try rfl
  simp

lemma hasDerivAt_divParamSlope (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    HasDerivAt (fun h ↦ -X / h ^ 2) (2 * X / h ^ 3) h := by
  convert (hasDerivAt_const h (-X)).div ((hasDerivAt_id h).pow 2) (pow_ne_zero 2 hh) using 1 <;> try rfl
  dsimp
  field_simp
  ring

lemma second_deriv_comp_div {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    deriv (deriv (fun H ↦ f (X / H))) h =
      deriv (deriv f) (X / h) * (X / h ^ 2) ^ 2 + deriv f (X / h) * (2 * X / h ^ 3) := by
  have heq : deriv (fun H ↦ f (X / H)) =ᶠ[𝓝 h]
      (fun H ↦ deriv f (X / H) * (-X / H ^ 2)) := by
    filter_upwards [eventually_ne_nhds hh] with H hH
    exact (((hf.contDiffAt.differentiableAt (by norm_num)).hasDerivAt).comp H
      (hasDerivAt_divParam X hH)).deriv
  rw [heq.deriv_eq]
  have hfd : DifferentiableAt ℝ (deriv f) (X / h) :=
    ((hf.contDiffAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hd := ((hfd.hasDerivAt.comp h (hasDerivAt_divParam X hh)).mul
    (hasDerivAt_divParamSlope X hh)).deriv
  convert hd using 1 <;> try rfl
  dsimp only [Function.comp_apply]
  ring

lemma rho_comp_div_second_bound {X h : ℝ} (hX : 0 < X) (hh : 0 < h) :
    deriv (deriv (fun H ↦ rho (X / H))) h ≤ 2 / h ^ 2 := by
  rw [second_deriv_comp_div contDiff_rho X (ne_of_gt hh)]
  have hk := div_pos hX hh
  have hn := mul_nonpos_of_nonpos_of_nonneg (second_deriv_rho_nonpos hk) (sq_nonneg (X / h ^ 2))
  have hb := (mul_rhoSlope_le hk.le).trans (rho_spec hk.le).2.1.le
  have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ 2 / h ^ 2 by positivity)
  rw [deriv_rho_eq] at hn ⊢
  have heq : X / h * rhoSlope (X / h) * (2 / h ^ 2) = rhoSlope (X / h) * (2 * X / h ^ 3) := by
    field_simp
  rw [heq] at hm
  linarith

end CubicTorus.Scalar

namespace CubicTorus.Reduction
open Set Filter
open scoped Topology

lemma second_deriv_nonneg_of_local_min {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra! hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hmin, hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const'] at hz
  rw [hz] at hneg
  exact (lt_irrefl 0) hneg

lemma second_deriv_sub {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y => f y - g y)) x =
      deriv (deriv f) x - deriv (deriv g) x := by
  have heq : deriv (fun y => f y - g y) =ᶠ[𝓝 x]
      (fun y => deriv f y - deriv g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact deriv_sub (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [heq.deriv_eq]
  exact deriv_sub
    ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

lemma jet_comparison {I C F : ℝ → ℝ} {x : ℝ}
    (hs : UpperSupport I C x) (hF : ContDiffAt ℝ 2 F x)
    (hm : IsLocalMin (fun y => I y - F y) x) :
    deriv C x = deriv F x ∧ deriv (deriv F) x ≤ deriv (deriv C) x := by
  have hmc : IsLocalMin (fun y => C y - F y) x := by
    filter_upwards [hm, hs.above] with y hy habove
    change C x - F x ≤ C y - F y
    rw [hs.contact]
    linarith
  have h1 := hmc.deriv_eq_zero
  change deriv (C - F) x = 0 at h1
  rw [deriv_sub (hs.smooth.differentiableAt (by norm_num))
    (hF.differentiableAt (by norm_num))] at h1
  have h2 := second_deriv_nonneg_of_local_min hmc (hs.smooth.continuousAt.sub hF.continuousAt)
  rw [second_deriv_sub hs.smooth hF] at h2
  exact ⟨sub_eq_zero.mp h1, sub_nonneg.mp h2⟩

lemma second_deriv_quadratic (α β γ x : ℝ) :
    deriv (deriv (fun y => α * y ^ 2 + β * y + γ)) x = 2 * α := by
  have hd (y : ℝ) : HasDerivAt (fun z => α * z ^ 2 + β * z + γ) (2 * α * y + β) y := by
    convert! (((hasDerivAt_pow 2 y).const_mul α).add
      ((hasDerivAt_id y).const_mul β)).add_const γ using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hdeq : deriv (fun y => α * y ^ 2 + β * y + γ) = (fun y => 2 * α * y + β) := by
    funext y
    exact (hd y).deriv
  rw [hdeq]
  have hd2 : HasDerivAt (fun y : ℝ => 2 * α * y + β) (2 * α) x := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id x).const_mul (2 * α)).add_const β
  exact hd2.deriv

theorem chord_below_of_upper_support {I : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hI : ContinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ 0) :
    ∀ x ∈ Icc a b, I a + (x - a) * (I b - I a) / (b - a) ≤ I x := by
  intro c hc
  by_contra! hgap
  let m := (I b - I a) / (b - a)
  let L := fun x : ℝ => I a + (x - a) * m
  have hLa : L a = I a := by simp [L]
  have hLb : L b = I b := by
    dsimp [L, m]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hgap' : I c < L c := by simpa [L, m, mul_div_assoc] using hgap
  have hca : a < c := by
    refine lt_of_le_of_ne hc.1 ?_
    intro heq
    subst c
    rw [hLa] at hgap'
    exact (lt_irrefl _ hgap')
  have hcb : c < b := by
    refine lt_of_le_of_ne hc.2 ?_
    intro heq
    subst c
    rw [hLb] at hgap'
    exact (lt_irrefl _ hgap')
  let ε := (L c - I c) / (2 * ((c - a) * (b - c)))
  have hε : 0 < ε := div_pos (sub_pos.mpr hgap')
    (mul_pos (by norm_num) (mul_pos (sub_pos.mpr hca) (sub_pos.mpr hcb)))
  let F := fun x : ℝ => ε * x ^ 2 + (m - ε * (a + b)) * x +
    (I a - a * m + ε * a * b)
  have hF_eq (x : ℝ) : F x = L x + ε * (x - a) * (x - b) := by dsimp [F, L]; ring
  have hFa : F a = I a := by rw [hF_eq, hLa]; ring
  have hFb : F b = I b := by rw [hF_eq, hLb]; ring
  have hFc : I c < F c := by
    have hprod : ε * (c - a) * (b - c) = (L c - I c) / 2 := by
      dsimp [ε]
      field_simp [ne_of_gt (sub_pos.mpr hca), ne_of_gt (sub_pos.mpr hcb)]
    rw [hF_eq]
    nlinarith
  have hF : ContDiff ℝ 2 F := by dsimp [F]; fun_prop
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hab.le) (hI.sub hF.continuous.continuousOn)
  have hneg : I x - F x < 0 := lt_of_le_of_lt (hmin hc) (sub_neg.mpr hFc)
  have hxa : a < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro heq
    subst x
    rw [hFa, sub_self] at hneg
    exact lt_irrefl _ hneg
  have hxb : x < b := by
    refine lt_of_le_of_ne hx.2 ?_
    intro heq
    subst x
    rw [hFb, sub_self] at hneg
    exact lt_irrefl _ hneg
  obtain ⟨C, hC, hC''⟩ := hsupport x ⟨hxa, hxb⟩
  have hj := (jet_comparison hC hF.contDiffAt
    (hmin.isLocalMin (Icc_mem_nhds hxa hxb))).2
  have hF'' : deriv (deriv F) x = 2 * ε := second_deriv_quadratic _ _ _ _
  rw [hF''] at hj
  linarith

end CubicTorus.Reduction

namespace CubicTorus.Reduction
open Set Filter
open scoped Topology

theorem concaveOn_of_upper_support {I : ℝ → ℝ} {a b : ℝ}
    (hI : ContinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ 0) : ConcaveOn ℝ (Icc a b) I := by
  apply concaveOn_of_slope_anti_adjacent (convex_Icc a b)
  intro x y z hx hz hxy hyz
  have hsub : Icc x z ⊆ Icc a b := Icc_subset_Icc hx.1 hz.2
  have hc := chord_below_of_upper_support (hxy.trans hyz) (hI.mono hsub)
    (fun t ht ↦ hsupport t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hz.2⟩) y ⟨hxy.le, hyz.le⟩
  have hdiv : (y - x) * (I z - I x) / (z - x) ≤ I y - I x := by linarith only [hc]
  have hm := (div_le_iff₀ (sub_pos.2 (hxy.trans hyz))).1 hdiv
  apply (div_le_div_iff₀ (sub_pos.2 hyz) (sub_pos.2 hxy)).2
  nlinarith only [hm]

lemma UpperSupport.sub_quadratic {I C : ℝ → ℝ} {x : ℝ}
    (hs : UpperSupport I C x) (K : ℝ) :
    UpperSupport (fun y ↦ I y - K / 2 * y ^ 2) (fun y ↦ C y - K / 2 * y ^ 2) x := by
  refine ⟨hs.smooth.sub (by fun_prop), ?_, ?_⟩
  · rw [hs.contact]
  · filter_upwards [hs.above] with y hy
    exact sub_le_sub_right hy _

lemma second_deriv_half_quadratic (K x : ℝ) :
    deriv (deriv (fun y : ℝ ↦ K / 2 * y ^ 2)) x = K := by
  simp

theorem concaveOn_sub_quadratic_of_support {I : ℝ → ℝ} {a b K : ℝ}
    (hI : ContinuousOn I (Icc a b))
    (hsupport : ∀ x ∈ Ioo a b, ∃ C : ℝ → ℝ,
      UpperSupport I C x ∧ deriv (deriv C) x ≤ K) :
    ConcaveOn ℝ (Icc a b) (fun y ↦ I y - K / 2 * y ^ 2) := by
  apply concaveOn_of_upper_support (hI.sub (by fun_prop))
  intro x hx
  obtain ⟨C, hC, hCK⟩ := hsupport x hx
  refine ⟨_, hC.sub_quadratic K, ?_⟩
  rw [second_deriv_sub hC.smooth (by fun_prop), second_deriv_half_quadratic]
  linarith

end CubicTorus.Reduction

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma continuousOn_sectionLength_h (X : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (sectionLength X) (Icc a b) := by
  have hdiv : ContinuousOn (fun h : ℝ ↦ X / h) (Icc a b) :=
    continuousOn_const.div continuousOn_id (fun h hh ↦ ne_of_gt (ha.trans_le hh.1))
  exact (continuousOn_const.mul (hdiv.pow 2)).inf
    (hdiv.inf (continuous_rho.comp_continuousOn hdiv))

lemma contDiffAt_rho_comp_div (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    ContDiffAt ℝ 2 (fun H ↦ rho (X / H)) h :=
  contDiff_rho.contDiffAt.comp h (contDiffAt_const.div contDiffAt_id hh)

lemma second_deriv_quadratic_div (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    deriv (deriv (fun H ↦ Real.pi * (X / H) ^ 2)) h =
      6 * (Real.pi * (X / h) ^ 2) / h ^ 2 := by
  rw [second_deriv_comp_div (f := fun k : ℝ ↦ Real.pi * k ^ 2) (by fun_prop) X hh]
  have hd : deriv (fun k : ℝ ↦ Real.pi * k ^ 2) (X / h) = 2 * Real.pi * (X / h) := by
    convert ((((hasDerivAt_id (X / h)).pow 2).const_mul Real.pi).deriv) using 1 <;> try rfl
    dsimp
    ring
  have hd2 : deriv (deriv (fun k : ℝ ↦ Real.pi * k ^ 2)) (X / h) = 2 * Real.pi := by
    have := second_deriv_quadratic Real.pi 0 0 (X / h)
    simpa only [zero_mul, add_zero] using this
  rw [hd, hd2]
  ring

lemma second_deriv_linear_div (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    deriv (deriv (fun H ↦ X / H)) h = 2 * (X / h) / h ^ 2 := by
  have heq : deriv (fun H ↦ X / H) =ᶠ[𝓝 h] (fun H ↦ -X / H ^ 2) := by
    filter_upwards [eventually_ne_nhds hh] with H hH
    exact (hasDerivAt_divParam X hH).deriv
  rw [heq.deriv_eq, (hasDerivAt_divParamSlope X hh).deriv]
  ring

lemma sectionLength_upper_support {X h : ℝ} (hX : 0 ≤ X) (hh : 0 < h) :
    ∃ C : ℝ → ℝ, UpperSupport (sectionLength X) C h ∧
      deriv (deriv C) h ≤ 2 / h ^ 2 := by
  rcases hX.eq_or_lt with hX | hX
  · subst X
    refine ⟨fun _ ↦ 0, ⟨by fun_prop, by simp [sectionLength, rho_zero], ?_⟩, ?_⟩
    · exact Filter.Eventually.of_forall (fun H ↦ by simp [sectionLength, rho_zero])
    · norm_num
      positivity
  let k := X / h
  have hk : 0 < k := div_pos hX hh
  have hne : h ≠ 0 := ne_of_gt hh
  by_cases hquad : Real.pi * k ^ 2 ≤ min k (rho k)
  · refine ⟨fun H ↦ Real.pi * (X / H) ^ 2, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact contDiffAt_const.mul ((contDiffAt_const.div contDiffAt_id hne).pow 2)
    · exact (min_eq_left hquad).symm
    · exact Filter.Eventually.of_forall (fun H ↦ min_le_left _ _)
    · rw [second_deriv_quadratic_div X hne]
      have hqk : Real.pi * k ^ 2 ≤ k := hquad.trans (min_le_left _ _)
      have hpk : Real.pi * k ≤ 1 := by
        have : k * (Real.pi * k) ≤ k * 1 := by nlinarith only [hqk]
        exact (mul_le_mul_iff_right₀ hk).1 this
      have hkp : k ≤ 1 / Real.pi := (le_div_iff₀ Real.pi_pos).2 (by nlinarith only [hpk])
      have hb : 6 * (Real.pi * k ^ 2) ≤ 2 := by
        have hp : (6 : ℝ) / Real.pi < 2 := (div_lt_iff₀ Real.pi_pos).2 (by linarith [Real.pi_gt_three])
        have hm := mul_le_mul_of_nonneg_left (hqk.trans hkp) (by norm_num : (0 : ℝ) ≤ 6)
        rw [mul_one_div] at hm
        exact hm.trans hp.le
      exact div_le_div_of_nonneg_right hb (sq_nonneg h)
  · by_cases hlin : k ≤ rho k
    · refine ⟨fun H ↦ X / H, ⟨contDiffAt_const.div contDiffAt_id hne, ?_, ?_⟩, ?_⟩
      · change k = min (Real.pi * k ^ 2) (min k (rho k))
        rw [min_eq_right (le_of_not_ge hquad), min_eq_left hlin]
      · exact Filter.Eventually.of_forall (fun H ↦ (min_le_right _ _).trans (min_le_left _ _))
      · rw [second_deriv_linear_div X hne]
        have hk1 := hlin.trans (rho_spec hk.le).2.1.le
        exact div_le_div_of_nonneg_right (by nlinarith only [hk1]) (sq_nonneg h)
    · refine ⟨fun H ↦ rho (X / H), ⟨contDiffAt_rho_comp_div X hne, ?_, ?_⟩,
        rho_comp_div_second_bound hX hh⟩
      · change rho k = min (Real.pi * k ^ 2) (min k (rho k))
        rw [min_eq_right (le_of_not_ge hquad), min_eq_right (le_of_not_ge hlin)]
      · exact Filter.Eventually.of_forall (fun H ↦ (min_le_right _ _).trans (min_le_right _ _))

theorem concaveOn_sectionLength_corrected_oai {X a b : ℝ} (hX : 0 ≤ X) (ha : 0 < a) :
    ConcaveOn ℝ (Icc a b) (fun h ↦ sectionLength X h - h ^ 2 / a ^ 2) := by
  have hc := concaveOn_sub_quadratic_of_support (a := a) (b := b) (K := 2 / a ^ 2)
    (continuousOn_sectionLength_h X ha) (fun h hh ↦ ?_)
  · convert hc using 1
    all_goals try with_reducible_and_instances rfl
    funext h
    ring
  · obtain ⟨C, hC, hbound⟩ := sectionLength_upper_support hX (ha.trans hh.1)
    refine ⟨C, hC, hbound.trans ?_⟩
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha)
      (pow_le_pow_left₀ ha.le hh.1.le 2)

open MeasureTheory

end CubicTorus.Scalar

end
end
end
end ReusedScalar205
end
end

end OAI
end

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_sectionLength_corrected_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_sectionLength_corrected_oai

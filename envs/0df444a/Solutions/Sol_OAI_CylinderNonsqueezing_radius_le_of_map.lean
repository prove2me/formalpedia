-- Prove2me | solution 1 for OAI.CylinderNonsqueezing.radius_le_of_map
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:31:11.235459+00:00
-- url     : https://prove2.me/submissions/f410295e-595a-4a34-bcf7-084df9549f96

import Mathlib
import Definitions.Def_OAIQWSP000
import Theorems.Thm_AGT_brouwer_fixed_point
import Theorems.Thm_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal

section
-- module Solutions.OAIQW_SymmetricPolar.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_SymmetricPolar.LocalODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u3 u4 u5 u6

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u5} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

noncomputable section

theorem curve_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    EqOn (curve hV h hh x) (fun _ => x) (Icc 0 1) := by
  apply EqOn.symm
  apply curve_unique hV h hh x continuousOn_const
  · intro t _
    simpa only [hx, smul_zero] using (hasDerivWithinAt_const t (Ici t) x)
  · rfl

@[simp] theorem step_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    step hV h hh x = x := by
  have he := curve_of_eq_zero hV h hh x hx (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa using he

end
end SmoothODE

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.SmoothDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u78 u79

section NonsqueezingInline
section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace SmoothDegree
noncomputable section

 theorem exists_zero {E : Type u78} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} (hf : ContDiff ℝ ∞ f)
    {R : ℝ} (hR : 0 < R) (hId : ∀ x, R ≤ ‖x‖ → f x = x) : ∃ x, f x = 0 := by
  -- from the published Brouwer theorem AGT.brouwer_fixed_point: x ↦ x - f x vanishes outside
  -- the ball of radius R, so it maps a large closed ball into itself; a fixed point is a zero of f
  have hc : Continuous (fun x => x - f x) := continuous_id.sub hf.continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn hc.continuousOn
  have hbd (x : E) : ‖x - f x‖ ≤ max M 0 := by
    by_cases hx : ‖x‖ ≤ R
    · exact (hM x (mem_closedBall_zero_iff.mpr hx)).trans (le_max_left _ _)
    · rw [hId x (not_le.mp hx).le, sub_self, norm_zero]
      exact le_max_right _ _
  obtain ⟨x, -, hx⟩ := AGT.brouwer_fixed_point (convex_closedBall (0:E) (max M 0))
    (isCompact_closedBall _ _) (Metric.nonempty_closedBall.mpr (le_max_right _ _))
    (fun x => x - f x) hc.continuousOn (fun x _ => mem_closedBall_zero_iff.mpr (hbd x))
  exact ⟨x, sub_eq_self.mp hx⟩

end
end SmoothDegree

end
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FiniteDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u80 u81 u82 u83

section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace SmoothLinking
noncomputable section
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type u80} {F : Type u81} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem degreeMap_eq_self {η : E × F → E × F} {e : F} (he : ‖e‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ) {z : E × ℝ} (hz : 0 < z.2+ρ)
    (hη : η (z.1, (z.2+ρ) • e) = (z.1, (z.2+ρ) • e)) :
    degreeMap η e ρ z = z := by
  simp only [degreeMap, ite_eq_left hz, hη, norm_smul, he, mul_one,
    Real.norm_eq_abs, sq_abs]
  apply Prod.ext
  · rfl
  change ((z.2+ρ)^2-ρ^2)/(z.2+2*ρ) = z.2
  apply (div_eq_iff (by linarith : z.2+2*ρ ≠ 0)).mpr
  ring

theorem contDiffAt_degreeMap_pos {η : E × F → E × F} (hη : ContDiff ℝ ∞ η)
    (e : F) {ρ : ℝ} (hρ : 0 < ρ) {z : E × ℝ} (hz : 0 < z.2+ρ) :
    ContDiffAt ℝ ∞ (degreeMap η e ρ) z := by
  have hinput : ContDiff ℝ ∞ (fun w : E × ℝ => (w.1, (w.2+ρ) • e)) :=
    contDiff_fst.prodMk ((contDiff_snd.add contDiff_const).smul contDiff_const)
  have hout := hη.comp hinput
  have hn : z.2+2*ρ ≠ 0 := by linarith
  have hd : ContDiffAt ℝ ∞ (fun w : E × ℝ =>
      ((η (w.1, (w.2+ρ) • e)).1, (‖(η (w.1, (w.2+ρ) • e)).2‖^2-ρ^2)/(w.2+2*ρ))) z := by
    exact (contDiff_fst.comp hout).contDiffAt.prodMk
      (((contDiff_norm_sq ℝ).comp (contDiff_snd.comp hout)).contDiffAt.sub contDiffAt_const |>.div
        (contDiffAt_snd.add contDiffAt_const) hn)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const (continuous_snd.add continuous_const)).mem_nhds hz] with w hw
  change 0 < w.2+ρ at hw
  simp only [degreeMap, ite_eq_left hw]

theorem contDiff_degreeMap {η : E × F → E × F} (hη : ContDiff ℝ ∞ η)
    {e : F} (he : ‖e‖ = 1) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hfixed : ∀ (y : E) (s : ℝ), 0 < s → s < ε → η (y, s • e) = (y, s • e)) :
    ContDiff ℝ ∞ (degreeMap η e ρ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : 0 < z.2+ρ
  · exact contDiffAt_degreeMap_pos hη e hρ hz
  have hz' : z.2+ρ < ε := lt_of_le_of_lt (le_of_not_gt hz) hε
  apply (contDiffAt_id : ContDiffAt ℝ ∞ (id : E × ℝ → E × ℝ) z).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt (continuous_snd.add continuous_const) continuous_const).mem_nhds hz'] with w hw
  by_cases hp : 0 < w.2+ρ
  · exact degreeMap_eq_self he hρ hp (hfixed w.1 (w.2+ρ) hp hw)
  · simp only [degreeMap, ite_eq_right hp, id_eq]

omit [NormedSpace ℝ E] in
theorem norm_translate_le (z : E × ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖z‖ ≤ ‖(z.1, z.2+ρ)‖ + ρ := by
  have he : z = (z.1, z.2+ρ) - (0,ρ) := by ext <;> simp
  calc
    ‖z‖ = ‖(z.1, z.2+ρ) - (0,ρ)‖ := congrArg norm he
    _ ≤ ‖(z.1, z.2+ρ)‖+‖((0,ρ) : E × ℝ)‖ := norm_sub_le _ _
    _ = _ := by simp [Prod.norm_def, abs_of_nonneg hρ, hρ]

omit [NormedSpace ℝ E] in
theorem degreeMap_identity_outside {η : E × F → E × F} {e : F} (he : ‖e‖ = 1)
    {ρ R : ℝ} (hρ : 0 < ρ)
    (hfixed : ∀ (y : E) (s : ℝ), 0 < s → R ≤ ‖(y,s)‖ → η (y, s • e) = (y, s • e))
    (z : E × ℝ) (hz : R+ρ ≤ ‖z‖) : degreeMap η e ρ z = z := by
  by_cases hp : 0 < z.2+ρ
  · apply degreeMap_eq_self he hρ hp
    apply hfixed _ _ hp
    have hn := norm_translate_le z hρ.le
    linarith
  · simp only [degreeMap, ite_eq_right hp]

theorem sphere_linking [FiniteDimensional ℝ E]
    {η : E × F → E × F} (hη : ContDiff ℝ ∞ η) {e : F} (he : ‖e‖ = 1)
    {ρ ε R : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hR : ρ < R)
    (hnear : ∀ (y : E) (s : ℝ), 0 < s → s < ε → η (y, s • e) = (y, s • e))
    (hfar : ∀ (y : E) (s : ℝ), 0 < s → R ≤ ‖(y,s)‖ → η (y, s • e) = (y, s • e)) :
    ∃ (y : E) (s : ℝ), 0 < s ∧ ‖(y,s)‖ < R ∧ (η (y, s • e)).1 = 0 ∧ ‖(η (y, s • e)).2‖ = ρ := by
  obtain ⟨z, hz⟩ := SmoothDegree.exists_zero (contDiff_degreeMap hη he hρ hε hnear)
    (show 0 < R+ρ by linarith) (degreeMap_identity_outside he hρ hfar)
  have hp : 0 < z.2+ρ := by
    by_contra h
    have heq : z = 0 := by simpa only [degreeMap, ite_eq_right h] using hz
    simp only [heq, Prod.snd_zero, zero_add] at h
    exact h hρ
  have hfst : (η (z.1, (z.2+ρ) • e)).1 = 0 := by
    simpa only [degreeMap, ite_eq_left hp, Prod.fst_zero, Prod.fst] using congrArg Prod.fst hz
  have hsnd : ‖(η (z.1, (z.2+ρ) • e)).2‖ = ρ := by
    have h := congrArg Prod.snd hz
    simp only [degreeMap, ite_eq_left hp, Prod.snd_zero] at h
    have hd : z.2+2*ρ ≠ 0 := by linarith
    have hsq : ‖(η (z.1, (z.2+ρ) • e)).2‖^2 = ρ^2 :=
      sub_eq_zero.mp ((div_eq_zero_iff).mp h |>.resolve_right hd)
    nlinarith [norm_nonneg (η (z.1, (z.2+ρ) • e)).2]
  refine ⟨z.1, z.2+ρ, hp, ?_, hfst, hsnd⟩
  by_contra! hn
  have hid := hfar z.1 (z.2+ρ) hp hn
  rw [hid] at hfst hsnd
  simp only [norm_smul, he, mul_one, Real.norm_eq_abs,
    abs_of_pos hp] at hfst hsnd
  rw [hfst, hsnd] at hn
  have : ‖((0 : E),ρ)‖ = ρ := by simp [Prod.norm_def, abs_of_pos hρ, hρ.le]
  rw [this] at hn
  exact hR.not_ge hn

end
end SmoothLinking

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace FlowDescent
noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
variable {E : Type u82} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem curve_displacement {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {L : ℝ}
    (hL : ∀ x, ‖V x‖ ≤ L) (x : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖SmoothODE.curve hV h hh x t - x‖ ≤ h*L*t := by
  have hb (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1) :
      ‖h • V (SmoothODE.curve hV h hh x s)‖ ≤ h*L := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (hL _) h0
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (SmoothODE.hasDerivAt_curve hV h hh x ⟨s,hs⟩).hasDerivWithinAt)
    hb (convex_Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) ht
  simpa only [SmoothODE.curve_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] using hm

 theorem curve_energy_deriv {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (x : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => Φ (SmoothODE.curve hV h hh x s))
      (h * fderiv ℝ Φ (SmoothODE.curve hV h hh x t) (V (SmoothODE.curve hV h hh x t))) t := by
  have hd := (hΦ (SmoothODE.curve hV h hh x t)).hasFDerivAt.comp_hasDerivAt t
    (SmoothODE.hasDerivAt_curve hV h hh x ⟨t,ht⟩)
  simpa only [Function.comp_def, map_smul, smul_eq_mul] using hd

 theorem curve_energy_antitone {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0) (x : E) :
    AntitoneOn (fun t => Φ (SmoothODE.curve hV h hh x t)) (Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
    (hΦ.continuous.comp (SmoothODE.continuous_curve hV h hh x)).continuousOn
    (fun t ht => (curve_energy_deriv hV hh hΦ x (interior_subset ht)).hasDerivWithinAt)
  intro t _
  exact mul_nonpos_of_nonneg_of_nonpos h0 (hdec _)

 theorem step_energy_le {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0) (x : E) :
    Φ (SmoothODE.step hV h hh x) ≤ Φ x := by
  simpa only [SmoothODE.curve_one, SmoothODE.curve_zero] using
    (curve_energy_antitone hV hh h0 hΦ hdec x (by simp) (by simp) zero_le_one)

 theorem step_energy_drop {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0) {L M a b : ℝ}
    (hL : ∀ x, ‖V x‖ ≤ L)
    (hrate : ∀ x, ‖x‖ ≤ M → a ≤ Φ x → Φ x ≤ b → fderiv ℝ Φ x (V x) ≤ -1)
    (x : E) (hx : ‖x‖+h*L ≤ M) (hxb : Φ x ≤ b) :
    Φ (SmoothODE.step hV h hh x) ≤ max a (Φ x-h) := by
  by_cases hxa : Φ (SmoothODE.step hV h hh x) ≤ a
  · exact hxa.trans (le_max_left _ _)
  have ha := le_of_lt (lt_of_not_ge hxa)
  have ham := curve_energy_antitone hV hh h0 hΦ hdec x
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      fderiv ℝ Φ (SmoothODE.curve hV h hh x t) (V (SmoothODE.curve hV h hh x t)) ≤ -1 := by
    apply hrate
    · have hdn := curve_displacement hV hh h0 hL x ht
      have hLn : 0 ≤ L := le_trans (norm_nonneg (V x)) (hL x)
      have hn := norm_le_norm_sub_add (SmoothODE.curve hV h hh x t) x
      have htime := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg h0 hLn)
      linarith
    · exact ha.trans (by simpa only [SmoothODE.curve_one] using ham ht (by simp) ht.2)
    · exact (show Φ (SmoothODE.curve hV h hh x t) ≤ Φ x from by
        simpa only [SmoothODE.curve_zero] using ham (by simp) ht ht.1).trans hxb
  have hm : AntitoneOn (fun t => Φ (SmoothODE.curve hV h hh x t)+h*t) (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
      (((hΦ.continuous.comp (SmoothODE.continuous_curve hV h hh x)).add
        (continuous_const.mul continuous_id)).continuousOn)
      (fun t ht => ((curve_energy_deriv hV hh hΦ x (interior_subset ht)).add
        ((hasDerivAt_id t).const_mul h)).hasDerivWithinAt)
    intro t ht
    have := mul_le_mul_of_nonneg_left (hb t (interior_subset ht)) h0
    linarith
  have hend := hm (by simp) (by simp) zero_le_one
  simp only [SmoothODE.curve_one, SmoothODE.curve_zero, mul_one, mul_zero, add_zero] at hend
  exact (by linarith : Φ (SmoothODE.step hV h hh x) ≤ Φ x-h).trans (le_max_right _ _)

end
end FlowDescent

namespace FlowDescent
noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
variable {E : Type u83} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem iterate_norm_le {f : E → E} {D : ℝ} (hD : ∀ x, ‖f x-x‖ ≤ D) (j : ℕ) (x : E) :
    ‖f^[j] x‖ ≤ ‖x‖+j*D := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hn := norm_le_norm_sub_add (f (f^[j] x)) (f^[j] x)
    have hd := hD (f^[j] x)
    push_cast
    linarith

 omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
 theorem iterate_energy_le {f : E → E} {Φ : E → ℝ} (hf : ∀ x, Φ (f x) ≤ Φ x)
    (j : ℕ) (x : E) : Φ (f^[j] x) ≤ Φ x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (hf (f^[j] x)).trans ih

 omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem iterate_energy_drop {f : E → E} {Φ : E → ℝ} {h D M a b : ℝ} (h0 : 0 ≤ h)
    (hD0 : 0 ≤ D) (hD : ∀ x, ‖f x-x‖ ≤ D) (hdec : ∀ x, Φ (f x) ≤ Φ x)
    (hdrop : ∀ x, ‖x‖+D ≤ M → Φ x ≤ b → Φ (f x) ≤ max a (Φ x-h))
    (N : ℕ) (x : E) (hx : ‖x‖+N*D ≤ M) (hb : Φ x ≤ b) :
    Φ (f^[N] x) ≤ max a (Φ x-N*h) := by
  suffices hs : ∀ j, j ≤ N → Φ (f^[j] x) ≤ max a (Φ x-j*h) by exact hs N le_rfl
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hij := ih (Nat.le_trans (Nat.le_succ j) hj)
    have hn := iterate_norm_le hD j x
    have hb' := (iterate_energy_le hdec j x).trans hb
    have hjR : (j : ℝ)+1 ≤ N := by exact_mod_cast hj
    have hx' : ‖f^[j] x‖+D ≤ M := by
      have := mul_le_mul_of_nonneg_right hjR hD0
      nlinarith
    have hd := hdrop (f^[j] x) hx' hb'
    rw [Function.iterate_succ_apply']
    apply hd.trans
    apply max_le (le_max_left _ _)
    apply (sub_le_sub_right hij h).trans
    rw [← max_sub_sub_right]
    apply max_le
    · exact (sub_le_self a h0).trans (le_max_left _ _)
    · apply le_trans _ (le_max_right _ _)
      push_cast
      linarith

 omit [CompleteSpace E] in
 theorem contDiff_iterate {f : E → E} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ (f^[j]) := by
  induction j with
  | zero => exact contDiff_id
  | succ j ih =>
    convert! hf.comp ih using 1
    ext x
    exact Function.iterate_succ_apply' f j x

 theorem exists_descent_map [ProperSpace E] {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V) {Φ : E → ℝ}
    (hΦ : Differentiable ℝ Φ) (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0)
    {L M a b B T : ℝ} (hT : 0 < T) (hba : b-T ≤ a)
    (hL : ∀ x, ‖V x‖ ≤ L) (hM : B+T*L ≤ M)
    (hrate : ∀ x, ‖x‖ ≤ M → a ≤ Φ x → Φ x ≤ b → fderiv ℝ Φ x (V x) ≤ -1) :
    ∃ η : E → E, ContDiff ℝ ∞ η ∧ (∀ x, Φ (η x) ≤ Φ x) ∧
      (∀ x, V x = 0 → η x = x) ∧
      ∀ x, ‖x‖ ≤ B → Φ x ≤ b → Φ (η x) ≤ a := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (T*(K : ℝ)) 0)
  have hN0 : (0 : ℝ) < N := (le_max_right _ _).trans_lt hN
  have hNne : (N : ℝ) ≠ 0 := hN0.ne'
  let h := T/N
  have h0 : 0 ≤ h := (div_pos hT hN0).le
  have hh : ‖h‖₊ * K < 1 := by
    change ‖h‖*(K : ℝ) < (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    dsimp [h]
    rw [div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr ((le_max_left _ _).trans_lt hN)
  have hNh : (N : ℝ)*h = T := by dsimp [h]; field_simp
  let f := SmoothODE.step hV h hh
  have hf : ContDiff ℝ ∞ f := SmoothODE.contDiff_step hV hVs h hh
  have hfd (x : E) : Φ (f x) ≤ Φ x := step_energy_le hV hh h0 hΦ hdec x
  have hfD (x : E) : ‖f x-x‖ ≤ h*L := by
    simpa only [SmoothODE.curve_one, mul_one] using
      (curve_displacement hV hh h0 hL x (t := 1) (by simp))
  have hL0 : 0 ≤ L := (norm_nonneg (V 0)).trans (hL 0)
  refine ⟨f^[N], contDiff_iterate hf N, iterate_energy_le hfd N, ?_, ?_⟩
  · intro x hx
    have hfix : f x = x := by
      simpa only [SmoothODE.curve_one] using
        (SmoothODE.curve_of_eq_zero hV h hh x hx (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1))
    exact Function.iterate_fixed hfix N
  · intro x hx hb
    have hbound : ‖x‖+(N : ℝ)*(h*L) ≤ M := by nlinarith [mul_assoc (N : ℝ) h L]
    have hd := iterate_energy_drop h0 (mul_nonneg h0 hL0) hfD hfd
      (fun y hy hby => step_energy_drop hV hh h0 hΦ hdec hL hrate y hy hby) N x hbound hb
    rw [hNh] at hd
    exact hd.trans (max_le le_rfl (by linarith))

end
end FlowDescent

end
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.GradientLinking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u84 u85 u86 u87 u88

section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff
variable {E : Type u84} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

 theorem contDiff_gradient {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (gradient Φ) := by
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
    (hΦ.fderiv_right (by simp))

 theorem denom_pos (Φ : E → ℝ) {ε : ℝ} (hε : 0 < ε) (x : E) :
    0 < ‖gradient Φ x‖^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)

 theorem contDiff_field {Φ σ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hσ : ContDiff ℝ ∞ σ)
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (field Φ σ ε) := by
  have hg := contDiff_gradient hΦ
  exact ((contDiff_const.mul hσ).div (((contDiff_norm_sq ℝ).comp hg).add contDiff_const)
    (fun x => (denom_pos Φ hε x).ne')).neg.smul hg

 theorem field_eq_zero {Φ σ : E → ℝ} {ε : ℝ} {x : E} (hσ : σ x = 0) :
    field Φ σ ε x = 0 := by simp [field, hσ]

 theorem field_rate (Φ σ : E → ℝ) (ε : ℝ) (x : E) :
    fderiv ℝ Φ x (field Φ σ ε x) = -(2*σ x/(‖gradient Φ x‖^2+ε^2))*‖gradient Φ x‖^2 := by
  rw [field, map_smul, smul_eq_mul, ← inner_gradient_left]
  rw [real_inner_self_eq_norm_sq]

 theorem field_nonincrease (Φ : E → ℝ) {σ : E → ℝ} (hσ : ∀ x, 0 ≤ σ x)
    {ε : ℝ} (hε : 0 < ε) (x : E) : fderiv ℝ Φ x (field Φ σ ε x) ≤ 0 := by
  rw [field_rate]
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (div_nonneg (mul_nonneg (by norm_num) (hσ x)) (denom_pos Φ hε x).le)
  · exact sq_nonneg _

 theorem field_decrease (Φ : E → ℝ) {σ : E → ℝ} {ε : ℝ} (hε : 0 < ε)
    {x : E} (hσ : σ x = 1) (hx : ε ≤ ‖gradient Φ x‖) :
    fderiv ℝ Φ x (field Φ σ ε x) ≤ -1 := by
  rw [field_rate, hσ, mul_one]
  have hd := denom_pos Φ hε x
  have he : -(2/(‖gradient Φ x‖^2+ε^2))*‖gradient Φ x‖^2 =
      -(2*‖gradient Φ x‖^2/(‖gradient Φ x‖^2+ε^2)) := by ring
  rw [he, neg_le_neg_iff, le_div_iff₀ hd]
  nlinarith [norm_nonneg (gradient Φ x)]

 theorem field_norm_le (Φ : E → ℝ) {σ : E → ℝ} (hσ : ∀ x, σ x ∈ Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) (x : E) : ‖field Φ σ ε x‖ ≤ 1/ε := by
  have hden := denom_pos Φ hε x
  rw [field, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) (hσ x).1) hden.le)]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hden hε]
  have hs := mul_le_mul_of_nonneg_right (hσ x).2 (norm_nonneg (gradient Φ x))
  nlinarith [sq_nonneg (‖gradient Φ x‖-ε)]

 theorem field_hasCompactSupport {Φ σ : E → ℝ} (hσ : HasCompactSupport σ) (ε : ℝ) :
    HasCompactSupport (field Φ σ ε) := by
  apply HasCompactSupport.of_support_subset_isCompact hσ.isCompact
  intro x hx
  by_contra hn
  apply hx
  exact field_eq_zero (image_eq_zero_of_notMem_tsupport hn)

end
end GradientDescent

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {E : Type u85} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 theorem exists_uniform_gradient_lower {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a b : ℝ} (hnocrit : ∀ x, a ≤ Φ x → Φ x ≤ b → gradient Φ x ≠ 0)
    (hcoercive : ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → 1 ≤ ‖gradient Φ x‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, a ≤ Φ x → Φ x ≤ b → ε ≤ ‖gradient Φ x‖ := by
  obtain ⟨R,hR⟩ := hcoercive
  let S := closedBall (0 : E) R ∩ Φ ⁻¹' Icc a b
  have hS : IsCompact S := (isCompact_closedBall (0 : E) R).inter_right
    (isClosed_Icc.preimage hΦ.continuous)
  by_cases hne : S.Nonempty
  · obtain ⟨x,hx,hm⟩ := hS.exists_isMinOn hne (contDiff_gradient hΦ).continuous.norm.continuousOn
    have hxg : 0 < ‖gradient Φ x‖ := norm_pos_iff.mpr (hnocrit x hx.2.1 hx.2.2)
    refine ⟨min 1 ‖gradient Φ x‖, lt_min zero_lt_one hxg, ?_⟩
    intro y ha hb
    by_cases hy : ‖y‖ ≤ R
    · exact (min_le_right _ _).trans (hm ⟨by simpa using hy, ha, hb⟩)
    · exact (min_le_left _ _).trans (hR y (le_of_lt (lt_of_not_ge hy)))
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y ha hb
    apply hR
    by_contra h
    exact hne ⟨y, by simpa using (le_of_lt (lt_of_not_ge h)), ha, hb⟩

 omit [FiniteDimensional ℝ E] in
 theorem energyCutoff_contDiff {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (a : ℝ) :
    ContDiff ℝ ∞ (energyCutoff Φ a) := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul hΦ).sub contDiff_const).div_const a)

 omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem energyCutoff_mem (Φ : E → ℝ) (a : ℝ) (x : E) :
    energyCutoff Φ a x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

 omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem energyCutoff_one (Φ : E → ℝ) {a : ℝ} (ha : 0 < a) {x : E} (hx : a ≤ Φ x) :
    energyCutoff Φ a x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ ha]
  linarith

 omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
 theorem energyCutoff_zero (Φ : E → ℝ) {a : ℝ} (ha : 0 < a) {x : E} (hx : Φ x ≤ a/2) :
    energyCutoff Φ a x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le

 theorem exists_cutoff_field {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a b ε M : ℝ} (ha : 0 < a) (hε : 0 < ε) (hM : 0 < M)
    (hgrad : ∀ x, a ≤ Φ x → Φ x ≤ b → ε ≤ ‖gradient Φ x‖) :
    ∃ (V : E → E) (K : ℝ≥0), ContDiff ℝ ∞ V ∧ LipschitzWith K V ∧
      (∀ x, ‖V x‖ ≤ 1/ε) ∧ (∀ x, fderiv ℝ Φ x (V x) ≤ 0) ∧
      (∀ x, Φ x ≤ a/2 → V x = 0) ∧
      (∀ x, ‖x‖ ≤ M → a ≤ Φ x → Φ x ≤ b → fderiv ℝ Φ x (V x) ≤ -1) := by
  let χ : ContDiffBump (0 : E) := ⟨M, M+1, hM, by linarith⟩
  let σ : E → ℝ := fun x => χ x * energyCutoff Φ a x
  have hσ : ContDiff ℝ ∞ σ := χ.contDiff.mul (energyCutoff_contDiff hΦ a)
  have hσc : HasCompactSupport σ := χ.hasCompactSupport.mul_right
  have hσm (x : E) : σ x ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg χ.nonneg (energyCutoff_mem Φ a x).1, ?_⟩
    exact (mul_le_of_le_one_left (energyCutoff_mem Φ a x).1 χ.le_one).trans
      (energyCutoff_mem Φ a x).2
  let V := field Φ σ ε
  have hV : ContDiff ℝ ∞ V := contDiff_field hΦ hσ hε
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (field_hasCompactSupport hσc ε) hV (by simp)
  refine ⟨V,K,hV,hK,field_norm_le Φ hσm hε,field_nonincrease Φ (fun x => (hσm x).1) hε,?_,?_⟩
  · intro x hx
    apply field_eq_zero
    simp only [σ, energyCutoff_zero Φ ha hx, mul_zero]
  · intro x hx hxa hxb
    apply field_decrease Φ hε _ (hgrad x hxa hxb)
    have hχ : χ x = 1 := χ.one_of_mem_closedBall (by simpa using hx)
    simp only [σ, hχ, energyCutoff_one Φ ha hxa, mul_one]

end
end GradientDescent

namespace FiniteLinking
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {H : Type u86} {E : Type u87} {F : Type u88} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

 theorem exists_critical (l : H ≃L[ℝ] E × F) {Φ : H → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {e : F} (he : ‖e‖ = 1) {a b ρ ε R : ℝ}
    (ha : 0 < a) (hba : a ≤ b) (hρ : 0 < ρ) (hε : 0 < ε) (hR : ρ < R)
    (hpos : ∀ z : F, ‖z‖ = ρ → 2*a ≤ Φ (l.symm (0,z)))
    (hnear : ∀ (y : E) (s : ℝ), 0 < s → s < ε → Φ (l.symm (y,s • e)) ≤ a/2)
    (hfar : ∀ (y : E) (s : ℝ), 0 < s → R ≤ ‖(y,s)‖ → Φ (l.symm (y,s • e)) ≤ a/2)
    (hupper : ∀ (y : E) (s : ℝ), 0 < s → ‖(y,s)‖ < R → Φ (l.symm (y,s • e)) ≤ b)
    (hcoercive : ∃ C : ℝ, ∀ x, C ≤ ‖x‖ → 1 ≤ ‖gradient Φ x‖) :
    ∃ x : H, a ≤ Φ x ∧ Φ x ≤ b ∧ gradient Φ x = 0 := by
  by_contra! hn
  obtain ⟨δ,hδ,hgrad⟩ := GradientDescent.exists_uniform_gradient_lower hΦ hn hcoercive
  let B := ‖l.symm.toContinuousLinearMap‖ * R
  let T := b-a+1
  let M := B+T*(1/δ)+1
  have hR0 : 0 < R := hρ.trans hR
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT : 0 < T := by dsimp [T]; linarith
  have hM : 0 < M := by
    have : 0 < T*(1/δ) := mul_pos hT (one_div_pos.mpr hδ)
    dsimp [M]
    linarith
  obtain ⟨V,K,hVs,hV,hL,hdec,hfix,hrate⟩ :=
    GradientDescent.exists_cutoff_field hΦ ha hδ hM hgrad
  obtain ⟨η,hη,_,hηfix,hηlow⟩ := FlowDescent.exists_descent_map hV hVs
    (hΦ.differentiable (by simp)) hdec hT (show b-T ≤ a by dsimp [T]; linarith)
    hL (show B+T*(1/δ) ≤ M by dsimp [M]; linarith) hrate
  let ψ : E × F → E × F := l ∘ η ∘ l.symm
  have hψ : ContDiff ℝ ∞ ψ := l.contDiff.comp (hη.comp l.symm.contDiff)
  have hψeq (y : E) (s : ℝ) (hx : Φ (l.symm (y,s • e)) ≤ a/2) :
      ψ (y,s • e) = (y,s • e) := by
    simp only [ψ, Function.comp_apply, hηfix _ (hfix _ hx), l.apply_symm_apply]
  obtain ⟨y,s,hs,hys,hfst,hsnd⟩ := SmoothLinking.sphere_linking hψ he hρ hε hR
    (fun y s hs heps => hψeq y s (hnear y s hs heps))
    (fun y s hs hnorm => hψeq y s (hfar y s hs hnorm))
  have hncone : ‖(y,s • e)‖ = ‖(y,s)‖ := by
    simp only [Prod.norm_def, norm_smul, he, mul_one, Real.norm_eq_abs]
  have hxB : ‖l.symm (y,s • e)‖ ≤ B :=
    (l.symm.toContinuousLinearMap.le_opNorm _).trans (by
      rw [hncone]
      exact mul_le_mul_of_nonneg_left hys.le (norm_nonneg l.symm.toContinuousLinearMap))
  have hlow := hηlow (l.symm (y,s • e)) hxB (hupper y s hs hys)
  have hhigh := hpos (ψ (y,s • e)).2 hsnd
  have heq : l.symm (0,(ψ (y,s • e)).2) = η (l.symm (y,s • e)) := by
    rw [← hfst]
    change l.symm (ψ (y,s • e)) = _
    simp only [ψ, Function.comp_apply, l.symm_apply_apply]
  rw [heq] at hhigh
  linarith

end
end FiniteLinking

end

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FourierIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u89 u90 u91 u92 u93 u94 u95 u96 u97 u98 u99

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

 attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions
theorem continuous_eval {ι : Type u90} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) :
    Continuous (eval k a) := by
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (fourier (k i)).continuous)

 theorem integral_fourier (k : ℤ) :
    (∫ t : Time, fourier k t ∂μ) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Pi.single_apply,
    eq_comm (a := (0 : ℤ))] using h

 theorem integral_conj_fourier_mul (k l : ℤ) :
    (∫ t : Time, conj (fourier k t) * fourier l t ∂μ) = if k = l then 1 else 0 := by
  simp_rw [← fourier_neg, ← fourier_add]
  rw [integral_fourier]
  simp only [neg_add_eq_zero]

 theorem integral_conj_eval_mul {ι : Type u92} {κ : Type u93} [Fintype ι] [Fintype κ]
    (k : ι → ℤ) (l : κ → ℤ) (a : ι → ℂ) (b : κ → ℂ) :
    (∫ t : Time, conj (eval k a t) * eval l b t ∂μ) =
      ∑ i, ∑ j, if k i = l j then conj (a i) * b j else 0 := by
  classical
  have he (t : Time) : conj (eval k a t) * eval l b t =
      ∑ i, ∑ j, conj (a i)*conj (fourier (k i) t)*(b j*fourier (l j) t) := by
    change conj (∑ i, a i*fourier (k i) t) * eval l b t = _
    rw [map_sum, Finset.sum_mul]
    simp only [map_mul, eval, Finset.mul_sum]
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      simp_rw [show ∀ t : Time, conj (a i) * conj (fourier (k i) t) *
          (b j * fourier (l j) t) =
          (conj (a i)*b j) * (conj (fourier (k i) t)*fourier (l j) t) by intro t; ring]
      rw [integral_const_mul, integral_conj_fourier_mul]
      split_ifs <;> simp
    · intro j _
      exact integrable_continuous ((continuous_const.mul ((fourier (k i)).continuous.star)).mul
        (continuous_const.mul (fourier (l j)).continuous))
  · intro i _
    apply integrable_finsetSum
    intro j _
    exact integrable_continuous ((continuous_const.mul ((fourier (k i)).continuous.star)).mul
      (continuous_const.mul (fourier (l j)).continuous))

 theorem norm_sq_re (z : ℂ) : ‖z‖^2 = (conj z*z).re := by
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]

 theorem integral_norm_sq {ι : Type u94} [Fintype ι] (k : ι → ℤ) (hk : Function.Injective k)
    (a : ι → ℂ) : (∫ t : Time, ‖eval k a t‖^2 ∂μ) = ∑ i, ‖a i‖^2 := by
  classical
  simp_rw [norm_sq_re]
  have hI : Integrable (fun t : Time => conj (eval k a t) * eval k a t) μ :=
    integrable_continuous ((continuous_eval k a).star.mul (continuous_eval k a))
  change (∫ t : Time, RCLike.re (conj (eval k a t)*eval k a t) ∂μ) = _
  rw [integral_re hI, integral_conj_eval_mul]
  simp only [hk.eq_iff]
  simp

 theorem coe_integral_norm_fourth {ι : Type u95} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) :
    (((∫ t : Time, ‖eval k a t‖^4 ∂μ) : ℝ) : ℂ) =
      ∑ p : ι × ι, ∑ q : ι × ι,
        if k p.1+k p.2 = k q.1+k q.2 then conj (a p.1*a p.2)*(a q.1*a q.2) else 0 := by
  let k' : ι × ι → ℤ := fun p => k p.1+k p.2
  let a' : ι × ι → ℂ := fun p => a p.1*a p.2
  have heval (t : Time) : eval k' a' t = eval k a t * eval k a t := by
    simp only [eval, k', a', Fintype.sum_prod_type, fourier_add, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hintegrand (t : Time) : (↑(‖eval k a t‖^4) : ℂ) =
      conj (eval k' a' t)*eval k' a' t := by
    rw [heval, map_mul, mul_mul_mul_comm, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.sq_norm]
    push_cast
    ring
  rw [← integral_complex_ofReal]
  simp_rw [hintegrand]
  exact integral_conj_eval_mul k' k' a' a'

end
end FourierPolynomial

namespace WeightedSchur
noncomputable section
open Finset

 theorem two_mul_le_weighted {w v : ℝ} (hw : 0 < w) (hv : 0 < v) (x y : ℝ) :
    2*x*y ≤ w*x^2/v + v*y^2/w := by
  rw [div_add_div _ _ hv.ne' hw.ne', le_div_iff₀ (mul_pos hv hw)]
  nlinarith [sq_nonneg (w*x-v*y)]

 theorem sum_le {ι : Type u96} [Fintype ι] (r : ι → ι → Prop) [DecidableRel r]
    (hr : ∀ {i j}, r i j → r j i) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (x : ι → ℝ)
    {C : ℝ} (hrow : ∀ i, (∑ j, if r i j then 1/w j else 0) ≤ C) :
    (∑ i, ∑ j, if r i j then x i*x j else 0) ≤ C * ∑ i, w i*x i^2 := by
  have hp (i j : ι) : 2*(if r i j then x i*x j else 0) ≤
      (if r i j then w i*x i^2/w j else 0) +
      (if r j i then w j*x j^2/w i else 0) := by
    by_cases hij : r i j
    · simp only [ite_eq_left hij, ite_eq_left (hr hij)]
      simpa only [mul_assoc] using two_mul_le_weighted (hw i) (hw j) (x i) (x j)
    · have hji : ¬r j i := fun h => hij (hr h)
      simp only [ite_eq_right hij, ite_eq_right hji, mul_zero, add_zero, le_refl]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) => hp i j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hcomm : (∑ i : ι, ∑ j : ι, if r j i then w j*x j^2/w i else 0) =
      ∑ i : ι, ∑ j : ι, if r i j then w i*x i^2/w j else 0 := Finset.sum_comm
  rw [hcomm] at hs
  have hh : (∑ i : ι, ∑ j : ι, if r i j then w i*x i^2/w j else 0) ≤
      C * ∑ i, w i*x i^2 := by
    calc
      _ = ∑ i, w i*x i^2 * (∑ j, if r i j then 1/w j else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ ≤ ∑ i, w i*x i^2*C := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hrow i) (mul_nonneg (hw i).le (sq_nonneg _)))
      _ = _ := by rw [← Finset.sum_mul]; ring
  linarith

 theorem reciprocal_pair_rows {ι : Type u97} [Fintype ι] (k : ι → ℕ)
    (hk : Function.Injective k) (hk0 : ∀ i, 0 < k i) (p : ι × ι) :
    (∑ q : ι × ι, if k p.1+k p.2 = k q.1+k q.2 then
      1 / ((k q.1 : ℝ)*(k q.2 : ℝ)) else 0) ≤ 1 := by
  classical
  let m := k p.1+k p.2
  have hm : 2 ≤ m := by dsimp [m]; have := hk0 p.1; have := hk0 p.2; omega
  let Q := univ.filter (fun q : ι × ι => k q.1+k q.2 = m)
  have hQ (q : ι × ι) : q ∈ Q ↔ k q.1+k q.2 = m := by simp [Q]
  have hmaps : Set.MapsTo (fun q : ι × ι => k q.1) (↑Q : Set (ι × ι))
      (↑(Icc 1 (m-1)) : Set ℕ) := by
    intro q hq
    have he := (hQ q).mp hq
    have h0 := hk0 q.1
    have h1 := hk0 q.2
    simp only [mem_coe, mem_Icc]
    omega
  have hinj : Set.InjOn (fun q : ι × ι => k q.1) (↑Q : Set (ι × ι)) := by
    intro q hq z hz he
    change k q.1 = k z.1 at he
    have hq' := (hQ q).mp hq
    have hz' := (hQ z).mp hz
    apply Prod.ext (hk he)
    apply hk
    omega
  have hc : Q.card ≤ m-1 := by
    have hc' := Finset.card_le_card_of_injOn (fun q : ι × ι => k q.1) hmaps hinj
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc'
  have hd : 0 < (m : ℝ)-1 := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hterm (q : ι × ι) (hq : q ∈ Q) :
      1/((k q.1 : ℝ)*(k q.2 : ℝ)) ≤ 1/((m : ℝ)-1) := by
    apply one_div_le_one_div_of_le hd
    have h0 : 1 ≤ (k q.1 : ℝ) := by exact_mod_cast (show 1 ≤ k q.1 from hk0 q.1)
    have h1 : 1 ≤ (k q.2 : ℝ) := by exact_mod_cast (show 1 ≤ k q.2 from hk0 q.2)
    have he : (k q.1 : ℝ)+(k q.2 : ℝ) = m := by exact_mod_cast (hQ q).mp hq
    nlinarith [mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  calc
    _ = ∑ q ∈ Q, 1/((k q.1 : ℝ)*(k q.2 : ℝ)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q _
      simp only [m, eq_comm (a := k q.1+k q.2)]
    _ ≤ ∑ _q ∈ Q, 1/((m : ℝ)-1) := Finset.sum_le_sum hterm
    _ = (Q.card : ℝ)/((m : ℝ)-1) := by simp [div_eq_mul_inv]
    _ ≤ 1 := by
      rw [div_le_one hd]
      have hcR : (Q.card : ℝ) ≤ (m-1 : ℕ) := by exact_mod_cast hc
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at hcR
      exact hcR

end
end WeightedSchur

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

 local instance instFactLtRealOfNat_solutions_1_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
theorem integral_norm_fourth_le_pairs {ι : Type u98} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) :
    (∫ t : Time, ‖eval k a t‖^4 ∂μ) ≤
      ∑ p : ι × ι, ∑ q : ι × ι,
        if k p.1+k p.2 = k q.1+k q.2 then
          (‖a p.1‖*‖a p.2‖)*(‖a q.1‖*‖a q.2‖) else 0 := by
  classical
  have hI : 0 ≤ ∫ t : Time, ‖eval k a t‖^4 ∂μ := integral_nonneg (fun _ => by positivity)
  calc
    _ = ‖(((∫ t : Time, ‖eval k a t‖^4 ∂μ) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hI]
    _ = ‖∑ p : ι × ι, ∑ q : ι × ι,
        if k p.1+k p.2 = k q.1+k q.2 then conj (a p.1*a p.2)*(a q.1*a q.2) else 0‖ :=
      congrArg norm (coe_integral_norm_fourth k a)
    _ ≤ ∑ p : ι × ι, ∑ q : ι × ι,
        ‖if k p.1+k p.2 = k q.1+k q.2 then conj (a p.1*a p.2)*(a q.1*a q.2) else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp only [norm_mul, Complex.norm_conj, norm_zero]

 theorem positive_L4 {ι : Type u99} [Fintype ι] (k : ι → ℕ)
    (hk : Function.Injective k) (hk0 : ∀ i, 0 < k i) (a : ι → ℂ) :
    (∫ t : Time, ‖eval (fun i => (k i : ℤ)) a t‖^4 ∂μ) ≤
      (∑ i, (k i : ℝ)*‖a i‖^2)^2 := by
  classical
  have hrows := WeightedSchur.reciprocal_pair_rows k hk hk0
  let w : ι × ι → ℝ := fun p => (k p.1 : ℝ)*(k p.2 : ℝ)
  have hw (p : ι × ι) : 0 < w p := by
    exact mul_pos (by exact_mod_cast hk0 p.1) (by exact_mod_cast hk0 p.2)
  have hS := WeightedSchur.sum_le
    (fun p q : ι × ι => k p.1+k p.2 = k q.1+k q.2)
    (fun h => h.symm) w hw (fun p => ‖a p.1‖*‖a p.2‖) hrows
  have hpair := integral_norm_fourth_le_pairs (fun i => (k i : ℤ)) a
  simp only [← Nat.cast_add, Int.natCast_inj] at hpair
  apply hpair.trans
  apply (hS.trans_eq _)
  simp only [one_mul, Fintype.sum_prod_type, w]
  calc
    _ = ∑ i, ∑ j, ((k i : ℝ)*‖a i‖^2)*((k j : ℝ)*‖a j‖^2) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← Finset.sum_mul_sum]; ring

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FourierPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u100 u101 u102 u103 u104 u105 u106 u107 u108 u109 u110 u111

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
 local instance instFactLtRealOfNat_solutions_2_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
theorem real_inner_eq_complex_re {α : Type u100} [Fintype α] (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) a b = RCLike.re (inner (𝕜 := ℂ) a b) := by
  simp only [PiLp.inner_apply, real_inner_eq_re_inner, map_sum]

variable {ι : Type u101} {κ : Type u102} [Fintype ι] [Fintype κ]

 theorem integral_loop_norm_sq (k : ι → ℤ) (hk : Function.Injective k) (a : Coeff ι κ) :
    (∫ t : Time, ‖loop k a t‖^2 ∂μ) = ‖a‖^2 := by
  classical
  simp_rw [EuclideanSpace.norm_sq_eq, loop_coord]
  rw [integral_finsetSum]
  · simp_rw [integral_norm_sq k hk]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
  · intro j _
    exact integrable_continuous ((continuous_eval k _).norm.pow 2)

 theorem integral_loop_coord_sq (k : ι → ℤ) (hk : Function.Injective k)
    (a : Coeff ι κ) (j : κ) :
    (∫ t : Time, ‖loop k a t j‖^2 ∂μ) = ∑ i, ‖a (i,j)‖^2 := by
  simp_rw [loop_coord]
  exact integral_norm_sq k hk _

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_3_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u106} {κ : Type u107} [Fintype ι] [Fintype κ]

 theorem vector_norm_fourth_le (z : Vector κ) :
    ‖z‖^4 ≤ (Fintype.card κ : ℝ) * ∑ j, ‖z j‖^4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset κ)
    (fun j => ‖z j‖^2) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, ← pow_mul] at h
  calc
    _ = (∑ j, ‖z j‖^2)^2 := by rw [← EuclideanSpace.norm_sq_eq]; ring
    _ ≤ _ := by simpa only [mul_comm] using h

 theorem integral_loop_norm_fourth_le (k : ι → ℕ)
    (hk : Function.Injective k) (hk0 : ∀ i, 0 < k i) (a : Coeff ι κ) :
    (∫ t : Time, ‖loop (fun i => (k i : ℤ)) a t‖^4 ∂μ) ≤
      (Fintype.card κ : ℝ) * (∑ p : ι × κ, (k p.1 : ℝ)*‖a p‖^2)^2 := by
  classical
  let L := loop (fun i => (k i : ℤ)) a
  have hcont : Continuous (fun t : Time => (Fintype.card κ : ℝ)*∑ j, ‖L t j‖^4) :=
    continuous_const.mul (continuous_finsetSum _ (fun j _ =>
      (((PiLp.continuous_apply 2 _ j).comp L.continuous).norm.pow 4)))
  calc
    _ ≤ ∫ t : Time, (Fintype.card κ : ℝ)*∑ j, ‖L t j‖^4 ∂μ :=
      integral_mono (integrable_continuous (L.continuous.norm.pow 4))
        (integrable_continuous hcont) (fun t => vector_norm_fourth_le (L t))
    _ = (Fintype.card κ : ℝ)*∑ j, ∫ t : Time, ‖L t j‖^4 ∂μ := by
      rw [integral_const_mul, integral_finsetSum]
      intro j _
      exact integrable_continuous (((PiLp.continuous_apply 2 _ j).comp L.continuous).norm.pow 4)
    _ ≤ (Fintype.card κ : ℝ)*∑ j, (∑ i, (k i : ℝ)*‖a (i,j)‖^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      simp only [L, loop_coord]
      exact positive_L4 k hk hk0 _
    _ ≤ (Fintype.card κ : ℝ)*(∑ j, ∑ i, (k i : ℝ)*‖a (i,j)‖^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ =>
        Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
    _ = _ := by rw [Finset.sum_comm, Fintype.sum_prod_type]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_4
variable {ι : Type u108} {κ : Type u109} [Fintype ι] [Fintype κ]

 theorem fourierCoeff_eval (k : ι → ℤ) (a : ι → ℂ) (j : ℤ) :
    fourierCoeff (eval k a) j = ∑ i, if j = k i then a i else 0 := by
  classical
  simp only [fourierCoeff, eval, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    have he (t : Time) : fourier (-j) t * (a i * fourier (k i) t) =
        a i*(conj (fourier j t)*fourier (k i) t) := by rw [fourier_neg]; ring
    simp_rw [he]
    rw [integral_const_mul, integral_conj_fourier_mul]
    split_ifs <;> simp only [mul_one, mul_zero]
  · intro i _
    exact integrable_continuous ((fourier (-j)).continuous.mul
      (continuous_const.mul (fourier (k i)).continuous))

 theorem project_loop (k : ι → ℤ) (hk : Function.Injective k) (a : Coeff ι κ) :
    project k (loop k a) = a := by
  classical
  ext p
  simp only [project_apply, loop_coord, fourierCoeff_eval, hk.eq_iff]
  simp

 theorem integral_fourier_mul_conj (k : ℤ) (f : C(Time, ℂ)) :
    (∫ t : Time, conj (f t) * fourier k t ∂μ) = conj (fourierCoeff f k) := by
  rw [fourierCoeff, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul, map_mul, fourier_neg, starRingEnd_self_apply]
  ring

 theorem integral_inner_loop (k : ι → ℤ) (f : C(Time, Vector κ)) (a : Coeff ι κ) :
    (∫ t : Time, inner (𝕜 := ℝ) (f t) (loop k a t) ∂μ) =
      inner (𝕜 := ℝ) (project k f) a := by
  classical
  have hstage (j : κ) :
      (∫ t : Time, conj (f t j)*eval k (fun i => a (i,j)) t ∂μ) =
        ∑ i, conj (project k f (i,j))*a (i,j) := by
    simp only [eval, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      have he (t : Time) : conj (f t j) * (a (i,j) * fourier (k i) t) =
          (conj (f t j) * fourier (k i) t) * a (i,j) := by ring
      simp_rw [he]
      rw [integral_mul_const]
      exact congrArg (fun z => z*a (i,j))
        (integral_fourier_mul_conj (k i)
          ⟨fun t => f t j, (PiLp.continuous_apply 2 _ j).comp f.continuous⟩)
    · intro i _
      exact integrable_continuous
        ((((PiLp.continuous_apply 2 _ j).comp f.continuous).star).mul
          (continuous_const.mul (fourier (k i)).continuous))
  have hcomplex : (∫ t : Time, inner (𝕜 := ℂ) (f t) (loop k a t) ∂μ) =
      inner (𝕜 := ℂ) (project k f) a := by
    change (∫ t : Time, ∑ j, loop k a t j * conj (f t j) ∂μ) =
      ∑ p : ι × κ, a p * conj (project k f p)
    simp_rw [loop_coord, mul_comm (eval k _ _)]
    rw [integral_finsetSum]
    · simp_rw [hstage]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      congr 1
      ext j
      apply Finset.sum_congr rfl
      intro i _
      ring
    · intro j _
      exact integrable_continuous
        ((((PiLp.continuous_apply 2 _ j).comp f.continuous).star).mul
          (continuous_eval k _))
  simp only [real_inner_eq_complex_re]
  rw [integral_re (integrable_continuous
    (show Continuous (fun t => inner (𝕜 := ℂ) (f t) (loop k a t)) from
      f.continuous.inner (loop k a).continuous)), hcomplex]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_5_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u110} {κ : Type u111} [Fintype ι] [Fintype κ]

 theorem project_bessel (k : ι → ℤ) (hk : Function.Injective k) (f : C(Time, Vector κ)) :
    ‖project k f‖^2 ≤ ∫ t : Time, ‖f t‖^2 ∂μ := by
  -- coordinatewise from the published scalar Bessel inequality
  -- MeasureTheory.sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal, for the
  -- orthonormal characters fourier (k i), reindexed by Fin (card ι)
  classical
  let σ := Fintype.equivFin ι
  let e : Fin (Fintype.card ι) → Time → ℂ := fun i t => fourier (k (σ.symm i)) t
  have hcf (j : κ) : Continuous (fun t => f t j) :=
    (PiLp.continuous_apply 2 _ j).comp f.continuous
  have hj (j : κ) : ∑ i, ‖project k f (i, j)‖^2 ≤ ∫ t : Time, ‖f t j‖^2 ∂μ := by
    have h := MeasureTheory.sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal μ e
      (fun i i' => integrable_continuous
        ((fourier _).continuous.mul (Complex.continuous_conj.comp (fourier _).continuous)))
      (fun i i' => by
        have h0 := integral_conj_fourier_mul (k (σ.symm i')) (k (σ.symm i))
        simp_rw [e, mul_comm (fourier (k (σ.symm i)) _)]
        rw [h0]
        simp only [hk.eq_iff, σ.symm.injective.eq_iff, eq_comm])
      (fun t => f t j) (integrable_continuous ((hcf j).norm.pow 2))
      (fun i => integrable_continuous
        ((hcf j).mul (Complex.continuous_conj.comp (fourier _).continuous)))
    have hc (i : Fin (Fintype.card ι)) :
        (∫ t : Time, f t j * conj (e i t) ∂μ) = project k f (σ.symm i, j) := by
      rw [project_apply, fourierCoeff]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [e, smul_eq_mul, fourier_neg, mul_comm]
    simp_rw [hc] at h
    rw [← σ.symm.sum_comp]
    exact h
  calc ‖project k f‖^2 = ∑ j, ∑ i, ‖project k f (i, j)‖^2 := by
        rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    _ ≤ ∑ j, ∫ t : Time, ‖f t j‖^2 ∂μ := Finset.sum_le_sum fun j _ => hj j
    _ = ∫ t : Time, ‖f t‖^2 ∂μ := by
        rw [← integral_finsetSum]
        · simp_rw [EuclideanSpace.norm_sq_eq]
        · intro j _
          exact integrable_continuous ((hcf j).norm.pow 2)

 theorem project_bounded (k : ι → ℤ) (hk : Function.Injective k)
    (f : C(Time, Vector κ)) {B : ℝ} (hB : 0 ≤ B) (hf : ∀ t, ‖f t‖ ≤ B) :
    ‖project k f‖ ≤ B := by
  have hi : (∫ t : Time, ‖f t‖^2 ∂μ) ≤ B^2 := by
    calc
      _ ≤ ∫ _ : Time, B^2 ∂μ := integral_mono
        (integrable_continuous (f.continuous.norm.pow 2)) (integrable_const _) (fun t =>
          pow_le_pow_left₀ (norm_nonneg _) (hf t) 2)
      _ = _ := by simp
  have h := (project_bessel k hk f).trans hi
  nlinarith [norm_nonneg (project k f)]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_6
variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem contDiff_potential (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (potential k H) := by
  exact average.contDiff.comp ((SmoothPaths.contDiff_superpose hH).comp (loopCLM k).contDiff)

 theorem hasGradientAt_potential (k : ι → ℤ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) :
    HasGradientAt (potential k H) (project k (gradLoop k hH a)) a := by
  have hl : HasFDerivAt (loop k) (loopCLM k) a := by
    change HasFDerivAt (loopCLM k) (loopCLM k) a
    exact (loopCLM (κ := κ) k).hasFDerivAt (x := a)
  have hS := (SmoothPaths.hasFDerivAt_superpose
    (hH.differentiable (by simp)) (hH.fderiv_right (m := ∞) (by simp)).continuous (loop k a)).comp
      a hl
  have hi := average.hasFDerivAt.comp a hS
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt (potential k H) _ a at hi
  apply hi.congr_fderiv
  ext b
  change (∫ t : Time, fderiv ℝ H (loop k a t) (loop k b t) ∂μ) =
    inner (𝕜 := ℝ) (project k (gradLoop k hH a)) b
  simp_rw [← inner_gradient_left]
  exact integral_inner_loop k (gradLoop k hH a) b

 theorem gradient_potential (k : ι → ℤ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) :
    gradient (potential k H) a = project k (gradLoop k hH a) :=
  (hasGradientAt_potential k hH a).gradient

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.QuadraticAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u112

section NonsqueezingInline

namespace DiagonalQuadratic
noncomputable section
open Finset
open scoped ComplexConjugate ContDiff
variable {α : Type u112} [Fintype α]

 theorem real_inner_eq_sum (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) a b = ∑ p, inner (𝕜 := ℝ) (a p) (b p) := by
  exact PiLp.inner_apply a b

 theorem inner_diag (w : α → ℝ) (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) (diag w a) b = ∑ p, w p * inner (𝕜 := ℝ) (a p) (b p) := by
  rw [real_inner_eq_sum]
  simp only [diag_apply, real_inner_smul_left]

 theorem self_adjoint (w : α → ℝ) (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) (diag w a) b = inner (𝕜 := ℝ) a (diag w b) := by
  rw [inner_diag, real_inner_eq_sum]
  simp only [diag_apply, real_inner_smul_right]

 theorem energy_eq_inner (w : α → ℝ) (a : EuclideanSpace ℂ α) :
    energy w a = inner (𝕜 := ℝ) (diag w a) a := by
  rw [inner_diag]
  simp only [energy, real_inner_self_eq_norm_sq]

 theorem contDiff_energy (w : α → ℝ) : ContDiff ℝ ∞ (energy w) := by
  simp_rw [funext (energy_eq_inner w)]
  exact (diagCLM w).contDiff.inner ℝ contDiff_id

 theorem hasGradientAt_energy (w : α → ℝ) (a : EuclideanSpace ℂ α) :
    HasGradientAt (energy w) ((2 : ℝ) • diag w a) a := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (diagCLM w).hasFDerivAt.inner ℝ (hasFDerivAt_id a)
  simp only [diagCLM_apply] at h
  change HasFDerivAt (fun x => inner (𝕜 := ℝ) (diag w x) x) _ a at h
  simp_rw [← energy_eq_inner] at h
  apply h.congr_fderiv
  ext b
  change inner (𝕜 := ℝ) (diag w a) b + inner (𝕜 := ℝ) (diag w b) a =
    inner (𝕜 := ℝ) ((2 : ℝ) • diag w a) b
  rw [real_inner_smul_left, self_adjoint w b a]
  rw [real_inner_comm b (diag w a)]
  ring

 theorem norm_diag_sq (w : α → ℝ) (a : EuclideanSpace ℂ α) :
    ‖diag w a‖^2 = ∑ p, (w p)^2*‖a p‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, diag_apply, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]

 theorem norm_diag_lower (w : α → ℝ) {d : ℝ} (hd : 0 ≤ d) (hw : ∀ p, d ≤ |w p|)
    (a : EuclideanSpace ℂ α) : d*‖a‖ ≤ ‖diag w a‖ := by
  have h : (d*‖a‖)^2 ≤ ‖diag w a‖^2 := by
    rw [mul_pow, norm_diag_sq, EuclideanSpace.norm_sq_eq, mul_sum]
    apply sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    calc
      d^2 ≤ |w p|^2 := pow_le_pow_left₀ hd (hw p) 2
      _ = _ := sq_abs _
  nlinarith [norm_nonneg (diag w a), mul_nonneg hd (norm_nonneg a)]

 theorem norm_diag_upper (w : α → ℝ) {d : ℝ} (hd : 0 ≤ d) (hw : ∀ p, |w p| ≤ d)
    (a : EuclideanSpace ℂ α) : ‖diag w a‖ ≤ d*‖a‖ := by
  have h : ‖diag w a‖^2 ≤ (d*‖a‖)^2 := by
    rw [mul_pow, norm_diag_sq, EuclideanSpace.norm_sq_eq, mul_sum]
    apply sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    calc
      (w p)^2 = |w p|^2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (hw p) 2
  nlinarith [norm_nonneg (diag w a), mul_nonneg hd (norm_nonneg a)]

 theorem energy_smul (w : α → ℝ) (r : ℝ) (a : EuclideanSpace ℂ α) :
    energy w (r • a) = r^2*energy w a := by
  simp only [energy, PiLp.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    mul_sum]
  apply sum_congr rfl
  intro p _
  ring

 theorem energy_mul (w : α → ℝ) (r : ℝ) (a : EuclideanSpace ℂ α) :
    energy (fun p => r*w p) a = r*energy w a := by
  simp only [energy, mul_sum, mul_assoc]

 theorem energy_lower (w : α → ℝ) (d : ℝ) (hw : ∀ p, d ≤ w p)
    (a : EuclideanSpace ℂ α) : d*‖a‖^2 ≤ energy w a := by
  simp only [EuclideanSpace.norm_sq_eq, mul_sum, energy]
  exact sum_le_sum (fun p _ => mul_le_mul_of_nonneg_right (hw p) (sq_nonneg _))

 theorem energy_nonpos (w : α → ℝ) (hw : ∀ p, w p ≤ 0)
    (a : EuclideanSpace ℂ α) : energy w a ≤ 0 :=
  sum_nonpos (fun p _ => mul_nonpos_of_nonpos_of_nonneg (hw p) (sq_nonneg _))

 theorem energy_single [DecidableEq α] (w : α → ℝ) (p : α) (z : ℂ) :
    energy w (PiLp.single 2 p z) = w p * ‖z‖^2 := by
  classical
  unfold energy
  rw [sum_eq_single p]
  · simp
  · intro q _ hq
    simp [hq]
  · simp

end
end DiagonalQuadratic

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_7_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 theorem contDiff_action (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (action k H) :=
  (contDiff_energy _).sub (contDiff_potential k hH)

 theorem hasGradientAt_action (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : Coeff ι κ) :
    HasGradientAt (action k H)
      ((2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)) a - project k (gradLoop k hH a)) a := by
  have h := (hasGradientAt_energy (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a).hasFDerivAt.sub
    (hasGradientAt_potential k hH a).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt (action k H) _ a at h
  apply h.congr_fderiv
  ext b
  simp only [map_sub]

 theorem gradient_action (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : Coeff ι κ) : gradient (action k H) a =
      (2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)) a - project k (gradLoop k hH a) :=
  (hasGradientAt_action k hH a).gradient

 theorem potential_nonneg (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ∀ z, 0 ≤ H z)
    (a : Coeff ι κ) : 0 ≤ potential k H a := integral_nonneg (fun _ => hH _)

 theorem integral_energy (k : ι → ℤ) (hk : Function.Injective k) (d : κ → ℝ)
    (a : Coeff ι κ) :
    (∫ t : Time, energy d (loop k a t) ∂μ) = energy (fun p => d p.2) a := by
  classical
  simp only [energy]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, integral_loop_coord_sq k hk, mul_sum]
    rw [Fintype.sum_prod_type, sum_comm]
  · intro j _
    exact integrable_continuous (continuous_const.mul
      ((((PiLp.continuous_apply 2 _ j).comp (loop k a).continuous).norm.pow 2)))

 theorem potential_lower (k : ι → ℤ) (hk : Function.Injective k) {H : Vector κ → ℝ}
    (hH : Continuous H) (d : κ → ℝ) (C : ℝ) (hlo : ∀ z, energy d z-C ≤ H z)
    (a : Coeff ι κ) : energy (fun p => d p.2) a-C ≤ potential k H a := by
  have hi : Integrable (fun t : Time => energy d (loop k a t)) μ :=
    integrable_continuous ((contDiff_energy d).continuous.comp (loop k a).continuous)
  calc
    _ = ∫ t : Time, energy d (loop k a t)-C ∂μ := by
      rw [integral_sub hi (integrable_const _), integral_energy k hk]
      simp
    _ ≤ _ := integral_mono (hi.sub (integrable_const _))
      (integrable_continuous (hH.comp (loop k a).continuous)) (fun t => hlo _)

 theorem potential_upper_fourth (k : ι → ℕ) (hk : Function.Injective k)
    (hk0 : ∀ i, 0 < k i) {H : Vector κ → ℝ} (hH : Continuous H)
    {C : ℝ} (hC : 0 ≤ C) (hup : ∀ z, H z ≤ C*‖z‖^4) (a : Coeff ι κ) :
    potential (fun i => (k i : ℤ)) H a ≤
      C*(Fintype.card κ : ℝ)*(∑ p : ι × κ, (k p.1 : ℝ)*‖a p‖^2)^2 := by
  calc
    _ ≤ ∫ t : Time, C*‖loop (fun i => (k i : ℤ)) a t‖^4 ∂μ :=
      integral_mono (integrable_continuous (hH.comp (loop _ a).continuous))
        (integrable_continuous (continuous_const.mul ((loop _ a).continuous.norm.pow 4)))
        (fun t => hup _)
    _ = C*(∫ t : Time, ‖loop (fun i => (k i : ℤ)) a t‖^4 ∂μ) := integral_const_mul _ _
    _ ≤ _ := by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (integral_loop_norm_fourth_le k hk hk0 a) hC

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_8_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

omit [Fintype ι] in
 theorem project_sub (k : ι → ℤ) (f g : C(Time, Vector κ)) :
    project k (f-g) = project k f - project k g := by
  ext p
  simp only [project_apply, ContinuousMap.sub_apply, PiLp.sub_apply, fourierCoeff,
    smul_sub]
  rw [integral_sub]
  · exact integrable_continuous ((fourier (-k p.1)).continuous.smul
      ((PiLp.continuous_apply 2 _ p.2).comp f.continuous))
  · exact integrable_continuous ((fourier (-k p.1)).continuous.smul
      ((PiLp.continuous_apply 2 _ p.2).comp g.continuous))

 theorem loop_diag (k : ι → ℤ) (d : κ → ℝ) (a : Coeff ι κ) (t : Time) :
    loop k (diag (fun p => d p.2) a) t = diag d (loop k a t) := by
  ext j
  simp only [loop_coord, eval, diag_apply, RCLike.real_smul_eq_coe_mul, mul_assoc,
    ← mul_sum]

 theorem loop_smul (k : ι → ℤ) (r : ℝ) (a : Coeff ι κ) :
    loop k (r • a) = r • loop k a := (loopCLM k).map_smul r a

 theorem loop_zero (k : ι → ℤ) : loop k (0 : Coeff ι κ) = 0 := (loopCLM k).map_zero

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_9_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 theorem remainderLoop_apply (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (d : κ → ℝ) (a : Coeff ι κ) (t : Time) :
    remainderLoop k hH d a t = gradient H (loop k a t)-(2 : ℝ) • diag d (loop k a t) := by
  simp only [remainderLoop, ContinuousMap.sub_apply, gradLoop, ContinuousMap.coe_mk,
    loop_smul, ContinuousMap.smul_apply, loop_diag]

 theorem gradient_action_remainder (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) (a : Coeff ι κ) :
    gradient (action k H) a =
      (2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)-d p.2) a-project k (remainderLoop k hH d a) := by
  rw [gradient_action k hH, remainderLoop, project_sub, project_loop k hk]
  have he : diag (fun p : ι × κ => Real.pi*(k p.1 : ℝ)-d p.2) a =
      diag (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a-diag (fun p : ι × κ => d p.2) a := by
    ext p
    simp only [diag_apply, PiLp.sub_apply, sub_smul]
  rw [he, smul_sub]
  abel

 theorem norm_gradient_lower (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B : ℝ}
    (hγ : 0 ≤ γ) (hB : 0 ≤ B) (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ) :
    2*γ*‖a‖ ≤ ‖gradient (action k H) a‖+B := by
  have hb : ‖project k (remainderLoop k hH d a)‖ ≤ B :=
    project_bounded k hk _ hB (fun t => by rw [remainderLoop_apply]; exact hrem _)
  have hd := norm_diag_lower (fun p : ι × κ => Real.pi*(k p.1 : ℝ)-d p.2) hγ
    (fun p => hgap p.1 p.2) a
  have ht := norm_sub_le (gradient (action k H) a) (-project k (remainderLoop k hH d a))
  rw [sub_neg_eq_add, norm_neg] at ht
  have he : gradient (action k H) a + project k (remainderLoop k hH d a) =
      (2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)-d p.2) a := by
    rw [gradient_action_remainder k hk hH]; abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  nlinarith

 theorem gradient_coercive (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) :
    ∃ C : ℝ, ∀ a : Coeff ι κ, C ≤ ‖a‖ → 1 ≤ ‖gradient (action k H) a‖ := by
  refine ⟨(B+1)/(2*γ), fun a ha => ?_⟩
  have h := norm_gradient_lower k hk hH d hγ.le hB hgap hrem a
  have hm := (div_le_iff₀ (mul_pos (by norm_num) hγ)).mp ha
  nlinarith

 theorem critical_norm_bound (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ)
    (ha : gradient (action k H) a = 0) : ‖a‖ ≤ B/(2*γ) := by
  have h := norm_gradient_lower k hk hH d hγ.le hB hgap hrem a
  rw [ha, norm_zero, zero_add] at h
  rw [le_div_iff₀ (mul_pos (by norm_num) hγ)]
  nlinarith

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.GalerkinBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u113

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_10_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

 theorem energy_joinCoeff (w : (ι ⊕ ν) × κ → ℝ) (a : Coeff ι κ) (b : Coeff ν κ) :
    energy w (joinCoeff a b) = energy (fun p => w (Sum.inl p.1,p.2)) a +
      energy (fun p => w (Sum.inr p.1,p.2)) b := by
  simp only [energy, Fintype.sum_prod_type, Fintype.sum_sum_type,
    joinCoeff_inl, joinCoeff_inr]

 theorem loop_joinCoeff (k : ι → ℤ) (l : ν → ℤ) (a : Coeff ι κ) (b : Coeff ν κ) :
    loop (Sum.elim k l) (joinCoeff a b) = loop k a + loop l b := by
  ext t j
  simp only [ContinuousMap.add_apply, PiLp.add_apply, loop_coord, eval,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, joinCoeff_inl, joinCoeff_inr]

 theorem energy_scaled (k : ν → ℕ) (hk : ∀ i, 0 < k i) (b : Coeff ν κ) :
    energy (fun p => (k p.1 : ℝ))
      (diag (fun p => (Real.sqrt (k p.1 : ℝ))⁻¹) b) = ‖b‖^2 := by
  classical
  simp only [energy, EuclideanSpace.norm_sq_eq]
  apply sum_congr rfl
  intro p _
  have hp : 0 < (k p.1 : ℝ) := by exact_mod_cast hk p.1
  rw [diag_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, inv_pow, Real.sq_sqrt hp.le]
  field_simp

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_11_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

 theorem action_positive_lower (k : ι → ℤ) (l : ν → ℕ)
    (hl : Function.Injective l) (hl0 : ∀ i, 0 < l i)
    {H : Vector κ → ℝ} (hH : Continuous H) {C : ℝ} (hC : 0 ≤ C)
    (hup : ∀ z, H z ≤ C*‖z‖^4) (b : Coeff ν κ) :
    Real.pi*‖b‖^2-C*(Fintype.card κ : ℝ)*‖b‖^4 ≤
      action (Sum.elim k (fun i => (l i : ℤ))) H ((positiveScale l hl0).symm (0,b)) := by
  let v := diag (fun p : ν × κ => (Real.sqrt (l p.1 : ℝ))⁻¹) b
  have hkin : energy (fun p : (ι ⊕ ν) × κ =>
      Real.pi*((Sum.elim k (fun i => (l i : ℤ)) p.1 : ℤ) : ℝ)) (joinCoeff 0 v) = Real.pi*‖b‖^2 := by
    rw [energy_joinCoeff]
    simp only [Sum.elim_inl, Sum.elim_inr, Int.cast_natCast]
    have hz : energy (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) 0 = 0 := by simp [energy]
    rw [hz, zero_add, energy_mul, energy_scaled l hl0]
  have hp := potential_upper_fourth l hl hl0 hH hC hup v
  change _ ≤ C*(Fintype.card κ : ℝ)*(energy (fun p : ν × κ => (l p.1 : ℝ)) v)^2 at hp
  rw [energy_scaled l hl0] at hp
  have hlo : potential (Sum.elim k (fun i => (l i : ℤ))) H (joinCoeff 0 v) =
      potential (fun i => (l i : ℤ)) H v := by
    unfold potential
    rw [loop_joinCoeff, loop_zero, zero_add]
  change _ ≤ energy _ (joinCoeff 0 v)-potential _ H (joinCoeff 0 v)
  rw [hkin, hlo]
  nlinarith

 theorem cone_scaled_single [DecidableEq ν] [DecidableEq κ]
    (l : ν → ℕ) (hl0 : ∀ i, 0 < l i) (i₀ : ν) (hl1 : l i₀ = 1) (j₀ : κ)
    (a : Coeff ι κ) (s : ℝ) :
    (positiveScale l hl0).symm (a,s • PiLp.single 2 (i₀,j₀) (1 : ℂ)) =
      joinCoeff a (s • PiLp.single 2 (i₀,j₀) (1 : ℂ)) := by
  apply congrArg (joinCoeff a)
  ext p
  simp only [diag_apply, PiLp.smul_apply, PiLp.single_apply]
  split_ifs with hp
  · subst p
    simp [hl1]
  · simp

 theorem action_cone_upper [DecidableEq ν] [DecidableEq κ]
    (k : ι → ℤ) (hk0 : ∀ i, k i ≤ 0) (l : ν → ℕ) (hl0 : ∀ i, 0 < l i)
    (i₀ : ν) (hl1 : l i₀ = 1) (j₀ : κ)
    {H : Vector κ → ℝ} (hH : ∀ z, 0 ≤ H z) (a : Coeff ι κ) (s : ℝ) :
    action (Sum.elim k (fun i => (l i : ℤ))) H
      ((positiveScale l hl0).symm (a,s • PiLp.single 2 (i₀,j₀) (1 : ℂ))) ≤ Real.pi*s^2 := by
  rw [cone_scaled_single l hl0 i₀ hl1 j₀]
  have hn := energy_nonpos (fun p : ι × κ => Real.pi*(k p.1 : ℝ))
    (fun p => mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (by exact_mod_cast hk0 p.1)) a
  have hp := potential_nonneg (Sum.elim k (fun i => (l i : ℤ))) hH
    (joinCoeff a (s • PiLp.single 2 (i₀,j₀) (1 : ℂ)))
  unfold action
  rw [energy_joinCoeff]
  simp only [Sum.elim_inl, Sum.elim_inr, Int.cast_natCast, energy_smul,
    energy_single, hl1, Nat.cast_one, norm_one, one_pow, mul_one]
  nlinarith

 theorem action_cone_far [DecidableEq ν] [DecidableEq κ]
    (k : ι → ℤ) (hk0 : ∀ i, k i ≤ 0) (l : ν → ℕ) (hl0 : ∀ i, 0 < l i)
    (hkl : Function.Injective (Sum.elim k (fun i => (l i : ℤ))))
    (i₀ : ν) (hl1 : l i₀ = 1) (j₀ : κ)
    {H : Vector κ → ℝ} (hH : Continuous H) (d : κ → ℝ) (C η : ℝ)
    (hd : ∀ j, η ≤ d j) (hd0 : Real.pi+η ≤ d j₀)
    (hlo : ∀ z, energy d z-C ≤ H z) (a : Coeff ι κ) (s : ℝ) :
    action (Sum.elim k (fun i => (l i : ℤ))) H
      ((positiveScale l hl0).symm (a,s • PiLp.single 2 (i₀,j₀) (1 : ℂ))) ≤
      C-η*(‖a‖^2+s^2) := by
  rw [cone_scaled_single l hl0 i₀ hl1 j₀]
  have hn := energy_nonpos (fun p : ι × κ => Real.pi*(k p.1 : ℝ))
    (fun p => mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (by exact_mod_cast hk0 p.1)) a
  have hdlo := energy_lower (fun p : ι × κ => d p.2) η (fun p => hd p.2) a
  have hp := potential_lower (Sum.elim k (fun i => (l i : ℤ))) hkl hH d C hlo
    (joinCoeff a (s • PiLp.single 2 (i₀,j₀) (1 : ℂ)))
  unfold action
  rw [energy_joinCoeff]
  rw [energy_joinCoeff] at hp
  simp only [Sum.elim_inl, Sum.elim_inr, Int.cast_natCast, energy_smul,
    energy_single, hl1, Nat.cast_one, norm_one, one_pow, mul_one] at hp ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hd0) (sq_nonneg s)]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_12
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

omit [Fintype ι] [Fintype κ] in
 theorem mode_velocityCoeff (k : ι → ℤ) (a : Coeff ι κ) (i : ι) :
    mode (velocityCoeff k a) i = (2*(Real.pi : ℂ)*Complex.I*(k i : ℂ)) • mode a i := by
  ext j
  simp only [mode_apply, velocityCoeff, PiLp.smul_apply, diag_apply,
    RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  simp only [map_mul, map_intCast, map_ofNat]
  change Complex.I * ((2 : ℂ) * (((Real.pi : ℂ)*(k i : ℂ))*a (i,j))) =
    (2*(Real.pi : ℂ)*Complex.I*(k i : ℂ))*a (i,j)
  ring

 theorem hasDerivAt_loop (k : ι → ℤ) (a : Coeff ι κ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => loop k a (s : Time)) (loop k (velocityCoeff k a) (t : Time)) t := by
  have hs := HasDerivAt.fun_sum (u := univ) (fun i _ =>
    (hasDerivAt_fourier (1 : ℝ) (k i) t).smul_const (mode a i))
  change HasDerivAt (fun s : ℝ => loop k a (s : Time)) _ t at hs
  apply hs.congr_deriv
  simp only [loop_apply, mode_velocityCoeff, smul_smul, div_one, Complex.ofReal_one]
  apply sum_congr rfl
  intro i _
  congr 1
  ring

 theorem norm_velocityCoeff_critical (k : ι → ℤ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) (ha : gradient (action k H) a = 0) :
    ‖velocityCoeff k a‖ = ‖project k (gradLoop k hH a)‖ := by
  rw [gradient_action k hH, sub_eq_zero] at ha
  simp only [velocityCoeff, ha, norm_smul, Complex.norm_I, one_mul]

 theorem norm_project_grad (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hd : ∀ j, |d j| ≤ D)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ) :
    ‖project k (gradLoop k hH a)‖ ≤ B+2*D*‖a‖ := by
  have hb : ‖project k (remainderLoop k hH d a)‖ ≤ B :=
    project_bounded k hk _ hB (fun t => by rw [remainderLoop_apply]; exact hrem _)
  have he : project k (gradLoop k hH a) = project k (remainderLoop k hH d a) +
      (2 : ℝ) • diag (fun p => d p.2) a := by
    rw [remainderLoop, project_sub, project_loop k hk]
    abel
  have hn := norm_add_le (project k (remainderLoop k hH d a))
    ((2 : ℝ) • diag (fun p => d p.2) a)
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)] at hn
  have hdiag := norm_diag_upper (fun p : ι × κ => d p.2) hD (fun p => hd p.2) a
  nlinarith

 theorem intervalIntegral_eq_average {E : Type u113} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Time → E) : (∫ t in (0:ℝ)..1, f (t : Time)) = ∫ t : Time, f t ∂μ := by
  rw [AddCircle.integral_haarAddCircle]
  simpa only [zero_add, inv_one, one_smul] using AddCircle.intervalIntegral_preimage (1 : ℝ) 0 f

 theorem contDiff_meanAction {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (meanAction hH) := by
  have hg : ContDiff ℝ ∞ (fun z : Vector κ => inner (𝕜 := ℝ) (gradient H z) z/2-H z) :=
    (((contDiff_gradient_function hH).inner ℝ contDiff_id).div_const 2).sub hH
  exact average.contDiff.comp (SmoothPaths.contDiff_superpose hg)

 theorem critical_action_eq (k : ι → ℤ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) (ha : gradient (action k H) a = 0) :
    action k H a = meanAction hH (loop k a) := by
  have he : (2 : ℝ) • diag (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a = project k (gradLoop k hH a) := by
    simpa only [gradient_action k hH, sub_eq_zero] using ha
  have hi := integral_inner_loop k (gradLoop k hH a) a
  rw [← he, real_inner_smul_left, ← energy_eq_inner] at hi
  have hgi : Integrable (fun t : Time => inner (𝕜 := ℝ) (gradient H (loop k a t)) (loop k a t)) μ :=
    integrable_continuous ((gradLoop k hH a).continuous.inner (loop k a).continuous)
  have hpi : Integrable (fun t : Time => H (loop k a t)) μ :=
    integrable_continuous (hH.continuous.comp (loop k a).continuous)
  unfold meanAction
  rw [integral_sub (hgi.div_const 2) hpi, integral_div]
  change action k H a = (∫ t : Time, inner (𝕜 := ℝ) (gradLoop k hH a t) (loop k a t) ∂μ)/2-potential k H a
  rw [hi]
  unfold action
  ring

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_13_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

 theorem linkRadius_pos {M : ℝ} (hM : 0 ≤ M) : 0 < linkRadius κ M := by
  unfold linkRadius
  apply Real.sqrt_pos.2
  exact div_pos Real.pi_pos (by positivity)

 theorem linkRadius_sq {M : ℝ} (hM : 0 ≤ M) :
    (linkRadius κ M)^2 = Real.pi/(2*(M*(Fintype.card κ : ℝ)+1)) :=
  Real.sq_sqrt (by positivity)

 theorem linkLevel_pos {M : ℝ} (hM : 0 ≤ M) : 0 < linkLevel κ M := by
  unfold linkLevel
  exact mul_pos (div_pos Real.pi_pos (by norm_num)) (sq_pos_of_pos (linkRadius_pos hM))

 theorem linkLevel_bound {M : ℝ} (hM : 0 ≤ M) :
    2*linkLevel κ M ≤ Real.pi*(linkRadius κ M)^2-
      M*(Fintype.card κ : ℝ)*(linkRadius κ M)^4 := by
  have hden : 0 < 2*(M*(Fintype.card κ : ℝ)+1) := by positivity
  have he : 2*(M*(Fintype.card κ : ℝ)+1)*(linkRadius κ M)^2 = Real.pi := by
    rw [linkRadius_sq hM]
    field_simp
  have hr : 0 ≤ (linkRadius κ M)^2 := sq_nonneg _
  have hm : M*(Fintype.card κ : ℝ)*(linkRadius κ M)^2 ≤ Real.pi/2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hm hr
  unfold linkLevel
  nlinarith

 theorem exists_link_epsilon {a : ℝ} (ha : 0 < a) :
    ∃ ε > 0, ∀ s : ℝ, 0 < s → s < ε → Real.pi*s^2 ≤ a/2 := by
  let ε := Real.sqrt (a/(2*Real.pi))
  have hε : 0 < ε := Real.sqrt_pos.2 (div_pos ha (by positivity))
  have hεsq : ε^2 = a/(2*Real.pi) := Real.sq_sqrt (by positivity)
  refine ⟨ε,hε,fun s hs hse => ?_⟩
  have hs2 : s^2 ≤ ε^2 := pow_le_pow_left₀ hs.le hse.le 2
  have hm := mul_le_mul_of_nonneg_left hs2 Real.pi_pos.le
  rw [hεsq] at hm
  have hid : Real.pi*(a/(2*Real.pi)) = a/2 := by field_simp
  rwa [hid] at hm

 theorem exists_link_far {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (C : ℝ) :
    ∃ R : ℝ, ρ < R ∧ ∀ u s : ℝ, 0 ≤ u → R ≤ max u |s| → C-η*(u^2+s^2) ≤ 0 := by
  let R := max (ρ+1) (max 1 ((|C|+1)/η))
  have hR : ρ < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hR1 : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRc : (|C|+1)/η ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hReq : |C|+1 ≤ η*R := by
    have := (div_le_iff₀ hη).mp hRc
    linarith
  refine ⟨R,hR,fun u s _ hfar => ?_⟩
  have hsq : R^2 ≤ u^2+s^2 := by
    rcases le_max_iff.mp hfar with hy | hss
    · have := pow_le_pow_left₀ (by linarith : 0 ≤ R) hy 2
      nlinarith [sq_nonneg s]
    · have := pow_le_pow_left₀ (by linarith : 0 ≤ R) hss 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg u]
  have hh : R ≤ R^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left (hh.trans hsq) hη.le
  linarith [le_abs_self C]
 theorem finite_critical [DecidableEq ν] [DecidableEq κ]
    (k : ι → ℤ) (hk0 : ∀ i, k i ≤ 0) (l : ν → ℕ)
    (hl : Function.Injective l) (hl0 : ∀ i, 0 < l i)
    (hkl : Function.Injective (Sum.elim k (fun i => (l i : ℤ))))
    (i₀ : ν) (hl1 : l i₀ = 1) (j₀ : κ)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hH0 : ∀ z, 0 ≤ H z)
    (d₀ d : κ → ℝ) {C M η γ B : ℝ}
    (hM : 0 ≤ M) (hη : 0 < η) (hγ : 0 < γ) (hB : 0 ≤ B)
    (hup : ∀ z, H z ≤ M*‖z‖^4)
    (hd : ∀ j, η ≤ d₀ j) (hd0 : Real.pi+η ≤ d₀ j₀)
    (hlo : ∀ z, energy d₀ z-C ≤ H z)
    (hgap : ∀ i j, γ ≤ |Real.pi*((Sum.elim k (fun i => (l i : ℤ)) i : ℤ) : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) :
    ∃ x : Coeff (ι ⊕ ν) κ,
      linkLevel κ M ≤ action (Sum.elim k (fun i => (l i : ℤ))) H x ∧
      action (Sum.elim k (fun i => (l i : ℤ))) H x ≤ max C (linkLevel κ M) ∧
      gradient (action (Sum.elim k (fun i => (l i : ℤ))) H) x = 0 := by
  have ha : 0 < linkLevel κ M := linkLevel_pos hM
  have hρ : 0 < linkRadius κ M := linkRadius_pos hM
  obtain ⟨ε,hε,hnear⟩ := exists_link_epsilon ha
  obtain ⟨R,hR,hfar⟩ := exists_link_far hρ hη C
  let e : Coeff ν κ := PiLp.single 2 (i₀,j₀) (1 : ℂ)
  have he : ‖e‖ = 1 := by simp [e]
  apply FiniteLinking.exists_critical
    (H := Coeff (ι ⊕ ν) κ) (E := Coeff ι κ) (F := Coeff ν κ)
    (Φ := action (Sum.elim k (fun i => (l i : ℤ))) H)
    (positiveScale l hl0) (contDiff_action (Sum.elim k (fun i => (l i : ℤ))) hH) he ha
    (le_max_right _ _) hρ hε hR
  ·
    intro z hz
    have hb := action_positive_lower k l hl hl0 hH.continuous hM hup z
    rw [hz] at hb
    exact (linkLevel_bound hM).trans hb
  ·
    intro y s hs hse
    exact (action_cone_upper k hk0 l hl0 i₀ hl1 j₀ hH0 y s).trans (hnear s hs hse)
  ·
    intro y s _ hys
    have hs := hfar ‖y‖ s (norm_nonneg y) (by simpa only [Prod.norm_def, Real.norm_eq_abs] using hys)
    exact (action_cone_far k hk0 l hl0 hkl i₀ hl1 j₀ hH.continuous d₀ C η hd hd0 hlo y s).trans
      (hs.trans (by positivity))
  ·
    intro y s _ _
    have hnon : 0 ≤ η*(‖y‖^2+s^2) := mul_nonneg hη.le (add_nonneg (sq_nonneg _) (sq_nonneg _))
    exact (action_cone_far k hk0 l hl0 hkl i₀ hl1 j₀ hH.continuous d₀ C η hd hd0 hlo y s).trans
      ((sub_le_self C hnon).trans (le_max_left _ _))
  ·
    exact gradient_coercive _ hkl hH d hγ hB hgap hrem

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PeriodicFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u114 u115

section NonsqueezingInline

namespace L2Paths
noncomputable section
open Set intervalIntegral
open MeasureTheory (volume)
open scoped Topology BoundedContinuousFunction
variable {E : Type u114} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem integral_sq_le (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, f t)^2 ≤ (b-a)*(∫ t in a..b, (f t)^2) := by
  rcases hab.eq_or_lt with he | hab
  · subst b
    simp
  let avg := ∫ t in a..b, f t
  let L := b-a
  have hL : 0 < L := sub_pos.mpr hab
  have hnon : 0 ≤ ∫ t in a..b, (L*f t-avg)^2 :=
    integral_nonneg_of_forall hab.le (fun _ => sq_nonneg _)
  have he (t : ℝ) : (L*f t-avg)^2 = L^2*(f t)^2-(2*L*avg)*f t+avg^2 := by ring
  simp_rw [he] at hnon
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_const] at hnon
  · simp only [smul_eq_mul] at hnon
    change 0 ≤ L^2*(∫ t in a..b, (f t)^2)-(2*L*avg)*avg+L*avg^2 at hnon
    change avg^2 ≤ L*(∫ t in a..b, (f t)^2)
    nlinarith
  · exact (hf.pow 2).intervalIntegrable _ _ |>.const_mul _
  · exact hf.intervalIntegrable _ _ |>.const_mul _
  · exact (((hf.pow 2).const_mul _).sub (hf.const_mul _)).intervalIntegrable _ _
  · exact intervalIntegrable_const

 theorem norm_sub_sq_le (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {a b : ℝ} (hab : a ≤ b) :
    ‖x b-x a‖^2 ≤ (b-a)*(∫ t in a..b, ‖v t‖^2) := by
  have he := integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hv.intervalIntegrable a b)
  have hn : ‖x b-x a‖ ≤ ∫ t in a..b, ‖v t‖ := by
    rw [← he]
    exact norm_integral_le_integral_norm hab
  have hi := integral_sq_le (fun t => ‖v t‖) hv.norm hab
  have hs : ‖x b-x a‖^2 ≤ (∫ t in a..b, ‖v t‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact hs.trans hi

 theorem norm_sub_sq_le_global (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {D : ℝ}
    (hD : (∫ t in (0:ℝ)..1, ‖v t‖^2) ≤ D^2)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    ‖x b-x a‖^2 ≤ D^2*|b-a| := by
  wlog hab : a ≤ b generalizing a b
  · have h := this hb ha (le_of_not_ge hab)
    rwa [norm_sub_rev, abs_sub_comm] at h
  have hi := integral_mono_interval (μ := volume) ha.1 hab hb.2
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖v t‖)) ((hv.norm.pow 2).intervalIntegrable 0 1)
  have hc := norm_sub_sq_le x v hv hd hab
  have hm := mul_le_mul_of_nonneg_left (hi.trans hD) (sub_nonneg.mpr hab)
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  exact hc.trans (by nlinarith)

 theorem norm_bound (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hxm : (∫ t in (0:ℝ)..1, ‖x t‖^2) ≤ A^2)
    (hvm : (∫ t in (0:ℝ)..1, ‖v t‖^2) ≤ D^2)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖x t‖ ≤ A+D := by
  have hx : Continuous x := continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)
  have hpoint (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖x t‖ ≤ ‖x s‖+D := by
    have hdiff := norm_sub_sq_le_global x v hv hd hvm hs ht
    have hab : |t-s| ≤ 1 := (abs_le).mpr ⟨by linarith [ht.1,hs.2], by linarith [ht.2,hs.1]⟩
    have hmul := mul_le_mul_of_nonneg_left hab (sq_nonneg D)
    have hn : ‖x t-x s‖ ≤ D := by nlinarith [norm_nonneg (x t-x s)]
    have htri := norm_sub_le (x t-x s) (-x s)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
    linarith
  have hi : ∫ s in (0:ℝ)..1, ‖x t‖ ≤ ∫ s in (0:ℝ)..1, ‖x s‖+D :=
    integral_mono_on (by norm_num) intervalIntegrable_const
      ((hx.norm.add continuous_const).intervalIntegrable _ _) hpoint
  rw [integral_const, integral_add (hx.norm.intervalIntegrable _ _) intervalIntegrable_const,
    integral_const] at hi
  simp only [sub_zero, one_smul] at hi
  have hcs := integral_sq_le (fun s => ‖x s‖) hx.norm (show (0:ℝ) ≤ 1 by norm_num)
  simp only [sub_zero, one_mul] at hcs
  have hmean : ∫ t_1 in (0:ℝ)..1, ‖x t_1‖ ≤ A := by
    nlinarith [integral_nonneg_of_forall (μ := volume) (show (0:ℝ) ≤ 1 by norm_num) (fun s => norm_nonneg (x s))]
  linarith

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem exists_subsequence [ProperSpace E] (u : ℕ → C(Segment,E)) {D R : ℝ}
    (hmod : ∀ n (t s : Segment), dist (u n t) (u n s)^2 ≤ D^2*dist t s)
    (hbound : ∀ n (t : Segment), ‖u n t‖ ≤ R) :
    ∃ x : C(Segment,E), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 x) := by
  let eqv := ContinuousMap.isometryEquivBoundedOfCompact Segment E
  let v : ℕ → (Segment →ᵇ E) := fun n => eqv (u n)
  have heq : Equicontinuous ((↑) : Set.range v → Segment → E) := by
    apply UniformEquicontinuous.equicontinuous
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    refine ⟨ε^2/(D^2+1), by positivity, fun t s hts f => ?_⟩
    rcases f.property with ⟨n,hn⟩
    have hm := hmod n t s
    have hd : (D^2+1)*dist t s < ε^2 := by
      have := (lt_div_iff₀ (by positivity : 0 < D^2+1)).mp hts
      linarith
    rw [← hn]
    change dist (u n t) (u n s) < ε
    nlinarith [(dist_nonneg : 0 ≤ dist (u n t) (u n s)), (dist_nonneg : 0 ≤ dist t s)]
  have hc : IsCompact (closure (Set.range v)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:E) R)
      (isCompact_closedBall _ _) (Set.range v)
      (fun f t hf => by
        rcases hf with ⟨n,rfl⟩
        change dist (u n t) (0:E) ≤ R
        simpa only [dist_zero_right] using hbound n t) heq
  obtain ⟨x,hx,φ,hφ,ht⟩ := hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨eqv.symm x,φ,hφ,?_⟩
  exact eqv.symm.continuous.continuousAt.tendsto.comp ht

attribute [local instance] OAI.L2Paths.instFactLtRealOfNat_solutions
omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem restriction_isometry : Isometry (restriction (E := E)) := by
  rw [isometry_iff_dist_eq]
  intro x y
  apply le_antisymm
  · apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist x y)).2
    intro t
    exact ContinuousMap.dist_apply_le_dist (t.val : Time)
  · apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist (restriction x) (restriction y))).2
    intro t
    let r := AddCircle.equivIoc (1 : ℝ) 0 t
    have hr : r.val ∈ Set.Icc (0:ℝ) 1 := ⟨r.property.1.le, by simpa using r.property.2⟩
    have h := ContinuousMap.dist_apply_le_dist (f := restriction x) (g := restriction y) ⟨r.val,hr⟩
    simpa only [restriction, ContinuousMap.coe_mk, r, AddCircle.coe_equivIoc] using h

omit [NormedSpace ℝ E] in
 theorem exists_periodic_subsequence [ProperSpace E] (u : ℕ → C(Time,E)) {D R : ℝ}
    (hmod : ∀ n (t s : Segment), dist (u n (t.val : Time)) (u n (s.val : Time))^2 ≤ D^2*dist t s)
    (hbound : ∀ n (t : Segment), ‖u n (t.val : Time)‖ ≤ R) :
    ∃ x : C(Time,E), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 x) := by
  obtain ⟨x,φ,hφ,ht⟩ := exists_subsequence (fun n => restriction (u n)) hmod hbound
  have hc' : Cauchy (Filter.map restriction (Filter.map (u ∘ φ) Filter.atTop)) := by
    rw [Filter.map_map]
    exact ht.cauchySeq
  have hc : CauchySeq (u ∘ φ) :=
    restriction_isometry.isUniformInducing.cauchy_map_iff.mp hc'
  obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨y,φ,hφ,hy⟩

end
end L2Paths

namespace PeriodicFourier
noncomputable section
open MeasureTheory AddCircle Finset Set
open scoped ComplexConjugate Topology
open FourierPolynomial (integrable_continuous)

 attribute [local instance] OAI.PeriodicFourier.instFactLtRealOfNat_solutions
theorem coefficient_ext {f g : C(Time,ℂ)} (h : ∀ n, coefficient n f = coefficient n g) : f = g := by
  have hz (n : ℤ) : fourierCoeff (f-g) n = 0 := by
    change coefficient n (f-g) = 0
    rw [map_sub, h, sub_self]
  have hs : Summable (fourierCoeff (f-g)) := by
    simpa only [funext hz] using (summable_zero : Summable (fun _ : ℤ => (0:ℂ)))
  have hh := hasSum_fourier_series_of_summable hs
  simp only [hz, zero_smul] at hh
  have he : f-g = 0 := hh.unique hasSum_zero
  exact sub_eq_zero.mp he

 theorem coefficient_const (n : ℤ) (c : ℂ) :
    coefficient n (ContinuousMap.const Time c) = if n = 0 then c else 0 := by
  rw [coefficient_apply, fourierCoeff]
  simp only [ContinuousMap.coe_const, Function.const_apply, smul_eq_mul]
  rw [integral_mul_const, FourierPolynomial.integral_fourier]
  simp only [neg_eq_zero]
  split_ifs <;> simp

 theorem constant_of_nonzero_coeff {f : C(Time,ℂ)}
    (h : ∀ n : ℤ, n ≠ 0 → coefficient n f = 0) :
    f = ContinuousMap.const Time (coefficient 0 f) := by
  apply coefficient_ext
  intro n
  rw [coefficient_const]
  by_cases hn : n = 0
  · subst n; simp
  · simp [hn,h n hn]

 theorem coefficient_eq_on (f : C(Time,ℂ)) (n : ℤ) :
    fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun t : ℝ => f (t : Time)) n = coefficient n f := by
  rw [fourierCoeffOn_eq_integral, coefficient_apply, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp

 theorem derivative_coefficient (v : C(Time,ℂ)) (hzero : coefficient 0 v = 0)
    {n : ℤ} (hn : n ≠ 0) :
    (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)) * coefficient n (periodicPrimitive v hzero) = coefficient n v := by
  have hp := periodic_primitive v hzero
  have hi := fourierCoeffOn_of_hasDerivAt (show (0:ℝ) < 1 by norm_num) hn
    (fun t _ => hasDerivAt_primitive v t)
    ((v.continuous.comp continuous_quot_mk).intervalIntegrable 0 1)
  have ht : primitive v 1 = primitive v 0 := by simpa using hp 0
  simp only [ht, sub_self, mul_zero, Complex.ofReal_one, Complex.ofReal_zero, sub_zero, one_mul, zero_sub] at hi
  change fourierCoeffOn _ (fun t : ℝ => periodicPrimitive v hzero (t : Time)) n =
    1 / (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * -fourierCoeffOn _ (fun t : ℝ => v (t : Time)) n at hi
  rw [coefficient_eq_on, coefficient_eq_on] at hi
  rw [hi]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp

 theorem hasDerivAt_of_coefficients (x v : C(Time,ℂ))
    (h : ∀ n : ℤ, coefficient n v = (2*(Real.pi : ℂ)*Complex.I*(n : ℂ))*coefficient n x)
    (t : ℝ) : HasDerivAt (fun s : ℝ => x (s : Time)) (v (t : Time)) t := by
  have hz : coefficient 0 v = 0 := by simpa using h 0
  let y := periodicPrimitive v hz
  have hc : x-y = ContinuousMap.const Time (coefficient 0 (x-y)) := by
    apply constant_of_nonzero_coeff
    intro n hn
    rw [map_sub]
    have he := derivative_coefficient v hz hn
    rw [h n] at he
    have hn' : (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
      exact_mod_cast hn
    have heq := (mul_left_cancel₀ hn') he
    change coefficient n x-coefficient n (periodicPrimitive v hz) = 0
    exact sub_eq_zero.mpr heq.symm
  have hx (s : ℝ) : x (s : Time) = primitive v s+coefficient 0 (x-y) := by
    have he := congrArg (fun f : C(Time,ℂ) => f (s : Time)) hc
    change x (s : Time)-primitive v s = coefficient 0 (x-y) at he
    exact sub_eq_iff_eq_add'.mp he
  simpa only [← hx] using (hasDerivAt_primitive v t).add_const (coefficient 0 (x-y))

end
end PeriodicFourier

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PeriodicSolutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_14
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 theorem critical_H1_bounds (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B D : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hd : ∀ j, |d j| ≤ D)
    (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ)
    (ha : gradient (action k H) a = 0) :
    (∫ t in (0:ℝ)..1, ‖loop k a (t : Time)‖^2) ≤ (B/(2*γ))^2 ∧
    (∫ t in (0:ℝ)..1, ‖loop k (velocityCoeff k a) (t : Time)‖^2) ≤
      (B+2*D*(B/(2*γ)))^2 := by
  have hn := critical_norm_bound k hk hH d hγ hB hgap hrem a ha
  have hv := norm_project_grad k hk hH d hB hD hd hrem a
  rw [← norm_velocityCoeff_critical k hH a ha] at hv
  have hd' : 0 ≤ 2*D := mul_nonneg (by norm_num) hD
  have hvel : ‖velocityCoeff k a‖ ≤ B+2*D*(B/(2*γ)) :=
    hv.trans (by linarith [mul_le_mul_of_nonneg_left hn hd'])
  rw [intervalIntegral_eq_average (fun t : Time => ‖loop k a t‖^2),
    intervalIntegral_eq_average (fun t : Time => ‖loop k (velocityCoeff k a) t‖^2),
    integral_loop_norm_sq k hk, integral_loop_norm_sq k hk]
  exact ⟨pow_le_pow_left₀ (norm_nonneg _) hn 2, pow_le_pow_left₀ (norm_nonneg _) hvel 2⟩

 theorem critical_modulus (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B D : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hd : ∀ j, |d j| ≤ D)
    (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ)
    (ha : gradient (action k H) a = 0) (t s : L2Paths.Segment) :
    dist (loop k a (t.val : Time)) (loop k a (s.val : Time))^2 ≤
      (B+2*D*(B/(2*γ)))^2*dist t s := by
  have hb := (critical_H1_bounds k hk hH d hγ hB hD hd hgap hrem a ha).2
  have h := L2Paths.norm_sub_sq_le_global
    (fun t : ℝ => loop k a (t : Time)) (fun t : ℝ => loop k (velocityCoeff k a) (t : Time))
    ((loop k (velocityCoeff k a)).continuous.comp continuous_quot_mk)
    (hasDerivAt_loop k a) hb s.property t.property
  simpa only [dist_eq_norm, Subtype.dist_eq, Real.dist_eq, Real.norm_eq_abs] using h

 theorem critical_loop_bound (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B D : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hd : ∀ j, |d j| ≤ D)
    (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ)
    (ha : gradient (action k H) a = 0) (t : L2Paths.Segment) :
    ‖loop k a (t.val : Time)‖ ≤ B/(2*γ)+(B+2*D*(B/(2*γ))) := by
  have hb := critical_H1_bounds k hk hH d hγ hB hD hd hgap hrem a ha
  apply L2Paths.norm_bound
    (fun t : ℝ => loop k a (t : Time)) (fun t : ℝ => loop k (velocityCoeff k a) (t : Time))
    ((loop k (velocityCoeff k a)).continuous.comp continuous_quot_mk)
    (hasDerivAt_loop k a) (by positivity) (by positivity) hb.1 hb.2 t.property

 theorem critical_subsequence {α : ℕ → Type} [∀ n, Fintype (α n)]
    (k : (n : ℕ) → α n → ℤ) (hk : ∀ n, Function.Injective (k n))
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B D : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hd : ∀ j, |d j| ≤ D)
    (hgap : ∀ n i j, γ ≤ |Real.pi*(k n i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B)
    (a : (n : ℕ) → Coeff (α n) κ) (ha : ∀ n, gradient (action (k n) H) (a n) = 0) :
    ∃ x : C(Time,Vector κ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => loop (k (φ n)) (a (φ n))) atTop (𝓝 x) := by
  exact L2Paths.exists_periodic_subsequence (fun n => loop (k n) (a n))
    (fun n t s => critical_modulus (k n) (hk n) hH d hγ hB hD hd (hgap n) hrem (a n) (ha n) t s)
    (fun n t => critical_loop_bound (k n) (hk n) hH d hγ hB hD hd (hgap n) hrem (a n) (ha n) t)

 theorem contDiff_gradPath {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (gradPath hH) :=
   SmoothPaths.contDiff_superpose (contDiff_gradient_function hH)

 theorem critical_coefficient (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ)
    (ha : gradient (action k H) a = 0) (i : ι) (j : κ) :
    PeriodicFourier.coefficient (k i) (coordPath j (gradPath hH (loop k a))) =
      (2*(Real.pi : ℂ)*(k i : ℂ))*PeriodicFourier.coefficient (k i) (coordPath j (loop k a)) := by
  have he : (2 : ℝ) • diag (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a = project k (gradLoop k hH a) := by
    simpa only [gradient_action k hH, sub_eq_zero] using ha
  change project k (gradLoop k hH a) (i,j) = (2*(Real.pi : ℂ)*(k i : ℂ))*project k (loop k a) (i,j)
  rw [project_loop k hk, ← he]
  simp only [PiLp.smul_apply, diag_apply, RCLike.real_smul_eq_coe_mul, map_mul, map_intCast, map_ofNat]
  change (2:ℂ)*((Real.pi : ℂ)*(k i : ℂ)*a (i,j)) = (2*(Real.pi : ℂ)*(k i : ℂ))*a (i,j)
  ring

 theorem limit_coefficient {α : ℕ → Type} [∀ n, Fintype (α n)]
    (k : (n : ℕ) → α n → ℤ) (hk : ∀ n, Function.Injective (k n))
    (hex : ∀ m : ℤ, ∀ᶠ n in atTop, m ∈ Set.range (k n))
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : (n : ℕ) → Coeff (α n) κ) (ha : ∀ n, gradient (action (k n) H) (a n) = 0)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (x : C(Time,Vector κ))
    (ht : Tendsto (fun n => loop (k (φ n)) (a (φ n))) atTop (𝓝 x)) (m : ℤ) (j : κ) :
    PeriodicFourier.coefficient m (coordPath j (gradPath hH x)) =
      (2*(Real.pi : ℂ)*(m : ℂ))*PeriodicFourier.coefficient m (coordPath j x) := by
  have hg := (contDiff_gradPath hH).continuous.continuousAt.tendsto.comp ht
  have hc := (PeriodicFourier.coefficient m).continuous.comp (coordPath j).continuous
  have hleft := hc.continuousAt.tendsto.comp hg
  have hright := (tendsto_const_nhds (x := (2*(Real.pi : ℂ)*(m : ℂ)))).mul
    (hc.continuousAt.tendsto.comp ht)
  apply tendsto_nhds_unique_of_eventuallyEq hleft hright
  filter_upwards [hφ.tendsto_atTop.eventually (hex m)] with n hn
  rcases hn with ⟨i,rfl⟩
  exact critical_coefficient (k (φ n)) (hk (φ n)) hH (a (φ n)) (ha (φ n)) i j

 theorem hasDerivAt_of_critical_coefficients {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (x : C(Time,Vector κ))
    (h : ∀ m j, PeriodicFourier.coefficient m (coordPath j (gradPath hH x)) =
      (2*(Real.pi : ℂ)*(m : ℂ))*PeriodicFourier.coefficient m (coordPath j x)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x (s : Time)) (Complex.I • gradient H (x (t : Time))) t := by
  have hj (j : κ) : HasDerivAt (fun s : ℝ => x (s : Time) j)
      (Complex.I • gradient H (x (t : Time)) j) t := by
    have hc (m : ℤ) : PeriodicFourier.coefficient m (Complex.I • coordPath j (gradPath hH x)) =
        (2*(Real.pi : ℂ)*Complex.I*(m : ℂ))*PeriodicFourier.coefficient m (coordPath j x) := by
      rw [map_smul, h]
      simp only [smul_eq_mul]
      ring
    exact PeriodicFourier.hasDerivAt_of_coefficients (coordPath j x)
      (Complex.I • coordPath j (gradPath hH x)) hc t
  have hp := hasDerivAt_pi.mpr hj
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.hasFDerivAt.comp_hasDerivAt t hp

 theorem positive_action_limit {α : ℕ → Type} [∀ n, Fintype (α n)]
    (k : (n : ℕ) → α n → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : (n : ℕ) → Coeff (α n) κ) (ha : ∀ n, gradient (action (k n) H) (a n) = 0)
    {L : ℝ} (hL : ∀ n, L ≤ action (k n) H (a n))
    (φ : ℕ → ℕ) (x : C(Time,Vector κ))
    (ht : Tendsto (fun n => loop (k (φ n)) (a (φ n))) atTop (𝓝 x)) :
    L ≤ meanAction hH x := by
  apply ge_of_tendsto' ((contDiff_meanAction hH).continuous.continuousAt.tendsto.comp ht)
  intro n
  change L ≤ meanAction hH (loop (k (φ n)) (a (φ n)))
  rw [← critical_action_eq _ hH _ (ha (φ n))]
  exact hL (φ n)

end
end FourierPolynomial

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
open DiagonalQuadratic FourierPolynomial

 local instance instFactLtRealOfNat_solutions_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
theorem negativeMode_nonpos (N : ℕ) (i : Fin (N+1)) : negativeMode N i ≤ 0 := by
  simp [negativeMode]

 theorem positiveMode_pos (N : ℕ) (i : Fin (N+1)) : 0 < positiveMode N i := Nat.succ_pos _

 theorem positiveMode_injective (N : ℕ) : Function.Injective (positiveMode N) := by
  intro i j hij
  apply Fin.ext
  simpa [positiveMode] using hij

 theorem frequency_injective (N : ℕ) : Function.Injective (frequency N) := by
  intro i j hij
  cases i <;> cases j
  · simp only [frequency, Sum.elim_inl, negativeMode, neg_inj, Nat.cast_inj] at hij
    exact congrArg Sum.inl (Fin.ext hij)
  · simp only [frequency, Sum.elim_inl, Sum.elim_inr, negativeMode, positiveMode, Nat.cast_add, Nat.cast_one] at hij
    omega
  · simp only [frequency, Sum.elim_inl, Sum.elim_inr, negativeMode, positiveMode, Nat.cast_add, Nat.cast_one] at hij
    omega
  · simp only [frequency, Sum.elim_inr, Nat.cast_inj] at hij
    exact congrArg Sum.inr (positiveMode_injective N hij)

 theorem frequency_exhausts (m : ℤ) : ∀ᶠ N in atTop, m ∈ Set.range (frequency N) := by
  cases m with
  | ofNat m =>
    cases m with
    | zero =>
      filter_upwards [] with N
      exact ⟨Sum.inl ⟨0,Nat.succ_pos N⟩, by simp [frequency,negativeMode]⟩
    | succ m =>
      filter_upwards [eventually_ge_atTop m] with N hN
      exact ⟨Sum.inr ⟨m,by omega⟩, by simp [frequency,positiveMode]⟩
  | negSucc m =>
    filter_upwards [eventually_ge_atTop (m+1)] with N hN
    exact ⟨Sum.inl ⟨m+1,by omega⟩, by simp [frequency,negativeMode,Int.negSucc_eq]⟩

 variable {κ : Type} [Fintype κ] [DecidableEq κ]

 theorem exists_positive_periodic
    (j₀ : κ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hH0 : ∀ z, 0 ≤ H z)
    (d₀ d : κ → ℝ) {C M η γ B D : ℝ}
    (hM : 0 ≤ M) (hη : 0 < η) (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hup : ∀ z, H z ≤ M*‖z‖^4)
    (hd : ∀ j, η ≤ d₀ j) (hd0 : Real.pi+η ≤ d₀ j₀)
    (hlo : ∀ z, energy d₀ z-C ≤ H z) (hdD : ∀ j, |d j| ≤ D)
    (hgap : ∀ m : ℤ, ∀ j, γ ≤ |Real.pi*(m : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) :
    ∃ x : C(Time,Vector κ), 0 < meanAction hH x ∧
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => x (s : Time))
        (Complex.I • gradient H (x (t : Time))) t := by
  have he (N : ℕ) := finite_critical (negativeMode N) (negativeMode_nonpos N)
    (positiveMode N) (positiveMode_injective N) (positiveMode_pos N) (frequency_injective N)
    (⟨0,Nat.succ_pos N⟩ : Fin (N+1)) rfl j₀ hH hH0 d₀ d hM hη hγ hB hup hd hd0 hlo
    (fun i j => hgap (frequency N i) j) hrem
  choose a ha hupper hz using he
  obtain ⟨x,φ,hφ,ht⟩ := critical_subsequence frequency frequency_injective hH d hγ hB hD hdD
    (fun n i j => hgap (frequency n i) j) hrem a hz
  refine ⟨x,lt_of_lt_of_le (linkLevel_pos hM) (positive_action_limit frequency hH a hz ha φ x ht),?_⟩
  exact hasDerivAt_of_critical_coefficients hH x
    (limit_coefficient frequency frequency_injective frequency_exhausts hH a hz φ hφ x ht)

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HamiltonianODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u116 u117 u118

section NonsqueezingInline

namespace HamiltonianODE
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
open FourierPolynomial DiagonalQuadratic
local instance instFactLtRealOfNat_solutions_rc74a79_2 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {κ : Type u116} [Fintype κ]

 theorem inner_I_self (z : Vector κ) : inner (𝕜 := ℝ) z (Complex.I • z) = 0 := by
  rw [real_inner_eq_complex_re, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [pow_two]

 theorem inner_I_left (z w : Vector κ) :
    inner (𝕜 := ℝ) (Complex.I • z) w = -inner (𝕜 := ℝ) z (Complex.I • w) := by
  simp only [real_inner_eq_complex_re, inner_smul_left, inner_smul_right]
  simp [Complex.mul_re]

 theorem inner_I_I (z w : Vector κ) :
    inner (𝕜 := ℝ) (Complex.I • z) (Complex.I • w) = inner (𝕜 := ℝ) z w := by
  rw [inner_I_left, smul_smul]
  simp

 theorem zero_derivative_constant {E : Type u117} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℝ → E} (hx : ∀ t, HasDerivAt x 0 t) (s t : ℝ) : x s = x t := by
  exact is_const_of_deriv_eq_zero (fun t => (hx t).differentiableAt) (fun t => (hx t).deriv) s t

 theorem energy_constant {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t) (s t : ℝ) : H (x s) = H (x t) := by
  apply zero_derivative_constant (x := H ∘ x) _ s t
  intro u
  have hh := ((hH.differentiable (by simp) (x u)).hasGradientAt.hasFDerivAt).comp_hasDerivAt u (hx u)
  simpa only [InnerProductSpace.toDual_apply_apply, inner_I_self] using hh

 theorem quadratic_constant (d : κ → ℝ) {a : ℝ → ℝ} {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • ((2*a t) • diag d (x t))) t) (s t : ℝ) :
    energy d (x s) = energy d (x t) := by
  apply zero_derivative_constant (x := energy d ∘ x) _ s t
  intro u
  have hh := (hasGradientAt_energy d (x u)).hasFDerivAt.comp_hasDerivAt u (hx u)
  simpa only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left, smul_comm Complex.I (2*a u),
    real_inner_smul_right, inner_I_self, mul_zero] using hh

 theorem linear_solution {x : ℝ → ℂ} (v : ℂ)
    (hx : ∀ t, HasDerivAt x (v*x t) t) (t : ℝ) :
    x t = Complex.exp (v*(t : ℂ))*x 0 := by
  have hd (s : ℝ) : HasDerivAt (fun u : ℝ => Complex.exp (-v*(u : ℂ))*x u) 0 s := by
    have he := ((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (-v)).cexp
    have hh := he.mul (hx s)
    apply hh.congr_deriv
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
    ring
  have hc := zero_derivative_constant hd t 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hc
  have he := congrArg (fun z : ℂ => Complex.exp (v*(t:ℂ))*z) hc
  rw [← mul_assoc, ← Complex.exp_add] at he
  have hz : v*(t:ℂ)+ -v*(t:ℂ) = 0 := by ring
  simpa only [hz, Complex.exp_zero, one_mul] using he

 theorem periodic_frequency {x : ℝ → ℂ} (a : ℝ)
    (hx : ∀ t, HasDerivAt x ((2*(a:ℂ)*Complex.I)*x t) t)
    (hp : x 1 = x 0) (hzero : x 0 ≠ 0) : ∃ m : ℤ, a = Real.pi*m := by
  have he := linear_solution (2*(a:ℂ)*Complex.I) hx 1
  rw [Complex.ofReal_one, mul_one, hp] at he
  have hh : Complex.exp (2*(a:ℂ)*Complex.I) = 1 := by
    apply mul_right_cancel₀ hzero
    simpa only [one_mul] using he.symm
  obtain ⟨m,hm⟩ := Complex.exp_eq_one_iff.mp hh
  refine ⟨m,?_⟩
  have hi := congrArg Complex.im hm
  simp [Complex.mul_im, Complex.mul_re] at hi
  linarith

 theorem slow_linear_constant {x : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (haπ : a < Real.pi)
    (hx : ∀ t, HasDerivAt x ((2*(a:ℂ)*Complex.I)*x t) t)
    (hp : x 1 = x 0) (t : ℝ) : x t = x 0 := by
  by_cases hz : x 0 = 0
  · simp only [linear_solution _ hx t, hz, mul_zero]
  obtain ⟨m,hm⟩ := periodic_frequency a hx hp hz
  have hm0 : 0 ≤ m := by
    have : 0 ≤ (m:ℝ) := (mul_nonneg_iff_of_pos_left Real.pi_pos).mp (hm ▸ ha)
    exact_mod_cast this
  have hm1 : m < 1 := by
    have : (m:ℝ) < 1 := (mul_lt_mul_iff_right₀ Real.pi_pos).mp (by simpa [mul_comm] using hm ▸ haπ)
    exact_mod_cast this
  have hmz : m = 0 := by omega
  have haz : a = 0 := by simp [hm,hmz]
  simp only [linear_solution _ hx t, haz, Complex.ofReal_zero, mul_zero, zero_mul,
    Complex.exp_zero, one_mul]

end
end HamiltonianODE

namespace HamiltonianODE
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic
variable {κ : Type u118} [Fintype κ]

 theorem energy_one (z : Vector κ) : energy (fun _ => 1) z = ‖z‖^2 := by
   simp only [energy, one_mul, EuclideanSpace.norm_sq_eq]

 theorem gradient_comp_energy (d : κ → ℝ) {f : ℝ → ℝ} {v : ℝ} (z : Vector κ)
    (hf : HasDerivAt f v (energy d z)) :
    gradient (fun w => f (energy d w)) z = (2*v) • diag d z := by
   apply HasGradientAt.gradient
   rw [hasGradientAt_iff_hasFDerivAt]
   have h := hf.comp_hasFDerivAt z (hasGradientAt_energy d z).hasFDerivAt
   apply h.congr_fderiv
   ext w
   change v * inner (𝕜 := ℝ) ((2 : ℝ) • diag d z) w =
     inner (𝕜 := ℝ) ((2*v) • diag d z) w
   simp only [real_inner_smul_left]
   ring

 theorem coordinate_derivative (d : κ → ℝ) (v : ℝ) {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • ((2*v) • diag d (x t))) t) (j : κ) (t : ℝ) :
    HasDerivAt (fun s => x s j) ((2*((v*d j : ℝ):ℂ)*Complex.I)*x t j) t := by
   have h := (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : κ => ℂ) j).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt t (hx t)
   apply h.congr_deriv
   change Complex.I * ((2*v) • (d j • x t j)) = (2*((v*d j : ℝ):ℂ)*Complex.I)*x t j
   simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
   ring

 theorem slow_diagonal_constant (d : κ → ℝ) (v : ℝ)
    (hv : ∀ j, 0 ≤ v*d j) (hvπ : ∀ j, v*d j < Real.pi)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • ((2*v) • diag d (x t))) t)
    (hp : x 1 = x 0) (t : ℝ) : x t = x 0 := by
   ext j
   exact slow_linear_constant (hv j) (hvπ j) (coordinate_derivative d v hx j)
     (congrArg (fun z : Vector κ => z j) hp) t

 theorem slow_radial_constant {f v : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (v s) s)
    (hv : ∀ s, 0 ≤ v s) (hvπ : ∀ s, v s < Real.pi)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient (fun z : Vector κ => f (‖z‖^2)) (x t)) t)
    (hp : x 1 = x 0) (t : ℝ) : x t = x 0 := by
   have he (s : ℝ) : gradient (fun z : Vector κ => f (‖z‖^2)) (x s) =
       (2*v (‖x s‖^2)) • diag (fun _ => 1) (x s) := by
     simpa only [energy_one] using gradient_comp_energy (fun _ => 1) (x s) (hf (energy (fun _ => 1) (x s)))
   have hode (s : ℝ) := (hx s).congr_deriv (congrArg (fun z : Vector κ => Complex.I • z) (he s))
   have hc (s : ℝ) : ‖x s‖^2 = ‖x 0‖^2 := by
     simpa only [energy_one] using quadratic_constant (fun _ => 1) hode s 0
   apply slow_diagonal_constant (fun _ => 1) (v (‖x 0‖^2)) (by simpa only [mul_one] using fun _ : κ => hv (‖x 0‖^2))
     (by simpa only [mul_one] using fun _ : κ => hvπ (‖x 0‖^2)) _ hp t
   intro s
   simpa only [hc s] using hode s

 theorem moderate_linear_either {x : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (ha2π : a < 2*Real.pi)
    (hx : ∀ t, HasDerivAt x ((2*(a:ℂ)*Complex.I)*x t) t)
    (hp : x 1 = x 0) : a = Real.pi ∨ ∀ t, x t = x 0 := by
   by_cases hz : x 0 = 0
   · exact Or.inr (fun t => by simp only [linear_solution _ hx t,hz,mul_zero])
   obtain ⟨m,hm⟩ := periodic_frequency a hx hp hz
   have hm0 : 0 ≤ m := by
     have : 0 ≤ (m:ℝ) := (mul_nonneg_iff_of_pos_left Real.pi_pos).mp (hm ▸ ha)
     exact_mod_cast this
   have hm2 : m < 2 := by
     have : (m:ℝ) < 2 := by nlinarith [Real.pi_pos]
     exact_mod_cast this
   have he : m = 0 ∨ m = 1 := by omega
   rcases he with he | he
   · have haz : a = 0 := by simp [hm,he]
     exact Or.inr (fun t => by simp only [linear_solution _ hx t,haz,Complex.ofReal_zero,
       mul_zero,zero_mul,Complex.exp_zero,one_mul])
   · exact Or.inl (by simpa [he] using hm)

 theorem diagonal_either (j₀ : κ) (d : κ → ℝ) {v : ℝ}
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hd : ∀ j, 0 ≤ d j)
    (hdπ : ∀ j, j ≠ j₀ → d j < Real.pi) (hd2π : d j₀ < 2*Real.pi)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • ((2*v) • diag d (x t))) t)
    (hp : x 1 = x 0) : v*d j₀ = Real.pi ∨ ∀ t, x t = x 0 := by
   have hvd (j : κ) : v*d j ≤ d j := by nlinarith [hd j]
   rcases moderate_linear_either (mul_nonneg hv (hd j₀)) (lt_of_le_of_lt (hvd j₀) hd2π)
     (coordinate_derivative d v hx j₀) (congrArg (fun z : Vector κ => z j₀) hp) with he | he
   · exact Or.inl he
   · right
     intro t
     ext j
     by_cases hj : j = j₀
     · subst j; exact he t
     · exact slow_linear_constant (mul_nonneg hv (hd j)) (lt_of_le_of_lt (hvd j) (hdπ j hj))
         (coordinate_derivative d v hx j) (congrArg (fun z : Vector κ => z j) hp) t

end
end HamiltonianODE

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HamiltonianGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u119 u120

section NonsqueezingInline

namespace HamiltonianGrowth
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE
variable {κ : Type u119} [Fintype κ]

 theorem contDiff_gradient {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (gradient H) :=
   (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.contDiff.comp
     (hH.fderiv_right (by simp))

 theorem gradient_translate {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (p z : Vector κ) :
    gradient (fun w => H (w+p)) z = gradient H (z+p) := by
   apply HasGradientAt.gradient
   rw [hasGradientAt_iff_hasFDerivAt]
   have hh := ((hH.differentiable (by simp) (z+p)).hasGradientAt.hasFDerivAt).comp z
       ((hasFDerivAt_id z).add_const p)
   convert! hh using 1

 theorem energy_upper (d : κ → ℝ) (D : ℝ) (hd : ∀ j, d j ≤ D) (z : Vector κ) :
    energy d z ≤ D*‖z‖^2 := by
   simp only [energy, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
   exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hd j) (sq_nonneg _))

 theorem energy_sub_uniform (d : κ → ℝ) (η : ℝ) (z : Vector κ) :
    energy (fun j => d j-η) z = energy d z-η*‖z‖^2 := by
   simp only [energy, sub_mul, Finset.sum_sub_distrib, EuclideanSpace.norm_sq_eq, Finset.mul_sum]

 theorem quadratic_error {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (h0 : H 0 = 0)
    (d : κ → ℝ) {B : ℝ} (hb : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (z : Vector κ) :
    |H z-energy d z| ≤ B*‖z‖ := by
   have hr (w : Vector κ) : HasGradientAt (fun v => H v-energy d v)
       (gradient H w-(2 : ℝ) • diag d w) w := by
     rw [hasGradientAt_iff_hasFDerivAt]
     have hh := ((hH.differentiable (by simp) w).hasGradientAt.hasFDerivAt).sub
       (hasGradientAt_energy d w).hasFDerivAt
     convert! hh using 1
     ext v
     change inner (𝕜 := ℝ) (gradient H w-(2 : ℝ) • diag d w) v =
       inner (𝕜 := ℝ) (gradient H w) v-inner (𝕜 := ℝ) ((2 : ℝ) • diag d w) v
     exact inner_sub_left _ _ _
   have bound (w : Vector κ) : ‖fderiv ℝ (fun v => H v-energy d v) w‖ ≤ B := by
     rw [(hr w).hasFDerivAt.fderiv]
     simpa only [LinearIsometryEquiv.norm_map] using hb w
   have hm := (convex_univ : Convex ℝ (univ : Set (Vector κ))).norm_image_sub_le_of_norm_fderiv_le
     (fun w _ => (hr w).hasFDerivAt.differentiableAt) (fun w _ => bound w)
     (mem_univ (0 : Vector κ)) (mem_univ z)
   simpa [h0, energy] using hm

 theorem quartic_bound {H : Vector κ → ℝ} {A B r : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r)
    (hz : ∀ z, ‖z‖ < r → H z = 0) (hu : ∀ z, H z ≤ A*‖z‖^2+B*‖z‖) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, H z ≤ M*‖z‖^4 := by
   refine ⟨A/r^2+B/r^3, by positivity, ?_⟩
   intro z
   by_cases hzr : ‖z‖ < r
   · rw [hz z hzr]; positivity
   have hnr : r ≤ ‖z‖ := le_of_not_gt hzr
   have h2 : r^2*‖z‖^2 ≤ ‖z‖^4 := by
     have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hnr 2) (sq_nonneg ‖z‖)
     nlinarith only [this]
   have h3 : r^3*‖z‖ ≤ ‖z‖^4 := by
     have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hnr 3) (norm_nonneg z)
     nlinarith only [this]
   have ha : A*‖z‖^2 ≤ (A/r^2)*‖z‖^4 := by
     rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr 2)]
     nlinarith only [mul_le_mul_of_nonneg_left h2 hA]
   have hb : B*‖z‖ ≤ (B/r^3)*‖z‖^4 := by
     rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr 3)]
     nlinarith only [mul_le_mul_of_nonneg_left h3 hB]
   calc
     H z ≤ A*‖z‖^2+B*‖z‖ := hu z
     _ ≤ (A/r^2+B/r^3)*‖z‖^4 := by nlinarith only [ha,hb]

 theorem lower_bound {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (h0 : H 0 = 0)
    (d : κ → ℝ) {B η : ℝ} (hη : 0 < η)
    (hb : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (z : Vector κ) :
    energy (fun j => d j-η) z-B^2/(4*η) ≤ H z := by
   have he := (abs_le.mp (quadratic_error hH h0 d hb z)).1
   have hc : (4*η)*(B^2/(4*η)) = B^2 := by field_simp
   rw [energy_sub_uniform]
   nlinarith [sq_nonneg (2*η*‖z‖-B)]

 theorem bounded_remainder_translate {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (d : κ → ℝ) {B : ℝ} (hb : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B)
    (p z : Vector κ) :
    ‖gradient (fun w => H (w+p)) z-(2 : ℝ) • diag d z‖ ≤ B+‖(2 : ℝ) • diag d p‖ := by
   rw [gradient_translate hH]
   have hd : diag d (z+p) = diag d z+diag d p := (diagCLM d).map_add z p
   have he : gradient H (z+p)-(2 : ℝ) • diag d z =
       (gradient H (z+p)-(2 : ℝ) • diag d (z+p))+(2 : ℝ) • diag d p := by
     rw [hd, smul_add]; abel
   rw [he]
   have hh := norm_add_le (gradient H (z+p)-(2 : ℝ) • diag d (z+p)) ((2 : ℝ) • diag d p)
   linarith [hb (z+p)]

 theorem bound_remainder_of_compact {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (d : κ → ℝ) {S : Set (Vector κ)} (hS : IsCompact S)
    (he : ∀ z ∉ S, gradient H z = (2 : ℝ) • diag d z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B := by
   have hc : Continuous (fun z => gradient H z-(2 : ℝ) • diag d z) :=
     (contDiff_gradient hH).continuous.sub ((diagCLM d).continuous.const_smul (2 : ℝ))
   obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
   refine ⟨max B 0,le_max_right _ _,?_⟩
   intro z
   by_cases hz : z ∈ S
   · exact (hB z hz).trans (le_max_left _ _)
   · rw [he z hz, sub_self, norm_zero]
     exact le_max_right _ _

end
end HamiltonianGrowth

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth
variable {κ : Type u120} [Fintype κ]

 theorem integral_gradient_pairing {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    {x : ℝ → Vector κ} (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t)
    (hp : x 1 = x 0) (p : Vector κ) :
    (∫ t in (0:ℝ)..1, inner (𝕜 := ℝ) (gradient H (x t)) p) = 0 := by
   have hc : Continuous x := continuous_iff_continuousAt.mpr (fun t => (hx t).continuousAt)
   have hi : IntervalIntegrable (fun t => inner (𝕜 := ℝ) (gradient H (x t)) p) volume 0 1 :=
     (((contDiff_gradient hH).continuous.comp hc).inner continuous_const).intervalIntegrable 0 1
   have hd (t : ℝ) : HasDerivAt (fun s => inner (𝕜 := ℝ) (x s) (Complex.I • p))
       (inner (𝕜 := ℝ) (gradient H (x t)) p) t := by
     simpa only [inner_zero_right, add_zero, zero_add, inner_I_I] using
       (hx t).inner ℝ (hasDerivAt_const t (Complex.I • p))
   have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
   simpa only [hp, sub_self] using he

 theorem action_translate {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (p : Vector κ)
    {y : ℝ → Vector κ}
    (hy : ∀ t, HasDerivAt y (Complex.I • gradient (fun z => H (z+p)) (y t)) t)
    (hp : y 1 = y 0) :
    actionIntegral H (fun t => y t+p) = actionIntegral (fun z => H (z+p)) y := by
   have hc : Continuous y := continuous_iff_continuousAt.mpr (fun t => (hy t).continuousAt)
   have hxt (t : ℝ) : HasDerivAt (fun s => y s+p) (Complex.I • gradient H (y t+p)) t := by
     simpa only [gradient_translate hH] using (hy t).add_const p
   have hz := integral_gradient_pairing hH hxt (by simp only [hp]) p
   have hg : Continuous (fun t => gradient H (y t+p)) :=
     (contDiff_gradient hH).continuous.comp (hc.add continuous_const)
   have hi1 : IntervalIntegrable (fun t => inner (𝕜 := ℝ) (gradient H (y t+p)) (y t)/2-H (y t+p)) volume 0 1 :=
     (((hg.inner hc).div_const 2).sub (hH.continuous.comp (hc.add continuous_const))).intervalIntegrable _ _
   have hi2 : IntervalIntegrable (fun t => inner (𝕜 := ℝ) (gradient H (y t+p)) p/2) volume 0 1 :=
     ((hg.inner continuous_const).div_const 2).intervalIntegrable _ _
   unfold actionIntegral
   simp_rw [gradient_translate hH]
   have he (t : ℝ) : inner (𝕜 := ℝ) (gradient H (y t+p)) (y t+p)/2-H (y t+p) =
       (inner (𝕜 := ℝ) (gradient H (y t+p)) (y t)/2-H (y t+p))+
       inner (𝕜 := ℝ) (gradient H (y t+p)) p/2 := by rw [inner_add_right]; ring
   simp_rw [he]
   rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_div, hz, zero_div, add_zero]

end
end HamiltonianPeriodic

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth
variable {κ : Type} [Fintype κ] [DecidableEq κ]

 theorem exists_positive_flat (j₀ : κ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (hH0 : ∀ z, 0 ≤ H z)
    (hflat : ∀ᶠ z in 𝓝 (0 : Vector κ), H z = 0)
    (d : κ → ℝ) {η γ B D : ℝ}
    (hη : 0 < η) (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hd : ∀ j, 2*η ≤ d j) (hd0 : Real.pi+2*η ≤ d j₀) (hdD : ∀ j, |d j| ≤ D)
    (hgap : ∀ m : ℤ, ∀ j, γ ≤ |Real.pi*(m : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) :
    ∃ x : ℝ → Vector κ, x 1 = x 0 ∧ 0 < actionIntegral H x ∧
      ∀ t : ℝ, HasDerivAt x (Complex.I • gradient H (x t)) t := by
   have h0 := hflat.self_of_nhds
   obtain ⟨r,hr,hzr⟩ := Metric.eventually_nhds_iff.mp hflat
   have hu (z : Vector κ) : H z ≤ D*‖z‖^2+B*‖z‖ := by
     have he := (abs_le.mp (quadratic_error hH h0 d hrem z)).2
     have hd' := energy_upper d D (fun j => (le_abs_self _).trans (hdD j)) z
     linarith
   obtain ⟨M,hM,hup⟩ := quartic_bound hD hB hr (fun z hz => hzr (by simpa only [dist_zero_right] using hz)) hu
   obtain ⟨x,ha,hx⟩ := exists_positive_periodic j₀ hH hH0 (fun j => d j-η) d hM hη hγ hB hD hup
     (fun j => by linarith [hd j]) (by linarith)
     (lower_bound hH h0 d hη hrem) hdD hgap hrem
   refine ⟨fun t => x (t : Time),?_,?_,hx⟩
   · simp only [AddCircle.coe_period, AddCircle.coe_zero]
   · change 0 < ∫ t in (0:ℝ)..1, (fun s : Time => inner (𝕜 := ℝ) (gradient H (x s)) (x s)/2-H (x s)) (t : Time)
     have he := intervalIntegral_eq_average (fun s : Time => inner (𝕜 := ℝ) (gradient H (x s)) (x s)/2-H (x s))
     exact he.symm ▸ ha

 theorem exists_positive_at_flat_point (j₀ : κ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (hH0 : ∀ z, 0 ≤ H z) (p : Vector κ)
    (hflat : ∀ᶠ z in 𝓝 p, H z = 0)
    (d : κ → ℝ) {η γ B D : ℝ}
    (hη : 0 < η) (hγ : 0 < γ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hd : ∀ j, 2*η ≤ d j) (hd0 : Real.pi+2*η ≤ d j₀) (hdD : ∀ j, |d j| ≤ D)
    (hgap : ∀ m : ℤ, ∀ j, γ ≤ |Real.pi*(m : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) :
    ∃ x : ℝ → Vector κ, x 1 = x 0 ∧ 0 < actionIntegral H x ∧
      ∀ t : ℝ, HasDerivAt x (Complex.I • gradient H (x t)) t := by
   have ht : ContDiff ℝ ∞ (fun z : Vector κ => H (z+p)) := hH.comp (contDiff_id.add contDiff_const)
   have hz : ∀ᶠ z in 𝓝 (0 : Vector κ), H (z+p) = 0 := by
     have hc : Tendsto (fun z : Vector κ => z+p) (𝓝 0) (𝓝 p) := by
       have hc : Continuous (fun z : Vector κ => z+p) := continuous_id.add continuous_const
       have hc0 : Tendsto (fun z : Vector κ => z+p) (𝓝 0) (𝓝 ((0 : Vector κ)+p)) := hc.continuousAt
       simpa only [zero_add] using hc0
     exact hc.eventually hflat
   obtain ⟨y,hp,ha,hy⟩ := exists_positive_flat j₀ ht (fun z => hH0 (z+p)) hz d hη hγ
     (add_nonneg hB (norm_nonneg _)) hD hd hd0 hdD hgap (bounded_remainder_translate hH d hrem p)
   refine ⟨fun t => y t+p,by simp only [hp],?_,?_⟩
   · rw [action_translate hH p hy hp]
     exact ha
   · intro t
     simpa only [gradient_translate hH] using (hy t).add_const p

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.EmbeddingInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u121 u122

section NonsqueezingInline

namespace EmbeddingInverse
noncomputable section
open Set Filter
open scoped ContDiff Topology
variable {E : Type u121} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem contDiffAt_inverse (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source)
    (hD : ∀ x ∈ e.source, (fderiv ℝ e x).IsInvertible)
    {y : E} (hy : y ∈ e.target) : ContDiffAt ℝ ∞ e.symm y := by
  have hs := he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))
  obtain ⟨D,hD⟩ := hD _ (e.map_target hy)
  apply e.contDiffAt_symm hy (f₀' := D) _ hs
  rw [hD]
  exact (hs.differentiableAt (by simp)).hasFDerivAt

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem extendFunction_apply (e : OpenPartialHomeomorph E E) (f : E → ℝ)
    {x : E} (hx : x ∈ e.source) : extendFunction e f (e x) = f x := by
  simp only [extendFunction, ite_eq_left (e.map_source hx), e.left_inv hx]

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem extendFunction_zero (e : OpenPartialHomeomorph E E) (f : E → ℝ)
    (S : Set E) (hz : ∀ x ∉ S, f x = 0) {y : E} (hy : y ∉ e '' S) :
    extendFunction e f y = 0 := by
  unfold extendFunction
  split_ifs with hyt
  · apply hz
    intro hin
    exact hy ⟨e.symm y,hin,e.right_inv hyt⟩
  · rfl

 theorem contDiff_extendFunction (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source)
    (hD : ∀ x ∈ e.source, (fderiv ℝ e x).IsInvertible)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {S : Set E} (hS : IsCompact S)
    (hSU : S ⊆ e.source) (hz : ∀ x ∉ S, f x = 0) :
    ContDiff ℝ ∞ (extendFunction e f) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ e.target
  · apply (hf.contDiffAt.comp y (contDiffAt_inverse e he hD hy)).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    simp only [extendFunction, hz, ite_true, Function.comp_apply]
  · have hT : IsClosed (e '' S) := (hS.image_of_continuousOn (e.continuousOn.mono hSU)).isClosed
    have hyt : y ∈ (e '' S)ᶜ := by
      rintro ⟨x,hx,rfl⟩
      exact hy (e.map_source (hSU hx))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hT.isOpen_compl.mem_nhds hyt] with z hz'
    exact extendFunction_zero e f S hz hz'

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem extendFunction_mem_range (e : OpenPartialHomeomorph E E) (f : E → ℝ) (y : E) :
    extendFunction e f y = 0 ∨ ∃ x ∈ e.source, extendFunction e f y = f x := by
  by_cases hy : y ∈ e.target
  · exact Or.inr ⟨e.symm y,e.map_target hy, by simp only [extendFunction,hy,ite_true]⟩
  · exact Or.inl (by simp only [extendFunction,hy,ite_false])

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem eventually_of_comp (e : OpenPartialHomeomorph E E) {x : E} (hx : x ∈ e.source)
    {P : E → Prop} (hP : ∀ᶠ z in 𝓝 x, P (e z)) : ∀ᶠ y in 𝓝 (e x), P y := by
   rw [← e.map_nhds_eq hx]
   exact hP

end
end EmbeddingInverse

namespace ComplexSymplectic
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial HamiltonianODE
variable {κ : Type u122} [Fintype κ]

 theorem form_ext {v w : Vector κ} (h : ∀ z, form v z = form w z) : v = w := by
   exact smul_right_injective _ Complex.I_ne_zero (ext_inner_right ℝ h)

 theorem form_I (v w : Vector κ) : form (Complex.I • v) w = -inner (𝕜 := ℝ) v w := by
   simp [form, smul_smul]

 theorem injective {A : Vector κ →L[ℝ] Vector κ} (hA : Preserves A) : Function.Injective A := by
   intro v w hvw
   apply form_ext
   intro z
   calc
     form v z = form (A v) (A z) := (hA v z).symm
     _ = form (A w) (A z) := by rw [hvw]
     _ = form w z := hA w z

 theorem invertible {A : Vector κ →L[ℝ] Vector κ} (hA : Preserves A) : A.IsInvertible := by
   have hi := injective hA
   exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hi)
     (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hi)), rfl⟩

 theorem push_gradient {A : Vector κ →L[ℝ] Vector κ} (hA : Preserves A) (a b : Vector κ)
    (hh : ∀ v, inner (𝕜 := ℝ) b (A v) = inner (𝕜 := ℝ) a v) :
    A (Complex.I • a) = Complex.I • b := by
   apply form_ext
   intro w
   obtain ⟨v,rfl⟩ := (LinearMap.surjective_of_injective (injective hA)) w
   change form (A (Complex.I • a)) (A v) = form (Complex.I • b) (A v)
   rw [hA, form_I, form_I, hh]

 theorem push_hamiltonian (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hω : ∀ x ∈ e.source, Preserves (fderiv ℝ e x))
    {H G : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (hcomp : ∀ x ∈ e.source, H (e x) = G x) {x : Vector κ} (hx : x ∈ e.source) :
    fderiv ℝ e x (Complex.I • gradient G x) = Complex.I • gradient H (e x) := by
   apply push_gradient (hω x hx)
   intro v
   have hed := ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
   have hhd := ((hH.differentiable (by simp) (e x)).hasGradientAt.hasFDerivAt).comp x hed
   have hgd := ((hG.differentiable (by simp) x).hasGradientAt.hasFDerivAt)
   have heq : H ∘ e =ᶠ[𝓝 x] G := by
     filter_upwards [e.open_source.mem_nhds hx] with z hz
     exact hcomp z hz
   have hh := hhd.unique (hgd.congr_of_eventuallyEq heq)
   exact congrArg (fun D : Vector κ →L[ℝ] ℝ => D v) hh

 theorem inverse_curve (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hω : ∀ x ∈ e.source, Preserves (fderiv ℝ e x))
    {H G : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (hcomp : ∀ x ∈ e.source, H (e x) = G x)
    {x : ℝ → Vector κ} (hxt : ∀ t, x t ∈ e.target)
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t) (t : ℝ) :
    HasDerivAt (fun s => e.symm (x s)) (Complex.I • gradient G (e.symm (x t))) t := by
   let y := e.symm (x t)
   have hy : y ∈ e.source := e.map_target (hxt t)
   obtain ⟨D,hD⟩ := invertible (hω y hy)
   have hed : HasFDerivAt e D.toContinuousLinearMap y := by
     rw [hD]
     exact ((he.contDiffAt (e.open_source.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
   have hcd := (e.hasFDerivAt_symm (hxt t) hed).comp_hasDerivAt t (hx t)
   apply hcd.congr_deriv
   apply D.injective
   simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
   have hh := push_hamiltonian e he hω hH hG hcomp hy
   rw [e.right_inv (hxt t)] at hh
   change Complex.I • gradient H (x t) = D.toContinuousLinearMap (Complex.I • gradient G y)
   rw [hD]
   exact hh.symm

end
end ComplexSymplectic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.SmoothProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NonsqueezingInline

namespace SmoothProfiles
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

 theorem hasDerivAt_primitive {v : ℝ → ℝ} (hv : Continuous v) (s : ℝ) :
    HasDerivAt (primitive v) (v s) s :=
  intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable _ _)
    hv.stronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt

 theorem contDiff_primitive {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (primitive v) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun x => (hasDerivAt_primitive hv.continuous x).differentiableAt,
    by simpa only [(funext (fun x => (hasDerivAt_primitive hv.continuous x).deriv))] using hv⟩

 theorem primitive_zero {v : ℝ → ℝ} (hz : ∀ t ≤ 0, v t = 0) {s : ℝ} (hs : s ≤ 0) :
    primitive v s = 0 := by
  rw [primitive, intervalIntegral.integral_symm]
  have hi : ∫ t in s..0, v t = 0 := by
    calc
      _ = ∫ _t in s..0, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
        hz t (by rw [Set.uIcc_of_le hs] at ht; exact ht.2))
      _ = _ := by simp
  simp only [hi, neg_zero]

 theorem primitive_nonneg {v : ℝ → ℝ} (_hv : Continuous v)
    (hn : ∀ t, 0 ≤ v t) (hz : ∀ t ≤ 0, v t = 0) (s : ℝ) : 0 ≤ primitive v s := by
  by_cases hs : s ≤ 0
  · simp only [primitive_zero hz hs, le_refl]
  · exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => hn t)

 theorem primitive_mono {v : ℝ → ℝ} (hv : Continuous v) (hn : ∀ t, 0 ≤ v t) :
    Monotone (primitive v) := by
  exact monotone_of_deriv_nonneg (fun t => (hasDerivAt_primitive hv t).differentiableAt)
    (fun t => by simpa only [(hasDerivAt_primitive hv t).deriv] using hn t)

 theorem contDiff_exteriorSlope (δ : ℝ) : ContDiff ℝ ∞ (exteriorSlope δ) :=
   Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)

 theorem contDiff_exterior (δ : ℝ) : ContDiff ℝ ∞ (exterior δ) :=
   contDiff_primitive (contDiff_exteriorSlope δ)

 theorem hasDerivAt_exterior (δ s : ℝ) : HasDerivAt (exterior δ) (exteriorSlope δ s) s :=
   hasDerivAt_primitive (contDiff_exteriorSlope δ).continuous s

 theorem exteriorSlope_nonneg (δ s : ℝ) : 0 ≤ exteriorSlope δ s := Real.smoothTransition.nonneg _
 theorem exteriorSlope_le_one (δ s : ℝ) : exteriorSlope δ s ≤ 1 := Real.smoothTransition.le_one _
 theorem exteriorSlope_zero {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : s ≤ 0) : exteriorSlope δ s = 0 :=
   Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs hδ.le)
 theorem exteriorSlope_one {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : δ ≤ s) : exteriorSlope δ s = 1 :=
   Real.smoothTransition.one_of_one_le ((one_le_div hδ).mpr hs)

 theorem exterior_zero {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : s ≤ 0) : exterior δ s = 0 :=
   primitive_zero (fun _ ht => exteriorSlope_zero hδ ht) hs

 theorem exterior_nonneg {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : 0 ≤ exterior δ s :=
   primitive_nonneg (contDiff_exteriorSlope δ).continuous (exteriorSlope_nonneg δ)
     (fun _ ht => exteriorSlope_zero hδ ht) s

 theorem primitive_zero_below {v : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hz : ∀ t ≤ b, v t = 0) {s : ℝ} (hs : s ≤ b) : primitive v s = 0 := by
  unfold primitive
  calc
    _ = ∫ _t in (0:ℝ)..s, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
      hz t (ht.2.trans (max_le hb hs)))
    _ = _ := by simp

 theorem primitive_const_above {v : ℝ → ℝ} (hv : Continuous v) {b : ℝ}
    (hz : ∀ t, b ≤ t → v t = 0) {s : ℝ} (hs : b ≤ s) : primitive v s = primitive v b := by
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hv.intervalIntegrable (μ := volume) 0 b) (hv.intervalIntegrable (μ := volume) b s)
  have he : (∫ t in b..s, v t) = 0 := by
    calc
      _ = ∫ _t in b..s, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
        hz t (by rw [Set.uIcc_of_le hs] at ht; exact ht.1))
      _ = _ := by simp
  change primitive v b+_ = primitive v s at hi
  simpa only [he, add_zero] using hi.symm

 theorem contDiff_ballSlope (r L ε : ℝ) : ContDiff ℝ ∞ (ballSlope r L ε) :=
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const ε))).mul
      (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const ε))

 theorem contDiff_ballProfile (r L ε : ℝ) : ContDiff ℝ ∞ (ballProfile r L ε) :=
    contDiff_primitive (contDiff_ballSlope r L ε)

 theorem hasDerivAt_ballProfile (r L ε s : ℝ) :
    HasDerivAt (ballProfile r L ε) (ballSlope r L ε s) s :=
    hasDerivAt_primitive (contDiff_ballSlope r L ε).continuous s

 theorem ballSlope_nonneg {r : ℝ} (hr : 0 ≤ r) (L ε s : ℝ) : 0 ≤ ballSlope r L ε s :=
    mul_nonneg (mul_nonneg hr (Real.smoothTransition.nonneg _)) (Real.smoothTransition.nonneg _)

 theorem ballSlope_le {r : ℝ} (hr : 0 ≤ r) (L ε s : ℝ) : ballSlope r L ε s ≤ r := by
    have h1 := Real.smoothTransition.le_one ((s-ε)/ε)
    have h2 := Real.smoothTransition.le_one ((L-ε-s)/ε)
    have h0 := Real.smoothTransition.nonneg ((s-ε)/ε)
    have hp := mul_le_mul_of_nonneg_left h2 (mul_nonneg hr h0)
    have hq := mul_le_mul_of_nonneg_left h1 hr
    dsimp [ballSlope]
    nlinarith

 theorem ballSlope_zero_left (r L : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : s ≤ ε) :
    ballSlope r L ε s = 0 := by
    unfold ballSlope
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)]
    ring

 theorem ballSlope_zero_right (r L : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : L-ε ≤ s) :
    ballSlope r L ε s = 0 := by
    unfold ballSlope
    rw [show Real.smoothTransition ((L-ε-s)/ε) = 0 from
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)]
    ring

 theorem ballSlope_middle (r L : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ}
    (hs : 2*ε ≤ s) (ht : s ≤ L-2*ε) : ballSlope r L ε s = r := by
    unfold ballSlope
    rw [Real.smoothTransition.one_of_one_le ((one_le_div hε).mpr (by linarith)),
      Real.smoothTransition.one_of_one_le ((one_le_div hε).mpr (by linarith))]
    ring

 theorem ballProfile_zero (r L : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : s ≤ ε) :
    ballProfile r L ε s = 0 :=
    primitive_zero_below hε.le (fun _ ht => ballSlope_zero_left r L hε ht) hs

 theorem ballProfile_plateau (r L : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : L-ε ≤ s) :
    ballProfile r L ε s = ballHeight r L ε :=
    primitive_const_above (contDiff_ballSlope r L ε).continuous
      (fun _ ht => ballSlope_zero_right r L hε ht) hs

 theorem ballProfile_nonneg {r : ℝ} (hr : 0 ≤ r) (L : ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ ballProfile r L ε s :=
    primitive_nonneg (contDiff_ballSlope r L ε).continuous (ballSlope_nonneg hr L ε)
      (fun _ ht => ballSlope_zero_left r L hε (ht.trans hε.le)) s

 theorem ballProfile_le_height {r : ℝ} (hr : 0 ≤ r) (L : ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ballProfile r L ε s ≤ ballHeight r L ε := by
    by_cases hs : L-ε ≤ s
    · rw [ballProfile_plateau r L hε hs]
    · exact primitive_mono (contDiff_ballSlope r L ε).continuous (ballSlope_nonneg hr L ε) (le_of_not_ge hs)

 theorem ballHeight_lower {r : ℝ} (hr : 0 ≤ r) (L : ℝ) {ε : ℝ} (hε : 0 < ε) (hL : 4*ε ≤ L) :
    r*(L-4*ε) ≤ ballHeight r L ε := by
    have hm := primitive_mono (contDiff_ballSlope r L ε).continuous (ballSlope_nonneg hr L ε)
    have hn := ballProfile_nonneg hr L hε (2*ε)
    have hc := (contDiff_ballSlope r L ε).continuous
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 (2*ε)) (hc.intervalIntegrable (μ := volume) (2*ε) (L-2*ε))
    have he : (∫ t in (2*ε)..(L-2*ε), ballSlope r L ε t) = r*(L-4*ε) := by
      calc
        _ = ∫ _t in (2*ε)..(L-2*ε), r := intervalIntegral.integral_congr (fun t ht => by
          rw [Set.uIcc_of_le (by linarith)] at ht
          exact ballSlope_middle r L hε ht.1 ht.2)
        _ = _ := by simp; ring
    change ballProfile r L ε (2*ε)+_ = ballProfile r L ε (L-2*ε) at hi
    rw [he] at hi
    have hmono : ballProfile r L ε (L-2*ε) ≤ ballHeight r L ε := hm (by linarith)
    linarith

 theorem exists_ball_parameters {A L : ℝ} (hA : 0 ≤ A) (hL : 0 < L) (hAL : A < Real.pi*L) :
    ∃ r ε : ℝ, 0 < r ∧ r < Real.pi ∧ 0 < ε ∧ 4*ε < L ∧ A < r*(L-4*ε) := by
    obtain ⟨r,hrA,hrπ⟩ := exists_between ((div_lt_iff₀ hL).mpr (by simpa [mul_comm] using hAL))
    have hr : 0 < r := lt_of_le_of_lt (div_nonneg hA hL.le) hrA
    have hrl : A < r*L := (div_lt_iff₀ hL).mp hrA
    let ε := (r*L-A)/(8*r)
    have hε : 0 < ε := div_pos (sub_pos.mpr hrl) (by positivity)
    have he : 8*r*ε = r*L-A := by dsimp [ε]; field_simp
    refine ⟨r,ε,hr,hrπ,hε,?_,?_⟩ <;> nlinarith

end
end SmoothProfiles

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.ExteriorHamiltonian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u123 u124 u125 u126

section NonsqueezingInline

namespace PushedBall
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial HamiltonianODE SmoothProfiles EmbeddingInverse
variable {κ : Type u123} [Fintype κ]

 theorem isOpen_domain (L : ℝ) : IsOpen (domain (κ := κ) L) :=
   isOpen_lt (continuous_norm.pow 2) continuous_const

 theorem core_compact (L ε : ℝ) : IsCompact (core (κ := κ) L ε) := isCompact_closedBall _ _

 theorem mem_core_iff {L ε : ℝ} (hL : 0 ≤ L-ε) (z : Vector κ) :
    z ∈ core L ε ↔ ‖z‖^2 ≤ L-ε := by
   simp only [core, Metric.mem_closedBall, dist_zero_right]
   exact (Real.le_sqrt (norm_nonneg z) hL)

 theorem core_subset_domain {L ε : ℝ} (hε : 0 < ε) (hL : ε ≤ L) :
    core (κ := κ) L ε ⊆ domain L := by
   intro z hz
   have hh := (mem_core_iff (sub_nonneg.mpr hL) z).mp hz
   change ‖z‖^2 < L
   linarith

 theorem contDiff_radial (r L ε : ℝ) : ContDiff ℝ ∞ (radial (κ := κ) r L ε) :=
   (contDiff_ballProfile r L ε).comp ((contDiff_id : ContDiff ℝ ∞ (id : Vector κ → Vector κ)).norm_sq ℝ)

 theorem radial_eq_height {r L ε : ℝ} (hε : 0 < ε) (hL : ε ≤ L)
    {z : Vector κ} (hz : z ∉ core L ε) : radial r L ε z = ballHeight r L ε := by
   apply ballProfile_plateau r L hε
   exact le_of_lt (lt_of_not_ge ((mem_core_iff (sub_nonneg.mpr hL) z).not.mp hz))

 theorem contDiff_pushed (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source) {L : ℝ} (hs : e.source = domain L)
    (hD : ∀ x ∈ e.source, (fderiv ℝ e x).IsInvertible)
    {r ε : ℝ} (hε : 0 < ε) (hL : ε ≤ L) : ContDiff ℝ ∞ (pushed e r L ε) := by
   apply (contDiff_extendFunction e he hD ((contDiff_radial r L ε).sub contDiff_const)
     (core_compact L ε) _ _).add contDiff_const
   · rw [hs]; exact core_subset_domain hε hL
   · intro z hz
     rw [radial_eq_height hε hL hz, sub_self]

 theorem pushed_apply (e : OpenPartialHomeomorph (Vector κ) (Vector κ)) (r L ε : ℝ)
    {x : Vector κ} (hx : x ∈ e.source) : pushed e r L ε (e x) = radial r L ε x := by
   simp only [pushed, extendFunction_apply e _ hx, sub_add_cancel]

 theorem pushed_plateau (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    {r L ε : ℝ} (hε : 0 < ε) (hL : ε ≤ L) {x : Vector κ} (hx : x ∉ e '' core L ε) :
    pushed e r L ε x = ballHeight r L ε := by
   rw [pushed, extendFunction_zero e _ (core L ε) (fun z hz => by rw [radial_eq_height hε hL hz,sub_self]) hx,
     zero_add]

 theorem pushed_bounds (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    {r L ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) (x : Vector κ) :
    0 ≤ pushed e r L ε x ∧ pushed e r L ε x ≤ ballHeight r L ε := by
   rcases extendFunction_mem_range e (fun w => radial r L ε w-ballHeight r L ε) x with hz | ⟨w,_,hw⟩
   · simp only [pushed,hz,zero_add,le_refl,and_true]
     exact ballProfile_nonneg hr L hε (L-ε)
   · simp only [pushed,hw,sub_add_cancel]
     exact ⟨ballProfile_nonneg hr L hε _,ballProfile_le_height hr L hε _⟩

 theorem zero_mem_domain {L : ℝ} (hL : 0 < L) : (0 : Vector κ) ∈ domain L := by
   simpa only [domain, mem_ofPred_eq, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hL

 theorem radial_flat {r L ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 (0 : Vector κ), radial r L ε z = 0 := by
   have hsmall : ∀ᶠ z in 𝓝 (0 : Vector κ), ‖z‖^2 < ε :=
     (isOpen_domain ε).mem_nhds (zero_mem_domain hε)
   filter_upwards [hsmall] with z hz
   exact ballProfile_zero r L hε hz.le

 theorem pushed_flat (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    {r L ε : ℝ} (hs : e.source = domain L) (hε : 0 < ε) (hL : ε ≤ L) :
    ∀ᶠ z in 𝓝 (e 0), pushed e r L ε z = 0 := by
   have h0 : (0 : Vector κ) ∈ e.source := by
     rw [hs]; exact zero_mem_domain (hε.trans_le hL)
   apply eventually_of_comp e h0
   filter_upwards [e.open_source.mem_nhds h0,radial_flat (r := r) (L := L) hε] with z hz hflat
   rw [pushed_apply e r L ε hz]
   exact hflat

 theorem radial_slow {r L ε : ℝ} (hr : 0 ≤ r) (hrπ : r < Real.pi)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient (radial r L ε) (x t)) t)
    (hp : x 1 = x 0) (t : ℝ) : x t = x 0 :=
   slow_radial_constant (hasDerivAt_ballProfile r L ε) (ballSlope_nonneg hr L ε)
     (fun s => (ballSlope_le hr L ε s).trans_lt hrπ) hx hp t

end
end PushedBall

namespace ExteriorHamiltonian
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth SmoothProfiles
variable {κ : Type u124} [Fintype κ]

 theorem contDiff_potential (d : κ → ℝ) (T δ : ℝ) : ContDiff ℝ ∞ (potential d T δ) :=
   (contDiff_exterior δ).comp ((contDiff_energy d).sub contDiff_const)

 theorem contDiff_full {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀) (d : κ → ℝ) (T δ : ℝ) :
    ContDiff ℝ ∞ (full H₀ d T δ) := hH₀.add (contDiff_potential d T δ)

 theorem gradient_potential (d : κ → ℝ) (T δ : ℝ) (z : Vector κ) :
    gradient (potential d T δ) z = (2*exteriorSlope δ (energy d z-T)) • diag d z := by
   change gradient (fun w : Vector κ => exterior δ (energy d w-T)) z = _
   convert! gradient_comp_energy d z ((hasDerivAt_exterior δ (energy d z-T)).comp (energy d z)
     ((hasDerivAt_id (energy d z)).sub_const T)) using 1
   simp only [mul_one]

 theorem gradient_sum {H G : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (z : Vector κ) : gradient (fun w => H w+G w) z = gradient H z+gradient G z := by
   apply HasGradientAt.gradient
   rw [hasGradientAt_iff_hasFDerivAt]
   have hh := ((hH.differentiable (by simp) z).hasGradientAt.hasFDerivAt).add
     ((hG.differentiable (by simp) z).hasGradientAt.hasFDerivAt)
   convert! hh using 1
   ext w
   change inner (𝕜 := ℝ) (gradient H z+gradient G z) w =
     inner (𝕜 := ℝ) (gradient H z) w+inner (𝕜 := ℝ) (gradient G z) w
   exact inner_add_left _ _ _

 theorem gradient_full {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀)
    (d : κ → ℝ) (T δ : ℝ) (z : Vector κ) :
    gradient (full H₀ d T δ) z = gradient H₀ z+(2*exteriorSlope δ (energy d z-T)) • diag d z := by
   change gradient (fun w => H₀ w+potential d T δ w) z = _
   rw [gradient_sum hH₀ (contDiff_potential d T δ), gradient_potential]

 theorem gradient_at_max {H : Vector κ → ℝ} {m : ℝ} (hm : ∀ z, H z ≤ m)
    {z : Vector κ} (hz : H z = m) : gradient H z = 0 := by
   have he : IsLocalMax H z := Filter.Eventually.of_forall (fun w => by rw [hz]; exact hm w)
   simp only [gradient,he.fderiv_eq_zero,map_zero]

 theorem gradient_at_min {H : Vector κ → ℝ} {m : ℝ} (hm : ∀ z, m ≤ H z)
    {z : Vector κ} (hz : H z = m) : gradient H z = 0 := by
   have he : IsLocalMin H z := Filter.Eventually.of_forall (fun w => by rw [hz]; exact hm w)
   simp only [gradient,he.fderiv_eq_zero,map_zero]

 theorem potential_zero (d : κ → ℝ) (T : ℝ) {δ : ℝ} (hδ : 0 < δ) {z : Vector κ}
    (hz : energy d z ≤ T) : potential d T δ z = 0 := exterior_zero hδ (sub_nonpos.mpr hz)

 theorem potential_nonneg (d : κ → ℝ) (T : ℝ) {δ : ℝ} (hδ : 0 < δ) (z : Vector κ) :
    0 ≤ potential d T δ z := exterior_nonneg hδ _

 theorem compact_sublevel (d : κ → ℝ) {b C : ℝ} (hb : 0 < b) (hd : ∀ j, b ≤ d j) (hC : 0 ≤ C) :
    IsCompact {z : Vector κ | energy d z ≤ C} := by
   apply (isCompact_closedBall (0 : Vector κ) (Real.sqrt (C/b))).of_isClosed_subset
     (isClosed_le (contDiff_energy d).continuous continuous_const)
   intro z hz
   simp only [Metric.mem_closedBall,dist_zero_right]
   apply (Real.le_sqrt (norm_nonneg z) (div_nonneg hC hb.le)).mpr
   apply (le_div_iff₀ hb).mpr
   have he := energy_lower d b hd z
   change energy d z ≤ C at hz
   nlinarith

 theorem bounded_remainder {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀)
    {m : ℝ} (hm : ∀ z, H₀ z ≤ m) {S : Set (Vector κ)} (hS : IsCompact S)
    (he : ∀ z ∉ S, H₀ z = m) (d : κ → ℝ) {b T δ : ℝ}
    (hb : 0 < b) (hd : ∀ j, b ≤ d j) (hδ : 0 < δ) (hT : 0 ≤ T+δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z,
      ‖gradient (full H₀ d T δ) z-(2 : ℝ) • diag d z‖ ≤ B := by
   apply bound_remainder_of_compact (contDiff_full hH₀ d T δ) d
     (hS.union (compact_sublevel d hb hd hT))
   intro z hz
   have hzS : z ∉ S := fun h => hz (Or.inl h)
   have hzQ : T+δ < energy d z := lt_of_not_ge (fun h => hz (Or.inr h))
   rw [gradient_full hH₀, gradient_at_max hm (he z hzS),
     exteriorSlope_one hδ (by linarith), mul_one, zero_add]

 theorem full_flat {H₀ : Vector κ → ℝ} (d : κ → ℝ) {T δ : ℝ} (hδ : 0 < δ)
    {p : Vector κ} (hf : ∀ᶠ z in 𝓝 p, H₀ z = 0) (hp : energy d p < T) :
    ∀ᶠ z in 𝓝 p, full H₀ d T δ z = 0 := by
   have hq : ∀ᶠ z in 𝓝 p, energy d z < T :=
     (isOpen_lt (contDiff_energy d).continuous continuous_const).mem_nhds hp
   filter_upwards [hf,hq] with z hz hze
   simp only [full,hz,potential_zero d T hδ hze.le,add_zero]

end
end ExteriorHamiltonian

namespace ExteriorHamiltonian
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles HamiltonianPeriodic
variable {κ : Type u125} [Fintype κ]

 theorem action_nonpos {H : Vector κ → ℝ} {x : ℝ → Vector κ}
    (h : ∀ t, inner (𝕜 := ℝ) (gradient H (x t)) (x t)/2-H (x t) ≤ 0) :
    actionIntegral H x ≤ 0 := by
   rw [actionIntegral,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
   exact integral_nonpos h

 theorem gradient_of_constant_curve {H : Vector κ → ℝ} {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t)
    (hc : ∀ t, x t = x 0) (t : ℝ) : gradient H (x t) = 0 := by
   have he : x = fun _ => x 0 := funext hc
   have hd0 : HasDerivAt x 0 t := by
     convert! hasDerivAt_const t (x 0) using 1
   have hd := (hx t).unique hd0
   exact (smul_eq_zero.mp hd).resolve_left Complex.I_ne_zero

 theorem action_nonpos_of_constant {H : Vector κ → ℝ} (hH0 : ∀ z, 0 ≤ H z)
    {x : ℝ → Vector κ} (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t)
    (hc : ∀ t, x t = x 0) : actionIntegral H x ≤ 0 := by
   apply action_nonpos
   intro t
   rw [gradient_of_constant_curve hx hc t,inner_zero_left,zero_div,zero_sub]
   exact neg_nonpos.mpr (hH0 (x t))

 theorem high_orbit_nonpos (j₀ : κ) {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀)
    {m : ℝ} (hm : ∀ z, H₀ z ≤ m) (hH₀0 : ∀ z, 0 ≤ H₀ z)
    (d : κ → ℝ) (hd : ∀ j, 0 ≤ d j) (hda : Real.pi < d j₀)
    (hdb : ∀ j, j ≠ j₀ → d j < Real.pi) (hda2 : d j₀ < 2*Real.pi)
    {T δ : ℝ} (hδ : 0 < δ) (hmag : Real.pi*(T+δ) < m*d j₀)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient (full H₀ d T δ) (x t)) t)
    (hp : x 1 = x 0) (hplateau : ∀ t, H₀ (x t) = m) :
    actionIntegral (full H₀ d T δ) x ≤ 0 := by
   have he (t : ℝ) : gradient (full H₀ d T δ) (x t) =
       (2*exteriorSlope δ (energy d (x t)-T)) • diag d (x t) := by
     rw [gradient_full hH₀,gradient_at_max hm (hplateau t),zero_add]
   have hode (t : ℝ) := (hx t).congr_deriv (congrArg (fun z : Vector κ => Complex.I • z) (he t))
   have hQ (t : ℝ) := quadratic_constant d hode t 0
   let v := exteriorSlope δ (energy d (x 0)-T)
   have hv : 0 ≤ v := exteriorSlope_nonneg _ _
   have hv1 : v ≤ 1 := exteriorSlope_le_one _ _
   have hode' (t : ℝ) : HasDerivAt x (Complex.I • ((2*v) • diag d (x t))) t := by
     simpa only [hQ t] using hode t
   rcases diagonal_either j₀ d hv hv1 hd hdb hda2 hode' hp with heq | hc
   · have ha0 : 0 < d j₀ := Real.pi_pos.trans hda
     have hvlt : v < 1 := by nlinarith
     have hQt : energy d (x 0) < T+δ := by
       by_contra hn
       have hz : v = 1 := exteriorSlope_one hδ (by linarith)
       linarith
     have hvT : v*(T+δ) < m := by
       apply (mul_lt_mul_iff_left₀ ha0).mp
       calc
         (v*(T+δ))*d j₀ = Real.pi*(T+δ) := by rw [← heq]; ring
         _ < m*d j₀ := hmag
     apply action_nonpos
     intro t
     rw [he t,hQ t,real_inner_smul_left,← energy_eq_inner, hQ t]
     have hg := potential_nonneg d T hδ (x t)
     change (2*v)*energy d (x 0)/2-(H₀ (x t)+potential d T δ (x t)) ≤ 0
     rw [hplateau t]
     nlinarith [mul_le_mul_of_nonneg_left hQt.le hv]
   · apply action_nonpos_of_constant _ hx hc
     intro z
     exact add_nonneg (hH₀0 z) (potential_nonneg d T hδ z)

 theorem zero_vector_at_plateau {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀)
    {m : ℝ} (hm : ∀ z, H₀ z ≤ m) (d : κ → ℝ) {T δ : ℝ} (hδ : 0 < δ)
    {U : Set (Vector κ)} (hU : ∀ z ∈ U, energy d z ≤ T)
    (he : ∀ z ∉ U, H₀ z = m) {z : Vector κ} (hz : full H₀ d T δ z = m) :
    gradient (full H₀ d T δ) z = 0 := by
   have hp : potential d T δ z = 0 := by
     by_cases hu : z ∈ U
     · exact potential_zero d T hδ (hU z hu)
     · have hh := he z hu
       change H₀ z+potential d T δ z=m at hz
       linarith
   have h0 : H₀ z = m := by simpa only [full,hp,add_zero] using hz
   change gradient (fun w => H₀ w+potential d T δ w) z = 0
   rw [gradient_sum hH₀ (contDiff_potential d T δ),gradient_at_max hm h0,
     gradient_at_min (potential_nonneg d T hδ) hp,add_zero]

 theorem all_orbits_nonpos (j₀ : κ) {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀)
    {m : ℝ} (hm : ∀ z, H₀ z ≤ m) (hH₀0 : ∀ z, 0 ≤ H₀ z)
    (d : κ → ℝ) (hd : ∀ j, 0 ≤ d j) (hda : Real.pi < d j₀)
    (hdb : ∀ j, j ≠ j₀ → d j < Real.pi) (hda2 : d j₀ < 2*Real.pi)
    {T δ : ℝ} (hδ : 0 < δ) (hmag : Real.pi*(T+δ) < m*d j₀)
    {U : Set (Vector κ)} (hU : ∀ z ∈ U, energy d z ≤ T)
    (he : ∀ z ∉ U, H₀ z = m)
    (hslow : ∀ x : ℝ → Vector κ, (∀ t, x t ∈ U) → x 1 = x 0 →
      (∀ t, HasDerivAt x (Complex.I • gradient (full H₀ d T δ) (x t)) t) → ∀ t, x t = x 0)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient (full H₀ d T δ) (x t)) t)
    (hp : x 1 = x 0) : actionIntegral (full H₀ d T δ) x ≤ 0 := by
   have hH0 (z : Vector κ) : 0 ≤ full H₀ d T δ z :=
     add_nonneg (hH₀0 z) (potential_nonneg d T hδ z)
   have hE (t : ℝ) := energy_constant (contDiff_full hH₀ d T δ) hx t 0
   rcases lt_trichotomy (full H₀ d T δ (x 0)) m with hl | heq | hh
   · have hxt (t : ℝ) : x t ∈ U := by
       by_contra hn
       have hz := he (x t) hn
       have hg := potential_nonneg d T hδ (x t)
       have ht : full H₀ d T δ (x t) < m := by rw [hE t]; exact hl
       change H₀ (x t)+potential d T δ (x t) < m at ht
       linarith
     exact action_nonpos_of_constant hH0 hx (hslow x hxt hp hx)
   · apply action_nonpos_of_constant hH0 hx
     intro s
     apply zero_derivative_constant _ s 0
     intro t
     have hz := zero_vector_at_plateau hH₀ hm d hδ hU he ((hE t).trans heq)
     simpa only [hz,smul_zero] using hx t
   · apply high_orbit_nonpos j₀ hH₀ hm hH₀0 d hd hda hdb hda2 hδ hmag hx hp
     intro t
     apply he
     intro hu
     have hpz := potential_zero d T hδ (hU (x t) hu)
     have ht : m < full H₀ d T δ (x t) := by rw [hE t]; exact hh
     simp only [full,hpz,add_zero] at ht
     exact (not_lt_of_ge (hm (x t))) ht

end
end ExteriorHamiltonian

namespace PushedBall
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles ExteriorHamiltonian
variable {κ : Type u126} [Fintype κ]

 theorem pushed_full_comp (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (r L ε : ℝ) (d : κ → ℝ) {T δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ z ∈ e.target, energy d z ≤ T) {z : Vector κ} (hz : z ∈ e.source) :
    full (pushed e r L ε) d T δ (e z) = radial r L ε z := by
   rw [full,pushed_apply e r L ε hz,potential_zero d T hδ (hQ _ (e.map_source hz)),add_zero]

 theorem pushed_full_slow (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source) (hω : ∀ z ∈ e.source, ComplexSymplectic.Preserves (fderiv ℝ e z))
    {r L ε : ℝ} (hs : e.source = domain L) (hr : 0 ≤ r) (hrπ : r < Real.pi)
    (hε : 0 < ε) (hL : ε ≤ L) (d : κ → ℝ) {T δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ z ∈ e.target, energy d z ≤ T)
    {x : ℝ → Vector κ} (hxt : ∀ t, x t ∈ e.target) (hp : x 1 = x 0)
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient (full (pushed e r L ε) d T δ) (x t)) t)
    (t : ℝ) : x t = x 0 := by
   have hD (z) (hz : z ∈ e.source) := ComplexSymplectic.invertible (hω z hz)
   have hH := contDiff_full (contDiff_pushed e he hs hD (r := r) hε hL) d T δ
   have hy (s : ℝ) := ComplexSymplectic.inverse_curve e he hω hH (contDiff_radial r L ε)
     (fun z hz => pushed_full_comp e r L ε d hδ hQ hz) hxt hx s
   have hp' : e.symm (x 1) = e.symm (x 0) := congrArg e.symm hp
   have hc := radial_slow hr hrπ hy hp' t
   have hh := congrArg e hc
   simpa only [e.right_inv (hxt t),e.right_inv (hxt 0)] using hh

 theorem pushed_plateau_outside (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    {r L ε : ℝ} (hs : e.source = domain L) (hε : 0 < ε) (hL : ε ≤ L)
    {z : Vector κ} (hz : z ∉ e.target) : pushed e r L ε z = ballHeight r L ε := by
   apply pushed_plateau e hε hL
   rintro ⟨x,hx,rfl⟩
   apply hz
   apply e.map_source
   rw [hs]
   exact core_subset_domain hε hL hx

end
end PushedBall

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.Nonsqueezing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u127

section NonsqueezingInline

namespace CylinderParameters
noncomputable section
open Set Filter Finset
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE
variable {κ : Type u127} [Fintype κ] [DecidableEq κ]

 theorem energy_weights (j₀ : κ) (a b : ℝ) (z : Vector κ) :
    energy (weights j₀ a b) z = (a-b)*‖z j₀‖^2+b*‖z‖^2 := by
   have hh (j : κ) : weights j₀ a b j*‖z j‖^2 =
       b*‖z j‖^2+(if j=j₀ then (a-b)*‖z j‖^2 else 0) := by
     by_cases hj : j=j₀ <;> simp only [weights,hj,ite_true,ite_false] <;> ring
   simp only [energy,hh,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
     ← Finset.mul_sum,← EuclideanSpace.norm_sq_eq]
   ring

 theorem energy_weights_upper (j₀ : κ) {a b R M : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hR : 0 ≤ R) {z : Vector κ} (hz : ‖z‖^2 ≤ M) (hz₀ : ‖z j₀‖^2 ≤ R) :
    energy (weights j₀ a b) z ≤ a*R+b*M := by
   rw [energy_weights]
   have h1 := mul_le_mul_of_nonneg_left hz (show 0 ≤ b from hb)
   have h2 := mul_le_mul_of_nonneg_left hz₀ (sub_nonneg.mpr hab)
   nlinarith

 theorem gap_first {m : ℤ} : Real.pi/2 ≤ |Real.pi*(m:ℝ)-3*Real.pi/2| := by
   rcases le_or_gt m 1 with hm | hm
   · have hm' : (m:ℝ) ≤ 1 := by exact_mod_cast hm
     apply (le_abs.mpr (Or.inr ?_))
     nlinarith [Real.pi_pos]
   · have hm' : (2:ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
     apply (le_abs.mpr (Or.inl ?_))
     nlinarith [Real.pi_pos]

 theorem gap_small {b : ℝ} (hb : 0 < b) (hbπ : b ≤ Real.pi/2) (m : ℤ) :
    b ≤ |Real.pi*(m:ℝ)-b| := by
   rcases le_or_gt m 0 with hm | hm
   · have hm' : (m:ℝ) ≤ 0 := by exact_mod_cast hm
     apply (le_abs.mpr (Or.inr ?_))
     nlinarith [Real.pi_pos]
   · have hm' : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
     apply (le_abs.mpr (Or.inl ?_))
     nlinarith [Real.pi_pos]

omit [Fintype κ] in
 theorem weights_bounds (j₀ : κ) {b : ℝ} (hb : 0 < b) (hbπ : b ≤ Real.pi/4) :
    (∀ j, b ≤ weights j₀ (3*Real.pi/2) b j) ∧
    Real.pi+b ≤ weights j₀ (3*Real.pi/2) b j₀ ∧
    (∀ j, |weights j₀ (3*Real.pi/2) b j| ≤ 3*Real.pi/2) ∧
    (∀ j, j ≠ j₀ → weights j₀ (3*Real.pi/2) b j < Real.pi) ∧
    (∀ m : ℤ, ∀ j, b ≤ |Real.pi*(m:ℝ)-weights j₀ (3*Real.pi/2) b j|) := by
   have hab : b ≤ 3*Real.pi/2 := by linarith [Real.pi_pos]
   refine ⟨?_,?_,?_,?_,?_⟩
   · intro j; unfold weights; split_ifs
     · exact hab
     · exact le_rfl
   · simp only [weights,ite_true]; linarith [Real.pi_pos]
   · intro j; unfold weights; split_ifs
     · rw [abs_of_pos (by positivity)]
     · rw [abs_of_pos hb]; exact hab
   · intro j hj; simp only [weights,hj,ite_false]; linarith [Real.pi_pos]
   · intro m j; unfold weights; split_ifs
     · exact (show b ≤ Real.pi/2 by linarith [Real.pi_pos]).trans gap_first
     · exact gap_small hb (by linarith [Real.pi_pos]) m

 theorem exists_parameters (j₀ : κ) {R M m : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hRm : Real.pi*R < m) :
    ∃ b T δ : ℝ, 0 < b ∧ b ≤ Real.pi/4 ∧ 0 < δ ∧ 0 < T ∧
      Real.pi*(T+δ) < m*(3*Real.pi/2) ∧
      ∀ z : Vector κ, ‖z‖^2 ≤ M → ‖z j₀‖^2 ≤ R →
        energy (weights j₀ (3*Real.pi/2) b) z < T := by
   let a := 3*Real.pi/2
   have ha : 0 < a := by dsimp [a]; positivity
   let τ := (m-Real.pi*R)/(4*Real.pi)
   have hτ : 0 < τ := div_pos (sub_pos.mpr hRm) (by positivity)
   have hτeq : 4*Real.pi*τ=m-Real.pi*R := by dsimp [τ]; field_simp
   let b := min (Real.pi/4) (a*τ/(M+1))
   have hb : 0 < b := lt_min (by positivity) (div_pos (mul_pos ha hτ) (by linarith))
   have hbπ : b ≤ Real.pi/4 := min_le_left _ _
   have hbb : b*(M+1) ≤ a*τ := (le_div_iff₀ (by linarith : 0 < M+1)).mp (min_le_right _ _)
   have hbM : b*M < a*τ := by nlinarith
   refine ⟨b,a*(R+τ),a*τ,hb,hbπ,mul_pos ha hτ,mul_pos ha (by linarith),?_,?_⟩
   · change Real.pi*(a*(R+τ)+a*τ) < m*a
     have hh : Real.pi*(R+2*τ)< m := by nlinarith
     nlinarith [mul_lt_mul_of_pos_left hh ha]
   · intro z hz hz₀
     have hab : b ≤ a := by dsimp [a]; linarith [Real.pi_pos]
     have he := energy_weights_upper j₀ hb.le hab hR hz hz₀
     change energy (weights j₀ a b) z < a*(R+τ)
     nlinarith

end
end CylinderParameters

namespace CylinderNonsqueezing
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles HamiltonianPeriodic
open ExteriorHamiltonian PushedBall CylinderParameters
variable {κ : Type} [Fintype κ] [DecidableEq κ]

 theorem radius_le_of_embedding (j₀ : κ) {L R M : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source) (hs : e.source = domain L)
    (hω : ∀ z ∈ e.source, ComplexSymplectic.Preserves (fderiv ℝ e z))
    (hbounded : ∀ z ∈ e.target, ‖z‖^2 ≤ M)
    (hcylinder : ∀ z ∈ e.target, ‖z j₀‖^2 ≤ R) : L ≤ R := by
   by_contra hn
   have hRL : R < L := lt_of_not_ge hn
   obtain ⟨r,ε,hr,hrπ,hε,hεL,hm⟩ := exists_ball_parameters (mul_nonneg Real.pi_pos.le hR) hL
     (mul_lt_mul_of_pos_left hRL Real.pi_pos)
   let m := ballHeight r L ε
   have hεL' : ε ≤ L := by linarith
   have hRm : Real.pi*R < m := hm.trans_le (ballHeight_lower hr.le L hε hεL.le)
   obtain ⟨b,T,δ,hb,hbπ,hδ,hT,hmag,hcontain⟩ := exists_parameters j₀ hR hM hRm
   let d := weights j₀ (3*Real.pi/2) b
   obtain ⟨hdb,hdb0,hdD,hdπ,hgap⟩ := weights_bounds j₀ hb hbπ
   have hQ (z : Vector κ) (hz : z ∈ e.target) : energy d z < T :=
     hcontain z (hbounded z hz) (hcylinder z hz)
   have hD (z) (hz : z ∈ e.source) := ComplexSymplectic.invertible (hω z hz)
   let H₀ := pushed e r L ε
   have hH₀ : ContDiff ℝ ∞ H₀ := contDiff_pushed e he hs hD hε hεL'
   have hH₀0 (z : Vector κ) : 0 ≤ H₀ z := (pushed_bounds e hr.le hε z).1
   have hH₀m (z : Vector κ) : H₀ z ≤ m := (pushed_bounds e hr.le hε z).2
   have hS : IsCompact (e '' core L ε) := (core_compact L ε).image_of_continuousOn
     (e.continuousOn.mono (by rw [hs]; exact core_subset_domain hε hεL'))
   obtain ⟨B,hB,hrem⟩ := bounded_remainder hH₀ hH₀m hS
     (fun z hz => pushed_plateau e hε hεL' hz) d hb hdb hδ (by linarith : 0 ≤ T+δ)
   have h0 : (0 : Vector κ) ∈ e.source := by rw [hs]; exact zero_mem_domain hL
   have hflat := full_flat d hδ (pushed_flat e (r := r) hs hε hεL') (hQ _ (e.map_source h0))
   have hnonneg (z : Vector κ) : 0 ≤ full H₀ d T δ z := add_nonneg (hH₀0 z) (potential_nonneg d T hδ z)
   obtain ⟨x,hp,ha,hx⟩ := exists_positive_at_flat_point j₀ (contDiff_full hH₀ d T δ) hnonneg (e 0)
     hflat d (div_pos hb (by norm_num : (0:ℝ) < 2)) hb hB
     (by positivity : 0 ≤ 3*Real.pi/2)
     (fun j => by dsimp [d]; linarith [hdb j])
     (by dsimp [d]; linarith) hdD hgap hrem
   have hn := all_orbits_nonpos j₀ hH₀ hH₀m hH₀0 d (fun j => hb.le.trans (hdb j))
     (by dsimp [d,weights]; simp only [ite_true]; linarith [Real.pi_pos]) hdπ
     (by dsimp [d,weights]; simp only [ite_true]; linarith [Real.pi_pos]) hδ
     (by simpa only [d,weights,ite_true] using hmag)
     (fun z hz => (hQ z hz).le)
     (fun z hz => pushed_plateau_outside e hs hε hεL' hz)
     (fun x hxt hp hx t => pushed_full_slow e he hω hs hr.le hrπ hε hεL' d hδ
       (fun z hz => (hQ z hz).le) hxt hp hx t) hx hp
   exact (not_lt_of_ge hn) ha

end
end CylinderNonsqueezing
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.UpperBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace CylinderNonsqueezing
noncomputable section
open Set
open scoped ContDiff
open FourierPolynomial
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem radius_le_of_map_oai (j₀ : κ) {L R M : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (f : Vector κ → Vector κ) (hf : ContDiffOn ℝ ∞ f (PushedBall.domain L))
    (hi : InjOn f (PushedBall.domain L))
    (hω : ∀ z ∈ PushedBall.domain L, ComplexSymplectic.Preserves (fderiv ℝ f z))
    (hbounded : ∀ z ∈ PushedBall.domain L, ‖f z‖^2 ≤ M)
    (hcylinder : ∀ z ∈ PushedBall.domain L, ‖f z j₀‖^2 ≤ R) : L ≤ R := by
  let hU := PushedBall.isOpen_domain (κ := κ) L
  have hD (z) (hz : z ∈ PushedBall.domain L) := ComplexSymplectic.invertible (hω z hz)
  let e := EmbeddingInverse.localEquiv hU f hf hi hD
  exact radius_le_of_embedding j₀ hL hR hM e hf rfl hω
    (by rintro _ ⟨z,hz,rfl⟩; exact hbounded z hz)
    (by rintro _ ⟨z,hz,rfl⟩; exact hcylinder z hz)

end
end CylinderNonsqueezing
end

end OAI
end

theorem solution : type_of% @OAI.CylinderNonsqueezing.radius_le_of_map_oai := @OAI.CylinderNonsqueezing.radius_le_of_map_oai

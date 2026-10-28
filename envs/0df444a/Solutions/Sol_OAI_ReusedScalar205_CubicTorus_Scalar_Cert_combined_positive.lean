-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:47:40.419447+00:00
-- url     : https://prove2.me/submissions/fee5cfa0-fbe4-499a-89bc-521aecbae235

import Mathlib
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_102
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_106
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_110
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_114
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_118
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_122
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_126
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_130
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_134
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_138
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_142
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_146
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_150
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_154
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_158
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_162
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_concaveOn_baseline_corrected
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_gain_upper_support

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_AtanPoly
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

namespace CubicTorus.Shape

lemma positive_quadratic_root {a : ℝ} (ha : 0 < a) :
    let r := 2 / (1 + Real.sqrt (1 + 4 * a / Real.pi))
    0 < r ∧ r < 1 ∧ a * r ^ 2 = Real.pi * (1 - r) := by
  have hp := Real.pi_pos
  have hr : 1 < 1 + 4 * a / Real.pi := by
    have : 0 < 4 * a / Real.pi := by positivity
    linarith
  have hs0 := Real.sqrt_nonneg (1 + 4 * a / Real.pi)
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + 4 * a / Real.pi)
  have hs1 : 1 < Real.sqrt (1 + 4 * a / Real.pi) := by nlinarith
  have hd : 0 < 1 + Real.sqrt (1 + 4 * a / Real.pi) := by linarith
  refine ⟨div_pos (by norm_num) hd, (div_lt_one hd).2 (by linarith), ?_⟩
  generalize hz : Real.sqrt (1 + 4 * a / Real.pi) = z at *
  field_simp at hs ⊢
  nlinarith

lemma t_spec {h : ℝ} (hh : 0 < h) :
    0 < t h ∧ t h < 1 ∧ h ^ 2 * t h ^ 2 = Real.pi * (1 - t h) := by
  exact positive_quadratic_root (sq_pos_of_pos hh)

theorem interval_placement {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    (1033 / 2700 : ℝ) ≤ u h - dm ∧ (38 / 100 : ℝ) < u h - dm ∧
    1 / Real.pi < (38 / 100 : ℝ) ∧ u h ≤ 1 - 1 / Real.pi ∧
    u h < t h ∧ h * u h ≤ 24 / 25 := by
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hh0 : 0 < h := by linarith [hh.1]
  have hu1 : u h ≤ 1 - 1 / Real.pi := min_le_left _ _
  have huv : u h ≤ (24 / 25 : ℝ) / h := min_le_right _ _
  have hu : (16 / 27 : ℝ) ≤ u h := by
    apply le_min
    · apply (le_sub_iff_add_le).2
      have hip : 1 / Real.pi ≤ (1 / 3 : ℝ) := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_of_lt hp3))
      linarith
    · apply (le_div_iff₀ hh0).2
      linarith [hh.2]
  have hhU : h * u h ≤ 24 / 25 := by
    have := (le_div_iff₀ hh0).1 huv
    nlinarith
  have htr := t_spec hh0
  have hlt : u h < t h := by
    by_contra! hn
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt htr.1) hn 2) (sq_nonneg h)
    have hsq := pow_le_pow_left₀ (mul_nonneg (le_of_lt hh0) (by linarith : 0 ≤ u h)) hhU 2
    have hip : 1 ≤ Real.pi * (1 - u h) := by
      have hh := mul_le_mul_of_nonneg_left hu1 (le_of_lt hp)
      field_simp at hh
      nlinarith
    nlinarith [htr.2.2]
  refine ⟨?_, ?_, ?_, hu1, hlt, hhU⟩
  · dsimp [dm]; linarith
  · dsimp [dm]; linarith
  · apply (div_lt_iff₀ hp).2
    nlinarith

end CubicTorus.Shape
end
end
end
end ReusedScalar205
end
end

end OAI
end

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
open Set MeasureTheory
open _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma critical_spec {l a p q : ℝ} (hl : 0 < l) (ha : 0 < a) (hp : 0 < p)
    (hq : q ≠ 0) :
    0 < critical l a p q ∧ critical l a p q < p ∧
      3 * a * q ^ 2 * (critical l a p q) ^ 2 = 2 * l * (p - critical l a p q) := by
  have hz : 0 < 6 * a * q ^ 2 * p / l := by positivity
  have hs0 := Real.sqrt_nonneg (1 + 6 * a * q ^ 2 * p / l)
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + 6 * a * q ^ 2 * p / l)
  have hs1 : 1 < Real.sqrt (1 + 6 * a * q ^ 2 * p / l) := by nlinarith
  have hd : 0 < 1 + Real.sqrt (1 + 6 * a * q ^ 2 * p / l) := by linarith
  unfold critical
  refine ⟨div_pos (by positivity) hd, (div_lt_iff₀ hd).2 (by nlinarith), ?_⟩
  generalize hx : Real.sqrt (1 + 6 * a * q ^ 2 * p / l) = x at *
  field_simp at hs ⊢
  nlinarith

lemma cubic_energy_min {l a p q r w : ℝ} (hl : 0 ≤ l) (ha : 0 ≤ a)
    (hq : q ≠ 0) (hr : 0 ≤ r) (hw : 0 ≤ w)
    (hcrit : 3 * a * q ^ 2 * r ^ 2 = 2 * l * (p - r)) :
    l * ((p - r) / q) ^ 2 + a * r ^ 3 ≤ l * ((p - w) / q) ^ 2 + a * w ^ 3 := by
  have hq2 : 0 < q ^ 2 := sq_pos_of_ne_zero hq
  have hpoly : 0 ≤ (w - r) ^ 2 * (l + a * q ^ 2 * (w + 2 * r)) := by positivity
  have hid : (w - r) ^ 2 * (l + a * q ^ 2 * (w + 2 * r)) =
      l * (p - w) ^ 2 + a * q ^ 2 * w ^ 3 - (l * (p - r) ^ 2 + a * q ^ 2 * r ^ 3) := by
    linear_combination -(w - r) * hcrit
  rw [hid] at hpoly
  apply (mul_le_mul_iff_of_pos_right hq2).mp
  have heq (z : ℝ) : (l * ((p - z) / q) ^ 2 + a * z ^ 3) * q ^ 2 =
      l * (p - z) ^ 2 + a * q ^ 2 * z ^ 3 := by field_simp [hq]
  rw [heq r, heq w]
  linarith

lemma cappedEnergy_nonneg {l a d p q y : ℝ} (hl : 0 ≤ l) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    0 ≤ cappedEnergy l a d p q y := by
  unfold cappedEnergy
  positivity

lemma cappedInf_formula {l a d p q : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hd : 0 ≤ d) (hp : 0 < p) (hq : 0 < q) :
    cappedInf l a d p q =
      min (a * d ^ 3) (l * ((p - critical l a p q) / q) ^ 2 + a * (critical l a p q) ^ 3) := by
  let r := critical l a p q
  change cappedInf l a d p q = min (a * d ^ 3) (l * ((p - r) / q) ^ 2 + a * r ^ 3)
  obtain ⟨hr, hrp, hcrit⟩ := critical_spec hl ha hp hq.ne'
  change 0 < r at hr
  change r < p at hrp
  change 3 * a * q ^ 2 * r ^ 2 = 2 * l * (p - r) at hcrit
  have hmin (w : ℝ) (hw : 0 ≤ w) := cubic_energy_min hl.le ha.le hq.ne' hr.le hw hcrit
  have hbdd : BddBelow ((cappedEnergy l a d p q) '' Ici 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    exact cappedEnergy_nonneg hl.le ha.le hd
  have hmem (y : ℝ) (hy : 0 ≤ y) : cappedEnergy l a d p q y ∈
      (cappedEnergy l a d p q) '' Ici 0 := ⟨y, hy, rfl⟩
  apply le_antisymm
  · apply le_min
    · apply (csInf_le hbdd (hmem 0 le_rfl)).trans
      simp only [cappedEnergy, mul_zero, sub_zero, sq, zero_add]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min hd (le_max_right _ _)) (min_le_left _ _) _) ha.le
    · have hy : 0 ≤ (p - r) / q := div_nonneg (by linarith) hq.le
      apply (csInf_le hbdd (hmem _ hy)).trans
      have heq : p - q * ((p - r) / q) = r := by field_simp; ring
      simp only [cappedEnergy, heq, max_eq_left hr.le]
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min hd hr.le) (min_le_right _ _) _) ha.le
  · apply le_csInf ⟨_, hmem 0 le_rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    by_cases hcap : d ≤ max (p - q * y) 0
    · apply (min_le_left _ _).trans
      simp only [cappedEnergy, min_eq_left hcap]
      nlinarith [sq_nonneg y]
    · have hun : min d (max (p - q * y) 0) = max (p - q * y) 0 := min_eq_right (le_of_not_ge hcap)
      apply (min_le_right _ _).trans
      by_cases hw : 0 ≤ p - q * y
      · have heq : (p - (p - q * y)) / q = y := by field_simp; ring
        rw [cappedEnergy, hun, max_eq_left hw]
        simpa only [heq] using hmin (p - q * y) hw
      · have hw' : p - q * y ≤ 0 := (lt_of_not_ge hw).le
        have hy' : p / q ≤ y := (div_le_iff₀ hq).2 (by nlinarith)
        have hpq : 0 ≤ p / q := by positivity
        have hh := mul_le_mul_of_nonneg_left (sq_le_sq₀ hpq hy |>.2 hy') hl.le
        have hm := hmin 0 le_rfl
        simp only [sub_zero, zero_pow (by decide : 3 ≠ 0), mul_zero, add_zero] at hm
        rw [cappedEnergy, hun, max_eq_right hw']
        simpa only [zero_pow (by decide : 3 ≠ 0), mul_zero, add_zero] using hm.trans hh

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma gain_parameters_pos {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    0 < P h ∧ 0 < Q h ∧ 0 < C₀ h := by
  have hh0 : 0 < h := by linarith [hh.1]
  obtain ⟨ht0, ht1, ht⟩ := t_spec hh0
  have hht0 : 0 < h * t h := by positivity
  have hhtt : t h ≤ h * t h := by nlinarith [hh.1]
  have hht : (3 / 4 : ℝ) < h * t h := by
    by_contra! hn
    have hs := pow_le_pow_left₀ hht0.le hn 2
    have ht' : (h * t h) ^ 2 = Real.pi * (1 - t h) := by nlinarith only [ht]
    nlinarith [Real.pi_gt_three]
  have hu : (16 / 27 : ℝ) ≤ u h := by
    have := (interval_placement hh).1
    norm_num [dm] at this
    linarith
  have hR : (21 / 44 : ℝ) < 2 * h * t h / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).2
    have hπ : Real.pi < (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · unfold P
    linarith
  · unfold Q
    positivity
  · unfold C₀
    exact lt_min (by positivity) (by norm_num)

theorem gain_formula {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    gain h = min (C₀ h * dm ^ 3)
      (ell * ((P h - critical ell (C₀ h) (P h) (Q h)) / Q h) ^ 2 +
        C₀ h * (critical ell (C₀ h) (P h) (Q h)) ^ 3) := by
  obtain ⟨hp, hq, hc⟩ := gain_parameters_pos hh
  exact cappedInf_formula (by norm_num [ell]) hc (by norm_num [dm]) hp hq

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

lemma contDiff_t {n : WithTop ℕ∞} : ContDiff ℝ n t := by
  have hs : ContDiff ℝ n (fun h : ℝ ↦ Real.sqrt (1 + 4 * h ^ 2 / Real.pi)) :=
    (by fun_prop : ContDiff ℝ n (fun h : ℝ ↦ 1 + 4 * h ^ 2 / Real.pi)).sqrt
      (fun h ↦ ne_of_gt (by positivity))
  exact contDiff_const.div (contDiff_const.add hs) (fun h ↦ ne_of_gt (by positivity))

lemma contDiff_R {n : WithTop ℕ∞} : ContDiff ℝ n R :=
  ((contDiff_const.mul contDiff_id).mul contDiff_t).div_const Real.pi

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma t_positive (h : ℝ) : 0 < t h := by unfold t; positivity
lemma Q_positive (h : ℝ) : 0 < Q h := by unfold Q; have := t_positive h; positivity

lemma contDiff_Q {n : WithTop ℕ∞} : ContDiff ℝ n Q := by
  unfold Q
  apply contDiff_const.mul
  apply ContDiff.sqrt
  · exact contDiff_const.add ((contDiff_const.mul (contDiff_id.pow 2)).mul contDiff_t)
  · intro h
    have := t_positive h
    exact ne_of_gt (by positivity)

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma continuous_C₀ : Continuous C₀ := by unfold C₀; fun_prop

lemma continuousOn_u {a b : ℝ} (ha : 0 < a) : ContinuousOn u (Icc a b) := by
  exact continuousOn_const.inf (continuousOn_const.div continuousOn_id
    (fun h hh ↦ ne_of_gt (ha.trans_le hh.1)))

lemma continuousOn_P {a b : ℝ} (ha : 0 < a) : ContinuousOn P (Icc a b) := by
  exact ((continuousOn_u ha).sub continuousOn_const).add (contDiff_R (n := 0)).continuous.continuousOn

lemma continuousOn_critical {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun h ↦ critical ell (C₀ h) (P h) (Q h)) (Icc a b) := by
  unfold critical
  apply (continuousOn_const.mul (continuousOn_P ha)).div
  · apply continuousOn_const.add
    exact Real.continuous_sqrt.comp_continuousOn
      (continuousOn_const.add ((((continuousOn_const.mul continuous_C₀.continuousOn).mul
        ((contDiff_Q (n := 0)).continuous.continuousOn.pow 2)).mul (continuousOn_P ha)).div_const ell))
  · intro h _
    have := Real.sqrt_nonneg (1 + 6 * C₀ h * Q h ^ 2 * P h / ell)
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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_GainBounds
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
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma continuousOn_gain : ContinuousOn gain (Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) := by
  have hc := continuousOn_critical (a := (51 / 50 : ℝ)) (b := (81 / 50 : ℝ)) (by norm_num)
  have hP := continuousOn_P (a := (51 / 50 : ℝ)) (b := (81 / 50 : ℝ)) (by norm_num)
  have hQ := (contDiff_Q (n := 0)).continuous.continuousOn (s := Icc (51 / 50 : ℝ) (81 / 50 : ℝ))
  have hformula : ContinuousOn (fun h ↦ min (C₀ h * dm ^ 3)
      (ell * ((P h - critical ell (C₀ h) (P h) (Q h)) / Q h) ^ 2 +
        C₀ h * critical ell (C₀ h) (P h) (Q h) ^ 3)) (Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) := by
    apply (continuous_C₀.continuousOn.mul continuousOn_const).inf
    exact (continuousOn_const.mul (((hP.sub hc).div hQ (fun h _ ↦ (Q_positive h).ne')).pow 2)).add
      (continuous_C₀.continuousOn.mul (hc.pow 3))
  exact hformula.congr (fun h hh ↦ gain_formula hh)

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

theorem concaveOn_gain_corrected :
    ConcaveOn ℝ (Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) (fun h ↦ gain h - (1 / 5 : ℝ) * h ^ 2) := by
  convert concaveOn_sub_quadratic_of_support
    (K := (2 / 5 : ℝ)) continuousOn_gain (fun _ hh ↦ gain_upper_support hh) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma semiconcave_chord_bound {f : ℝ → ℝ} {a b c x : ℝ} (hab : a < b) (hc : 0 ≤ c)
    (hf : ConcaveOn ℝ (Icc a b) (fun y ↦ f y - c * y ^ 2)) (hx : x ∈ Icc a b) :
    min (f a) (f b) - c * (b - a) ^ 2 / 4 ≤ f x := by
  let w := (b - x) / (b - a)
  let v := (x - a) / (b - a)
  have hd : 0 < b - a := sub_pos.2 hab
  have hw : 0 ≤ w := div_nonneg (sub_nonneg.2 hx.2) hd.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.2 hx.1) hd.le
  have hsum : w + v = 1 := by dsimp [w, v]; field_simp; ring
  have harg : w * a + v * b = x := by dsimp [w, v]; field_simp; ring
  have hcon := hf.2 (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hw hv hsum
  simp only [smul_eq_mul, harg] at hcon
  have hmin : min (f a) (f b) ≤ w * f a + v * f b := by
    have ha := mul_le_mul_of_nonneg_left (min_le_left (f a) (f b)) hw
    have hb := mul_le_mul_of_nonneg_left (min_le_right (f a) (f b)) hv
    calc
      _ = w * min (f a) (f b) + v * min (f a) (f b) := by rw [← add_mul, hsum, one_mul]
      _ ≤ _ := add_le_add ha hb
  have hcorr : w * c * a ^ 2 + v * c * b ^ 2 - c * x ^ 2 = c * (x - a) * (b - x) := by
    dsimp [w, v]
    field_simp
    ring
  have hprod : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - a - b)]
  have hprod' := mul_le_mul_of_nonneg_left hprod hc
  nlinarith only [hcon, hmin, hcorr, hprod']

lemma combined_chord_lower {a b x l r : ℝ} (ha : (51 / 50 : ℝ) ≤ a)
    (hb : b ≤ (81 / 50 : ℝ)) (hab : a < b) (hx : x ∈ Icc a b)
    (hl : l ≤ baseline a + gain a) (hr : r ≤ baseline b + gain b) :
    min l r - (1 / a ^ 2 + (1 / 5 : ℝ)) * (b - a) ^ 2 / 4 ≤ baseline x + gain x := by
  have ha0 : 0 < a := by linarith
  have hg := concaveOn_gain_corrected.subset (Icc_subset_Icc ha hb) (convex_Icc a b)
  have hf : ConcaveOn ℝ (Icc a b)
      (fun y ↦ baseline y + gain y - (1 / a ^ 2 + (1 / 5 : ℝ)) * y ^ 2) := by
    apply ((concaveOn_baseline_corrected (b := b) ha0).add hg).congr
    intro y _
    dsimp
    ring
  have hbound := semiconcave_chord_bound hab (by positivity : 0 ≤ (1 : ℝ) / a ^ 2 + 1 / 5) hf hx
  have hmin := min_le_min hl hr
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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_GainEnclosure150
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
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma positive_102_106 {h : ℝ} (hh : h ∈ Set.Icc (51 / 50 : ℝ) (53 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_102 combined_lower_106
  have hp : (0 : ℝ) < min (1696987851 / 1000000000000 : ℝ) (588471367 / 500000000000 : ℝ) - (1 / (51 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((53 / 50 : ℝ) - (51 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_106_110 {h : ℝ} (hh : h ∈ Set.Icc (53 / 50 : ℝ) (11 / 10 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_106 combined_lower_110
  have hp : (0 : ℝ) < min (588471367 / 500000000000 : ℝ) (813603931 / 1000000000000 : ℝ) - (1 / (53 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((11 / 10 : ℝ) - (53 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_110_114 {h : ℝ} (hh : h ∈ Set.Icc (11 / 10 : ℝ) (57 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_110 combined_lower_114
  have hp : (0 : ℝ) < min (813603931 / 1000000000000 : ℝ) (598682283 / 1000000000000 : ℝ) - (1 / (11 / 10 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((57 / 50 : ℝ) - (11 / 10 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_114_118 {h : ℝ} (hh : h ∈ Set.Icc (57 / 50 : ℝ) (59 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_114 combined_lower_118
  have hp : (0 : ℝ) < min (598682283 / 1000000000000 : ℝ) (65023907 / 125000000000 : ℝ) - (1 / (57 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((59 / 50 : ℝ) - (57 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_118_122 {h : ℝ} (hh : h ∈ Set.Icc (59 / 50 : ℝ) (61 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_118 combined_lower_122
  have hp : (0 : ℝ) < min (65023907 / 125000000000 : ℝ) (562218681 / 1000000000000 : ℝ) - (1 / (59 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((61 / 50 : ℝ) - (59 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_122_126 {h : ℝ} (hh : h ∈ Set.Icc (61 / 50 : ℝ) (63 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_122 combined_lower_126
  have hp : (0 : ℝ) < min (562218681 / 1000000000000 : ℝ) (667302631 / 1000000000000 : ℝ) - (1 / (61 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((63 / 50 : ℝ) - (61 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_126_130 {h : ℝ} (hh : h ∈ Set.Icc (63 / 50 : ℝ) (13 / 10 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_126 combined_lower_130
  have hp : (0 : ℝ) < min (667302631 / 1000000000000 : ℝ) (23593217 / 31250000000 : ℝ) - (1 / (63 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((13 / 10 : ℝ) - (63 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_130_134 {h : ℝ} (hh : h ∈ Set.Icc (13 / 10 : ℝ) (67 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_130 combined_lower_134
  have hp : (0 : ℝ) < min (23593217 / 31250000000 : ℝ) (88422833 / 100000000000 : ℝ) - (1 / (13 / 10 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((67 / 50 : ℝ) - (13 / 10 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_134_138 {h : ℝ} (hh : h ∈ Set.Icc (67 / 50 : ℝ) (69 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_134 combined_lower_138
  have hp : (0 : ℝ) < min (88422833 / 100000000000 : ℝ) (507522239 / 500000000000 : ℝ) - (1 / (67 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((69 / 50 : ℝ) - (67 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_138_142 {h : ℝ} (hh : h ∈ Set.Icc (69 / 50 : ℝ) (71 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_138 combined_lower_142
  have hp : (0 : ℝ) < min (507522239 / 500000000000 : ℝ) (174959141 / 200000000000 : ℝ) - (1 / (69 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((71 / 50 : ℝ) - (69 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_142_146 {h : ℝ} (hh : h ∈ Set.Icc (71 / 50 : ℝ) (73 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_142 combined_lower_146
  have hp : (0 : ℝ) < min (174959141 / 200000000000 : ℝ) (602265089 / 1000000000000 : ℝ) - (1 / (71 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((73 / 50 : ℝ) - (71 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_146_150 {h : ℝ} (hh : h ∈ Set.Icc (73 / 50 : ℝ) (3 / 2 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_146 combined_lower_150
  have hp : (0 : ℝ) < min (602265089 / 1000000000000 : ℝ) (75655309 / 125000000000 : ℝ) - (1 / (73 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((3 / 2 : ℝ) - (73 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_150_154 {h : ℝ} (hh : h ∈ Set.Icc (3 / 2 : ℝ) (77 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_150 combined_lower_154
  have hp : (0 : ℝ) < min (75655309 / 125000000000 : ℝ) (1030551187 / 1000000000000 : ℝ) - (1 / (3 / 2 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((77 / 50 : ℝ) - (3 / 2 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_154_158 {h : ℝ} (hh : h ∈ Set.Icc (77 / 50 : ℝ) (79 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_154 combined_lower_158
  have hp : (0 : ℝ) < min (1030551187 / 1000000000000 : ℝ) (1976421667 / 1000000000000 : ℝ) - (1 / (77 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((79 / 50 : ℝ) - (77 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_158_162 {h : ℝ} (hh : h ∈ Set.Icc (79 / 50 : ℝ) (81 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_158 combined_lower_162
  have hp : (0 : ℝ) < min (1976421667 / 1000000000000 : ℝ) (1702298751 / 500000000000 : ℝ) - (1 / (79 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((81 / 50 : ℝ) - (79 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma combined_positive_oai {h : ℝ} (hh : h ∈ Set.Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hl := hh.1
  have hu := hh.2

  by_cases hx : h ≤ (53 / 50 : ℝ)
  · exact positive_102_106 ⟨by linarith, hx⟩
  have hl : (53 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (11 / 10 : ℝ)
  · exact positive_106_110 ⟨by linarith, hx⟩
  have hl : (11 / 10 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (57 / 50 : ℝ)
  · exact positive_110_114 ⟨by linarith, hx⟩
  have hl : (57 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (59 / 50 : ℝ)
  · exact positive_114_118 ⟨by linarith, hx⟩
  have hl : (59 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (61 / 50 : ℝ)
  · exact positive_118_122 ⟨by linarith, hx⟩
  have hl : (61 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (63 / 50 : ℝ)
  · exact positive_122_126 ⟨by linarith, hx⟩
  have hl : (63 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (13 / 10 : ℝ)
  · exact positive_126_130 ⟨by linarith, hx⟩
  have hl : (13 / 10 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (67 / 50 : ℝ)
  · exact positive_130_134 ⟨by linarith, hx⟩
  have hl : (67 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (69 / 50 : ℝ)
  · exact positive_134_138 ⟨by linarith, hx⟩
  have hl : (69 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (71 / 50 : ℝ)
  · exact positive_138_142 ⟨by linarith, hx⟩
  have hl : (71 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (73 / 50 : ℝ)
  · exact positive_142_146 ⟨by linarith, hx⟩
  have hl : (73 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (3 / 2 : ℝ)
  · exact positive_146_150 ⟨by linarith, hx⟩
  have hl : (3 / 2 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (77 / 50 : ℝ)
  · exact positive_150_154 ⟨by linarith, hx⟩
  have hl : (77 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (79 / 50 : ℝ)
  · exact positive_154_158 ⟨by linarith, hx⟩
  have hl : (79 / 50 : ℝ) < h := lt_of_not_ge hx

  exact positive_158_162 ⟨by linarith, hu⟩

end CubicTorus.Scalar.Cert

end
end
end
end ReusedScalar205

end

end

end OAI
end

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_positive_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_positive_oai

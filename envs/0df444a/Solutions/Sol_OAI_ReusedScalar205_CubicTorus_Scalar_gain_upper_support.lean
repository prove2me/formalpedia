-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.gain_upper_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:50:38.948565+00:00
-- url     : https://prove2.me/submissions/76540fcd-123f-49d1-bc06-205363712165

import Mathlib
import Definitions.Def_OAIQ079A003

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

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma nonneg_quadratic_sublevel {a r v : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hv : 0 ≤ v)
    (heq : r ^ 2 = a * (1 - r)) :
    v ^ 2 ≤ a * (1 - v) ↔ v ≤ r := by
  constructor
  · intro hn
    by_contra! hrv
    have hs := (sq_lt_sq₀ hr hv).2 hrv
    have hm := mul_le_mul_of_nonneg_left hrv.le ha
    nlinarith
  · intro hvr
    have hs := (sq_le_sq₀ hv hr).2 hvr
    have hm := mul_le_mul_of_nonneg_left hvr ha
    nlinarith

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

lemma monotoneOn_rho : MonotoneOn rho (Ici 0) := by
  intro k hk K hK hkK
  obtain ⟨hr, hr1, hs⟩ := rho_spec hk
  obtain ⟨hR, _, hS⟩ := rho_spec hK
  apply (nonneg_quadratic_sublevel (by positivity : 0 ≤ Real.pi * K ^ 2) hR hr hS).1
  rw [hs]
  have hh := (sq_le_sq₀ hk hK).2 hkK
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh Real.pi_pos.le) (by linarith)

lemma rho_at_inverse {h : ℝ} (hh : 0 < h) : rho (1 / h) = t h := by
  obtain ⟨ht, ht1, hs⟩ := t_spec hh
  obtain ⟨hr, _, hrs⟩ := rho_spec (show 0 ≤ (1 : ℝ) / h by positivity)
  have hts : (t h) ^ 2 = Real.pi * (1 / h) ^ 2 * (1 - t h) := by
    field_simp
    nlinarith only [hs]
  apply le_antisymm
  · exact (nonneg_quadratic_sublevel (by positivity) ht.le hr hts).1 hrs.le
  · exact (nonneg_quadratic_sublevel (by positivity) hr ht.le hrs).1 hts.le

lemma antitoneOn_t : AntitoneOn t (Ioi 0) := by
  intro h hh H hH hhH
  change 0 < h at hh
  change 0 < H at hH
  rw [← rho_at_inverse hh, ← rho_at_inverse hH]
  exact monotoneOn_rho (show 0 ≤ (1 : ℝ) / H by positivity) (show 0 ≤ (1 : ℝ) / h by positivity)
    (div_le_div_of_nonneg_left (by norm_num) hh hhH)

lemma monotoneOn_ht : MonotoneOn (fun h ↦ h * t h) (Ioi 0) := by
  intro h hh H hH hhH
  change 0 < h at hh
  change 0 < H at hH
  obtain ⟨ht, _, htS⟩ := t_spec hh
  obtain ⟨hT, _, hTS⟩ := t_spec hH
  have htT := antitoneOn_t hh hH hhH
  apply (sq_le_sq₀ (by positivity : 0 ≤ h * t h) (by positivity : 0 ≤ H * t H)).1
  have hm := mul_le_mul_of_nonneg_left htT Real.pi_pos.le
  nlinarith only [htS, hTS, hm]

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
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

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

end CubicTorus.Scalar

namespace CubicTorus.Reduction
open Set Filter
open scoped Topology

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

end CubicTorus.Reduction

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma second_deriv_linear_div (X : ℝ) {h : ℝ} (hh : h ≠ 0) :
    deriv (deriv (fun H ↦ X / H)) h = 2 * (X / h) / h ^ 2 := by
  have heq : deriv (fun H ↦ X / H) =ᶠ[𝓝 h] (fun H ↦ -X / H ^ 2) := by
    filter_upwards [eventually_ne_nhds hh] with H hH
    exact (hasDerivAt_divParam X hH).deriv
  rw [heq.deriv_eq, (hasDerivAt_divParamSlope X hh).deriv]
  ring

open MeasureTheory

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma contDiff_t {n : WithTop ℕ∞} : ContDiff ℝ n t := by
  have hs : ContDiff ℝ n (fun h : ℝ ↦ Real.sqrt (1 + 4 * h ^ 2 / Real.pi)) :=
    (by fun_prop : ContDiff ℝ n (fun h : ℝ ↦ 1 + 4 * h ^ 2 / Real.pi)).sqrt
      (fun h ↦ ne_of_gt (by positivity))
  exact contDiff_const.div (contDiff_const.add hs) (fun h ↦ ne_of_gt (by positivity))

lemma deriv_t_eq {h : ℝ} (hh : 0 < h) :
    deriv t h = -2 * h * t h ^ 2 / (Real.pi + 2 * h ^ 2 * t h) := by
  have ht := (contDiff_t (n := 1)).differentiable (by norm_num) h
  have hd := (((hasDerivAt_id h).pow 2).mul (ht.hasDerivAt.pow 2)).add
    (ht.hasDerivAt.const_mul Real.pi)
  have heq : (fun H : ℝ ↦ H ^ 2 * t H ^ 2 + Real.pi * t H) =ᶠ[𝓝 h]
      (fun _ ↦ Real.pi) := by
    filter_upwards [Ioi_mem_nhds hh] with H hH
    have := (t_spec hH).2.2
    nlinarith only [this]
  have hd' : HasDerivAt (fun H : ℝ ↦ H ^ 2 * t H ^ 2 + Real.pi * t H)
      (2 * h * t h ^ 2 + (Real.pi + 2 * h ^ 2 * t h) * deriv t h) h := by
    convert hd using 1 <;> try rfl
    dsimp
    ring
  have heq' := heq.deriv_eq
  rw [hd'.deriv, deriv_const] at heq'
  have hD : 0 < Real.pi + 2 * h ^ 2 * t h := by have := (t_spec hh).1; positivity
  apply (eq_div_iff hD.ne').2
  nlinarith only [heq']

lemma hasDerivAt_t {h : ℝ} (hh : 0 < h) :
    HasDerivAt t (-2 * h * t h ^ 2 / (Real.pi + 2 * h ^ 2 * t h)) h := by
  rw [← deriv_t_eq hh]
  exact ((contDiff_t (n := 1)).differentiable (by norm_num) h).hasDerivAt

lemma contDiff_R {n : WithTop ℕ∞} : ContDiff ℝ n R :=
  ((contDiff_const.mul contDiff_id).mul contDiff_t).div_const Real.pi

lemma hasDerivAt_R {h : ℝ} (hh : 0 < h) : HasDerivAt R (RSlope h) h := by
  obtain ⟨ht0, ht1, ht⟩ := t_spec hh
  have hD : Real.pi + 2 * h ^ 2 * t h ≠ 0 := ne_of_gt (by positivity)
  have h2 : 2 - t h ≠ 0 := ne_of_gt (by linarith)
  convert ((((hasDerivAt_id h).const_mul 2).mul (hasDerivAt_t hh)).div_const Real.pi) using 1 <;> try rfl
  dsimp [RSlope]
  field_simp [hD, h2]
  nlinarith only [ht]

lemma monotoneOn_R : MonotoneOn R (Ioi 0) := by
  intro h hh H hH hle
  unfold R
  exact div_le_div_of_nonneg_right (by nlinarith only [monotoneOn_ht hh hH hle]) Real.pi_pos.le

lemma antitoneOn_RSlope : AntitoneOn RSlope (Ioi 0) := by
  intro h hh H hH hle
  have htt := antitoneOn_t hh hH hle
  have ht0 := (t_spec hh).1
  have ht1 := (t_spec hh).2.1
  have hT0 := (t_spec hH).1
  unfold RSlope
  apply div_le_div₀ (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0.le htt 2) (by norm_num))
    (mul_pos Real.pi_pos (by linarith))
  exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le

lemma second_deriv_R_nonpos {h : ℝ} (hh : 0 < h) : deriv (deriv R) h ≤ 0 := by
  have heq : deriv R =ᶠ[𝓝 h] RSlope := by
    filter_upwards [Ioi_mem_nhds hh] with H hH
    exact (hasDerivAt_R hH).deriv
  rw [heq.deriv_eq]
  have hn := antitoneOn_RSlope.derivWithin_nonpos (x := h)
  rwa [derivWithin_of_mem_nhds (Ioi_mem_nhds hh)] at hn

lemma lt_t_of_quadratic {h r : ℝ} (hh : 0 < h) (_hr : 0 ≤ r)
    (hp : h ^ 2 * r ^ 2 < Real.pi * (1 - r)) : r < t h := by
  by_contra! hn
  obtain ⟨ht0, _, ht⟩ := t_spec hh
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0.le hn 2) (sq_nonneg h)
  have hπ := mul_le_mul_of_nonneg_left hn Real.pi_pos.le
  nlinarith only [hp, hm, ht, hπ]

lemma t_lt_of_quadratic {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r)
    (hp : Real.pi * (1 - r) < h ^ 2 * r ^ 2) : t h < r := by
  by_contra! hn
  obtain ⟨_, _, ht⟩ := t_spec hh
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hn 2) (sq_nonneg h)
  have hπ := mul_le_mul_of_nonneg_left hn Real.pi_pos.le
  nlinarith only [hp, hm, ht, hπ]

lemma gain_t_bounds {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    (16 / 25 : ℝ) < t h ∧ t h < 4 / 5 := by
  have hh0 : 0 < h := by linarith [hh.1]
  have hlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 51 / 50) hh.1 2
  have hhi := pow_le_pow_left₀ hh0.le hh.2 2
  constructor
  · apply lt_t_of_quadratic hh0 (by norm_num)
    nlinarith [Real.pi_gt_d4]
  · apply t_lt_of_quadratic hh0 (by norm_num)
    nlinarith [Real.pi_lt_d4]

lemma gain_R_bounds {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    (19 / 100 : ℝ) < RSlope h ∧ RSlope h < 17 / 50 ∧ R h < 671 / 1000 := by
  have hh0 : 0 < h := by linarith [hh.1]
  obtain ⟨htlo, hthi⟩ := gain_t_bounds hh
  have ht0 := (t_spec hh0).1
  have hden : 0 < Real.pi * (2 - t h) := mul_pos Real.pi_pos (by linarith)
  have htend : t (81 / 50 : ℝ) < 13 / 20 := by
    apply t_lt_of_quadratic (by norm_num) (by norm_num)
    nlinarith [Real.pi_lt_d4]
  have hRend := monotoneOn_R hh0 (by norm_num : (0 : ℝ) < 81 / 50) hh.2
  refine ⟨?_, ?_, hRend.trans_lt ?_⟩
  · apply (lt_div_iff₀ hden).2
    have hp : Real.pi < (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
    have hm := mul_le_mul_of_nonneg_right hp.le (show 0 ≤ 2 - t h by linarith)
    nlinarith
  · apply (div_lt_iff₀ hden).2
    have hp : (157 / 50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
    have hm := mul_le_mul_of_nonneg_right hp.le (show 0 ≤ 2 - t h by linarith)
    nlinarith
  · unfold R
    apply (div_lt_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_gt_d4]

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma t_positive (h : ℝ) : 0 < t h := by unfold t; positivity
lemma Q_positive (h : ℝ) : 0 < Q h := by unfold Q; have := t_positive h; positivity
lemma QRad_positive (h : ℝ) : 0 < QRad h := by unfold QRad; positivity

lemma contDiff_Q {n : WithTop ℕ∞} : ContDiff ℝ n Q := by
  unfold Q
  apply contDiff_const.mul
  apply ContDiff.sqrt
  · exact contDiff_const.add ((contDiff_const.mul (contDiff_id.pow 2)).mul contDiff_t)
  · intro h
    have := t_positive h
    exact ne_of_gt (by positivity)

lemma Q_fourth {h : ℝ} (hh : 0 < h) : Q h ^ 4 = 16 * QRad h / Real.pi ^ 3 := by
  have ht := (t_spec hh).2.2
  have hE : (Real.pi + 2 * h ^ 2 * t h) ^ 2 = Real.pi * QRad h := by
    calc
      _ = Real.pi ^ 2 + 4 * h ^ 2 * (h ^ 2 * t h ^ 2 + Real.pi * t h) := by ring
      _ = Real.pi * QRad h := by rw [ht]; unfold QRad; ring
  have hroot : Real.sqrt (Real.pi + 2 * h ^ 2 * t h) ^ 4 =
      (Real.pi + 2 * h ^ 2 * t h) ^ 2 := by
    calc
      _ = (Real.sqrt (Real.pi + 2 * h ^ 2 * t h) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by have := t_positive h; positivity)]
  unfold Q
  rw [mul_pow, hroot, hE]
  field_simp
  ring

lemma hasDerivAt_QRad (h : ℝ) : HasDerivAt QRad (8 * h) h := by
  convert (((hasDerivAt_id h).pow 2).const_mul 4).const_add Real.pi using 1 <;> try rfl
  dsimp
  ring

lemma deriv_Q_eq {h : ℝ} (hh : 0 < h) :
    deriv Q h = Q h * (2 * h / QRad h) := by
  have hQd := (contDiff_Q (n := 1)).differentiable (by norm_num) h
  have hdleft : HasDerivAt (fun H ↦ Q H ^ 4) (4 * Q h ^ 3 * deriv Q h) h := by
    convert hQd.hasDerivAt.pow 4 using 1
    all_goals try with_reducible_and_instances rfl
  have hdright : HasDerivAt (fun H ↦ 16 * QRad H / Real.pi ^ 3)
      (128 * h / Real.pi ^ 3) h := by
    convert ((hasDerivAt_QRad h).const_mul 16).div_const (Real.pi ^ 3) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have heq : (fun H ↦ Q H ^ 4) =ᶠ[𝓝 h] (fun H ↦ 16 * QRad H / Real.pi ^ 3) := by
    filter_upwards [Ioi_mem_nhds hh] with H hH
    exact Q_fourth hH
  have hd := heq.deriv_eq
  rw [hdleft.deriv, hdright.deriv] at hd
  have hArepr : QRad h = Q h ^ 4 * Real.pi ^ 3 / 16 := by
    rw [Q_fourth hh]
    field_simp
  rw [← mul_div_assoc]
  apply (eq_div_iff (QRad_positive h).ne').2
  calc
    deriv Q h * QRad h = deriv Q h * (Q h ^ 4 * Real.pi ^ 3 / 16) := by rw [hArepr]
    _ = (4 * Q h ^ 3 * deriv Q h) * (Q h * Real.pi ^ 3 / 64) := by ring
    _ = (128 * h / Real.pi ^ 3) * (Q h * Real.pi ^ 3 / 64) := by rw [hd]
    _ = Q h * (2 * h) := by field_simp; ring

lemma hasDerivAt_Q {h : ℝ} (hh : 0 < h) :
    HasDerivAt Q (Q h * (2 * h / QRad h)) h := by
  rw [← deriv_Q_eq hh]
  exact ((contDiff_Q (n := 1)).differentiable (by norm_num) h).hasDerivAt

lemma hasDerivAt_QLogSlope (h : ℝ) :
    HasDerivAt (fun H ↦ 2 * H / QRad H) ((2 * Real.pi - 8 * h ^ 2) / QRad h ^ 2) h := by
  convert ((hasDerivAt_id h).const_mul 2).div (hasDerivAt_QRad h) (QRad_positive h).ne' using 1 <;> try rfl
  dsimp [QRad]
  ring

lemma second_deriv_Q_eq {h : ℝ} (hh : 0 < h) :
    deriv (deriv Q) h = Q h * ((2 * Real.pi - 4 * h ^ 2) / QRad h ^ 2) := by
  have heq : deriv Q =ᶠ[𝓝 h] (fun H ↦ Q H * (2 * H / QRad H)) := by
    filter_upwards [Ioi_mem_nhds hh] with H hH
    exact deriv_Q_eq hH
  rw [heq.deriv_eq]
  have hd := ((hasDerivAt_Q hh).mul (hasDerivAt_QLogSlope h)).deriv
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma Q_log_bounds {h : ℝ} (hh : 0 < h) :
    0 < 2 * h / QRad h ∧ 2 * h / QRad h ≤ 1 / (2 * h) ∧
      -(1 / (4 * h ^ 2)) ≤ (2 * Real.pi - 4 * h ^ 2) / QRad h ^ 2 := by
  refine ⟨div_pos (by positivity) (QRad_positive h), ?_, ?_⟩
  · apply (div_le_div_iff₀ (QRad_positive h) (by positivity : 0 < 2 * h)).2
    unfold QRad
    nlinarith [Real.pi_pos]
  · rw [← neg_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * h ^ 2) (sq_pos_of_pos (QRad_positive h))).2
    unfold QRad
    nlinarith [sq_nonneg Real.pi, mul_nonneg Real.pi_pos.le (sq_nonneg h)]

end CubicTorus.Scalar

namespace CubicTorus.Reduction
open Set Filter
open scoped Topology

lemma second_deriv_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y ↦ f y + g y)) x = deriv (deriv f) x + deriv (deriv g) x := by
  have heq : (fun y ↦ f y + g y) = (fun y ↦ f y - -g y) := by funext y; ring
  rw [heq, second_deriv_sub hf hg.neg]
  simp

lemma second_deriv_mul {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y ↦ f y * g y)) x =
      deriv (deriv f) x * g x + 2 * deriv f x * deriv g x + f x * deriv (deriv g) x := by
  have heq : deriv (fun y ↦ f y * g y) =ᶠ[𝓝 x]
      (fun y ↦ deriv f y * g y + f y * deriv g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact deriv_fun_mul (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  have hfdd := (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgdd := (hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [heq.deriv_eq]
  have hd := ((hfdd.hasDerivAt.mul hgd.hasDerivAt).add
    (hfd.hasDerivAt.mul hgdd.hasDerivAt)).deriv
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma second_deriv_cube {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (fun y ↦ f y ^ 3)) x =
      6 * f x * deriv f x ^ 2 + 3 * f x ^ 2 * deriv (deriv f) x := by
  have heq : deriv (fun y ↦ f y ^ 3) =ᶠ[𝓝 x] (fun y ↦ 3 * f y ^ 2 * deriv f y) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    convert ((hy.differentiableAt (by norm_num)).hasDerivAt.pow 3).deriv using 1
    all_goals try with_reducible_and_instances rfl
  have hfd := hf.differentiableAt (by norm_num)
  have hfdd := (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [heq.deriv_eq]
  have hd := (((hfd.hasDerivAt.pow 2).const_mul 3).mul hfdd.hasDerivAt).deriv
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  ring

lemma second_deriv_mul_cube {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y ↦ f y * g y ^ 3)) x =
      deriv (deriv f) x * g x ^ 3 + 6 * deriv f x * g x ^ 2 * deriv g x +
        6 * f x * g x * deriv g x ^ 2 + 3 * f x * g x ^ 2 * deriv (deriv g) x := by
  rw [second_deriv_mul hf (hg.pow 3), second_deriv_cube hg]
  have heq : deriv (fun y ↦ g y ^ 3) x = 3 * g x ^ 2 * deriv g x := by
    convert ((hg.differentiableAt (by norm_num)).hasDerivAt.pow 3).deriv using 1
    all_goals try with_reducible_and_instances rfl
  rw [heq]
  ring

end CubicTorus.Reduction

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma planar_switch_bound : 1 - 1 / Real.pi < (24 / 35 : ℝ) := by
  have hp : (11 / 35 : ℝ) < 1 / Real.pi := (lt_div_iff₀ Real.pi_pos).2 (by linarith [Real.pi_lt_d4])
  linarith

lemma u_upper_support {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    ∃ U : ℝ → ℝ, UpperSupport u U h ∧
      -(49 / 100 : ℝ) ≤ deriv U h ∧ deriv U h ≤ 0 ∧
      0 ≤ deriv (deriv U) h ∧ deriv (deriv U) h ≤ 7 / 10 := by
  have hh0 : 0 < h := by linarith [hh.1]
  by_cases hb : 1 - 1 / Real.pi ≤ (24 / 25 : ℝ) / h
  · refine ⟨fun _ ↦ 1 - 1 / Real.pi, ⟨by fun_prop, (min_eq_left hb).symm,
      Filter.Eventually.of_forall (fun _ ↦ min_le_left _ _)⟩, ?_⟩
    norm_num
  · have hh14 : (7 / 5 : ℝ) < h := by
      have hr := (lt_of_not_ge hb).trans planar_switch_bound
      have := (div_lt_iff₀ hh0).1 hr
      linarith
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 5) hh14.le 2
    have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 5) hh14.le 3
    refine ⟨fun H ↦ (24 / 25 : ℝ) / H, ⟨contDiffAt_const.div contDiffAt_id hh0.ne',
      (min_eq_right (le_of_not_ge hb)).symm,
      Filter.Eventually.of_forall (fun _ ↦ min_le_right _ _)⟩, ?_⟩
    rw [(hasDerivAt_divParam (24 / 25) hh0.ne').deriv, second_deriv_linear_div _ hh0.ne']
    refine ⟨?_, div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg h), by positivity, ?_⟩
    · apply (le_div_iff₀ (sq_pos_of_pos hh0)).2
      nlinarith only [hsq]
    · have heq : 2 * ((24 / 25 : ℝ) / h) / h ^ 2 = (48 / 25 : ℝ) / h ^ 3 := by ring
      rw [heq]
      apply (div_le_iff₀ (pow_pos hh0 3)).2
      nlinarith only [hcube]

lemma C₀_upper_support {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    ∃ C : ℝ → ℝ, UpperSupport C₀ C h ∧
      0 ≤ deriv C h ∧ deriv C h ≤ 27 / 25 ∧
      0 ≤ deriv (deriv C) h ∧ deriv (deriv C) h ≤ 54 / 25 := by
  have hh0 : 0 < h := by linarith [hh.1]
  by_cases hc : (67 / 500 : ℝ) * h ^ 3 ≤ 9 / 25
  · refine ⟨fun H ↦ (67 / 500 : ℝ) * H ^ 3, ⟨by fun_prop, (min_eq_left hc).symm,
      Filter.Eventually.of_forall (fun _ ↦ min_le_left _ _)⟩, ?_⟩
    have hd : deriv (fun H : ℝ ↦ (67 / 500 : ℝ) * H ^ 3) = fun H ↦ (201 / 500 : ℝ) * H ^ 2 := by
      funext H
      convert (((hasDerivAt_id H).pow 3).const_mul (67 / 500)).deriv using 1 <;> try rfl
      dsimp
      ring
    rw [hd]
    have hd2 : deriv (fun H : ℝ ↦ (201 / 500 : ℝ) * H ^ 2) h = (201 / 250 : ℝ) * h := by
      convert (((hasDerivAt_id h).pow 2).const_mul (201 / 500)).deriv using 1 <;> try rfl
      dsimp
      ring
    rw [hd2]
    have hsq := pow_le_pow_left₀ hh0.le hh.2 2
    refine ⟨by positivity, ?_, by positivity, ?_⟩ <;> nlinarith [hh.2]
  · refine ⟨fun _ ↦ (9 / 25 : ℝ), ⟨by fun_prop, (min_eq_right (le_of_not_ge hc)).symm,
      Filter.Eventually.of_forall (fun _ ↦ min_le_right _ _)⟩, ?_⟩
    norm_num

lemma gain_cubic_jet_bound {C C' C'' w w' w'' : ℝ}
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hCmax : C ≤ 9 / 25) (hC'max : C' ≤ 27 / 25)
    (hC''max : C'' ≤ 54 / 25) (hw : 0 ≤ w) (hwmax : w ≤ dm)
    (hw'lo : -(1 / 2 : ℝ) ≤ w') (hw'hi : w' ≤ 17 / 50) (hw'' : w'' ≤ 4 / 5) :
    C'' * w ^ 3 + 6 * C' * w ^ 2 * w' + 6 * C * w * w' ^ 2 + 3 * C * w ^ 2 * w'' ≤ 2 / 5 := by
  have hdm : 0 ≤ dm := by norm_num [dm]
  have hw2 := pow_le_pow_left₀ hw hwmax 2
  have hw3 := pow_le_pow_left₀ hw hwmax 3
  have hdw : w' ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (w' + 1 / 2), mul_nonneg (by linarith : 0 ≤ w' + 1 / 2)
      (by linarith : 0 ≤ 1 / 2 - w')]
  have h1 : C'' * w ^ 3 ≤ (54 / 25 : ℝ) * dm ^ 3 := by
    exact (mul_le_mul_of_nonneg_right hC''max (pow_nonneg hw 3)).trans
      (mul_le_mul_of_nonneg_left hw3 (by norm_num))
  have h2 : 6 * C' * w ^ 2 * w' ≤ 6 * (27 / 25 : ℝ) * dm ^ 2 * (17 / 50) := by
    apply (mul_le_mul_of_nonneg_left hw'hi (by positivity : 0 ≤ 6 * C' * w ^ 2)).trans
    gcongr
  have h3 : 6 * C * w * w' ^ 2 ≤ 6 * (9 / 25 : ℝ) * dm * (1 / 4) := by
    gcongr
  have h4 : 3 * C * w ^ 2 * w'' ≤ 3 * (9 / 25 : ℝ) * dm ^ 2 * (4 / 5) := by
    apply (mul_le_mul_of_nonneg_left hw'' (by positivity : 0 ≤ 3 * C * w ^ 2)).trans
    gcongr
  norm_num [dm] at h1 h2 h3 h4
  linarith

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma gain_P_lt {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    P h < 9 / 25 := by
  have hu := (min_le_left (1 - 1 / Real.pi) ((24 / 25 : ℝ) / h)).trans_lt planar_switch_bound
  have hR := (gain_R_bounds hh).2.2
  change u h < _ at hu
  change u h - 1 + R h < _
  linarith

lemma gain_le_cappedEnergy {h y : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ))
    (hy : 0 ≤ y) : gain h ≤ cappedEnergy ell (C₀ h) dm (P h) (Q h) y := by
  have hc := (gain_parameters_pos hh).2.2
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨z, _, rfl⟩
    exact cappedEnergy_nonneg (by norm_num [ell]) hc.le (by norm_num [dm])
  · exact ⟨y, hy, rfl⟩

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

lemma active_upper_argument_jets {h y : ℝ} {U : ℝ → ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) (hy : 0 ≤ y)
    (hU : UpperSupport u U h)
    (hU'lo : -(49 / 100 : ℝ) ≤ deriv U h) (hU'hi : deriv U h ≤ 0)
    (hU''hi : deriv (deriv U) h ≤ 7 / 10)
    (hw : 0 < U h - 1 + R h - Q h * y) :
    let w := fun H ↦ U H - 1 + R H - Q H * y;
    -(1 / 2 : ℝ) ≤ deriv w h ∧ deriv w h ≤ 17 / 50 ∧ deriv (deriv w) h ≤ 4 / 5 := by
  have hh0 : 0 < h := by linarith [hh.1]
  have hh1 : (1 : ℝ) ≤ h := by linarith [hh.1]
  have hsq : (1 : ℝ) ≤ h ^ 2 := by nlinarith
  have hQy0 : 0 ≤ Q h * y := mul_nonneg (Q_positive h).le hy
  have hQy : Q h * y ≤ 9 / 25 := by
    rw [hU.contact] at hw
    have := gain_P_lt hh
    change u h - 1 + R h < _ at this
    linarith
  have hlog := Q_log_bounds hh0
  have hlog1 : 2 * h / QRad h ≤ 1 / 2 := hlog.2.1.trans
    ((div_le_div_iff₀ (by positivity : 0 < 2 * h) (by norm_num : (0 : ℝ) < 2)).2 (by linarith))
  have hlog2 : -(1 / 4 : ℝ) ≤ (2 * Real.pi - 4 * h ^ 2) / QRad h ^ 2 := by
    apply le_trans _ hlog.2.2
    have hb : (1 : ℝ) / (4 * h ^ 2) ≤ 1 / 4 :=
      (div_le_div_iff₀ (by positivity : 0 < 4 * h ^ 2) (by norm_num : (0 : ℝ) < 4)).2 (by linarith)
    linarith
  have hQ'0 : 0 ≤ deriv Q h * y := by
    rw [deriv_Q_eq hh0]
    exact mul_nonneg (mul_nonneg (Q_positive h).le hlog.1.le) hy
  have hQ' : deriv Q h * y ≤ 9 / 50 := by
    rw [deriv_Q_eq hh0, mul_right_comm]
    exact (mul_le_mul_of_nonneg_left hlog1 hQy0).trans
      (by nlinarith only [hQy])
  have hQ'' : -(9 / 100 : ℝ) ≤ deriv (deriv Q) h * y := by
    rw [second_deriv_Q_eq hh0, mul_right_comm]
    have hm := mul_le_mul_of_nonneg_left hlog2 hQy0
    nlinarith only [hm, hQy]
  have hR := gain_R_bounds hh
  have hR'' := second_deriv_R_nonpos hh0
  have hw' : deriv (fun H ↦ U H - 1 + R H - Q H * y) h = deriv U h + RSlope h - deriv Q h * y := by
    exact (((hU.smooth.differentiableAt (by norm_num)).hasDerivAt.sub_const 1).add
      (hasDerivAt_R hh0) |>.sub (((contDiff_Q (n := 1)).differentiable (by norm_num) h).hasDerivAt.mul_const y)).deriv
  have hw'' : deriv (deriv (fun H ↦ U H - 1 + R H - Q H * y)) h =
      deriv (deriv U) h + deriv (deriv R) h - deriv (deriv Q) h * y := by
    rw [second_deriv_sub ((hU.smooth.sub contDiffAt_const).add contDiff_R.contDiffAt)
      (contDiff_Q.contDiffAt.mul contDiffAt_const),
      second_deriv_add (hU.smooth.sub contDiffAt_const) contDiff_R.contDiffAt,
      second_deriv_sub hU.smooth contDiffAt_const,
      second_deriv_mul contDiff_Q.contDiffAt contDiffAt_const]
    simp
  dsimp only
  rw [hw', hw'']
  exact ⟨by linarith [hR.1], by linarith [hR.2.1], by linarith⟩

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma gain_upper_support_oai {h : ℝ} (hh : h ∈ Ioo (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    ∃ F : ℝ → ℝ, UpperSupport gain F h ∧ deriv (deriv F) h ≤ 2 / 5 := by
  have hcc : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ) := ⟨hh.1.le, hh.2.le⟩
  obtain ⟨hp, hq, hc⟩ := gain_parameters_pos hcc
  obtain ⟨C, hC, hC'lo, hC'hi, _, hC''hi⟩ := C₀_upper_support hcc
  let r := critical ell (C₀ h) (P h) (Q h)
  let y := (P h - r) / Q h
  obtain ⟨hr0, hrP, _⟩ := critical_spec (by norm_num [ell] : 0 < ell) hc hp hq.ne'
  change 0 < r at hr0
  change r < P h at hrP
  have hy : 0 ≤ y := div_nonneg (by linarith) hq.le
  have hval : gain h = min (C₀ h * dm ^ 3) (ell * y ^ 2 + C₀ h * r ^ 3) := gain_formula hcc
  by_cases hcap : C₀ h * dm ^ 3 ≤ ell * y ^ 2 + C₀ h * r ^ 3
  · refine ⟨fun H ↦ C H * dm ^ 3, ⟨hC.smooth.mul contDiffAt_const, ?_, ?_⟩, ?_⟩
    · rw [hC.contact, hval, min_eq_left hcap]
    · filter_upwards [hC.above, Ioo_mem_nhds hh.1 hh.2] with H hCH hH
      rw [gain_formula ⟨hH.1.le, hH.2.le⟩]
      exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hCH (by norm_num [dm]))
    · rw [second_deriv_mul hC.smooth contDiffAt_const]
      simp only [deriv_const, mul_zero, add_zero]
      have hb := mul_le_mul_of_nonneg_right hC''hi (by norm_num [dm] : 0 ≤ dm ^ 3)
      norm_num [dm] at hb ⊢
      linarith
  · have hrmax : r ≤ dm := by
      by_contra! hn
      have hpow := pow_le_pow_left₀ (by norm_num [dm] : 0 ≤ dm) hn.le 3
      have hm := mul_le_mul_of_nonneg_left hpow hc.le
      have hl : 0 ≤ ell * y ^ 2 := mul_nonneg (by norm_num [ell]) (sq_nonneg y)
      exact hcap (by linarith)
    obtain ⟨U, hU, hU'lo, hU'hi, _, hU''hi⟩ := u_upper_support hcc
    let w := fun H ↦ U H - 1 + R H - Q H * y
    have hw : w h = r := by
      dsimp [w, y]
      rw [hU.contact]
      have heq : u h - 1 + R h = P h := rfl
      rw [heq]
      field_simp
      ring
    have hw0 : 0 < w h := by rw [hw]; exact hr0
    have hws : ContDiffAt ℝ 2 w h :=
      ((hU.smooth.sub contDiffAt_const).add contDiff_R.contDiffAt).sub
        (contDiff_Q.contDiffAt.mul contDiffAt_const)
    have hevent : ∀ᶠ H in 𝓝 h, 0 < w H := hws.continuousAt.eventually (Ioi_mem_nhds hw0)
    have hj := active_upper_argument_jets hcc hy hU hU'lo hU'hi hU''hi hw0
    change -(1 / 2 : ℝ) ≤ deriv w h ∧ deriv w h ≤ 17 / 50 ∧ deriv (deriv w) h ≤ 4 / 5 at hj
    refine ⟨fun H ↦ ell * y ^ 2 + C H * w H ^ 3,
      ⟨contDiffAt_const.add (hC.smooth.mul (hws.pow 3)), ?_, ?_⟩, ?_⟩
    · rw [hC.contact, hw, hval, min_eq_right (le_of_not_ge hcap)]
    · filter_upwards [hC.above, hU.above, hevent, Ioo_mem_nhds hh.1 hh.2]
        with H hCH hUH hwH hH
      have hCH0 := (gain_parameters_pos ⟨hH.1.le, hH.2.le⟩).2.2.le
      apply (gain_le_cappedEnergy ⟨hH.1.le, hH.2.le⟩ hy).trans
      unfold cappedEnergy
      apply add_le_add_right
      apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (le_min (by norm_num [dm]) (le_max_right _ _)) ?_ 3) hCH0).trans
      · exact mul_le_mul_of_nonneg_right hCH (pow_nonneg hwH.le 3)
      · apply (min_le_right _ _).trans
        apply max_le _ hwH.le
        change u H - 1 + R H - Q H * y ≤ U H - 1 + R H - Q H * y
        linarith
    · rw [second_deriv_add contDiffAt_const (hC.smooth.mul (hws.pow 3))]
      rw [second_deriv_mul_cube hC.smooth hws]
      simp only [deriv_const', deriv_const, zero_add]
      apply gain_cubic_jet_bound
      · rw [hC.contact]; exact hc.le
      · exact hC'lo
      · rw [hC.contact]; exact min_le_right _ _
      · exact hC'hi
      · exact hC''hi
      · rw [hw]; exact hr0.le
      · rw [hw]; exact hrmax
      · exact hj.1
      · exact hj.2.1
      · exact hj.2.2

end CubicTorus.Scalar

end
end
end
end ReusedScalar205
end
end

end OAI
end

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.gain_upper_support_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.gain_upper_support_oai

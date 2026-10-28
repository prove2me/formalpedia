-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_162
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:47:17.893473+00:00
-- url     : https://prove2.me/submissions/49a5c32d-3c70-4d83-866c-ba2c3e642660

import Mathlib
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_linearBaseline_eq_of_range

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

namespace CubicTorus.Arithmetic
open Set Filter
open scoped Topology

lemma atan_terms_antitone {x : ℝ} (hx : x ∈ Icc 0 1) :
    Antitone (fun n : ℕ ↦ x ^ (2 * n + 1) / ↑(2 * n + 1)) := by
  apply antitone_nat_of_succ_le
  intro n
  calc
    _ ≤ x ^ (2 * n + 1) / ↑(2 * (n + 1) + 1) :=
      div_le_div_of_nonneg_right (pow_le_pow_of_le_one hx.1 hx.2 (by omega)) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hx.1 _) (by positivity) (by norm_cast; omega)

lemma atanPoly_bounds {x : ℝ} (hx : x ∈ Ico 0 1) (n : ℕ) :
    atanPoly (2 * n) x ≤ Real.arctan x ∧ Real.arctan x ≤ atanPoly (2 * n + 1) x := by
  have hs := (Real.hasSum_arctan (show ‖x‖ < 1 by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)).tendsto_sum_nat
  have ha := atan_terms_antitone ⟨hx.1, hx.2.le⟩
  have heq : (fun k : ℕ ↦ ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / ↑(2 * i + 1))) =
      (fun k : ℕ ↦ ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ↑(2 * i + 1)) := by
    funext k
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← heq] at hs
  exact ⟨by simpa only [atanPoly, mul_div_assoc] using ha.alternating_series_le_tendsto hs n,
    by simpa only [atanPoly, mul_div_assoc] using ha.tendsto_le_alternating_series hs n⟩

lemma atanHalf_spec {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ atanHalf x ∧ atanHalf x < 1 ∧ 2 * Real.arctan (atanHalf x) = Real.arctan x := by
  have hs0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2)
  have hsx : x < Real.sqrt (1 + x ^ 2) := by nlinarith
  have hd : 0 < 1 + Real.sqrt (1 + x ^ 2) := by positivity
  have hz0 : 0 ≤ atanHalf x := div_nonneg hx hd.le
  have hz1 : atanHalf x < 1 := (div_lt_one hd).2 (by linarith)
  refine ⟨hz0, hz1, ?_⟩
  rw [Real.two_mul_arctan (by linarith) hz1]
  congr 1
  have hzden : 1 - atanHalf x ^ 2 ≠ 0 := by
    have := (sq_lt_sq₀ hz0 (by norm_num : (0 : ℝ) ≤ 1)).2 hz1
    nlinarith
  apply (div_eq_iff hzden).2
  unfold atanHalf
  field_simp
  nlinarith

lemma arcsin_quarter {z : ℝ} (hz : z ∈ Ico 0 1) :
    0 ≤ asinQuarterArg z ∧ asinQuarterArg z < 1 ∧
      Real.arcsin z = 4 * Real.arctan (asinQuarterArg z) := by
  let b := Real.sqrt (1 - z ^ 2)
  have hsq : z ^ 2 < 1 := by simpa only [one_pow] using (sq_lt_sq₀ hz.1 (by norm_num : (0 : ℝ) ≤ 1)).2 hz.2
  have hb0 : 0 < b := Real.sqrt_pos.2 (by linarith)
  have hb : b ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by linarith)
  let k := z / (1 + b)
  have hk0 : 0 ≤ k := div_nonneg hz.1 (by positivity)
  have hk1 : k < 1 := (div_lt_one (by positivity)).2 (by linarith [hz.2])
  obtain ⟨hv0, hv1, hv⟩ := atanHalf_spec hk0
  refine ⟨hv0, hv1, ?_⟩
  change Real.arcsin z = 4 * Real.arctan (atanHalf k)
  have hk : 2 * Real.arctan k = Real.arcsin z := by
    rw [Real.two_mul_arctan (by linarith) hk1, Real.arcsin_eq_arctan ⟨by linarith [hz.1], hz.2⟩]
    congr 1
    change 2 * k / (1 - k ^ 2) = z / b
    have hd : 1 - k ^ 2 ≠ 0 := by nlinarith
    apply (div_eq_div_iff hd hb0.ne').2
    dsimp [k]
    field_simp
    have hbz := congrArg (fun t : ℝ ↦ z * t) hb
    nlinarith only [hbz]
  linarith

lemma arcsin_enclosure {z l u : ℝ} (hz : z ∈ Ico 0 1)
    (hl : l ∈ Ico 0 1) (hu : u ∈ Ico 0 1)
    (hlo : l ≤ asinQuarterArg z) (hhi : asinQuarterArg z ≤ u) (n : ℕ) :
    4 * atanPoly (2 * n) l ≤ Real.arcsin z ∧
      Real.arcsin z ≤ 4 * atanPoly (2 * n + 1) u := by
  rw [(arcsin_quarter hz).2.2]
  exact ⟨mul_le_mul_of_nonneg_left ((atanPoly_bounds hl n).1.trans (Real.arctan_mono hlo)) (by norm_num),
    mul_le_mul_of_nonneg_left ((Real.arctan_mono hhi).trans (atanPoly_bounds hu n).2) (by norm_num)⟩

end CubicTorus.Arithmetic

namespace CubicTorus.Arithmetic

lemma Encl.exact (x : ℝ) : Encl x x x := ⟨le_rfl, le_rfl⟩

lemma Encl.add {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hL : L ≤ l + p) (hU : u + q ≤ U) : Encl (x + y) L U :=
  ⟨hL.trans (add_le_add hx.1 hy.1), (add_le_add hx.2 hy.2).trans hU⟩

lemma Encl.sub {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hL : L ≤ l - q) (hU : u - p ≤ U) : Encl (x - y) L U :=
  ⟨hL.trans (sub_le_sub hx.1 hy.2), (sub_le_sub hx.2 hy.1).trans hU⟩

lemma Encl.mul_nonneg {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hl : 0 ≤ l) (hp : 0 ≤ p) (hL : L ≤ l * p) (hU : u * q ≤ U) : Encl (x * y) L U := by
  refine ⟨hL.trans (mul_le_mul hx.1 hy.1 hp (hl.trans hx.1)), ?_⟩
  exact (mul_le_mul hx.2 hy.2 (hp.trans hy.1) (hl.trans (hx.1.trans hx.2))).trans hU

lemma Encl.div_nonneg {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hl : 0 ≤ l) (hp : 0 < p) (hL : L * q ≤ l) (hU : u ≤ U * p) : Encl (x / y) L U := by
  have hy0 := hp.trans_le hy.1
  have hq0 := hy0.trans_le hy.2
  have hu0 := hl.trans (hx.1.trans hx.2)
  have hU0 : 0 ≤ U := by nlinarith
  constructor
  · calc
      L ≤ l / q := (le_div_iff₀ hq0).2 hL
      _ ≤ x / y := div_le_div₀ (hl.trans hx.1) hx.1 hy0 hy.2
  · exact (div_le_iff₀ hy0).2 (hx.2.trans (hU.trans (mul_le_mul_of_nonneg_left hy.1 hU0)))

lemma Encl.sqrt {x l u L U : ℝ} (hx : Encl x l u)
    (hL0 : 0 ≤ L) (hU0 : 0 ≤ U) (hL : L ^ 2 ≤ l) (hU : u ≤ U ^ 2) : Encl (Real.sqrt x) L U := by
  have hx0 : 0 ≤ x := (sq_nonneg L).trans (hL.trans hx.1)
  exact ⟨(Real.le_sqrt hL0 hx0).2 (hL.trans hx.1), (Real.sqrt_le_iff).2 ⟨hU0, hx.2.trans hU⟩⟩

lemma Encl.min {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hL : L ≤ min l p) (hU : min u q ≤ U) : Encl (min x y) L U :=
  ⟨hL.trans (min_le_min hx.1 hy.1), (min_le_min hx.2 hy.2).trans hU⟩

lemma Encl.arcsin {z a b L U : ℝ} (hz : z ∈ Set.Ico 0 1)
    (ha : a ∈ Set.Ico 0 1) (hb : b ∈ Set.Ico 0 1)
    (harg : Encl (asinQuarterArg z) a b) (n : ℕ)
    (hL : L ≤ 4 * atanPoly (2 * n) a) (hU : 4 * atanPoly (2 * n + 1) b ≤ U) :
    Encl (Real.arcsin z) L U :=
  (arcsin_enclosure hz ha hb harg.1 harg.2 n).imp (hL.trans ·) (·.trans hU)

end CubicTorus.Arithmetic

namespace CubicTorus.Arithmetic
lemma Encl.pow {x l u L U : ℝ} (hx : Encl x l u) (hl : 0 ≤ l) (n : ℕ)
    (hL : L ≤ l ^ n) (hU : u ^ n ≤ U) : Encl (x ^ n) L U :=
  ⟨hL.trans (pow_le_pow_left₀ hl hx.1 n), (pow_le_pow_left₀ (hl.trans hx.1) hx.2 n).trans hU⟩
end CubicTorus.Arithmetic

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

namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma b0 : Encl e0 (314159265358979 / 100000000000000 : ℝ) (15707963267949 / 5000000000000 : ℝ) := by
  change Encl Real.pi _ _
  constructor
  · have := Real.pi_gt_d20; norm_num at this ⊢; linarith
  · have := Real.pi_lt_d20; norm_num at this ⊢; linarith

lemma b1 : Encl e1 (48 : ℝ) (48 : ℝ) := by
  exact Encl.exact (48 : ℝ)

lemma b2 : Encl e2 (277128129211 / 40000000000 : ℝ) (1732050807569 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3 : Encl e3 (7 : ℝ) (7 : ℝ) := by
  exact Encl.exact (7 : ℝ)

lemma b4 : Encl e4 (98974331861 / 100000000000 : ℝ) (989743318611 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2 b3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b5 : Encl e5 (1 : ℝ) (1 : ℝ) := by
  exact Encl.exact (1 : ℝ)

lemma b6 : Encl e6 (318309886183 / 1000000000000 : ℝ) (39788735773 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b5 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b7 : Encl e7 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b6 (by norm_num) (by norm_num)

lemma b8 : Encl e8 (49 / 50 : ℝ) (49 / 50 : ℝ) := by
  exact Encl.exact (49 / 50 : ℝ)

lemma b9 : Encl e9 (7 / 25 : ℝ) (7 / 25 : ℝ) := by
  exact Encl.exact (7 / 25 : ℝ)

lemma b10 : Encl e10 (21 / 100 : ℝ) (21 / 100 : ℝ) := by
  exact Encl.exact (21 / 100 : ℝ)

lemma b17 : Encl e17 (4 : ℝ) (4 : ℝ) := by
  exact Encl.exact (4 : ℝ)

lemma b23 : Encl e23 (2 : ℝ) (2 : ℝ) := by
  exact Encl.exact (2 : ℝ)

lemma b29 : Encl e29 (2 / 3 : ℝ) (2 / 3 : ℝ) := by
  exact Encl.exact (2 / 3 : ℝ)

lemma b35 : Encl e35 (3 : ℝ) (3 : ℝ) := by
  exact Encl.exact (3 : ℝ)

lemma b43 : Encl e43 (50 : ℝ) (50 : ℝ) := by
  exact Encl.exact (50 : ℝ)

lemma b59 : Encl e59 (51 / 100 : ℝ) (51 / 100 : ℝ) := by
  exact Encl.exact (51 / 100 : ℝ)

lemma b61 : Encl e61 (49 / 100 : ℝ) (49 / 100 : ℝ) := by
  exact Encl.exact (49 / 100 : ℝ)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures72To288
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
lemma b159 : Encl e159 (979591836733 / 1000000000000 : ℝ) (15306122449 / 15625000000 : ℝ) := by
  exact Encl.pow b4 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b162 : Encl e162 (318877551 / 15625000000 : ℝ) (20408163267 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b159 (by norm_num) (by norm_num)

lemma b163 : Encl e163 (35714285713 / 250000000000 : ℝ) (8928571429 / 62500000000 : ℝ) := by
  exact Encl.sqrt b162 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b169 : Encl e169 (285714285713 / 250000000000 : ℝ) (71428571429 / 62500000000 : ℝ) := by
  exact Encl.add b5 b163 (by norm_num) (by norm_num)

lemma b170 : Encl e170 (433012701889 / 500000000000 : ℝ) (866025403789 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b169 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b171 : Encl e171 (187499999997 / 250000000000 : ℝ) (93750000001 / 125000000000 : ℝ) := by
  exact Encl.pow b170 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b172 : Encl e172 (437499999997 / 250000000000 : ℝ) (218750000001 / 125000000000 : ℝ) := by
  exact Encl.add b5 b171 (by norm_num) (by norm_num)

lemma b173 : Encl e173 (1322875655527 / 1000000000000 : ℝ) (82679728471 / 62500000000 : ℝ) := by
  exact Encl.sqrt b172 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b174 : Encl e174 (2322875655527 / 1000000000000 : ℝ) (145179728471 / 62500000000 : ℝ) := by
  exact Encl.add b5 b173 (by norm_num) (by norm_num)

lemma b175 : Encl e175 (372824693269 / 1000000000000 : ℝ) (93206173319 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b170 b174 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b176 : Encl e176 (713724378853 / 500000000000 : ℝ) (1427448757923 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e4) (a := (372824693269 / 1000000000000 : ℝ)) (b := (93206173319 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (98974331861 / 100000000000 : ℝ) by norm_num).trans b4.1
        exact b4.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e4) (372824693269 / 1000000000000 : ℝ) (93206173319 / 250000000000 : ℝ) from b175) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b177 : Encl e177 (72799886643 / 100000000000 : ℝ) (727998866541 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b176 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b178 : Encl e178 (242487113059 / 500000000000 : ℝ) (12124355653 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b179 : Encl e179 (692820323 / 10000000000 : ℝ) (69282032307 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b178 b163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b180 : Encl e180 (658716834123 / 1000000000000 : ℝ) (658716834241 / 1000000000000 : ℝ) := by
  exact Encl.sub b177 b179 (by norm_num) (by norm_num)

lemma b181 : Encl e181 (35714285713 / 5000000000 : ℝ) (8928571429 / 1250000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b182 : Encl e182 (69282032299 / 500000000000 : ℝ) (138564064611 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b181 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b183 : Encl e183 (65019096189 / 125000000000 : ℝ) (520152769643 / 1000000000000 : ℝ) := by
  exact Encl.sub b180 b182 (by norm_num) (by norm_num)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures726To944
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
lemma b924 : Encl e924 (24 / 25 : ℝ) (24 / 25 : ℝ) := by
  exact Encl.exact (24 / 25 : ℝ)

lemma b932 : Encl e932 (636619772367 / 1000000000000 : ℝ) (39788735773 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b23 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b939 : Encl e939 (67 / 500 : ℝ) (67 / 500 : ℝ) := by
  exact Encl.exact (67 / 500 : ℝ)

lemma b941 : Encl e941 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.exact (9 / 25 : ℝ)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures945To1164
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
lemma b944 : Encl e944 (6 : ℝ) (6 : ℝ) := by
  exact Encl.exact (6 : ℝ)

lemma b954 : Encl e954 (9261 / 1000000 : ℝ) (9261 / 1000000 : ℝ) := by
  exact Encl.pow b10 (by norm_num) 3 (by norm_num) (by norm_num)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures2921To3142
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

lemma b3106 : Encl e3106 (81 / 50 : ℝ) (81 / 50 : ℝ) := by
  exact Encl.exact (81 / 50 : ℝ)

lemma b3107 : Encl e3107 (515662015617 / 1000000000000 : ℝ) (257831007809 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3106 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3108 : Encl e3108 (3969 / 2500 : ℝ) (3969 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b3106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3109 : Encl e3109 (101069755061 / 200000000000 : ℝ) (252674387653 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3108 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3110 : Encl e3110 (6561 / 2500 : ℝ) (6561 / 2500 : ℝ) := by
  exact Encl.pow b3106 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3111 : Encl e3111 (6561 / 625 : ℝ) (6561 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b3110 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3112 : Encl e3112 (1670744930601 / 500000000000 : ℝ) (3341489861203 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3111 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3113 : Encl e3113 (2170744930601 / 500000000000 : ℝ) (4341489861203 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3112 (by norm_num) (by norm_num)

lemma b3114 : Encl e3114 (260453026631 / 125000000000 : ℝ) (2083624213049 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3113 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3115 : Encl e3115 (385453026631 / 125000000000 : ℝ) (3083624213049 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3114 (by norm_num) (by norm_num)

lemma b3116 : Encl e3116 (648587461317 / 1000000000000 : ℝ) (648587461319 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b3115 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3117 : Encl e3117 (11350280573 / 62500000000 : ℝ) (18160448917 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3118 : Encl e3118 (686953264473 / 1000000000000 : ℝ) (171738316119 / 250000000000 : ℝ) := by
  exact Encl.add b3109 b3117 (by norm_num) (by norm_num)

lemma b3119 : Encl e3119 (-313046735527 / 1000000000000 : ℝ) (-78261683881 / 250000000000 : ℝ) := by
  exact Encl.sub b3118 b5 (by norm_num) (by norm_num)

lemma b3120 : Encl e3120 (598535408777 / 500000000000 : ℝ) (239414163511 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b3110 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3121 : Encl e3121 (5318146287 / 20000000000 : ℝ) (16619207147 / 62500000000 : ℝ) := by
  exact Encl.pow b3107 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3122 : Encl e3122 (45880792853 / 62500000000 : ℝ) (14681853713 / 20000000000 : ℝ) := by
  exact Encl.sub b5 b3121 (by norm_num) (by norm_num)

lemma b3123 : Encl e3123 (428396045047 / 500000000000 : ℝ) (53549505631 / 62500000000 : ℝ) := by
  exact Encl.sqrt b3122 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3124 : Encl e3124 (-19012542343 / 100000000000 : ℝ) (-190125423427 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b3123 (by norm_num) (by norm_num)

lemma b3125 : Encl e3125 (314482403229 / 500000000000 : ℝ) (9827575101 / 15625000000 : ℝ) := by
  exact Encl.pow b3123 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b3126 : Encl e3126 (104827467743 / 500000000000 : ℝ) (3275858367 / 15625000000 : ℝ) := by
  exact Encl.div_nonneg b3125 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3127 : Encl e3127 (2441189007 / 125000000000 : ℝ) (19529512061 / 1000000000000 : ℝ) := by
  exact Encl.add b3124 b3126 (by norm_num) (by norm_num)

lemma b3128 : Encl e3128 (9569460907 / 500000000000 : ℝ) (956946091 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b3127 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3129 : Encl e3129 (62070440991 / 200000000000 : ℝ) (310352204959 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3121 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3130 : Encl e3130 (-337929559009 / 200000000000 : ℝ) (-1689647795041 / 1000000000000 : ℝ) := by
  exact Encl.sub b3129 b23 (by norm_num) (by norm_num)

lemma b3131 : Encl e3131 (428396045047 / 250000000000 : ℝ) (53549505631 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3132 : Encl e3132 (23936385143 / 1000000000000 : ℝ) (23936385151 / 1000000000000 : ℝ) := by
  exact Encl.add b3130 b3131 (by norm_num) (by norm_num)

lemma b3133 : Encl e3133 (239363851 / 500000000000 : ℝ) (59840963 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b3132 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3134 : Encl e3134 (1866019411 / 100000000000 : ℝ) (9330097059 / 500000000000 : ℝ) := by
  exact Encl.sub b3128 b3133 (by norm_num) (by norm_num)

lemma b3135 : Encl e3135 (11168786909 / 500000000000 : ℝ) (22337573829 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3120 b3134 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3136 : Encl e3136 (-290709161709 / 1000000000000 : ℝ) (-58141832339 / 200000000000 : ℝ) := by
  exact Encl.add b3119 b3135 (by norm_num) (by norm_num)

lemma b3137 : Encl e3137 (928396045047 / 500000000000 : ℝ) (116049505631 / 62500000000 : ℝ) := by
  exact Encl.add b5 b3123 (by norm_num) (by norm_num)

lemma b3138 : Encl e3138 (277716615859 / 1000000000000 : ℝ) (277716615861 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3107 b3137 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3139 : Encl e3139 (19281629681 / 250000000000 : ℝ) (38563259363 / 500000000000 : ℝ) := by
  exact Encl.pow b3138 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3140 : Encl e3140 (269281629681 / 250000000000 : ℝ) (538563259363 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3139 (by norm_num) (by norm_num)

lemma b3141 : Encl e3141 (1037847059409 / 1000000000000 : ℝ) (1037847059411 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3140 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3142 : Encl e3142 (2037847059409 / 1000000000000 : ℝ) (2037847059411 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3141 (by norm_num) (by norm_num)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures3143To3335
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

lemma b3143 : Encl e3143 (136279420271 / 1000000000000 : ℝ) (136279420273 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3138 b3142 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3144 : Encl e3144 (541780137497 / 1000000000000 : ℝ) (270890068753 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e3107) (a := (136279420271 / 1000000000000 : ℝ)) (b := (136279420273 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (515662015617 / 1000000000000 : ℝ) by norm_num).trans b3107.1
        exact b3107.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e3107) (136279420271 / 1000000000000 : ℝ) (136279420273 / 1000000000000 : ℝ) from b3143) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b3145 : Encl e3145 (276307870123 / 1000000000000 : ℝ) (276307870129 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b3144 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3146 : Encl e3146 (63168596913 / 250000000000 : ℝ) (252674387653 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b3107 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3147 : Encl e3147 (216489416709 / 1000000000000 : ℝ) (216489416711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3146 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3148 : Encl e3148 (14954613353 / 250000000000 : ℝ) (2990922671 / 50000000000 : ℝ) := by
  exact Encl.sub b3145 b3147 (by norm_num) (by norm_num)

lemma b3149 : Encl e3149 (428396045047 / 10000000000 : ℝ) (53549505631 / 1250000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3150 : Encl e3150 (6018519797 / 500000000000 : ℝ) (2407407919 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b3107 b3149 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3151 : Encl e3151 (47781413817 / 1000000000000 : ℝ) (23890706913 / 500000000000 : ℝ) := by
  exact Encl.sub b3148 b3150 (by norm_num) (by norm_num)

lemma b3152 : Encl e3152 (236185677843 / 500000000000 : ℝ) (236185677913 / 500000000000 : ℝ) := by
  exact Encl.sub b183 b3151 (by norm_num) (by norm_num)

lemma b3153 : Encl e3153 (72896814149 / 250000000000 : ℝ) (291587256683 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3152 b3106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3154 : Encl e3154 (878094887 / 1000000000000 : ℝ) (219523747 / 250000000000 : ℝ) := by
  exact Encl.add b3136 b3153 (by norm_num) (by norm_num)

lemma b3155 : Encl e3155 (37037037037 / 62500000000 : ℝ) (592592592593 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b3106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3156 : Encl e3156 (37037037037 / 62500000000 : ℝ) (592592592593 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b3155 (by norm_num) (by norm_num)

lemma b3157 : Encl e3157 (-25462962963 / 62500000000 : ℝ) (-407407407407 / 1000000000000 : ℝ) := by
  exact Encl.sub b3156 b5 (by norm_num) (by norm_num)

lemma b3158 : Encl e3158 (81 / 25 : ℝ) (81 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b3106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3159 : Encl e3159 (2101423374667 / 1000000000000 : ℝ) (1050711687337 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b3158 b3116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3160 : Encl e3160 (334451917607 / 500000000000 : ℝ) (668903835217 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3159 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3161 : Encl e3161 (130748213903 / 500000000000 : ℝ) (26149642781 / 100000000000 : ℝ) := by
  exact Encl.add b3157 b3160 (by norm_num) (by norm_num)

lemma b3162 : Encl e3162 (6561 / 1250 : ℝ) (6561 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b3110 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3163 : Encl e3163 (42553823337 / 12500000000 : ℝ) (851076466743 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3162 b3116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3164 : Encl e3164 (6545898520549 / 1000000000000 : ℝ) (3272949260281 / 500000000000 : ℝ) := by
  exact Encl.add b0 b3163 (by norm_num) (by norm_num)

lemma b3165 : Encl e3165 (127924768131 / 50000000000 : ℝ) (2558495362623 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3164 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3166 : Encl e3166 (1628788735353 / 1000000000000 : ℝ) (814394367679 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b3165 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3167 : Encl e3167 (531441 / 125000 : ℝ) (531441 / 125000 : ℝ) := by
  exact Encl.pow b3106 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b3168 : Encl e3168 (35606547 / 62500000 : ℝ) (35606547 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b3167 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3169 : Encl e3169 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b3168 b941 (by norm_num) (by norm_num)

lemma b3170 : Encl e3170 (130748213903 / 250000000000 : ℝ) (26149642781 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3161 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3171 : Encl e3171 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b3169 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3172 : Encl e3172 (663238186103 / 250000000000 : ℝ) (265295274443 / 100000000000 : ℝ) := by
  exact Encl.pow b3166 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3173 : Encl e3173 (5730377927929 / 1000000000000 : ℝ) (5730377927969 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3171 b3172 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3174 : Encl e3174 (1498473358131 / 1000000000000 : ℝ) (749236679083 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b3173 b3161 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3175 : Encl e3175 (5351690564753 / 1000000000000 : ℝ) (5351690564879 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3174 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3176 : Encl e3176 (6351690564753 / 1000000000000 : ℝ) (6351690564879 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3175 (by norm_num) (by norm_num)

lemma b3177 : Encl e3177 (1260128025713 / 500000000000 : ℝ) (630064012863 / 250000000000 : ℝ) := by
  exact Encl.sqrt b3176 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3178 : Encl e3178 (1760128025713 / 500000000000 : ℝ) (880064012863 / 250000000000 : ℝ) := by
  exact Encl.add b5 b3177 (by norm_num) (by norm_num)

lemma b3179 : Encl e3179 (5942668351 / 40000000000 : ℝ) (7428335439 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b3170 b3178 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3180 : Encl e3180 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b3169 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3181 : Encl e3181 (56464859513 / 500000000000 : ℝ) (22585943807 / 200000000000 : ℝ) := by
  exact Encl.sub b3161 b3179 (by norm_num) (by norm_num)

lemma b3182 : Encl e3182 (34666779237 / 500000000000 : ℝ) (69333558481 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3181 b3166 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3183 : Encl e3183 (480714233 / 100000000000 : ℝ) (1201785583 / 250000000000 : ℝ) := by
  exact Encl.pow b3182 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3184 : Encl e3184 (336499963 / 250000000000 : ℝ) (1345999853 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3183 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3185 : Encl e3185 (3279174343 / 1000000000000 : ℝ) (409896793 / 125000000000 : ℝ) := by
  exact Encl.pow b3179 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b3186 : Encl e3186 (1180502763 / 1000000000000 : ℝ) (295125691 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3169 b3185 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3187 : Encl e3187 (505300523 / 200000000000 : ℝ) (2526502617 / 1000000000000 : ℝ) := by
  exact Encl.add b3184 b3186 (by norm_num) (by norm_num)

lemma b3188 : Encl e3188 (505300523 / 200000000000 : ℝ) (2526502617 / 1000000000000 : ℝ) := by
  exact Encl.min b3180 b3187 (by norm_num) (by norm_num)

end CubicTorus.Scalar.Cert
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

lemma baseline_enclosure_162 : Encl (linearBaseline (81 / 50 : ℝ)) (878094887 / 1000000000000 : ℝ) (219523747 / 250000000000 : ℝ) := by
  exact b3154

lemma gain_enclosure_162 : Encl (gain (81 / 50 : ℝ)) (505300523 / 200000000000 : ℝ) (2526502617 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b3188

lemma baseline_lower_162 : (878094887 / 1000000000000 : ℝ) ≤ baseline (81 / 50 : ℝ) :=
  (baseline_enclosure_162).1.trans ((linearBaseline_eq_of_range (h := (81 / 50 : ℝ)) (by norm_num) (by norm_num)).le)

lemma combined_lower_162_oai : (1702298751 / 500000000000 : ℝ) ≤ baseline (81 / 50 : ℝ) + gain (81 / 50 : ℝ) := by
  have hb := baseline_lower_162
  have hg := (gain_enclosure_162).1
  linarith

end CubicTorus.Scalar.Cert

end
end
end
end ReusedScalar205

end

end

end OAI
end

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_162_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_162_oai

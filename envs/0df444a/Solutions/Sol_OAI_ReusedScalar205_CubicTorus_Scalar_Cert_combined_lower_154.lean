-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_154
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:45:48.275009+00:00
-- url     : https://prove2.me/submissions/750755ec-72c4-4e8b-aaa1-8f3d338e2fb8

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

lemma b2940 : Encl e2940 (77 / 50 : ℝ) (77 / 50 : ℝ) := by
  exact Encl.exact (77 / 50 : ℝ)

lemma b2941 : Encl e2941 (490197224723 / 1000000000000 : ℝ) (122549306181 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2940 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2942 : Encl e2942 (3773 / 2500 : ℝ) (3773 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2940 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2943 : Encl e2943 (120098320057 / 250000000000 : ℝ) (480393280229 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2942 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2944 : Encl e2944 (5929 / 2500 : ℝ) (5929 / 2500 : ℝ) := by
  exact Encl.pow b2940 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2945 : Encl e2945 (5929 / 625 : ℝ) (5929 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b2944 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2946 : Encl e2946 (3019614904293 / 1000000000000 : ℝ) (1509807452147 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2945 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2947 : Encl e2947 (4019614904293 / 1000000000000 : ℝ) (2009807452147 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2946 (by norm_num) (by norm_num)

lemma b2948 : Encl e2948 (400979545827 / 200000000000 : ℝ) (125306108071 / 62500000000 : ℝ) := by
  exact Encl.sqrt b2947 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2949 : Encl e2949 (600979545827 / 200000000000 : ℝ) (187806108071 / 62500000000 : ℝ) := by
  exact Encl.add b5 b2948 (by norm_num) (by norm_num)

lemma b2950 : Encl e2950 (166395014097 / 250000000000 : ℝ) (665580056389 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2949 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2951 : Encl e2951 (46590603947 / 250000000000 : ℝ) (186362415789 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2950 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2952 : Encl e2952 (41672231001 / 62500000000 : ℝ) (333377848009 / 500000000000 : ℝ) := by
  exact Encl.add b2943 b2951 (by norm_num) (by norm_num)

lemma b2953 : Encl e2953 (-20827768999 / 62500000000 : ℝ) (-166622151991 / 500000000000 : ℝ) := by
  exact Encl.sub b2952 b5 (by norm_num) (by norm_num)

lemma b2954 : Encl e2954 (264934445403 / 200000000000 : ℝ) (165584028377 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2944 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2955 : Encl e2955 (120146659563 / 500000000000 : ℝ) (30036664891 / 125000000000 : ℝ) := by
  exact Encl.pow b2941 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2956 : Encl e2956 (94963335109 / 125000000000 : ℝ) (379853340437 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2955 (by norm_num) (by norm_num)

lemma b2957 : Encl e2957 (174322308483 / 200000000000 : ℝ) (871611542417 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2956 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2958 : Encl e2958 (-204944875751 / 1000000000000 : ℝ) (-51236218937 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b2957 (by norm_num) (by norm_num)

lemma b2959 : Encl e2959 (662169111897 / 1000000000000 : ℝ) (331084555951 / 500000000000 : ℝ) := by
  exact Encl.pow b2957 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2960 : Encl e2960 (220723037299 / 1000000000000 : ℝ) (220723037301 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2959 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2961 : Encl e2961 (3944540387 / 250000000000 : ℝ) (15778161553 / 1000000000000 : ℝ) := by
  exact Encl.add b2958 b2960 (by norm_num) (by norm_num)

lemma b2962 : Encl e2962 (15462598317 / 1000000000000 : ℝ) (7731299161 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2961 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2963 : Encl e2963 (275688546367 / 1000000000000 : ℝ) (275688546371 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2955 b2957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2964 : Encl e2964 (-1724311453633 / 1000000000000 : ℝ) (-1724311453629 / 1000000000000 : ℝ) := by
  exact Encl.sub b2963 b23 (by norm_num) (by norm_num)

lemma b2965 : Encl e2965 (174322308483 / 100000000000 : ℝ) (871611542417 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2966 : Encl e2966 (18911631197 / 1000000000000 : ℝ) (3782326241 / 200000000000 : ℝ) := by
  exact Encl.add b2964 b2965 (by norm_num) (by norm_num)

lemma b2967 : Encl e2967 (378232623 / 1000000000000 : ℝ) (3025861 / 8000000000 : ℝ) := by
  exact Encl.div_nonneg b2966 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2968 : Encl e2968 (3771091423 / 250000000000 : ℝ) (15084365699 / 1000000000000 : ℝ) := by
  exact Encl.sub b2962 b2967 (by norm_num) (by norm_num)

lemma b2969 : Encl e2969 (9990920147 / 500000000000 : ℝ) (1248865019 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2954 b2968 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2970 : Encl e2970 (-31326246369 / 100000000000 : ℝ) (-156631231839 / 500000000000 : ℝ) := by
  exact Encl.add b2953 b2969 (by norm_num) (by norm_num)

lemma b2971 : Encl e2971 (374322308483 / 200000000000 : ℝ) (1871611542417 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2957 (by norm_num) (by norm_num)

lemma b2972 : Encl e2972 (130955920503 / 500000000000 : ℝ) (16369490063 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b2941 b2971 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2973 : Encl e2973 (68597812459 / 1000000000000 : ℝ) (68597812461 / 1000000000000 : ℝ) := by
  exact Encl.pow b2972 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2974 : Encl e2974 (1068597812459 / 1000000000000 : ℝ) (1068597812461 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2973 (by norm_num) (by norm_num)

lemma b2975 : Encl e2975 (206746009631 / 200000000000 : ℝ) (1033730048157 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2974 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2976 : Encl e2976 (406746009631 / 200000000000 : ℝ) (2033730048157 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2975 (by norm_num) (by norm_num)

lemma b2977 : Encl e2977 (32195993913 / 250000000000 : ℝ) (64391987827 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2972 b2976 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2978 : Encl e2978 (256158007239 / 500000000000 : ℝ) (512316014487 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2941) (a := (32195993913 / 250000000000 : ℝ)) (b := (64391987827 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (490197224723 / 1000000000000 : ℝ) by norm_num).trans b2941.1
        exact b2941.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2941) (32195993913 / 250000000000 : ℝ) (64391987827 / 500000000000 : ℝ) from b2977) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2979 : Encl e2979 (261281167383 / 1000000000000 : ℝ) (261281167389 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2978 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2980 : Encl e2980 (120098320057 / 500000000000 : ℝ) (48039328023 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2941 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2981 : Encl e2981 (52339540993 / 250000000000 : ℝ) (8374326559 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b2980 b2957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2982 : Encl e2982 (3245187713 / 62500000000 : ℝ) (51923003417 / 1000000000000 : ℝ) := by
  exact Encl.sub b2979 b2981 (by norm_num) (by norm_num)

lemma b2983 : Encl e2983 (174322308483 / 4000000000 : ℝ) (871611542417 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2984 : Encl e2984 (2812016597 / 250000000000 : ℝ) (11248066389 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2941 b2983 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2985 : Encl e2985 (40674937019 / 1000000000000 : ℝ) (40674937029 / 1000000000000 : ℝ) := by
  exact Encl.sub b2982 b2984 (by norm_num) (by norm_num)

lemma b2986 : Encl e2986 (479477832483 / 1000000000000 : ℝ) (29967364539 / 62500000000 : ℝ) := by
  exact Encl.sub b183 b2985 (by norm_num) (by norm_num)

lemma b2987 : Encl e2987 (19459327617 / 62500000000 : ℝ) (77837310491 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2986 b2940 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2988 : Encl e2988 (-956610909 / 500000000000 : ℝ) (-956610857 / 500000000000 : ℝ) := by
  exact Encl.add b2970 b2987 (by norm_num) (by norm_num)

lemma b2989 : Encl e2989 (38961038961 / 62500000000 : ℝ) (623376623377 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2940 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2990 : Encl e2990 (38961038961 / 62500000000 : ℝ) (623376623377 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2989 (by norm_num) (by norm_num)

lemma b2991 : Encl e2991 (-23538961039 / 62500000000 : ℝ) (-376623376623 / 1000000000000 : ℝ) := by
  exact Encl.sub b2990 b5 (by norm_num) (by norm_num)

lemma b2992 : Encl e2992 (77 / 25 : ℝ) (77 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b2940 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2993 : Encl e2993 (81999462947 / 40000000000 : ℝ) (2049986573679 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2992 b2950 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2994 : Encl e2994 (40783187059 / 62500000000 : ℝ) (652530992947 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2993 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2995 : Encl e2995 (862211301 / 3125000000 : ℝ) (68976904081 / 250000000000 : ℝ) := by
  exact Encl.add b2991 b2994 (by norm_num) (by norm_num)

lemma b2996 : Encl e2996 (5929 / 1250 : ℝ) (5929 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b2944 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2997 : Encl e2997 (3156979323459 / 1000000000000 : ℝ) (631395864693 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2996 b2950 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2998 : Encl e2998 (787321497131 / 125000000000 : ℝ) (1259714395411 / 200000000000 : ℝ) := by
  exact Encl.add b0 b2997 (by norm_num) (by norm_num)

lemma b2999 : Encl e2999 (2509695594499 / 1000000000000 : ℝ) (2509695594501 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3000 : Encl e3000 (624110093 / 390625000 : ℝ) (319544367617 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2999 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3001 : Encl e3001 (456533 / 125000 : ℝ) (456533 / 125000 : ℝ) := by
  exact Encl.pow b2940 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b3002 : Encl e3002 (30587711 / 62500000 : ℝ) (30587711 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b3001 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3003 : Encl e3003 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b3002 b941 (by norm_num) (by norm_num)

lemma b3004 : Encl e3004 (862211301 / 1562500000 : ℝ) (68976904081 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2995 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3005 : Encl e3005 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b3003 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3006 : Encl e3006 (2552715071877 / 1000000000000 : ℝ) (1276357535947 / 500000000000 : ℝ) := by
  exact Encl.pow b3000 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3007 : Encl e3007 (2756932277627 / 500000000000 : ℝ) (1378466138823 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3005 b3006 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3008 : Encl e3008 (1521317226151 / 1000000000000 : ℝ) (304263445237 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b3007 b2995 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3009 : Encl e3009 (2716637903841 / 500000000000 : ℝ) (1358318951951 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b3008 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3010 : Encl e3010 (3216637903841 / 500000000000 : ℝ) (1608318951951 / 250000000000 : ℝ) := by
  exact Encl.add b5 b3009 (by norm_num) (by norm_num)

lemma b3011 : Encl e3011 (507278062119 / 200000000000 : ℝ) (126819515531 / 50000000000 : ℝ) := by
  exact Encl.sqrt b3010 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3012 : Encl e3012 (707278062119 / 200000000000 : ℝ) (176819515531 / 50000000000 : ℝ) := by
  exact Encl.add b5 b3011 (by norm_num) (by norm_num)

lemma b3013 : Encl e3013 (19504890021 / 125000000000 : ℝ) (39009780043 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b3004 b3012 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3014 : Encl e3014 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b3003 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3015 : Encl e3015 (29967124037 / 250000000000 : ℝ) (29967124039 / 250000000000 : ℝ) := by
  exact Encl.sub b2995 b3013 (by norm_num) (by norm_num)

lemma b3016 : Encl e3016 (75024634007 / 1000000000000 : ℝ) (75024634013 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3015 b3000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3017 : Encl e3017 (5628695707 / 1000000000000 : ℝ) (5628695709 / 1000000000000 : ℝ) := by
  exact Encl.pow b3016 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3018 : Encl e3018 (1576034797 / 1000000000000 : ℝ) (1576034799 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3017 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3019 : Encl e3019 (3799272801 / 1000000000000 : ℝ) (1899636401 / 500000000000 : ℝ) := by
  exact Encl.pow b3013 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b3020 : Encl e3020 (42741819 / 31250000000 : ℝ) (1367738209 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3003 b3019 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3021 : Encl e3021 (588754601 / 200000000000 : ℝ) (183985813 / 62500000000 : ℝ) := by
  exact Encl.add b3018 b3020 (by norm_num) (by norm_num)

lemma b3022 : Encl e3022 (588754601 / 200000000000 : ℝ) (183985813 / 62500000000 : ℝ) := by
  exact Encl.min b3014 b3021 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_154 : Encl (linearBaseline (77 / 50 : ℝ)) (-956610909 / 500000000000 : ℝ) (-956610857 / 500000000000 : ℝ) := by
  exact b2988

lemma gain_enclosure_154 : Encl (gain (77 / 50 : ℝ)) (588754601 / 200000000000 : ℝ) (183985813 / 62500000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b3022

lemma baseline_lower_154 : (-956610909 / 500000000000 : ℝ) ≤ baseline (77 / 50 : ℝ) :=
  (baseline_enclosure_154).1.trans ((linearBaseline_eq_of_range (h := (77 / 50 : ℝ)) (by norm_num) (by norm_num)).le)

lemma combined_lower_154_oai : (1030551187 / 1000000000000 : ℝ) ≤ baseline (77 / 50 : ℝ) + gain (77 / 50 : ℝ) := by
  have hb := baseline_lower_154
  have hg := (gain_enclosure_154).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_154_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_154_oai

-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_114
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:39:25.376659+00:00
-- url     : https://prove2.me/submissions/9b2361a8-c0da-46d1-b14e-7ec386687143

import Mathlib
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_twoChordBaseline_le_of_range

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
lemma b89 : Encl e89 (354490770181 / 200000000000 : ℝ) (886226925453 / 500000000000 : ℝ) := by
  exact Encl.sqrt b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b91 : Encl e91 (785398163397 / 1000000000000 : ℝ) (392699081699 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b97 : Encl e97 (785398163397 / 500000000000 : ℝ) (314159265359 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b159 : Encl e159 (979591836733 / 1000000000000 : ℝ) (15306122449 / 15625000000 : ℝ) := by
  exact Encl.pow b4 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b160 : Encl e160 (479999999999 / 500000000000 : ℝ) (480000000001 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b159 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b161 : Encl e161 (19999999999 / 500000000000 : ℝ) (20000000001 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b160 (by norm_num) (by norm_num)

lemma b162 : Encl e162 (318877551 / 15625000000 : ℝ) (20408163267 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b159 (by norm_num) (by norm_num)

lemma b163 : Encl e163 (35714285713 / 250000000000 : ℝ) (8928571429 / 62500000000 : ℝ) := by
  exact Encl.sqrt b162 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b164 : Encl e164 (69999999993 / 250000000000 : ℝ) (11200000001 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b161 b163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b165 : Encl e165 (28799999999 / 40000000000 : ℝ) (180000000007 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b164 (by norm_num) (by norm_num)

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures1165To1383
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

lemma b1326 : Encl e1326 (57 / 50 : ℝ) (57 / 50 : ℝ) := by
  exact Encl.exact (57 / 50 : ℝ)

lemma b1327 : Encl e1327 (362873270249 / 1000000000000 : ℝ) (1451493081 / 4000000000 : ℝ) := by
  exact Encl.div_nonneg b1326 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1328 : Encl e1328 (3108506919 / 4000000000 : ℝ) (97140841219 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1326 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1329 : Encl e1329 (2793 / 2500 : ℝ) (2793 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1330 : Encl e1330 (88903951211 / 250000000000 : ℝ) (71123160969 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1329 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1331 : Encl e1331 (3249 / 2500 : ℝ) (3249 / 2500 : ℝ) := by
  exact Encl.pow b1326 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1332 : Encl e1332 (3249 / 625 : ℝ) (3249 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b1331 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1333 : Encl e1333 (1654702112337 / 1000000000000 : ℝ) (827351056169 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1332 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1334 : Encl e1334 (2654702112337 / 1000000000000 : ℝ) (1327351056169 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1333 (by norm_num) (by norm_num)

lemma b1335 : Encl e1335 (814662830921 / 500000000000 : ℝ) (1629325661843 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1334 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1336 : Encl e1336 (1314662830921 / 500000000000 : ℝ) (2629325661843 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1335 (by norm_num) (by norm_num)

lemma b1337 : Encl e1337 (760651306539 / 1000000000000 : ℝ) (760651306541 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b1336 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1338 : Encl e1338 (21298236583 / 100000000000 : ℝ) (26622795729 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1339 : Encl e1339 (284299085337 / 500000000000 : ℝ) (568598170677 / 1000000000000 : ℝ) := by
  exact Encl.add b1330 b1338 (by norm_num) (by norm_num)

lemma b1340 : Encl e1340 (-215700914663 / 500000000000 : ℝ) (-431401829323 / 1000000000000 : ℝ) := by
  exact Encl.sub b1339 b5 (by norm_num) (by norm_num)

lemma b1341 : Encl e1341 (1208676767309 / 500000000000 : ℝ) (2417353534619 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b1331 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1342 : Encl e1342 (131677010261 / 1000000000000 : ℝ) (65838505131 / 500000000000 : ℝ) := by
  exact Encl.pow b1327 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1343 : Encl e1343 (434161494869 / 500000000000 : ℝ) (868322989739 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1342 (by norm_num) (by norm_num)

lemma b1344 : Encl e1344 (186367699963 / 200000000000 : ℝ) (116479812477 / 125000000000 : ℝ) := by
  exact Encl.sqrt b1343 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1345 : Encl e1345 (-5303436663 / 20000000000 : ℝ) (-66292958287 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b1344 (by norm_num) (by norm_num)

lemma b1346 : Encl e1346 (809136792111 / 1000000000000 : ℝ) (161827358423 / 200000000000 : ℝ) := by
  exact Encl.pow b1344 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1347 : Encl e1347 (269712264037 / 1000000000000 : ℝ) (269712264039 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1346 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1348 : Encl e1348 (4540430887 / 1000000000000 : ℝ) (4540430891 / 1000000000000 : ℝ) := by
  exact Encl.add b1345 b1347 (by norm_num) (by norm_num)

lemma b1349 : Encl e1349 (4449622269 / 1000000000000 : ℝ) (2224811137 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1348 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1350 : Encl e1350 (275993813 / 1953125000 : ℝ) (141308832259 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1342 b1344 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1351 : Encl e1351 (-3630256187 / 1953125000 : ℝ) (-1858691167741 / 1000000000000 : ℝ) := by
  exact Encl.sub b1350 b23 (by norm_num) (by norm_num)

lemma b1352 : Encl e1352 (186367699963 / 100000000000 : ℝ) (116479812477 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1344 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1353 : Encl e1353 (2492915943 / 500000000000 : ℝ) (4985831891 / 1000000000000 : ℝ) := by
  exact Encl.add b1351 b1352 (by norm_num) (by norm_num)

lemma b1354 : Encl e1354 (99716637 / 1000000000000 : ℝ) (49858319 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1353 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1355 : Encl e1355 (4349905631 / 1000000000000 : ℝ) (4349905637 / 1000000000000 : ℝ) := by
  exact Encl.sub b1349 b1354 (by norm_num) (by norm_num)

lemma b1356 : Encl e1356 (1314407469 / 125000000000 : ℝ) (10515259767 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1341 b1355 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1357 : Encl e1357 (-210443284787 / 500000000000 : ℝ) (-105221642389 / 250000000000 : ℝ) := by
  exact Encl.add b1340 b1356 (by norm_num) (by norm_num)

lemma b1358 : Encl e1358 (603925954091 / 1000000000000 : ℝ) (37745372131 / 62500000000 : ℝ) := by
  exact Encl.pow b1328 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1359 : Encl e1359 (24754627869 / 62500000000 : ℝ) (396074045909 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1358 (by norm_num) (by norm_num)

lemma b1360 : Encl e1360 (157336034871 / 250000000000 : ℝ) (629344139489 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1359 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1361 : Encl e1361 (407336034871 / 250000000000 : ℝ) (1629344139489 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1360 (by norm_num) (by norm_num)

lemma b1362 : Encl e1362 (238478388609 / 500000000000 : ℝ) (476956777221 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1328 b1361 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1363 : Encl e1363 (113743883667 / 500000000000 : ℝ) (113743883669 / 500000000000 : ℝ) := by
  exact Encl.pow b1362 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1364 : Encl e1364 (613743883667 / 500000000000 : ℝ) (613743883669 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1363 (by norm_num) (by norm_num)

lemma b1365 : Encl e1365 (1107920469769 / 1000000000000 : ℝ) (276980117443 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1364 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1366 : Encl e1366 (2107920469769 / 1000000000000 : ℝ) (526980117443 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1365 (by norm_num) (by norm_num)

lemma b1367 : Encl e1367 (226268867377 / 1000000000000 : ℝ) (11313443369 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b1362 b1366 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1368 : Encl e1368 (890087359603 / 1000000000000 : ℝ) (6953807497 / 7812500000 : ℝ) := by
  apply Encl.arcsin (z := e1328) (a := (226268867377 / 1000000000000 : ℝ)) (b := (11313443369 / 50000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (3108506919 / 4000000000 : ℝ) by norm_num).trans b1328.1
        exact b1328.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1328) (226268867377 / 1000000000000 : ℝ) (11313443369 / 50000000000 : ℝ) from b1367) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1369 : Encl e1369 (453944553397 / 1000000000000 : ℝ) (90788910681 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1368 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1370 : Encl e1370 (380792097577 / 1000000000000 : ℝ) (380792097579 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1328 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1371 : Encl e1371 (239649274971 / 1000000000000 : ℝ) (7489039843 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b1370 b1360 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1372 : Encl e1372 (214295278421 / 1000000000000 : ℝ) (107147639217 / 500000000000 : ℝ) := by
  exact Encl.sub b1369 b1371 (by norm_num) (by norm_num)

lemma b1373 : Encl e1373 (157336034871 / 5000000000 : ℝ) (629344139489 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1360 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1374 : Encl e1374 (24696399981 / 1000000000000 : ℝ) (24696399983 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1328 b1373 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1375 : Encl e1375 (94799439219 / 500000000000 : ℝ) (189598878453 / 1000000000000 : ℝ) := by
  exact Encl.sub b1372 b1374 (by norm_num) (by norm_num)

lemma b1376 : Encl e1376 (386367699963 / 200000000000 : ℝ) (241479812477 / 125000000000 : ℝ) := by
  exact Encl.add b5 b1344 (by norm_num) (by norm_num)

lemma b1377 : Encl e1377 (18783830547 / 100000000000 : ℝ) (2934973523 / 15625000000 : ℝ) := by
  exact Encl.div_nonneg b1327 b1376 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1378 : Encl e1378 (35283229001 / 1000000000000 : ℝ) (35283229003 / 1000000000000 : ℝ) := by
  exact Encl.pow b1377 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1379 : Encl e1379 (1035283229001 / 1000000000000 : ℝ) (1035283229003 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1378 (by norm_num) (by norm_num)

lemma b1380 : Encl e1380 (508744343703 / 500000000000 : ℝ) (63593042963 / 62500000000 : ℝ) := by
  exact Encl.sqrt b1379 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1381 : Encl e1381 (1008744343703 / 500000000000 : ℝ) (126093042963 / 62500000000 : ℝ) := by
  exact Encl.add b5 b1380 (by norm_num) (by norm_num)

lemma b1382 : Encl e1382 (46552505261 / 500000000000 : ℝ) (23276252631 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1377 b1381 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures1384To1602
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
lemma b1383 : Encl e1383 (11604671613 / 31250000000 : ℝ) (46418686453 / 125000000000 : ℝ) := by
  apply Encl.arcsin (z := e1327) (a := (46552505261 / 500000000000 : ℝ)) (b := (23276252631 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (362873270249 / 1000000000000 : ℝ) by norm_num).trans b1327.1
        exact b1327.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1327) (46552505261 / 500000000000 : ℝ) (23276252631 / 250000000000 : ℝ) from b1382) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1384 : Encl e1384 (47347060181 / 250000000000 : ℝ) (189388240729 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1383 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1385 : Encl e1385 (88903951211 / 500000000000 : ℝ) (177807902423 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1327 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1386 : Encl e1386 (20711031131 / 125000000000 : ℝ) (3313764981 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b1385 b1344 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1387 : Encl e1387 (11849995837 / 500000000000 : ℝ) (23699991681 / 1000000000000 : ℝ) := by
  exact Encl.sub b1384 b1386 (by norm_num) (by norm_num)

lemma b1388 : Encl e1388 (186367699963 / 4000000000 : ℝ) (116479812477 / 2500000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1344 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1389 : Encl e1389 (1947082409 / 250000000000 : ℝ) (7788329637 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1327 b1388 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1390 : Encl e1390 (15911662037 / 1000000000000 : ℝ) (3182332409 / 200000000000 : ℝ) := by
  exact Encl.sub b1387 b1389 (by norm_num) (by norm_num)

lemma b1391 : Encl e1391 (173687216393 / 1000000000000 : ℝ) (5427725513 / 31250000000 : ℝ) := by
  exact Encl.sub b1375 b1390 (by norm_num) (by norm_num)

lemma b1392 : Encl e1392 (76178603681 / 500000000000 : ℝ) (152357207383 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1391 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1393 : Encl e1393 (-67132340553 / 250000000000 : ℝ) (-268529362173 / 1000000000000 : ℝ) := by
  exact Encl.add b1357 b1392 (by norm_num) (by norm_num)

lemma b1394 : Encl e1394 (44171751209 / 25000000000 : ℝ) (1766870048363 / 1000000000000 : ℝ) := by
  exact Encl.add b1328 b4 (by norm_num) (by norm_num)

lemma b1395 : Encl e1395 (44171751209 / 50000000000 : ℝ) (441717512091 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1394 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1396 : Encl e1396 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1328 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1397 : Encl e1397 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1396 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1398 : Encl e1398 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1396 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1399 : Encl e1399 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1398 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1400 : Encl e1400 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1399 (by norm_num) (by norm_num)

lemma b1401 : Encl e1401 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1400 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1402 : Encl e1402 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1397 b1401 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1403 : Encl e1403 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1398 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1404 : Encl e1404 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1402 b1403 (by norm_num) (by norm_num)

lemma b1405 : Encl e1405 (150557230543 / 250000000000 : ℝ) (120445784439 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1395 b1404 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1406 : Encl e1406 (387471501833 / 500000000000 : ℝ) (774943003669 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1395 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1407 : Encl e1407 (1373550711079 / 1000000000000 : ℝ) (686775355543 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1406 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1408 : Encl e1408 (60053665893 / 100000000000 : ℝ) (75067082367 / 125000000000 : ℝ) := by
  exact Encl.pow b1406 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1409 : Encl e1409 (29478774311 / 62500000000 : ℝ) (235830194491 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1408 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1410 : Encl e1410 (91978774311 / 62500000000 : ℝ) (735830194491 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1409 (by norm_num) (by norm_num)

lemma b1411 : Encl e1411 (606560052463 / 500000000000 : ℝ) (1213120104929 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1410 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1412 : Encl e1412 (333256396549 / 200000000000 : ℝ) (833140991379 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1407 b1411 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1413 : Encl e1413 (29478774311 / 31250000000 : ℝ) (943320777963 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1408 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1414 : Encl e1414 (361480602391 / 500000000000 : ℝ) (361480602403 / 500000000000 : ℝ) := by
  exact Encl.sub b1412 b1413 (by norm_num) (by norm_num)

lemma b1415 : Encl e1415 (70229059601 / 125000000000 : ℝ) (561832476829 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1328 b1414 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1416 : Encl e1416 (40396445343 / 1000000000000 : ℝ) (40396445387 / 1000000000000 : ℝ) := by
  exact Encl.sub b1405 b1415 (by norm_num) (by norm_num)

lemma b1417 : Encl e1417 (780457441947 / 1000000000000 : ℝ) (24389295061 / 31250000000 : ℝ) := by
  exact Encl.pow b1395 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1418 : Encl e1418 (191212073277 / 250000000000 : ℝ) (764848293113 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1417 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1419 : Encl e1419 (235151706887 / 1000000000000 : ℝ) (58787926723 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b1418 (by norm_num) (by norm_num)

lemma b1420 : Encl e1420 (6860704939 / 31250000000 : ℝ) (219542558053 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1417 (by norm_num) (by norm_num)

lemma b1421 : Encl e1421 (117138421869 / 250000000000 : ℝ) (468553687483 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1420 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1422 : Encl e1422 (20074686267 / 40000000000 : ℝ) (250933578347 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1419 b1421 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1423 : Encl e1423 (249066421653 / 500000000000 : ℝ) (19925313733 / 40000000000 : ℝ) := by
  exact Encl.sub b5 b1422 (by norm_num) (by norm_num)

lemma b1424 : Encl e1424 (591847435009 / 1000000000000 : ℝ) (118369487003 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1358 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1425 : Encl e1425 (81630512997 / 200000000000 : ℝ) (408152564991 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1424 (by norm_num) (by norm_num)

lemma b1426 : Encl e1426 (648536372033 / 1000000000000 : ℝ) (648536372049 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1425 b1360 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1427 : Encl e1427 (351463627951 / 1000000000000 : ℝ) (351463627967 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1426 (by norm_num) (by norm_num)

lemma b1428 : Encl e1428 (146669215339 / 1000000000000 : ℝ) (73334607687 / 500000000000 : ℝ) := by
  exact Encl.sub b1423 b1427 (by norm_num) (by norm_num)

lemma b1429 : Encl e1429 (296245747 / 50000000000 : ℝ) (5924914949 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1416 b1428 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1430 : Encl e1430 (20635545477 / 500000000000 : ℝ) (41271091001 / 1000000000000 : ℝ) := by
  exact Encl.sub b1414 b1404 (by norm_num) (by norm_num)

lemma b1431 : Encl e1431 (367138421869 / 250000000000 : ℝ) (1468553687483 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1421 (by norm_num) (by norm_num)

lemma b1432 : Encl e1432 (300784040689 / 500000000000 : ℝ) (601568081383 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1395 b1431 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1433 : Encl e1433 (90471039133 / 250000000000 : ℝ) (361884156539 / 1000000000000 : ℝ) := by
  exact Encl.pow b1432 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1434 : Encl e1434 (340471039133 / 250000000000 : ℝ) (1361884156539 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1433 (by norm_num) (by norm_num)

lemma b1435 : Encl e1435 (1166997924819 / 1000000000000 : ℝ) (1166997924823 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1434 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1436 : Encl e1436 (2166997924819 / 1000000000000 : ℝ) (2166997924823 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1435 (by norm_num) (by norm_num)

lemma b1437 : Encl e1437 (69401091077 / 250000000000 : ℝ) (34700545539 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1432 b1436 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1438 : Encl e1438 (1083143407353 / 1000000000000 : ℝ) (108314340737 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e1395) (a := (69401091077 / 250000000000 : ℝ)) (b := (34700545539 / 125000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (44171751209 / 50000000000 : ℝ) by norm_num).trans b1395.1
        exact b1395.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1395) (69401091077 / 250000000000 : ℝ) (34700545539 / 125000000000 : ℝ) from b1437) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1439 : Encl e1439 (2209612551 / 4000000000 : ℝ) (552403137759 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1438 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1440 : Encl e1440 (54110395231 / 125000000000 : ℝ) (8657663237 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1395 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1441 : Encl e1441 (20282900173 / 100000000000 : ℝ) (40565800347 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1440 b1421 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1442 : Encl e1442 (69914827203 / 200000000000 : ℝ) (349574136029 / 1000000000000 : ℝ) := by
  exact Encl.sub b1439 b1441 (by norm_num) (by norm_num)

lemma b1443 : Encl e1443 (117138421869 / 5000000000 : ℝ) (468553687483 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1421 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1444 : Encl e1444 (37709020237 / 1000000000000 : ℝ) (37709020239 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1395 b1443 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1445 : Encl e1445 (2436446217 / 7812500000 : ℝ) (19491569737 / 62500000000 : ℝ) := by
  exact Encl.sub b1442 b1444 (by norm_num) (by norm_num)

lemma b1446 : Encl e1446 (122266237323 / 1000000000000 : ℝ) (61133118677 / 500000000000 : ℝ) := by
  exact Encl.sub b1445 b1375 (by norm_num) (by norm_num)

lemma b1447 : Encl e1447 (5046061001 / 1000000000000 : ℝ) (5046061009 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1430 b1446 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1448 : Encl e1448 (10970975941 / 1000000000000 : ℝ) (5485487979 / 500000000000 : ℝ) := by
  exact Encl.add b1429 b1447 (by norm_num) (by norm_num)

lemma b1449 : Encl e1449 (26577073607 / 250000000000 : ℝ) (3322134201 / 31250000000 : ℝ) := by
  exact Encl.sub b1395 b1328 (by norm_num) (by norm_num)

lemma b1450 : Encl e1450 (51599811659 / 500000000000 : ℝ) (103199623483 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1448 b1449 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1451 : Encl e1451 (-82664869447 / 500000000000 : ℝ) (-16532973869 / 100000000000 : ℝ) := by
  exact Encl.add b1393 b1450 (by norm_num) (by norm_num)

lemma b1452 : Encl e1452 (715546022047 / 1000000000000 : ℝ) (89443252759 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1414 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1453 : Encl e1453 (868195893517 / 1000000000000 : ℝ) (868195893519 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1454 : Encl e1454 (384709288701 / 250000000000 : ℝ) (1538837154809 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1453 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1455 : Encl e1455 (753764109519 / 1000000000000 : ℝ) (188441027381 / 250000000000 : ℝ) := by
  exact Encl.pow b1453 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1456 : Encl e1456 (2368019789 / 4000000000 : ℝ) (74000618407 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1455 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1457 : Encl e1457 (6368019789 / 4000000000 : ℝ) (199000618407 / 125000000000 : ℝ) := by
  exact Encl.add b5 b1456 (by norm_num) (by norm_num)

lemma b1458 : Encl e1458 (10093974273 / 8000000000 : ℝ) (9857396751 / 7812500000 : ℝ) := by
  exact Encl.sqrt b1457 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1459 : Encl e1459 (970811415683 / 500000000000 : ℝ) (1941622831377 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1454 b1458 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1460 : Encl e1460 (1184009894501 / 1000000000000 : ℝ) (1184009894511 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1455 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1461 : Encl e1461 (151522587371 / 200000000000 : ℝ) (189403234219 / 250000000000 : ℝ) := by
  exact Encl.sub b1459 b1460 (by norm_num) (by norm_num)

lemma b1462 : Encl e1462 (669301803189 / 1000000000000 : ℝ) (66930180321 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1395 b1461 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1463 : Encl e1463 (46244218837 / 1000000000000 : ℝ) (46244218883 / 1000000000000 : ℝ) := by
  exact Encl.sub b1452 b1462 (by norm_num) (by norm_num)

lemma b1464 : Encl e1464 (4437343133 / 20000000000 : ℝ) (110933578361 / 500000000000 : ℝ) := by
  exact Encl.sub b165 b1423 (by norm_num) (by norm_num)

lemma b1465 : Encl e1465 (80156823 / 7812500000 : ℝ) (10260073359 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1463 b1464 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1466 : Encl e1466 (34651732049 / 1000000000000 : ℝ) (17325866047 / 500000000000 : ℝ) := by
  exact Encl.sub b1461 b1414 (by norm_num) (by norm_num)

lemma b1467 : Encl e1467 (5207191343 / 25000000000 : ℝ) (208287653867 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b1445 (by norm_num) (by norm_num)

lemma b1468 : Encl e1468 (1443505593 / 200000000000 : ℝ) (7217527981 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1466 b1467 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1469 : Encl e1469 (17477601309 / 1000000000000 : ℝ) (873880067 / 50000000000 : ℝ) := by
  exact Encl.add b1465 b1468 (by norm_num) (by norm_num)

lemma b1470 : Encl e1470 (26577073607 / 250000000000 : ℝ) (106308294431 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b1395 (by norm_num) (by norm_num)

lemma b1471 : Encl e1471 (164404869841 / 1000000000000 : ℝ) (82202435069 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1469 b1470 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1472 : Encl e1472 (-924869053 / 1000000000000 : ℝ) (-115608569 / 125000000000 : ℝ) := by
  exact Encl.add b1451 b1471 (by norm_num) (by norm_num)

lemma b1473 : Encl e1473 (842105263157 / 1000000000000 : ℝ) (421052631579 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1474 : Encl e1474 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b1473 (by norm_num) (by norm_num)

lemma b1475 : Encl e1475 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b1474 b5 (by norm_num) (by norm_num)

lemma b1476 : Encl e1476 (57 / 25 : ℝ) (57 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b1326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1477 : Encl e1477 (433571244727 / 250000000000 : ℝ) (867142489457 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1476 b1337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1478 : Encl e1478 (276020027123 / 500000000000 : ℝ) (552040054249 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1477 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1479 : Encl e1479 (116865084031 / 500000000000 : ℝ) (116865084033 / 500000000000 : ℝ) := by
  exact Encl.add b1475 b1478 (by norm_num) (by norm_num)

lemma b1480 : Encl e1480 (3249 / 1250 : ℝ) (3249 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b1331 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1481 : Encl e1481 (494271218989 / 250000000000 : ℝ) (988542437981 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1480 b1337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1482 : Encl e1482 (1023735505909 / 200000000000 : ℝ) (319917345597 / 62500000000 : ℝ) := by
  exact Encl.add b0 b1481 (by norm_num) (by norm_num)

lemma b1483 : Encl e1483 (1131224726739 / 500000000000 : ℝ) (2262449453481 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1482 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1484 : Encl e1484 (288064011213 / 200000000000 : ℝ) (144032005607 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b1483 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1485 : Encl e1485 (185193 / 125000 : ℝ) (185193 / 125000 : ℝ) := by
  exact Encl.pow b1326 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1486 : Encl e1486 (12407931 / 62500000 : ℝ) (12407931 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b1485 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1487 : Encl e1487 (12407931 / 62500000 : ℝ) (12407931 / 62500000 : ℝ) := by
  exact Encl.min b1486 b941 (by norm_num) (by norm_num)

lemma b1488 : Encl e1488 (116865084031 / 250000000000 : ℝ) (116865084033 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1479 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1489 : Encl e1489 (37223793 / 31250000 : ℝ) (37223793 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b1487 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1490 : Encl e1490 (2074521863903 / 1000000000000 : ℝ) (1037260931959 / 500000000000 : ℝ) := by
  exact Encl.pow b1484 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1491 : Encl e1491 (617772579487 / 250000000000 : ℝ) (2471090317967 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1489 b1490 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1492 : Encl e1492 (57756835531 / 100000000000 : ℝ) (23102734213 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b1491 b1479 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1493 : Encl e1493 (2062744126107 / 1000000000000 : ℝ) (2062744126161 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1492 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1494 : Encl e1494 (3062744126107 / 1000000000000 : ℝ) (3062744126161 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1493 (by norm_num) (by norm_num)

lemma b1495 : Encl e1495 (875034874463 / 500000000000 : ℝ) (875034874471 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1494 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1496 : Encl e1496 (1375034874463 / 500000000000 : ℝ) (1375034874471 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1495 (by norm_num) (by norm_num)

lemma b1497 : Encl e1497 (84990632747 / 500000000000 : ℝ) (169981265499 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1488 b1496 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1498 : Encl e1498 (1838557583 / 1000000000000 : ℝ) (114909849 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b1487 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1499 : Encl e1499 (63748902563 / 1000000000000 : ℝ) (15937225643 / 250000000000 : ℝ) := by
  exact Encl.sub b1479 b1497 (by norm_num) (by norm_num)

lemma b1500 : Encl e1500 (44260233893 / 1000000000000 : ℝ) (442602339 / 10000000000 : ℝ) := by
  exact Encl.div_nonneg b1499 b1484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1501 : Encl e1501 (122435519 / 62500000000 : ℝ) (391793661 / 200000000000 : ℝ) := by
  exact Encl.pow b1500 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1502 : Encl e1502 (4388089 / 8000000000 : ℝ) (274255563 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1501 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1503 : Encl e1503 (4911375897 / 1000000000000 : ℝ) (2455687949 / 500000000000 : ℝ) := by
  exact Encl.pow b1497 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1504 : Encl e1504 (975040211 / 1000000000000 : ℝ) (975040213 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1487 b1503 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1505 : Encl e1505 (190443917 / 125000000000 : ℝ) (1523551339 / 1000000000000 : ℝ) := by
  exact Encl.add b1502 b1504 (by norm_num) (by norm_num)

lemma b1506 : Encl e1506 (190443917 / 125000000000 : ℝ) (1523551339 / 1000000000000 : ℝ) := by
  exact Encl.min b1498 b1505 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_114 : Encl (twoChordBaseline (57 / 50 : ℝ)) (-924869053 / 1000000000000 : ℝ) (-115608569 / 125000000000 : ℝ) := by
  exact b1472

lemma gain_enclosure_114 : Encl (gain (57 / 50 : ℝ)) (190443917 / 125000000000 : ℝ) (1523551339 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b1506

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

lemma baseline_lower_114 : (-924869053 / 1000000000000 : ℝ) ≤ baseline (57 / 50 : ℝ) :=
  (baseline_enclosure_114).1.trans (twoChordBaseline_le_of_range (h := (57 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_114_oai : (598682283 / 1000000000000 : ℝ) ≤ baseline (57 / 50 : ℝ) + gain (57 / 50 : ℝ) := by
  have hb := baseline_lower_114
  have hg := (gain_enclosure_114).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_114_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_114_oai

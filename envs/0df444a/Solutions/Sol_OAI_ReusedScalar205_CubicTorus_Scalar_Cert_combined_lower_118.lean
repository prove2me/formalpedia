-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_118
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:40:31.638269+00:00
-- url     : https://prove2.me/submissions/a9e641bb-8454-4b75-a8ff-db797a4da933

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
lemma b1507 : Encl e1507 (59 / 50 : ℝ) (59 / 50 : ℝ) := by
  exact Encl.exact (59 / 50 : ℝ)

lemma b1508 : Encl e1508 (11737677053 / 31250000000 : ℝ) (375605665697 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1507 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1509 : Encl e1509 (402197167151 / 500000000000 : ℝ) (160878866861 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1507 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1510 : Encl e1510 (2891 / 2500 : ℝ) (2891 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1511 : Encl e1511 (184046776191 / 500000000000 : ℝ) (368093552383 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1510 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1512 : Encl e1512 (3481 / 2500 : ℝ) (3481 / 2500 : ℝ) := by
  exact Encl.pow b1507 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1513 : Encl e1513 (3481 / 625 : ℝ) (3481 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b1512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1514 : Encl e1514 (1772858742089 / 1000000000000 : ℝ) (177285874209 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1513 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1515 : Encl e1515 (2772858742089 / 1000000000000 : ℝ) (277285874209 / 100000000000 : ℝ) := by
  exact Encl.add b5 b1514 (by norm_num) (by norm_num)

lemma b1516 : Encl e1516 (104074393879 / 62500000000 : ℝ) (333038060413 / 200000000000 : ℝ) := by
  exact Encl.sqrt b1515 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1517 : Encl e1517 (166574393879 / 62500000000 : ℝ) (533038060413 / 200000000000 : ℝ) := by
  exact Encl.add b5 b1516 (by norm_num) (by norm_num)

lemma b1518 : Encl e1518 (187603864389 / 250000000000 : ℝ) (375207728779 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b1517 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1519 : Encl e1519 (42023265623 / 200000000000 : ℝ) (210116328117 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1520 : Encl e1520 (578209880497 / 1000000000000 : ℝ) (1156419761 / 2000000000 : ℝ) := by
  exact Encl.add b1511 b1519 (by norm_num) (by norm_num)

lemma b1521 : Encl e1521 (-421790119503 / 1000000000000 : ℝ) (-843580239 / 2000000000 : ℝ) := by
  exact Encl.sub b1520 b5 (by norm_num) (by norm_num)

lemma b1522 : Encl e1522 (2256242928461 / 1000000000000 : ℝ) (1128121464231 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b1512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1523 : Encl e1523 (70539808051 / 500000000000 : ℝ) (17634952013 / 125000000000 : ℝ) := by
  exact Encl.pow b1508 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1524 : Encl e1524 (107365047987 / 125000000000 : ℝ) (429460191949 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b1523 (by norm_num) (by norm_num)

lemma b1525 : Encl e1525 (463389788379 / 500000000000 : ℝ) (23169489419 / 25000000000 : ℝ) := by
  exact Encl.sqrt b1524 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1526 : Encl e1526 (-130056455047 / 500000000000 : ℝ) (-260112910091 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b1525 (by norm_num) (by norm_num)

lemma b1527 : Encl e1527 (159205973971 / 200000000000 : ℝ) (796029869861 / 1000000000000 : ℝ) := by
  exact Encl.pow b1525 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1528 : Encl e1528 (265343289951 / 1000000000000 : ℝ) (132671644977 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1527 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1529 : Encl e1529 (5230379857 / 1000000000000 : ℝ) (5230379863 / 1000000000000 : ℝ) := by
  exact Encl.add b1526 b1528 (by norm_num) (by norm_num)

lemma b1530 : Encl e1530 (5125772259 / 1000000000000 : ℝ) (2562886133 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1529 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1531 : Encl e1531 (3805641051 / 25000000000 : ℝ) (152225642043 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1523 b1525 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1532 : Encl e1532 (-46194358949 / 25000000000 : ℝ) (-1847774357957 / 1000000000000 : ℝ) := by
  exact Encl.sub b1531 b23 (by norm_num) (by norm_num)

lemma b1533 : Encl e1533 (463389788379 / 250000000000 : ℝ) (23169489419 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1525 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1534 : Encl e1534 (1446198889 / 250000000000 : ℝ) (5784795563 / 1000000000000 : ℝ) := by
  exact Encl.add b1532 b1533 (by norm_num) (by norm_num)

lemma b1535 : Encl e1535 (115695911 / 1000000000000 : ℝ) (14461989 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1534 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1536 : Encl e1536 (5010076347 / 1000000000000 : ℝ) (1002015271 / 200000000000 : ℝ) := by
  exact Encl.sub b1530 b1535 (by norm_num) (by norm_num)

lemma b1537 : Encl e1537 (706496833 / 62500000000 : ℝ) (2825987337 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1522 b1536 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1538 : Encl e1538 (-16419446807 / 40000000000 : ℝ) (-51310771269 / 125000000000 : ℝ) := by
  exact Encl.add b1521 b1537 (by norm_num) (by norm_num)

lemma b1539 : Encl e1539 (647050245057 / 1000000000000 : ℝ) (323525122531 / 500000000000 : ℝ) := by
  exact Encl.pow b1509 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1540 : Encl e1540 (176474877469 / 500000000000 : ℝ) (352949754943 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1539 (by norm_num) (by norm_num)

lemma b1541 : Encl e1541 (297047872799 / 500000000000 : ℝ) (594095745603 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1540 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1542 : Encl e1542 (797047872799 / 500000000000 : ℝ) (1594095745603 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1541 (by norm_num) (by norm_num)

lemma b1543 : Encl e1543 (5046085447 / 10000000000 : ℝ) (7884508511 / 15625000000 : ℝ) := by
  exact Encl.div_nonneg b1509 b1542 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1544 : Encl e1544 (31828722923 / 125000000000 : ℝ) (254629783389 / 1000000000000 : ℝ) := by
  exact Encl.pow b1543 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1545 : Encl e1545 (156828722923 / 125000000000 : ℝ) (1254629783389 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1544 (by norm_num) (by norm_num)

lemma b1546 : Encl e1546 (112010257717 / 100000000000 : ℝ) (1120102577173 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1545 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1547 : Encl e1547 (212010257717 / 100000000000 : ℝ) (2120102577173 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1546 (by norm_num) (by norm_num)

lemma b1548 : Encl e1548 (238011382153 / 1000000000000 : ℝ) (59502845539 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1543 b1547 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1549 : Encl e1549 (467327644273 / 500000000000 : ℝ) (934655288559 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e1509) (a := (238011382153 / 1000000000000 : ℝ)) (b := (59502845539 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (402197167151 / 500000000000 : ℝ) by norm_num).trans b1509.1
        exact b1509.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1509) (238011382153 / 1000000000000 : ℝ) (59502845539 / 250000000000 : ℝ) from b1548) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1550 : Encl e1550 (238337098579 / 500000000000 : ℝ) (238337098583 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1549 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1551 : Encl e1551 (394153223807 / 1000000000000 : ℝ) (39415322381 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1509 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1552 : Encl e1552 (234164753377 / 1000000000000 : ℝ) (117082376691 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1551 b1541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1553 : Encl e1553 (3789210059 / 15625000000 : ℝ) (242509443789 / 1000000000000 : ℝ) := by
  exact Encl.sub b1550 b1552 (by norm_num) (by norm_num)

lemma b1554 : Encl e1554 (297047872799 / 10000000000 : ℝ) (594095745603 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1555 : Encl e1555 (27079619413 / 1000000000000 : ℝ) (13539809707 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1509 b1554 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1556 : Encl e1556 (107714912181 / 500000000000 : ℝ) (26928728047 / 125000000000 : ℝ) := by
  exact Encl.sub b1553 b1555 (by norm_num) (by norm_num)

lemma b1557 : Encl e1557 (963389788379 / 500000000000 : ℝ) (48169489419 / 25000000000 : ℝ) := by
  exact Encl.add b5 b1525 (by norm_num) (by norm_num)

lemma b1558 : Encl e1558 (38987922669 / 200000000000 : ℝ) (194939613347 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1508 b1557 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1559 : Encl e1559 (38001452851 / 1000000000000 : ℝ) (9500363213 / 250000000000 : ℝ) := by
  exact Encl.pow b1558 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1560 : Encl e1560 (1038001452851 / 1000000000000 : ℝ) (259500363213 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1559 (by norm_num) (by norm_num)

lemma b1561 : Encl e1561 (25470589079 / 25000000000 : ℝ) (1018823563161 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1560 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1562 : Encl e1562 (50470589079 / 25000000000 : ℝ) (2018823563161 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1561 (by norm_num) (by norm_num)

lemma b1563 : Encl e1563 (12070124459 / 125000000000 : ℝ) (48280497837 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1558 b1562 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1564 : Encl e1564 (77010040893 / 200000000000 : ℝ) (192525102237 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e1508) (a := (12070124459 / 125000000000 : ℝ)) (b := (48280497837 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (11737677053 / 31250000000 : ℝ) by norm_num).trans b1508.1
        exact b1508.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1508) (12070124459 / 125000000000 : ℝ) (48280497837 / 500000000000 : ℝ) from b1563) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1565 : Encl e1565 (196375604277 / 1000000000000 : ℝ) (98187802141 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1564 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1566 : Encl e1566 (184046776191 / 1000000000000 : ℝ) (1437865439 / 7812500000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1508 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1567 : Encl e1567 (170570793341 / 1000000000000 : ℝ) (1332584323 / 7812500000 : ℝ) := by
  exact Encl.mul_nonneg b1566 b1525 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1568 : Encl e1568 (25804810933 / 1000000000000 : ℝ) (25804810941 / 1000000000000 : ℝ) := by
  exact Encl.sub b1565 b1567 (by norm_num) (by norm_num)

lemma b1569 : Encl e1569 (463389788379 / 10000000000 : ℝ) (23169489419 / 500000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1525 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1570 : Encl e1570 (8105609469 / 1000000000000 : ℝ) (810560947 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1508 b1569 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1571 : Encl e1571 (17699201463 / 1000000000000 : ℝ) (276550023 / 15625000000 : ℝ) := by
  exact Encl.sub b1568 b1570 (by norm_num) (by norm_num)

lemma b1572 : Encl e1572 (19773062289 / 100000000000 : ℝ) (197730622913 / 1000000000000 : ℝ) := by
  exact Encl.sub b1556 b1571 (by norm_num) (by norm_num)

lemma b1573 : Encl e1573 (167568324483 / 1000000000000 : ℝ) (167568324503 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1572 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1574 : Encl e1574 (-60729461423 / 250000000000 : ℝ) (-242917845649 / 1000000000000 : ℝ) := by
  exact Encl.add b1538 b1573 (by norm_num) (by norm_num)

lemma b1575 : Encl e1575 (112133603307 / 62500000000 : ℝ) (448534413229 / 250000000000 : ℝ) := by
  exact Encl.add b1509 b4 (by norm_num) (by norm_num)

lemma b1576 : Encl e1576 (112133603307 / 125000000000 : ℝ) (448534413229 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1575 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1577 : Encl e1577 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1509 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1578 : Encl e1578 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1577 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1579 : Encl e1579 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1577 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1580 : Encl e1580 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1579 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1581 : Encl e1581 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1580 (by norm_num) (by norm_num)

lemma b1582 : Encl e1582 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1581 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1583 : Encl e1583 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1578 b1582 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1584 : Encl e1584 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1579 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1585 : Encl e1585 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1583 b1584 (by norm_num) (by norm_num)

lemma b1586 : Encl e1586 (611522950397 / 1000000000000 : ℝ) (30576147521 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b1576 b1585 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1587 : Encl e1587 (76022781903 / 100000000000 : ℝ) (760227819033 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1576 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1588 : Encl e1588 (336867181351 / 250000000000 : ℝ) (1347468725411 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1587 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1589 : Encl e1589 (577946336827 / 1000000000000 : ℝ) (9030411513 / 15625000000 : ℝ) := by
  exact Encl.pow b1587 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1590 : Encl e1590 (90783598297 / 200000000000 : ℝ) (453917991491 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1589 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1591 : Encl e1591 (290783598297 / 200000000000 : ℝ) (1453917991491 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1590 (by norm_num) (by norm_num)

lemma b1592 : Encl e1592 (75361576113 / 62500000000 : ℝ) (1205785217811 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1591 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1593 : Encl e1593 (32495157411 / 20000000000 : ℝ) (406189467641 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1588 b1592 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1594 : Encl e1594 (907835982971 / 1000000000000 : ℝ) (907835982981 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1589 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1595 : Encl e1595 (716921887569 / 1000000000000 : ℝ) (716921887593 / 1000000000000 : ℝ) := by
  exact Encl.sub b1593 b1594 (by norm_num) (by norm_num)

lemma b1596 : Encl e1596 (576687904497 / 1000000000000 : ℝ) (14417197613 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b1509 b1595 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1597 : Encl e1597 (34835045877 / 1000000000000 : ℝ) (34835045923 / 1000000000000 : ℝ) := by
  exact Encl.sub b1586 b1596 (by norm_num) (by norm_num)

lemma b1598 : Encl e1598 (804732479399 / 1000000000000 : ℝ) (804732479403 / 1000000000000 : ℝ) := by
  exact Encl.pow b1576 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1599 : Encl e1599 (788637829811 / 1000000000000 : ℝ) (157727565963 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1598 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1600 : Encl e1600 (42272434037 / 200000000000 : ℝ) (211362170189 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1599 (by norm_num) (by norm_num)

lemma b1601 : Encl e1601 (195267520597 / 1000000000000 : ℝ) (195267520601 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1598 (by norm_num) (by norm_num)

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures1603To1821
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
lemma b1602 : Encl e1602 (220945423463 / 500000000000 : ℝ) (441890846931 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1601 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1603 : Encl e1603 (59789134481 / 125000000000 : ℝ) (59789134483 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1600 b1602 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1604 : Encl e1604 (65210865517 / 125000000000 : ℝ) (65210865519 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b1603 (by norm_num) (by norm_num)

lemma b1605 : Encl e1605 (126821848031 / 200000000000 : ℝ) (634109240161 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1539 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1606 : Encl e1606 (365890759839 / 1000000000000 : ℝ) (73178151969 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b1605 (by norm_num) (by norm_num)

lemma b1607 : Encl e1607 (76984804753 / 125000000000 : ℝ) (15396960951 / 25000000000 : ℝ) := by
  exact Encl.div_nonneg b1606 b1541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1608 : Encl e1608 (9603039049 / 25000000000 : ℝ) (48015195247 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b1607 (by norm_num) (by norm_num)

lemma b1609 : Encl e1609 (1719567027 / 12500000000 : ℝ) (8597835137 / 62500000000 : ℝ) := by
  exact Encl.sub b1604 b1608 (by norm_num) (by norm_num)

lemma b1610 : Encl e1610 (4792095701 / 1000000000000 : ℝ) (479209571 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1597 b1609 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1611 : Encl e1611 (35231773741 / 1000000000000 : ℝ) (8807943447 / 250000000000 : ℝ) := by
  exact Encl.sub b1595 b1585 (by norm_num) (by norm_num)

lemma b1612 : Encl e1612 (720945423463 / 500000000000 : ℝ) (1441890846931 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1602 (by norm_num) (by norm_num)

lemma b1613 : Encl e1613 (622147528271 / 1000000000000 : ℝ) (155536882069 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1576 b1612 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1614 : Encl e1614 (387067546933 / 1000000000000 : ℝ) (19353377347 / 50000000000 : ℝ) := by
  exact Encl.pow b1613 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1615 : Encl e1615 (1387067546933 / 1000000000000 : ℝ) (69353377347 / 50000000000 : ℝ) := by
  exact Encl.add b5 b1614 (by norm_num) (by norm_num)

lemma b1616 : Encl e1616 (1177738318529 / 1000000000000 : ℝ) (1177738318533 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1615 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1617 : Encl e1617 (2177738318529 / 1000000000000 : ℝ) (2177738318533 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1616 (by norm_num) (by norm_num)

lemma b1618 : Encl e1618 (71421290953 / 250000000000 : ℝ) (35710645477 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1613 b1617 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1619 : Encl e1619 (1113090939099 / 1000000000000 : ℝ) (278272734779 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e1576) (a := (71421290953 / 250000000000 : ℝ)) (b := (35710645477 / 125000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (112133603307 / 125000000000 : ℝ) by norm_num).trans b1576.1
        exact b1576.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1576) (71421290953 / 250000000000 : ℝ) (35710645477 / 125000000000 : ℝ) from b1618) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1620 : Encl e1620 (28383818947 / 50000000000 : ℝ) (11353527579 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1619 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1621 : Encl e1621 (439563724963 / 1000000000000 : ℝ) (87912744993 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1576 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1622 : Encl e1622 (194239186701 / 1000000000000 : ℝ) (38847837341 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1621 b1602 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1623 : Encl e1623 (74687438447 / 200000000000 : ℝ) (373437192249 / 1000000000000 : ℝ) := by
  exact Encl.sub b1620 b1622 (by norm_num) (by norm_num)

lemma b1624 : Encl e1624 (220945423463 / 10000000000 : ℝ) (441890846931 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1602 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1625 : Encl e1625 (4060137623 / 100000000000 : ℝ) (5075172029 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1576 b1624 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1626 : Encl e1626 (332835816003 / 1000000000000 : ℝ) (332835816019 / 1000000000000 : ℝ) := by
  exact Encl.sub b1623 b1625 (by norm_num) (by norm_num)

lemma b1627 : Encl e1627 (117405991627 / 1000000000000 : ℝ) (117405991657 / 1000000000000 : ℝ) := by
  exact Encl.sub b1626 b1556 (by norm_num) (by norm_num)

lemma b1628 : Encl e1628 (1034105333 / 250000000000 : ℝ) (206821067 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b1611 b1627 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1629 : Encl e1629 (8928517033 / 1000000000000 : ℝ) (178570341 / 20000000000 : ℝ) := by
  exact Encl.add b1610 b1628 (by norm_num) (by norm_num)

lemma b1630 : Encl e1630 (92674492151 / 1000000000000 : ℝ) (23168623039 / 250000000000 : ℝ) := by
  exact Encl.sub b1576 b1509 (by norm_num) (by norm_num)

lemma b1631 : Encl e1631 (48171383653 / 500000000000 : ℝ) (19268553499 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1629 b1630 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1632 : Encl e1632 (-73287539193 / 500000000000 : ℝ) (-73287539077 / 500000000000 : ℝ) := by
  exact Encl.add b1574 b1631 (by norm_num) (by norm_num)

lemma b1633 : Encl e1633 (354784324093 / 500000000000 : ℝ) (177392162053 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1595 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1634 : Encl e1634 (167753104849 / 200000000000 : ℝ) (838765524247 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1635 : Encl e1635 (743336591727 / 500000000000 : ℝ) (1486673183459 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1634 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1636 : Encl e1636 (703527604661 / 1000000000000 : ℝ) (351763802333 / 500000000000 : ℝ) := by
  exact Encl.pow b1634 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1637 : Encl e1637 (552549288599 / 1000000000000 : ℝ) (110509857721 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1636 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1638 : Encl e1638 (1552549288599 / 1000000000000 : ℝ) (310509857721 / 200000000000 : ℝ) := by
  exact Encl.add b5 b1637 (by norm_num) (by norm_num)

lemma b1639 : Encl e1639 (623006679057 / 500000000000 : ℝ) (1246013358117 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1638 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1640 : Encl e1640 (1852414645733 / 1000000000000 : ℝ) (370482929149 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1635 b1639 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1641 : Encl e1641 (1105098577199 / 1000000000000 : ℝ) (1105098577209 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1636 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1642 : Encl e1642 (186829017131 / 250000000000 : ℝ) (373658034273 / 500000000000 : ℝ) := by
  exact Encl.sub b1640 b1641 (by norm_num) (by norm_num)

lemma b1643 : Encl e1643 (335196974291 / 500000000000 : ℝ) (167598487151 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1576 b1642 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1644 : Encl e1644 (19587349791 / 500000000000 : ℝ) (3917469963 / 100000000000 : ℝ) := by
  exact Encl.sub b1633 b1643 (by norm_num) (by norm_num)

lemma b1645 : Encl e1645 (198313075823 / 1000000000000 : ℝ) (49578268973 / 250000000000 : ℝ) := by
  exact Encl.sub b165 b1604 (by norm_num) (by norm_num)

lemma b1646 : Encl e1646 (60694181 / 7812500000 : ℝ) (7768855181 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1644 b1645 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1647 : Encl e1647 (30394180931 / 1000000000000 : ℝ) (30394180977 / 1000000000000 : ℝ) := by
  exact Encl.sub b1642 b1595 (by norm_num) (by norm_num)

lemma b1648 : Encl e1648 (187316953493 / 1000000000000 : ℝ) (4682923841 / 25000000000 : ℝ) := by
  exact Encl.sub b183 b1626 (by norm_num) (by norm_num)

lemma b1649 : Encl e1649 (45546763 / 8000000000 : ℝ) (5693345389 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1647 b1648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1650 : Encl e1650 (13462200543 / 1000000000000 : ℝ) (1346220057 / 100000000000 : ℝ) := by
  exact Encl.add b1646 b1649 (by norm_num) (by norm_num)

lemma b1651 : Encl e1651 (11584311519 / 125000000000 : ℝ) (18534898431 / 200000000000 : ℝ) := by
  exact Encl.sub b4 b1576 (by norm_num) (by norm_num)

lemma b1652 : Encl e1652 (36315819569 / 250000000000 : ℝ) (145263278573 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1650 b1651 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1653 : Encl e1653 (-131180011 / 100000000000 : ℝ) (-1311799581 / 1000000000000 : ℝ) := by
  exact Encl.add b1632 b1652 (by norm_num) (by norm_num)

lemma b1654 : Encl e1654 (813559322033 / 1000000000000 : ℝ) (406779661017 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1655 : Encl e1655 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b1654 (by norm_num) (by norm_num)

lemma b1656 : Encl e1656 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b1655 b5 (by norm_num) (by norm_num)

lemma b1657 : Encl e1657 (59 / 25 : ℝ) (59 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1658 : Encl e1658 (221372559979 / 125000000000 : ℝ) (1770980479837 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1657 b1518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1659 : Encl e1659 (563720594969 / 1000000000000 : ℝ) (563720594971 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1658 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1660 : Encl e1660 (49082141757 / 200000000000 : ℝ) (61352677197 / 250000000000 : ℝ) := by
  exact Encl.add b1656 b1659 (by norm_num) (by norm_num)

lemma b1661 : Encl e1661 (3481 / 1250 : ℝ) (3481 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b1512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1662 : Encl e1662 (2089756966201 / 1000000000000 : ℝ) (32652452597 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b1661 b1518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1663 : Encl e1663 (523134961979 / 100000000000 : ℝ) (2615674809899 / 500000000000 : ℝ) := by
  exact Encl.add b0 b1662 (by norm_num) (by norm_num)

lemma b1664 : Encl e1664 (71475449373 / 31250000000 : ℝ) (2287214379939 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1663 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1665 : Encl e1665 (1456085897909 / 1000000000000 : ℝ) (728042948957 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b1664 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1666 : Encl e1666 (205379 / 125000 : ℝ) (205379 / 125000 : ℝ) := by
  exact Encl.pow b1507 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1667 : Encl e1667 (13760393 / 62500000 : ℝ) (13760393 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b1666 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1668 : Encl e1668 (13760393 / 62500000 : ℝ) (13760393 / 62500000 : ℝ) := by
  exact Encl.min b1667 b941 (by norm_num) (by norm_num)

lemma b1669 : Encl e1669 (49082141757 / 100000000000 : ℝ) (61352677197 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1660 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1670 : Encl e1670 (41281179 / 31250000 : ℝ) (41281179 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b1668 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1671 : Encl e1671 (2120186142089 / 1000000000000 : ℝ) (424037228421 / 200000000000 : ℝ) := by
  exact Encl.pow b1665 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1672 : Encl e1672 (700190269159 / 250000000000 : ℝ) (1400380538329 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1670 b1671 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1673 : Encl e1673 (343668380477 / 500000000000 : ℝ) (687336760969 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1672 b1660 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1674 : Encl e1674 (306846768283 / 125000000000 : ℝ) (1227387073159 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1673 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1675 : Encl e1675 (431846768283 / 125000000000 : ℝ) (1727387073159 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1674 (by norm_num) (by norm_num)

lemma b1676 : Encl e1676 (1858702274777 / 1000000000000 : ℝ) (1858702274793 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1675 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1677 : Encl e1677 (2858702274777 / 1000000000000 : ℝ) (2858702274793 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1676 (by norm_num) (by norm_num)

lemma b1678 : Encl e1678 (171693786337 / 1000000000000 : ℝ) (171693786341 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1669 b1677 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1679 : Encl e1679 (2038959993 / 1000000000000 : ℝ) (1019479997 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1668 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1680 : Encl e1680 (18429230611 / 250000000000 : ℝ) (73716922451 / 1000000000000 : ℝ) := by
  exact Encl.sub b1660 b1678 (by norm_num) (by norm_num)

lemma b1681 : Encl e1681 (25313383829 / 500000000000 : ℝ) (3164172979 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b1680 b1665 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1682 : Encl e1682 (2563069603 / 1000000000000 : ℝ) (512613921 / 200000000000 : ℝ) := by
  exact Encl.pow b1681 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1683 : Encl e1683 (22426859 / 31250000000 : ℝ) (71765949 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1682 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1684 : Encl e1684 (5061319279 / 1000000000000 : ℝ) (5061319281 / 1000000000000 : ℝ) := by
  exact Encl.pow b1678 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1685 : Encl e1685 (557165939 / 500000000000 : ℝ) (1114331879 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1668 b1684 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1686 : Encl e1686 (915995683 / 500000000000 : ℝ) (1831991369 / 1000000000000 : ℝ) := by
  exact Encl.add b1683 b1685 (by norm_num) (by norm_num)

lemma b1687 : Encl e1687 (915995683 / 500000000000 : ℝ) (1831991369 / 1000000000000 : ℝ) := by
  exact Encl.min b1679 b1686 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_118 : Encl (twoChordBaseline (59 / 50 : ℝ)) (-131180011 / 100000000000 : ℝ) (-1311799581 / 1000000000000 : ℝ) := by
  exact b1653

lemma gain_enclosure_118 : Encl (gain (59 / 50 : ℝ)) (915995683 / 500000000000 : ℝ) (1831991369 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b1687

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

lemma baseline_lower_118 : (-131180011 / 100000000000 : ℝ) ≤ baseline (59 / 50 : ℝ) :=
  (baseline_enclosure_118).1.trans (twoChordBaseline_le_of_range (h := (59 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_118_oai : (65023907 / 125000000000 : ℝ) ≤ baseline (59 / 50 : ℝ) + gain (59 / 50 : ℝ) := by
  have hb := baseline_lower_118
  have hg := (gain_enclosure_118).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_118_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_118_oai

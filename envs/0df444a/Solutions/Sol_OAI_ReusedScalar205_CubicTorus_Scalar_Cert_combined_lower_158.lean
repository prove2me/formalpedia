-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_158
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:46:11.61159+00:00
-- url     : https://prove2.me/submissions/38d82f61-e9e1-4bf3-b336-8adc73b8348b

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

lemma b3023 : Encl e3023 (79 / 50 : ℝ) (79 / 50 : ℝ) := by
  exact Encl.exact (79 / 50 : ℝ)

lemma b3024 : Encl e3024 (50292962017 / 100000000000 : ℝ) (502929620171 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3023 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3025 : Encl e3025 (3871 / 2500 : ℝ) (3871 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b3023 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3026 : Encl e3026 (246435513883 / 500000000000 : ℝ) (492871027767 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3025 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3027 : Encl e3027 (6241 / 2500 : ℝ) (6241 / 2500 : ℝ) := by
  exact Encl.pow b3023 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3028 : Encl e3028 (6241 / 625 : ℝ) (6241 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b3027 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3029 : Encl e3029 (794628799869 / 250000000000 : ℝ) (3178515199477 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3028 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3030 : Encl e3030 (1044628799869 / 250000000000 : ℝ) (4178515199477 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3029 (by norm_num) (by norm_num)

lemma b3031 : Encl e3031 (127758854871 / 62500000000 : ℝ) (2044141677937 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3030 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3032 : Encl e3032 (190258854871 / 62500000000 : ℝ) (3044141677937 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3031 (by norm_num) (by norm_num)

lemma b3033 : Encl e3033 (65699964443 / 100000000000 : ℝ) (656999644431 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b3032 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3034 : Encl e3034 (4598997511 / 25000000000 : ℝ) (183959900441 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3033 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3035 : Encl e3035 (338415464103 / 500000000000 : ℝ) (42301933013 / 62500000000 : ℝ) := by
  exact Encl.add b3026 b3034 (by norm_num) (by norm_num)

lemma b3036 : Encl e3036 (-161584535897 / 500000000000 : ℝ) (-20198066987 / 62500000000 : ℝ) := by
  exact Encl.sub b3035 b5 (by norm_num) (by norm_num)

lemma b3037 : Encl e3037 (314612307081 / 250000000000 : ℝ) (50337969133 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b3027 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3038 : Encl e3038 (63234550711 / 250000000000 : ℝ) (126469101423 / 500000000000 : ℝ) := by
  exact Encl.pow b3024 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3039 : Encl e3039 (373530898577 / 500000000000 : ℝ) (186765449289 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b3038 (by norm_num) (by norm_num)

lemma b3040 : Encl e3040 (864327366889 / 1000000000000 : ℝ) (864327366891 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3039 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3041 : Encl e3041 (-7906428009 / 40000000000 : ℝ) (-98830350111 / 500000000000 : ℝ) := by
  exact Encl.sub b29 b3040 (by norm_num) (by norm_num)

lemma b3042 : Encl e3042 (161426489009 / 250000000000 : ℝ) (322852978021 / 500000000000 : ℝ) := by
  exact Encl.pow b3040 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b3043 : Encl e3043 (107617659339 / 500000000000 : ℝ) (215235318681 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3042 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3044 : Encl e3044 (17574618453 / 1000000000000 : ℝ) (17574618459 / 1000000000000 : ℝ) := by
  exact Encl.add b3041 b3043 (by norm_num) (by norm_num)

lemma b3045 : Encl e3045 (17223126083 / 1000000000000 : ℝ) (1722312609 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b3044 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3046 : Encl e3046 (292641668577 / 1000000000000 : ℝ) (292641668581 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3038 b3040 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3047 : Encl e3047 (-1707358331423 / 1000000000000 : ℝ) (-1707358331419 / 1000000000000 : ℝ) := by
  exact Encl.sub b3046 b23 (by norm_num) (by norm_num)

lemma b3048 : Encl e3048 (864327366889 / 500000000000 : ℝ) (864327366891 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3040 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3049 : Encl e3049 (4259280471 / 200000000000 : ℝ) (21296402363 / 1000000000000 : ℝ) := by
  exact Encl.add b3047 b3048 (by norm_num) (by norm_num)

lemma b3050 : Encl e3050 (425928047 / 1000000000000 : ℝ) (26620503 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b3049 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3051 : Encl e3051 (3359439607 / 200000000000 : ℝ) (16797198043 / 1000000000000 : ℝ) := by
  exact Encl.sub b3045 b3050 (by norm_num) (by norm_num)

lemma b3052 : Encl e3052 (4227684181 / 200000000000 : ℝ) (5284605229 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3037 b3051 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3053 : Encl e3053 (-302030650889 / 1000000000000 : ℝ) (-75507662719 / 250000000000 : ℝ) := by
  exact Encl.add b3036 b3052 (by norm_num) (by norm_num)

lemma b3054 : Encl e3054 (1864327366889 / 1000000000000 : ℝ) (1864327366891 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3040 (by norm_num) (by norm_num)

lemma b3055 : Encl e3055 (269764650297 / 1000000000000 : ℝ) (269764650299 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3024 b3054 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3056 : Encl e3056 (72772966549 / 1000000000000 : ℝ) (72772966551 / 1000000000000 : ℝ) := by
  exact Encl.pow b3055 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3057 : Encl e3057 (1072772966549 / 1000000000000 : ℝ) (1072772966551 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3056 (by norm_num) (by norm_num)

lemma b3058 : Encl e3058 (1035747539967 / 1000000000000 : ℝ) (1035747539969 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3057 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3059 : Encl e3059 (2035747539967 / 1000000000000 : ℝ) (2035747539969 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3058 (by norm_num) (by norm_num)

lemma b3060 : Encl e3060 (132513803897 / 1000000000000 : ℝ) (132513803899 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3055 b3059 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3061 : Encl e3061 (526984926001 / 1000000000000 : ℝ) (52698492601 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e3024) (a := (132513803897 / 1000000000000 : ℝ)) (b := (132513803899 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (50292962017 / 100000000000 : ℝ) by norm_num).trans b3024.1
        exact b3024.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e3024) (132513803897 / 1000000000000 : ℝ) (132513803899 / 1000000000000 : ℝ) from b3060) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b3062 : Encl e3062 (13438115613 / 50000000000 : ℝ) (134381156133 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b3061 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3063 : Encl e3063 (246435513883 / 1000000000000 : ℝ) (61608878471 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b3024 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3064 : Encl e3064 (106500479411 / 500000000000 : ℝ) (26625119853 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b3063 b3040 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3065 : Encl e3065 (13940338359 / 250000000000 : ℝ) (13940338361 / 250000000000 : ℝ) := by
  exact Encl.sub b3062 b3064 (by norm_num) (by norm_num)

lemma b3066 : Encl e3066 (864327366889 / 20000000000 : ℝ) (864327366891 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b3040 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3067 : Encl e3067 (11637479951 / 1000000000000 : ℝ) (727342497 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b3024 b3066 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3068 : Encl e3068 (11030968371 / 250000000000 : ℝ) (44123873493 / 1000000000000 : ℝ) := by
  exact Encl.sub b3065 b3067 (by norm_num) (by norm_num)

lemma b3069 : Encl e3069 (476028896019 / 1000000000000 : ℝ) (476028896159 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b3068 (by norm_num) (by norm_num)

lemma b3070 : Encl e3070 (75321027851 / 250000000000 : ℝ) (150642055747 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3069 b3023 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3071 : Encl e3071 (-149307897 / 200000000000 : ℝ) (-373269691 / 500000000000 : ℝ) := by
  exact Encl.add b3053 b3070 (by norm_num) (by norm_num)

lemma b3072 : Encl e3072 (151898734177 / 250000000000 : ℝ) (607594936709 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b3023 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3073 : Encl e3073 (151898734177 / 250000000000 : ℝ) (607594936709 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b3072 (by norm_num) (by norm_num)

lemma b3074 : Encl e3074 (-98101265823 / 250000000000 : ℝ) (-392405063291 / 1000000000000 : ℝ) := by
  exact Encl.sub b3073 b5 (by norm_num) (by norm_num)

lemma b3075 : Encl e3075 (79 / 25 : ℝ) (79 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b3023 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3076 : Encl e3076 (1038059438199 / 500000000000 : ℝ) (1038059438201 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b3075 b3033 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3077 : Encl e3077 (2643396653 / 4000000000 : ℝ) (165212290813 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b3076 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3078 : Encl e3078 (134222049979 / 500000000000 : ℝ) (268444099961 / 1000000000000 : ℝ) := by
  exact Encl.add b3074 b3077 (by norm_num) (by norm_num)

lemma b3079 : Encl e3079 (6241 / 1250 : ℝ) (6241 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b3027 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3080 : Encl e3080 (328026782471 / 100000000000 : ℝ) (820066956179 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3079 b3033 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3081 : Encl e3081 (6421860478299 / 1000000000000 : ℝ) (3210930239153 / 500000000000 : ℝ) := by
  exact Encl.add b0 b3080 (by norm_num) (by norm_num)

lemma b3082 : Encl e3082 (79191843793 / 31250000000 : ℝ) (2534139001379 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3081 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3083 : Encl e3083 (806641497101 / 500000000000 : ℝ) (1613282994207 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b3082 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3084 : Encl e3084 (493039 / 125000 : ℝ) (493039 / 125000 : ℝ) := by
  exact Encl.pow b3023 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b3085 : Encl e3085 (33033613 / 62500000 : ℝ) (33033613 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b3084 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3086 : Encl e3086 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b3085 b941 (by norm_num) (by norm_num)

lemma b3087 : Encl e3087 (134222049979 / 250000000000 : ℝ) (268444099961 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3078 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3088 : Encl e3088 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b3086 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3089 : Encl e3089 (2602682019381 / 1000000000000 : ℝ) (1301341009699 / 500000000000 : ℝ) := by
  exact Encl.pow b3083 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3090 : Encl e3090 (2810896580931 / 500000000000 : ℝ) (56217931619 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b3088 b3089 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3091 : Encl e3091 (754568602743 / 500000000000 : ℝ) (754568602757 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b3090 b3078 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3092 : Encl e3092 (2694887866939 / 500000000000 : ℝ) (5389775733979 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3091 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3093 : Encl e3093 (3194887866939 / 500000000000 : ℝ) (6389775733979 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3092 (by norm_num) (by norm_num)

lemma b3094 : Encl e3094 (252780057241 / 100000000000 : ℝ) (2527800572431 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3093 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3095 : Encl e3095 (352780057241 / 100000000000 : ℝ) (3527800572431 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3094 (by norm_num) (by norm_num)

lemma b3096 : Encl e3096 (3804694943 / 25000000000 : ℝ) (38046949431 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b3087 b3095 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3097 : Encl e3097 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b3086 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3098 : Encl e3098 (58128151117 / 500000000000 : ℝ) (116256302241 / 1000000000000 : ℝ) := by
  exact Encl.sub b3078 b3096 (by norm_num) (by norm_num)

lemma b3099 : Encl e3099 (72061939939 / 1000000000000 : ℝ) (14412387989 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b3098 b3083 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3100 : Encl e3100 (5192923187 / 1000000000000 : ℝ) (5192923189 / 1000000000000 : ℝ) := by
  exact Encl.pow b3099 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3101 : Encl e3101 (363504623 / 250000000000 : ℝ) (1454018493 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3100 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3102 : Encl e3102 (881210181 / 250000000000 : ℝ) (140993629 / 40000000000 : ℝ) := by
  exact Encl.pow b3096 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b3103 : Encl e3103 (63447133 / 50000000000 : ℝ) (1268942661 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3086 b3102 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3104 : Encl e3104 (10636567 / 3906250000 : ℝ) (1361480577 / 500000000000 : ℝ) := by
  exact Encl.add b3101 b3103 (by norm_num) (by norm_num)

lemma b3105 : Encl e3105 (10636567 / 3906250000 : ℝ) (1361480577 / 500000000000 : ℝ) := by
  exact Encl.min b3097 b3104 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_158 : Encl (linearBaseline (79 / 50 : ℝ)) (-149307897 / 200000000000 : ℝ) (-373269691 / 500000000000 : ℝ) := by
  exact b3071

lemma gain_enclosure_158 : Encl (gain (79 / 50 : ℝ)) (10636567 / 3906250000 : ℝ) (1361480577 / 500000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b3105

lemma baseline_lower_158 : (-149307897 / 200000000000 : ℝ) ≤ baseline (79 / 50 : ℝ) :=
  (baseline_enclosure_158).1.trans ((linearBaseline_eq_of_range (h := (79 / 50 : ℝ)) (by norm_num) (by norm_num)).le)

lemma combined_lower_158_oai : (1976421667 / 1000000000000 : ℝ) ≤ baseline (79 / 50 : ℝ) + gain (79 / 50 : ℝ) := by
  have hb := baseline_lower_158
  have hg := (gain_enclosure_158).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_158_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_158_oai

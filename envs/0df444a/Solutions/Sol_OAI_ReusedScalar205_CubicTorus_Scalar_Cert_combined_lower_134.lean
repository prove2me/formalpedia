-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_134
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:43:09.787997+00:00
-- url     : https://prove2.me/submissions/a7d186b8-9272-484b-97c5-71afaee750f0

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures2042To2262
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

lemma b2231 : Encl e2231 (67 / 50 : ℝ) (67 / 50 : ℝ) := by
  exact Encl.exact (67 / 50 : ℝ)

lemma b2232 : Encl e2232 (213267623743 / 500000000000 : ℝ) (426535247487 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2231 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2233 : Encl e2233 (913464752513 / 1000000000000 : ℝ) (182692950503 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2231 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2234 : Encl e2234 (3283 / 2500 : ℝ) (3283 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2235 : Encl e2235 (52250567817 / 125000000000 : ℝ) (418004542537 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2234 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2236 : Encl e2236 (4489 / 2500 : ℝ) (4489 / 2500 : ℝ) := by
  exact Encl.pow b2231 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2237 : Encl e2237 (4489 / 625 : ℝ) (4489 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b2236 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2238 : Encl e2238 (1143114463263 / 500000000000 : ℝ) (2286228926527 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2237 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2239 : Encl e2239 (1643114463263 / 500000000000 : ℝ) (3286228926527 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2238 (by norm_num) (by norm_num)

lemma b2240 : Encl e2240 (906397943307 / 500000000000 : ℝ) (362559177323 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2239 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2241 : Encl e2241 (1406397943307 / 500000000000 : ℝ) (562559177323 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2240 (by norm_num) (by norm_num)

lemma b2242 : Encl e2242 (142207261431 / 200000000000 : ℝ) (177759076789 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2241 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2243 : Encl e2243 (199090166003 / 1000000000000 : ℝ) (49772541501 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2242 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2244 : Encl e2244 (617094708539 / 1000000000000 : ℝ) (617094708541 / 1000000000000 : ℝ) := by
  exact Encl.add b2235 b2243 (by norm_num) (by norm_num)

lemma b2245 : Encl e2245 (-382905291461 / 1000000000000 : ℝ) (-382905291459 / 1000000000000 : ℝ) := by
  exact Encl.sub b2244 b5 (by norm_num) (by norm_num)

lemma b2246 : Encl e2246 (218700758353 / 125000000000 : ℝ) (69984242673 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2236 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2247 : Encl e2247 (181932317347 / 1000000000000 : ℝ) (181932317349 / 1000000000000 : ℝ) := by
  exact Encl.pow b2232 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2248 : Encl e2248 (818067682651 / 1000000000000 : ℝ) (818067682653 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2247 (by norm_num) (by norm_num)

lemma b2249 : Encl e2249 (113058867593 / 125000000000 : ℝ) (452235470373 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2248 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2250 : Encl e2250 (-1486276713 / 6250000000 : ℝ) (-237804274077 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b2249 (by norm_num) (by norm_num)

lemma b2251 : Encl e2251 (739918446519 / 1000000000000 : ℝ) (184979611631 / 250000000000 : ℝ) := by
  exact Encl.pow b2249 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2252 : Encl e2252 (246639482173 / 1000000000000 : ℝ) (9865579287 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b2251 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2253 : Encl e2253 (8835208093 / 1000000000000 : ℝ) (4417604049 / 500000000000 : ℝ) := by
  exact Encl.add b2250 b2252 (by norm_num) (by norm_num)

lemma b2254 : Encl e2254 (8658503931 / 1000000000000 : ℝ) (8658503937 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2253 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2255 : Encl e2255 (20114777507 / 100000000000 : ℝ) (100573887537 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2247 b2249 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2256 : Encl e2256 (-179885222493 / 100000000000 : ℝ) (-899426112463 / 500000000000 : ℝ) := by
  exact Encl.sub b2255 b23 (by norm_num) (by norm_num)

lemma b2257 : Encl e2257 (113058867593 / 62500000000 : ℝ) (452235470373 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2249 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2258 : Encl e2258 (5044828279 / 500000000000 : ℝ) (5044828283 / 500000000000 : ℝ) := by
  exact Encl.add b2256 b2257 (by norm_num) (by norm_num)

lemma b2259 : Encl e2259 (201793131 / 1000000000000 : ℝ) (50448283 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2258 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2260 : Encl e2260 (8456710799 / 1000000000000 : ℝ) (4228355403 / 500000000000 : ℝ) := by
  exact Encl.sub b2254 b2259 (by norm_num) (by norm_num)

lemma b2261 : Encl e2261 (14795912519 / 1000000000000 : ℝ) (3698978133 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2246 b2260 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures2263To2479
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
lemma b2262 : Encl e2262 (-184054689471 / 500000000000 : ℝ) (-368109378927 / 1000000000000 : ℝ) := by
  exact Encl.add b2245 b2261 (by norm_num) (by norm_num)

lemma b2263 : Encl e2263 (834417854083 / 1000000000000 : ℝ) (104302231761 / 125000000000 : ℝ) := by
  exact Encl.pow b2233 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2264 : Encl e2264 (20697768239 / 125000000000 : ℝ) (165582145917 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2263 (by norm_num) (by norm_num)

lemma b2265 : Encl e2265 (203458930691 / 500000000000 : ℝ) (406917861389 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2264 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2266 : Encl e2266 (703458930691 / 500000000000 : ℝ) (1406917861389 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2265 (by norm_num) (by norm_num)

lemma b2267 : Encl e2267 (324633291531 / 500000000000 : ℝ) (649266583067 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2233 b2266 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2268 : Encl e2268 (421547095881 / 1000000000000 : ℝ) (26346693493 / 62500000000 : ℝ) := by
  exact Encl.pow b2267 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2269 : Encl e2269 (1421547095881 / 1000000000000 : ℝ) (88846693493 / 62500000000 : ℝ) := by
  exact Encl.add b5 b2268 (by norm_num) (by norm_num)

lemma b2270 : Encl e2270 (298071624769 / 250000000000 : ℝ) (29807162477 / 25000000000 : ℝ) := by
  exact Encl.sqrt b2269 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2271 : Encl e2271 (548071624769 / 250000000000 : ℝ) (54807162477 / 25000000000 : ℝ) := by
  exact Encl.add b5 b2270 (by norm_num) (by norm_num)

lemma b2272 : Encl e2272 (29615955001 / 100000000000 : ℝ) (148079775007 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2267 b2271 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2273 : Encl e2273 (1151718929409 / 1000000000000 : ℝ) (575859464713 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e2233) (a := (29615955001 / 100000000000 : ℝ)) (b := (148079775007 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (913464752513 / 1000000000000 : ℝ) by norm_num).trans b2233.1
        exact b2233.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2233) (29615955001 / 100000000000 : ℝ) (148079775007 / 500000000000 : ℝ) from b2272) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2274 : Encl e2274 (293688326999 / 500000000000 : ℝ) (73422081751 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2273 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2275 : Encl e2275 (447597728731 / 1000000000000 : ℝ) (447597728733 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2233 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2276 : Encl e2276 (91067755267 / 500000000000 : ℝ) (182135510539 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2275 b2265 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2277 : Encl e2277 (405241143459 / 1000000000000 : ℝ) (202620571737 / 500000000000 : ℝ) := by
  exact Encl.sub b2274 b2276 (by norm_num) (by norm_num)

lemma b2278 : Encl e2278 (203458930691 / 10000000000 : ℝ) (406917861389 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2265 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2279 : Encl e2279 (5612095457 / 125000000000 : ℝ) (22448381829 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2233 b2278 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2280 : Encl e2280 (360344379801 / 1000000000000 : ℝ) (180172189909 / 500000000000 : ℝ) := by
  exact Encl.sub b2277 b2279 (by norm_num) (by norm_num)

lemma b2281 : Encl e2281 (238058867593 / 125000000000 : ℝ) (952235470373 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2249 (by norm_num) (by norm_num)

lemma b2282 : Encl e2282 (44793043397 / 200000000000 : ℝ) (111982608493 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2232 b2281 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2283 : Encl e2283 (50160418419 / 1000000000000 : ℝ) (2508020921 / 50000000000 : ℝ) := by
  exact Encl.pow b2282 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2284 : Encl e2284 (1050160418419 / 1000000000000 : ℝ) (52508020921 / 50000000000 : ℝ) := by
  exact Encl.add b5 b2283 (by norm_num) (by norm_num)

lemma b2285 : Encl e2285 (1024773349779 / 1000000000000 : ℝ) (1024773349781 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2284 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2286 : Encl e2286 (2024773349779 / 1000000000000 : ℝ) (2024773349781 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2285 (by norm_num) (by norm_num)

lemma b2287 : Encl e2287 (11061248757 / 100000000000 : ℝ) (110612487571 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2282 b2286 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2288 : Encl e2288 (220329302981 / 500000000000 : ℝ) (440658605967 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2232) (a := (11061248757 / 100000000000 : ℝ)) (b := (110612487571 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (213267623743 / 500000000000 : ℝ) by norm_num).trans b2232.1
        exact b2232.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2232) (11061248757 / 100000000000 : ℝ) (110612487571 / 1000000000000 : ℝ) from b2287) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2289 : Encl e2289 (2809198613 / 12500000000 : ℝ) (56183972261 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2288 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2290 : Encl e2290 (52250567817 / 250000000000 : ℝ) (209002271269 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2232 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2291 : Encl e2291 (189036480911 / 1000000000000 : ℝ) (189036480913 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2290 b2249 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2292 : Encl e2292 (35699408127 / 1000000000000 : ℝ) (35699408133 / 1000000000000 : ℝ) := by
  exact Encl.sub b2289 b2291 (by norm_num) (by norm_num)

lemma b2293 : Encl e2293 (113058867593 / 2500000000 : ℝ) (452235470373 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2249 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2294 : Encl e2294 (9431707051 / 1000000000000 : ℝ) (2357926763 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2232 b2293 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2295 : Encl e2295 (1050708043 / 40000000000 : ℝ) (13133850541 / 500000000000 : ℝ) := by
  exact Encl.sub b2292 b2294 (by norm_num) (by norm_num)

lemma b2296 : Encl e2296 (334076678719 / 1000000000000 : ℝ) (334076678743 / 1000000000000 : ℝ) := by
  exact Encl.sub b2280 b2295 (by norm_num) (by norm_num)

lemma b2297 : Encl e2297 (249310954267 / 1000000000000 : ℝ) (124655477143 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2296 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2298 : Encl e2298 (-4751936987 / 40000000000 : ℝ) (-118798424641 / 1000000000000 : ℝ) := by
  exact Encl.add b2262 b2297 (by norm_num) (by norm_num)

lemma b2299 : Encl e2299 (1903208071123 / 1000000000000 : ℝ) (951604035563 / 500000000000 : ℝ) := by
  exact Encl.add b2233 b4 (by norm_num) (by norm_num)

lemma b2300 : Encl e2300 (951604035561 / 1000000000000 : ℝ) (951604035563 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2299 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2301 : Encl e2301 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2233 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2302 : Encl e2302 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2301 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2303 : Encl e2303 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b2301 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2304 : Encl e2304 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2303 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2305 : Encl e2305 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2304 (by norm_num) (by norm_num)

lemma b2306 : Encl e2306 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2305 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2307 : Encl e2307 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2302 b2306 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2308 : Encl e2308 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2303 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2309 : Encl e2309 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b2307 b2308 (by norm_num) (by norm_num)

lemma b2310 : Encl e2310 (324349531649 / 500000000000 : ℝ) (648699063323 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2300 b2309 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2311 : Encl e2311 (5548064573 / 7812500000 : ℝ) (355076132673 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2300 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2312 : Encl e2312 (1258712117437 / 1000000000000 : ℝ) (1258712117443 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2311 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2313 : Encl e2313 (504316239973 / 1000000000000 : ℝ) (504316239977 / 1000000000000 : ℝ) := by
  exact Encl.pow b2311 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2314 : Encl e2314 (198044524323 / 500000000000 : ℝ) (7921780973 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2313 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2315 : Encl e2315 (698044524323 / 500000000000 : ℝ) (27921780973 / 20000000000 : ℝ) := by
  exact Encl.add b5 b2314 (by norm_num) (by norm_num)

lemma b2316 : Encl e2316 (1181562122211 / 1000000000000 : ℝ) (590781061107 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2315 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2317 : Encl e2317 (1487246560731 / 1000000000000 : ℝ) (1487246560743 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2312 b2316 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2318 : Encl e2318 (198044524323 / 250000000000 : ℝ) (792178097299 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2313 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2319 : Encl e2319 (86883557929 / 125000000000 : ℝ) (695068463451 / 1000000000000 : ℝ) := by
  exact Encl.sub b2317 b2318 (by norm_num) (by norm_num)

lemma b2320 : Encl e2320 (79365067741 / 125000000000 : ℝ) (158730135487 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2233 b2319 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2321 : Encl e2321 (275570427 / 20000000000 : ℝ) (2755704279 / 200000000000 : ℝ) := by
  exact Encl.sub b2310 b2320 (by norm_num) (by norm_num)

lemma b2322 : Encl e2322 (181110048099 / 200000000000 : ℝ) (1811100481 / 2000000000 : ℝ) := by
  exact Encl.pow b2300 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2323 : Encl e2323 (177487847137 / 200000000000 : ℝ) (88743923569 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2322 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2324 : Encl e2324 (11256076431 / 100000000000 : ℝ) (22512152863 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b2323 (by norm_num) (by norm_num)

lemma b2325 : Encl e2325 (188899519 / 2000000000 : ℝ) (18889951901 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b2322 (by norm_num) (by norm_num)

lemma b2326 : Encl e2326 (61465359187 / 200000000000 : ℝ) (38415849493 / 125000000000 : ℝ) := by
  exact Encl.sqrt b2325 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2327 : Encl e2327 (183128783099 / 500000000000 : ℝ) (183128783113 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2324 b2326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2328 : Encl e2328 (316871216887 / 500000000000 : ℝ) (316871216901 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2327 (by norm_num) (by norm_num)

lemma b2329 : Encl e2329 (817729497001 / 1000000000000 : ℝ) (817729497007 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2263 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2330 : Encl e2330 (182270502993 / 1000000000000 : ℝ) (182270502999 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2329 (by norm_num) (by norm_num)

lemma b2331 : Encl e2331 (17917178899 / 40000000000 : ℝ) (447929472499 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2330 b2265 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2332 : Encl e2332 (552070527501 / 1000000000000 : ℝ) (22082821101 / 40000000000 : ℝ) := by
  exact Encl.sub b5 b2331 (by norm_num) (by norm_num)

lemma b2333 : Encl e2333 (81671906249 / 1000000000000 : ℝ) (81671906301 / 1000000000000 : ℝ) := by
  exact Encl.sub b2328 b2332 (by norm_num) (by norm_num)

lemma b2334 : Encl e2334 (1125318103 / 1000000000000 : ℝ) (1125318109 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2321 b2333 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2335 : Encl e2335 (3344587401 / 250000000000 : ℝ) (6689174823 / 500000000000 : ℝ) := by
  exact Encl.sub b2319 b2309 (by norm_num) (by norm_num)

lemma b2336 : Encl e2336 (261465359187 / 200000000000 : ℝ) (163415849493 / 125000000000 : ℝ) := by
  exact Encl.add b5 b2326 (by norm_num) (by norm_num)

lemma b2337 : Encl e2337 (727900658437 / 1000000000000 : ℝ) (145580131689 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2300 b2336 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2338 : Encl e2338 (529839368553 / 1000000000000 : ℝ) (105967873713 / 200000000000 : ℝ) := by
  exact Encl.pow b2337 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2339 : Encl e2339 (1529839368553 / 1000000000000 : ℝ) (305967873713 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2338 (by norm_num) (by norm_num)

lemma b2340 : Encl e2340 (618433377283 / 500000000000 : ℝ) (309216688643 / 250000000000 : ℝ) := by
  exact Encl.sqrt b2339 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2341 : Encl e2341 (1118433377283 / 500000000000 : ℝ) (559216688643 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2340 (by norm_num) (by norm_num)

lemma b2342 : Encl e2342 (2033817663 / 6250000000 : ℝ) (65082165217 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2337 b2341 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2343 : Encl e2343 (251682745869 / 200000000000 : ℝ) (2013461967 / 1600000000 : ℝ) := by
  apply Encl.arcsin (z := e2300) (a := (2033817663 / 6250000000 : ℝ)) (b := (65082165217 / 200000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (951604035561 / 1000000000000 : ℝ) by norm_num).trans b2300.1
        exact b2300.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2300) (2033817663 / 6250000000 : ℝ) (65082165217 / 200000000000 : ℝ) from b2342) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2344 : Encl e2344 (128358200393 / 200000000000 : ℝ) (320895500991 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2343 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2345 : Encl e2345 (29142873589 / 62500000000 : ℝ) (233142988713 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2300 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2346 : Encl e2346 (143302175431 / 1000000000000 : ℝ) (35825543859 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2345 b2326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2347 : Encl e2347 (498488826529 / 1000000000000 : ℝ) (498488826551 / 1000000000000 : ℝ) := by
  exact Encl.sub b2344 b2346 (by norm_num) (by norm_num)

lemma b2348 : Encl e2348 (61465359187 / 4000000000 : ℝ) (38415849493 / 2500000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2349 : Encl e2349 (61927827193 / 1000000000000 : ℝ) (15481956799 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2300 b2348 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2350 : Encl e2350 (436560999333 / 1000000000000 : ℝ) (218280499679 / 500000000000 : ℝ) := by
  exact Encl.sub b2347 b2349 (by norm_num) (by norm_num)

lemma b2351 : Encl e2351 (15243323903 / 200000000000 : ℝ) (76216619557 / 1000000000000 : ℝ) := by
  exact Encl.sub b2350 b2280 (by norm_num) (by norm_num)

lemma b2352 : Encl e2352 (1019652581 / 1000000000000 : ℝ) (509826293 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2335 b2351 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2353 : Encl e2353 (536242671 / 250000000000 : ℝ) (428994139 / 200000000000 : ℝ) := by
  exact Encl.add b2334 b2352 (by norm_num) (by norm_num)

lemma b2354 : Encl e2354 (19069641523 / 500000000000 : ℝ) (762785661 / 20000000000 : ℝ) := by
  exact Encl.sub b2300 b2233 (by norm_num) (by norm_num)

lemma b2355 : Encl e2355 (1406011409 / 25000000000 : ℝ) (11248091331 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2353 b2354 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2356 : Encl e2356 (-12511593663 / 200000000000 : ℝ) (-31278983993 / 500000000000 : ℝ) := by
  exact Encl.add b2298 b2355 (by norm_num) (by norm_num)

lemma b2357 : Encl e2357 (343969683829 / 500000000000 : ℝ) (343969683839 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b2319 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2358 : Encl e2358 (738614416873 / 1000000000000 : ℝ) (369307208437 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2359 : Encl e2359 (8182249797 / 6250000000 : ℝ) (327289991881 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2358 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2360 : Encl e2360 (136387814203 / 250000000000 : ℝ) (109110251363 / 200000000000 : ℝ) := by
  exact Encl.pow b2358 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2361 : Encl e2361 (428474955139 / 1000000000000 : ℝ) (214237477571 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2360 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2362 : Encl e2362 (1428474955139 / 1000000000000 : ℝ) (714237477571 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2361 (by norm_num) (by norm_num)

lemma b2363 : Encl e2363 (29879706273 / 25000000000 : ℝ) (1195188250923 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2362 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2364 : Encl e2364 (782346305877 / 500000000000 : ℝ) (391173152941 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2359 b2363 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2365 : Encl e2365 (428474955139 / 500000000000 : ℝ) (214237477571 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2360 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2366 : Encl e2366 (70774270147 / 100000000000 : ℝ) (353871350743 / 500000000000 : ℝ) := by
  exact Encl.sub b2364 b2365 (by norm_num) (by norm_num)

lemma b2367 : Encl e2367 (673490810857 / 1000000000000 : ℝ) (5387926487 / 8000000000 : ℝ) := by
  exact Encl.mul_nonneg b2300 b2366 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2368 : Encl e2368 (14448556783 / 1000000000000 : ℝ) (14448556821 / 1000000000000 : ℝ) := by
  exact Encl.sub b2357 b2367 (by norm_num) (by norm_num)

lemma b2369 : Encl e2369 (86257566173 / 1000000000000 : ℝ) (43128783127 / 500000000000 : ℝ) := by
  exact Encl.sub b165 b2328 (by norm_num) (by norm_num)

lemma b2370 : Encl e2370 (623148671 / 500000000000 : ℝ) (311574337 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2368 b2369 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2371 : Encl e2371 (12674238019 / 1000000000000 : ℝ) (6337119027 / 500000000000 : ℝ) := by
  exact Encl.sub b2366 b2319 (by norm_num) (by norm_num)

lemma b2372 : Encl e2372 (41795885077 / 500000000000 : ℝ) (8359177031 / 100000000000 : ℝ) := by
  exact Encl.sub b183 b2350 (by norm_num) (by norm_num)

lemma b2373 : Encl e2373 (1059461991 / 1000000000000 : ℝ) (1059461997 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2371 b2372 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2374 : Encl e2374 (2305759333 / 1000000000000 : ℝ) (461151869 / 200000000000 : ℝ) := by
  exact Encl.add b2370 b2373 (by norm_num) (by norm_num)

lemma b2375 : Encl e2375 (38139283047 / 1000000000000 : ℝ) (762785661 / 20000000000 : ℝ) := by
  exact Encl.sub b4 b2300 (by norm_num) (by norm_num)

lemma b2376 : Encl e2376 (3022814207 / 50000000000 : ℝ) (60456284461 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2374 b2375 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2377 : Encl e2377 (-84067367 / 40000000000 : ℝ) (-84067341 / 40000000000 : ℝ) := by
  exact Encl.add b2356 b2376 (by norm_num) (by norm_num)

lemma b2378 : Encl e2378 (716417910447 / 1000000000000 : ℝ) (44776119403 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2379 : Encl e2379 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2378 (by norm_num) (by norm_num)

lemma b2380 : Encl e2380 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b2379 b5 (by norm_num) (by norm_num)

lemma b2381 : Encl e2381 (67 / 25 : ℝ) (67 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2382 : Encl e2382 (76223092127 / 40000000000 : ℝ) (1905577303179 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2381 b2242 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2383 : Encl e2383 (75820511811 / 125000000000 : ℝ) (60656409449 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2382 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2384 : Encl e2384 (18015888019 / 62500000000 : ℝ) (288254208307 / 1000000000000 : ℝ) := by
  exact Encl.add b2380 b2383 (by norm_num) (by norm_num)

lemma b2385 : Encl e2385 (4489 / 1250 : ℝ) (4489 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b2236 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2386 : Encl e2386 (510694717251 / 200000000000 : ℝ) (2553473586259 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2385 b2242 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2387 : Encl e2387 (1423766559961 / 250000000000 : ℝ) (5695066239849 / 1000000000000 : ℝ) := by
  exact Encl.add b0 b2386 (by norm_num) (by norm_num)

lemma b2388 : Encl e2388 (2386433791213 / 1000000000000 : ℝ) (477286758243 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2387 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2389 : Encl e2389 (151925093693 / 100000000000 : ℝ) (303850187387 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2388 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2390 : Encl e2390 (300763 / 125000 : ℝ) (300763 / 125000 : ℝ) := by
  exact Encl.pow b2231 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2391 : Encl e2391 (20151121 / 62500000 : ℝ) (20151121 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2390 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2392 : Encl e2392 (20151121 / 62500000 : ℝ) (20151121 / 62500000 : ℝ) := by
  exact Encl.min b2391 b941 (by norm_num) (by norm_num)

lemma b2393 : Encl e2393 (18015888019 / 31250000000 : ℝ) (288254208307 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2384 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2394 : Encl e2394 (60453363 / 31250000 : ℝ) (60453363 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b2392 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2395 : Encl e2395 (1154061704681 / 500000000000 : ℝ) (1154061704689 / 500000000000 : ℝ) := by
  exact Encl.pow b2389 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2396 : Encl e2396 (2232541157039 / 500000000000 : ℝ) (446508231411 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b2394 b2395 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2397 : Encl e2397 (40221211483 / 31250000000 : ℝ) (32176969187 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b2396 b2384 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2398 : Encl e2398 (4596709883771 / 1000000000000 : ℝ) (2298354941929 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2397 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2399 : Encl e2399 (5596709883771 / 1000000000000 : ℝ) (2798354941929 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2398 (by norm_num) (by norm_num)

lemma b2400 : Encl e2400 (2365736647171 / 1000000000000 : ℝ) (2365736647191 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2399 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2401 : Encl e2401 (3365736647171 / 1000000000000 : ℝ) (3365736647191 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2400 (by norm_num) (by norm_num)

lemma b2402 : Encl e2402 (171287440771 / 1000000000000 : ℝ) (6851497631 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b2393 b2401 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2403 : Encl e2403 (597182501 / 200000000000 : ℝ) (1492956253 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2392 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2404 : Encl e2404 (116966767529 / 1000000000000 : ℝ) (7310422971 / 62500000000 : ℝ) := by
  exact Encl.sub b2384 b2402 (by norm_num) (by norm_num)

lemma b2405 : Encl e2405 (15397952331 / 200000000000 : ℝ) (76989761661 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2404 b2389 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2406 : Encl e2406 (5927423399 / 1000000000000 : ℝ) (5927423401 / 1000000000000 : ℝ) := by
  exact Encl.pow b2405 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2407 : Encl e2407 (1659678551 / 1000000000000 : ℝ) (1659678553 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2406 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2408 : Encl e2408 (201018743 / 40000000000 : ℝ) (5025468577 / 1000000000000 : ℝ) := by
  exact Encl.pow b2402 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2409 : Encl e2409 (324060241 / 200000000000 : ℝ) (1620301207 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2392 b2408 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2410 : Encl e2410 (819994939 / 250000000000 : ℝ) (40999747 / 12500000000 : ℝ) := by
  exact Encl.add b2407 b2409 (by norm_num) (by norm_num)

lemma b2411 : Encl e2411 (597182501 / 200000000000 : ℝ) (1492956253 / 500000000000 : ℝ) := by
  exact Encl.min b2403 b2410 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_134 : Encl (twoChordBaseline (67 / 50 : ℝ)) (-84067367 / 40000000000 : ℝ) (-84067341 / 40000000000 : ℝ) := by
  exact b2377

lemma gain_enclosure_134 : Encl (gain (67 / 50 : ℝ)) (597182501 / 200000000000 : ℝ) (1492956253 / 500000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2411

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

lemma baseline_lower_134 : (-84067367 / 40000000000 : ℝ) ≤ baseline (67 / 50 : ℝ) :=
  (baseline_enclosure_134).1.trans (twoChordBaseline_le_of_range (h := (67 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_134_oai : (88422833 / 100000000000 : ℝ) ≤ baseline (67 / 50 : ℝ) + gain (67 / 50 : ℝ) := by
  have hb := baseline_lower_134
  have hg := (gain_enclosure_134).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_134_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_134_oai

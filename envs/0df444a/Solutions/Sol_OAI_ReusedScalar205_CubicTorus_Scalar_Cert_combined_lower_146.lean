-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_146
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:44:39.899588+00:00
-- url     : https://prove2.me/submissions/9a050981-f101-44c9-824a-47f88bbdaf3a

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures2701To2920
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
lemma b2774 : Encl e2774 (73 / 50 : ℝ) (73 / 50 : ℝ) := by
  exact Encl.exact (73 / 50 : ℝ)

lemma b2775 : Encl e2775 (116183108457 / 250000000000 : ℝ) (464732433829 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2774 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2776 : Encl e2776 (3577 / 2500 : ℝ) (3577 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2774 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2777 : Encl e2777 (455437785151 / 1000000000000 : ℝ) (7116215393 / 15625000000 : ℝ) := by
  exact Encl.div_nonneg b2776 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2778 : Encl e2778 (5329 / 2500 : ℝ) (5329 / 2500 : ℝ) := by
  exact Encl.pow b2774 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2779 : Encl e2779 (5329 / 625 : ℝ) (5329 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b2778 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2780 : Encl e2780 (2714037413557 / 1000000000000 : ℝ) (1357018706779 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2779 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2781 : Encl e2781 (3714037413557 / 1000000000000 : ℝ) (1857018706779 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2780 (by norm_num) (by norm_num)

lemma b2782 : Encl e2782 (1927183803781 / 1000000000000 : ℝ) (963591901891 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2781 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2783 : Encl e2783 (2927183803781 / 1000000000000 : ℝ) (1463591901891 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2782 (by norm_num) (by norm_num)

lemma b2784 : Encl e2784 (68325056917 / 100000000000 : ℝ) (683250569171 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2783 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2785 : Encl e2785 (191310159367 / 1000000000000 : ℝ) (23913769921 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2784 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2786 : Encl e2786 (323373972259 / 500000000000 : ℝ) (16168698613 / 25000000000 : ℝ) := by
  exact Encl.add b2777 b2785 (by norm_num) (by norm_num)

lemma b2787 : Encl e2787 (-176626027741 / 500000000000 : ℝ) (-8831301387 / 25000000000 : ℝ) := by
  exact Encl.sub b2786 b5 (by norm_num) (by norm_num)

lemma b2788 : Encl e2788 (294763806867 / 200000000000 : ℝ) (46056844823 / 31250000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2778 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2789 : Encl e2789 (215976235051 / 1000000000000 : ℝ) (215976235053 / 1000000000000 : ℝ) := by
  exact Encl.pow b2775 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2790 : Encl e2790 (784023764947 / 1000000000000 : ℝ) (784023764949 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2789 (by norm_num) (by norm_num)

lemma b2791 : Encl e2791 (885451164631 / 1000000000000 : ℝ) (885451164633 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2790 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2792 : Encl e2792 (-218784497967 / 1000000000000 : ℝ) (-54696124491 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b2791 (by norm_num) (by norm_num)

lemma b2793 : Encl e2793 (69421475577 / 100000000000 : ℝ) (27768590231 / 40000000000 : ℝ) := by
  exact Encl.pow b2791 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2794 : Encl e2794 (23140491859 / 100000000000 : ℝ) (3615701853 / 15625000000 : ℝ) := by
  exact Encl.div_nonneg b2793 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2795 : Encl e2795 (12620420623 / 1000000000000 : ℝ) (3155105157 / 250000000000 : ℝ) := by
  exact Encl.add b2792 b2794 (by norm_num) (by norm_num)

lemma b2796 : Encl e2796 (1236801221 / 100000000000 : ℝ) (1546001527 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2795 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2797 : Encl e2797 (48783319437 / 200000000000 : ℝ) (243916597189 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2789 b2791 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2798 : Encl e2798 (-351216680563 / 200000000000 : ℝ) (-1756083402811 / 1000000000000 : ℝ) := by
  exact Encl.sub b2797 b23 (by norm_num) (by norm_num)

lemma b2799 : Encl e2799 (885451164631 / 500000000000 : ℝ) (885451164633 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2791 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2800 : Encl e2800 (14818926447 / 1000000000000 : ℝ) (2963785291 / 200000000000 : ℝ) := by
  exact Encl.add b2798 b2799 (by norm_num) (by norm_num)

lemma b2801 : Encl e2801 (9261829 / 31250000000 : ℝ) (29637853 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2800 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2802 : Encl e2802 (150895421 / 12500000000 : ℝ) (1508954211 / 125000000000 : ℝ) := by
  exact Encl.sub b2796 b2801 (by norm_num) (by norm_num)

lemma b2803 : Encl e2803 (17791403493 / 1000000000000 : ℝ) (3558280701 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2788 b2802 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2804 : Encl e2804 (-335460651989 / 1000000000000 : ℝ) (-13418426079 / 40000000000 : ℝ) := by
  exact Encl.add b2787 b2803 (by norm_num) (by norm_num)

lemma b2805 : Encl e2805 (1885451164631 / 1000000000000 : ℝ) (1885451164633 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2791 (by norm_num) (by norm_num)

lemma b2806 : Encl e2806 (61620852683 / 250000000000 : ℝ) (123241705367 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2775 b2805 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2807 : Encl e2807 (30377035883 / 500000000000 : ℝ) (7594258971 / 125000000000 : ℝ) := by
  exact Encl.pow b2806 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2808 : Encl e2808 (530377035883 / 500000000000 : ℝ) (132594258971 / 125000000000 : ℝ) := by
  exact Encl.add b5 b2807 (by norm_num) (by norm_num)

lemma b2809 : Encl e2809 (205985831723 / 200000000000 : ℝ) (1029929158617 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2808 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2810 : Encl e2810 (405985831723 / 200000000000 : ℝ) (2029929158617 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2809 (by norm_num) (by norm_num)

lemma b2811 : Encl e2811 (121424636759 / 1000000000000 : ℝ) (121424636761 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2806 b2810 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2812 : Encl e2812 (96666481327 / 200000000000 : ℝ) (120833101661 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e2775) (a := (121424636759 / 1000000000000 : ℝ)) (b := (121424636761 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (116183108457 / 250000000000 : ℝ) by norm_num).trans b2775.1
        exact b2775.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2775) (121424636759 / 1000000000000 : ℝ) (121424636761 / 1000000000000 : ℝ) from b2811) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2813 : Encl e2813 (246499527383 / 1000000000000 : ℝ) (246499527389 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2812 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2814 : Encl e2814 (9108755703 / 40000000000 : ℝ) (227718892577 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2775 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2815 : Encl e2815 (201633958639 / 1000000000000 : ℝ) (100816979321 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2814 b2791 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2816 : Encl e2816 (44865568741 / 1000000000000 : ℝ) (7178491 / 160000000 : ℝ) := by
  exact Encl.sub b2813 b2815 (by norm_num) (by norm_num)

lemma b2817 : Encl e2817 (885451164631 / 20000000000 : ℝ) (885451164633 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2791 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2818 : Encl e2818 (2624269143 / 250000000000 : ℝ) (10497076573 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2775 b2817 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2819 : Encl e2819 (4296061521 / 125000000000 : ℝ) (17184246089 / 500000000000 : ℝ) := by
  exact Encl.sub b2816 b2818 (by norm_num) (by norm_num)

lemma b2820 : Encl e2820 (242892138667 / 500000000000 : ℝ) (19431371099 / 40000000000 : ℝ) := by
  exact Encl.sub b183 b2819 (by norm_num) (by norm_num)

lemma b2821 : Encl e2821 (166364478539 / 500000000000 : ℝ) (13309158287 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b2820 b2774 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2822 : Encl e2822 (-2731694911 / 1000000000000 : ℝ) (-6829237 / 2500000000 : ℝ) := by
  exact Encl.add b2804 b2821 (by norm_num) (by norm_num)

lemma b2823 : Encl e2823 (26301369863 / 40000000000 : ℝ) (41095890411 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2774 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2824 : Encl e2824 (26301369863 / 40000000000 : ℝ) (41095890411 / 62500000000 : ℝ) := by
  exact Encl.min b7 b2823 (by norm_num) (by norm_num)

lemma b2825 : Encl e2825 (-13698630137 / 40000000000 : ℝ) (-21404109589 / 62500000000 : ℝ) := by
  exact Encl.sub b2824 b5 (by norm_num) (by norm_num)

lemma b2826 : Encl e2826 (73 / 25 : ℝ) (73 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b2774 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2827 : Encl e2827 (249386457747 / 125000000000 : ℝ) (99754583099 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b2826 b2784 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2828 : Encl e2828 (635057399849 / 1000000000000 : ℝ) (158764349963 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2827 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2829 : Encl e2829 (36573955803 / 125000000000 : ℝ) (73147911607 / 250000000000 : ℝ) := by
  exact Encl.add b2825 b2828 (by norm_num) (by norm_num)

lemma b2830 : Encl e2830 (5329 / 1250 : ℝ) (5329 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b2778 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2831 : Encl e2831 (582566765297 / 200000000000 : ℝ) (291283382649 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b2830 b2784 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2832 : Encl e2832 (3027213240037 / 500000000000 : ℝ) (75680331001 / 12500000000 : ℝ) := by
  exact Encl.add b0 b2831 (by norm_num) (by norm_num)

lemma b2833 : Encl e2833 (492114884151 / 200000000000 : ℝ) (2460574420757 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2832 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2834 : Encl e2834 (1566450327633 / 1000000000000 : ℝ) (1566450327637 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2833 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2835 : Encl e2835 (389017 / 125000 : ℝ) (389017 / 125000 : ℝ) := by
  exact Encl.pow b2774 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2836 : Encl e2836 (26064139 / 62500000 : ℝ) (26064139 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2835 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2837 : Encl e2837 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b2836 b941 (by norm_num) (by norm_num)

lemma b2838 : Encl e2838 (36573955803 / 62500000000 : ℝ) (73147911607 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2829 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2839 : Encl e2839 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b2837 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2840 : Encl e2840 (2453766628941 / 1000000000000 : ℝ) (490753325791 / 200000000000 : ℝ) := by
  exact Encl.pow b2834 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2841 : Encl e2841 (331258494907 / 62500000000 : ℝ) (5300135918543 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2839 b2840 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2842 : Encl e2842 (387693873667 / 250000000000 : ℝ) (1550775494699 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2841 b2829 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2843 : Encl e2843 (692310488691 / 125000000000 : ℝ) (138462097741 / 25000000000 : ℝ) := by
  exact Encl.div_nonneg b2842 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2844 : Encl e2844 (817310488691 / 125000000000 : ℝ) (163462097741 / 25000000000 : ℝ) := by
  exact Encl.add b5 b2843 (by norm_num) (by norm_num)

lemma b2845 : Encl e2845 (319630741773 / 125000000000 : ℝ) (2557045934207 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2844 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2846 : Encl e2846 (444630741773 / 125000000000 : ℝ) (3557045934207 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2845 (by norm_num) (by norm_num)

lemma b2847 : Encl e2847 (164513842011 / 1000000000000 : ℝ) (32902768403 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2838 b2846 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2848 : Encl e2848 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b2837 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2849 : Encl e2849 (128077804409 / 1000000000000 : ℝ) (128077804417 / 1000000000000 : ℝ) := by
  exact Encl.sub b2829 b2847 (by norm_num) (by norm_num)

lemma b2850 : Encl e2850 (81763080609 / 1000000000000 : ℝ) (16352616123 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2849 b2834 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2851 : Encl e2851 (133704027 / 20000000000 : ℝ) (835650169 / 125000000000 : ℝ) := by
  exact Encl.pow b2850 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2852 : Encl e2852 (935928189 / 500000000000 : ℝ) (1871856379 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2851 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2853 : Encl e2853 (1113133731 / 250000000000 : ℝ) (178101397 / 40000000000 : ℝ) := by
  exact Encl.pow b2847 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2854 : Encl e2854 (400728143 / 250000000000 : ℝ) (1602912573 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2837 b2853 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2855 : Encl e2855 (69495379 / 20000000000 : ℝ) (434346119 / 125000000000 : ℝ) := by
  exact Encl.add b2852 b2854 (by norm_num) (by norm_num)

lemma b2856 : Encl e2856 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.min b2848 b2855 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_146 : Encl (linearBaseline (73 / 50 : ℝ)) (-2731694911 / 1000000000000 : ℝ) (-6829237 / 2500000000 : ℝ) := by
  exact b2822

lemma gain_enclosure_146 : Encl (gain (73 / 50 : ℝ)) (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2856

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

lemma baseline_lower_146 : (-2731694911 / 1000000000000 : ℝ) ≤ baseline (73 / 50 : ℝ) :=
  (baseline_enclosure_146).1.trans ((linearBaseline_eq_of_range (h := (73 / 50 : ℝ)) (by norm_num) (by norm_num)).le)

lemma combined_lower_146_oai : (602265089 / 1000000000000 : ℝ) ≤ baseline (73 / 50 : ℝ) + gain (73 / 50 : ℝ) := by
  have hb := baseline_lower_146
  have hg := (gain_enclosure_146).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_146_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_146_oai

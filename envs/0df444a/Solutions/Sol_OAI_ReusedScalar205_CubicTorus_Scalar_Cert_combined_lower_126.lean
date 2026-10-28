-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_126
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:41:17.822212+00:00
-- url     : https://prove2.me/submissions/d7336745-d749-4f4f-9da5-aa08bce84980

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures1822To2041
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
lemma b1869 : Encl e1869 (63 / 50 : ℝ) (63 / 50 : ℝ) := by
  exact Encl.exact (63 / 50 : ℝ)

lemma b1870 : Encl e1870 (401070456591 / 1000000000000 : ℝ) (25066903537 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b1869 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1871 : Encl e1871 (53683096463 / 62500000000 : ℝ) (85892954341 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1869 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1872 : Encl e1872 (3087 / 2500 : ℝ) (3087 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1873 : Encl e1873 (393049047459 / 1000000000000 : ℝ) (19652452373 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b1872 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1874 : Encl e1874 (3969 / 2500 : ℝ) (3969 / 2500 : ℝ) := by
  exact Encl.pow b1869 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1875 : Encl e1875 (3969 / 625 : ℝ) (3969 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b1874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1876 : Encl e1876 (2021395101221 / 1000000000000 : ℝ) (1010697550611 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1875 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1877 : Encl e1877 (3021395101221 / 1000000000000 : ℝ) (1510697550611 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1876 (by norm_num) (by norm_num)

lemma b1878 : Encl e1878 (1738216068623 / 1000000000000 : ℝ) (108638504289 / 62500000000 : ℝ) := by
  exact Encl.sqrt b1877 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1879 : Encl e1879 (2738216068623 / 1000000000000 : ℝ) (171138504289 / 62500000000 : ℝ) := by
  exact Encl.add b5 b1878 (by norm_num) (by norm_num)

lemma b1880 : Encl e1880 (365201275187 / 500000000000 : ℝ) (5843220403 / 8000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b1879 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1881 : Encl e1881 (25564089263 / 125000000000 : ℝ) (40902542821 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1880 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1882 : Encl e1882 (597561761563 / 1000000000000 : ℝ) (119512352313 / 200000000000 : ℝ) := by
  exact Encl.add b1873 b1881 (by norm_num) (by norm_num)

lemma b1883 : Encl e1883 (-402438238437 / 1000000000000 : ℝ) (-80487647687 / 200000000000 : ℝ) := by
  exact Encl.sub b1882 b5 (by norm_num) (by norm_num)

lemma b1884 : Encl e1884 (1978831351467 / 1000000000000 : ℝ) (494707837867 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b1874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1885 : Encl e1885 (3217150223 / 20000000000 : ℝ) (160857511151 / 1000000000000 : ℝ) := by
  exact Encl.pow b1870 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1886 : Encl e1886 (839142488849 / 1000000000000 : ℝ) (16782849777 / 20000000000 : ℝ) := by
  exact Encl.sub b5 b1885 (by norm_num) (by norm_num)

lemma b1887 : Encl e1887 (916047208853 / 1000000000000 : ℝ) (183209441771 / 200000000000 : ℝ) := by
  exact Encl.sqrt b1886 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1888 : Encl e1888 (-249380542189 / 1000000000000 : ℝ) (-124690271093 / 500000000000 : ℝ) := by
  exact Encl.sub b29 b1887 (by norm_num) (by norm_num)

lemma b1889 : Encl e1889 (384347067369 / 500000000000 : ℝ) (96086766843 / 125000000000 : ℝ) := by
  exact Encl.pow b1887 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1890 : Encl e1890 (128115689123 / 500000000000 : ℝ) (32028922281 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1889 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1891 : Encl e1891 (6850836057 / 1000000000000 : ℝ) (3425418031 / 500000000000 : ℝ) := by
  exact Encl.add b1888 b1890 (by norm_num) (by norm_num)

lemma b1892 : Encl e1892 (1342763867 / 200000000000 : ℝ) (6713819341 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1891 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1893 : Encl e1893 (87799793283 / 500000000000 : ℝ) (21949948321 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1885 b1887 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1894 : Encl e1894 (-912200206717 / 500000000000 : ℝ) (-228050051679 / 125000000000 : ℝ) := by
  exact Encl.sub b1893 b23 (by norm_num) (by norm_num)

lemma b1895 : Encl e1895 (916047208853 / 500000000000 : ℝ) (183209441771 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1887 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1896 : Encl e1896 (480875267 / 62500000000 : ℝ) (3847002139 / 500000000000 : ℝ) := by
  exact Encl.add b1894 b1895 (by norm_num) (by norm_num)

lemma b1897 : Encl e1897 (30776017 / 200000000000 : ℝ) (76940043 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1896 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1898 : Encl e1898 (6559939249 / 1000000000000 : ℝ) (819992407 / 125000000000 : ℝ) := by
  exact Encl.sub b1892 b1897 (by norm_num) (by norm_num)

lemma b1899 : Encl e1899 (12981013449 / 1000000000000 : ℝ) (1622626683 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1884 b1898 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1900 : Encl e1900 (-97364306247 / 250000000000 : ℝ) (-389457224971 / 1000000000000 : ℝ) := by
  exact Encl.add b1883 b1899 (by norm_num) (by norm_num)

lemma b1901 : Encl e1901 (737759960539 / 1000000000000 : ℝ) (737759960543 / 1000000000000 : ℝ) := by
  exact Encl.pow b1871 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1902 : Encl e1902 (262240039457 / 1000000000000 : ℝ) (262240039461 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1901 (by norm_num) (by norm_num)

lemma b1903 : Encl e1903 (512093779943 / 1000000000000 : ℝ) (128023444987 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1902 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1904 : Encl e1904 (1512093779943 / 1000000000000 : ℝ) (378023444987 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1903 (by norm_num) (by norm_num)

lemma b1905 : Encl e1905 (568039862869 / 1000000000000 : ℝ) (284019931437 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1871 b1904 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1906 : Encl e1906 (20166830363 / 62500000000 : ℝ) (161334642907 / 500000000000 : ℝ) := by
  exact Encl.pow b1905 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1907 : Encl e1907 (82666830363 / 62500000000 : ℝ) (661334642907 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1906 (by norm_num) (by norm_num)

lemma b1908 : Encl e1908 (115007360017 / 100000000000 : ℝ) (1150073600173 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1907 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1909 : Encl e1909 (215007360017 / 100000000000 : ℝ) (2150073600173 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1908 (by norm_num) (by norm_num)

lemma b1910 : Encl e1910 (26419554327 / 100000000000 : ℝ) (132097771637 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1905 b1909 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1911 : Encl e1911 (516587820431 / 500000000000 : ℝ) (516587820439 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e1871) (a := (26419554327 / 100000000000 : ℝ)) (b := (132097771637 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (53683096463 / 62500000000 : ℝ) by norm_num).trans b1871.1
        exact b1871.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1871) (26419554327 / 100000000000 : ℝ) (132097771637 / 500000000000 : ℝ) from b1910) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1912 : Encl e1912 (526919576839 / 1000000000000 : ℝ) (32932473553 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1911 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1913 : Encl e1913 (420875476269 / 1000000000000 : ℝ) (420875476271 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1871 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1914 : Encl e1914 (215527713527 / 1000000000000 : ℝ) (53881928383 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1913 b1903 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1915 : Encl e1915 (311391863307 / 1000000000000 : ℝ) (311391863321 / 1000000000000 : ℝ) := by
  exact Encl.sub b1912 b1914 (by norm_num) (by norm_num)

lemma b1916 : Encl e1916 (512093779943 / 20000000000 : ℝ) (128023444987 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1903 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1917 : Encl e1917 (33545790909 / 1000000000000 : ℝ) (3354579091 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1871 b1916 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1918 : Encl e1918 (277846072397 / 1000000000000 : ℝ) (69461518103 / 250000000000 : ℝ) := by
  exact Encl.sub b1915 b1917 (by norm_num) (by norm_num)

lemma b1919 : Encl e1919 (1916047208853 / 1000000000000 : ℝ) (383209441771 / 200000000000 : ℝ) := by
  exact Encl.add b5 b1887 (by norm_num) (by norm_num)

lemma b1920 : Encl e1920 (6541306347 / 31250000000 : ℝ) (104660901553 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1870 b1919 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1921 : Encl e1921 (21907808627 / 500000000000 : ℝ) (5476952157 / 125000000000 : ℝ) := by
  exact Encl.pow b1920 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1922 : Encl e1922 (521907808627 / 500000000000 : ℝ) (130476952157 / 125000000000 : ℝ) := by
  exact Encl.add b5 b1921 (by norm_num) (by norm_num)

lemma b1923 : Encl e1923 (6385455939 / 6250000000 : ℝ) (510836475121 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1922 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1924 : Encl e1924 (12635455939 / 6250000000 : ℝ) (1010836475121 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1923 (by norm_num) (by norm_num)

lemma b1925 : Encl e1925 (51769452393 / 500000000000 : ℝ) (25884726197 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1920 b1924 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1926 : Encl e1926 (51585638507 / 125000000000 : ℝ) (82537021613 / 200000000000 : ℝ) := by
  apply Encl.arcsin (z := e1870) (a := (51769452393 / 500000000000 : ℝ)) (b := (25884726197 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (401070456591 / 1000000000000 : ℝ) by norm_num).trans b1870.1
        exact b1870.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1870) (51769452393 / 500000000000 : ℝ) (25884726197 / 250000000000 : ℝ) from b1925) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1927 : Encl e1927 (52617351277 / 250000000000 : ℝ) (105234702557 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1926 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1928 : Encl e1928 (196524523729 / 1000000000000 : ℝ) (196524523731 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1870 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1929 : Encl e1929 (180025741433 / 1000000000000 : ℝ) (45006435359 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1928 b1887 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1930 : Encl e1930 (3805457959 / 125000000000 : ℝ) (30443663681 / 1000000000000 : ℝ) := by
  exact Encl.sub b1927 b1929 (by norm_num) (by norm_num)

lemma b1931 : Encl e1931 (916047208853 / 20000000000 : ℝ) (183209441771 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1887 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1932 : Encl e1932 (8756545573 / 1000000000000 : ℝ) (4378272787 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1870 b1931 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1933 : Encl e1933 (10843559049 / 500000000000 : ℝ) (5421779527 / 250000000000 : ℝ) := by
  exact Encl.sub b1930 b1932 (by norm_num) (by norm_num)

lemma b1934 : Encl e1934 (256158954289 / 1000000000000 : ℝ) (128079477157 / 500000000000 : ℝ) := by
  exact Encl.sub b1918 b1933 (by norm_num) (by norm_num)

lemma b1935 : Encl e1935 (50825189343 / 250000000000 : ℝ) (203300757393 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1934 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1936 : Encl e1936 (-5817389613 / 31250000000 : ℝ) (-93078233789 / 500000000000 : ℝ) := by
  exact Encl.add b1900 b1935 (by norm_num) (by norm_num)

lemma b1937 : Encl e1937 (924336431009 / 500000000000 : ℝ) (1848672862021 / 1000000000000 : ℝ) := by
  exact Encl.add b1871 b4 (by norm_num) (by norm_num)

lemma b1938 : Encl e1938 (924336431009 / 1000000000000 : ℝ) (924336431011 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1937 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1939 : Encl e1939 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1871 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1940 : Encl e1940 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1939 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1941 : Encl e1941 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1939 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1942 : Encl e1942 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1941 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1943 : Encl e1943 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1942 (by norm_num) (by norm_num)

lemma b1944 : Encl e1944 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1943 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1945 : Encl e1945 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1940 b1944 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1946 : Encl e1946 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1941 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1947 : Encl e1947 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1945 b1946 (by norm_num) (by norm_num)

lemma b1948 : Encl e1948 (4922742241 / 7812500000 : ℝ) (78763875859 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1938 b1947 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1949 : Encl e1949 (73360034207 / 100000000000 : ℝ) (733600342073 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1938 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1950 : Encl e1950 (1300272751327 / 1000000000000 : ℝ) (650136375667 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1949 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1951 : Encl e1951 (107633892377 / 200000000000 : ℝ) (53816946189 / 100000000000 : ℝ) := by
  exact Encl.pow b1949 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1952 : Encl e1952 (5283466337 / 12500000000 : ℝ) (211338653483 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1951 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1953 : Encl e1953 (17783466337 / 12500000000 : ℝ) (711338653483 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1952 (by norm_num) (by norm_num)

lemma b1954 : Encl e1954 (238552074563 / 200000000000 : ℝ) (1192760372819 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1953 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1955 : Encl e1955 (1550913811633 / 1000000000000 : ℝ) (24233028307 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b1950 b1954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1956 : Encl e1956 (845354613921 / 1000000000000 : ℝ) (845354613931 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1951 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1957 : Encl e1957 (352779598851 / 500000000000 : ℝ) (705559197727 / 1000000000000 : ℝ) := by
  exact Encl.sub b1955 b1956 (by norm_num) (by norm_num)

lemma b1958 : Encl e1958 (606025639529 / 1000000000000 : ℝ) (606025639553 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1871 b1957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1959 : Encl e1959 (4817073459 / 200000000000 : ℝ) (24085367343 / 1000000000000 : ℝ) := by
  exact Encl.sub b1948 b1958 (by norm_num) (by norm_num)

lemma b1960 : Encl e1960 (85439783769 / 100000000000 : ℝ) (170879567539 / 200000000000 : ℝ) := by
  exact Encl.pow b1938 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1961 : Encl e1961 (104663735117 / 125000000000 : ℝ) (418654940471 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1960 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1962 : Encl e1962 (81345059529 / 500000000000 : ℝ) (20336264883 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b1961 (by norm_num) (by norm_num)

lemma b1963 : Encl e1963 (29120432461 / 200000000000 : ℝ) (14560216231 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b1960 (by norm_num) (by norm_num)

lemma b1964 : Encl e1964 (76315702789 / 200000000000 : ℝ) (381578513953 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1963 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1965 : Encl e1965 (213180398147 / 500000000000 : ℝ) (2664754977 / 6250000000 : ℝ) := by
  exact Encl.div_nonneg b1962 b1964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1966 : Encl e1966 (3585245023 / 6250000000 : ℝ) (286819601853 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b1965 (by norm_num) (by norm_num)

lemma b1967 : Encl e1967 (45187797583 / 62500000000 : ℝ) (723004761333 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1901 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1968 : Encl e1968 (276995238667 / 1000000000000 : ℝ) (17312202417 / 62500000000 : ℝ) := by
  exact Encl.sub b5 b1967 (by norm_num) (by norm_num)

lemma b1969 : Encl e1969 (270453625403 / 500000000000 : ℝ) (270453625411 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1968 b1903 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1970 : Encl e1970 (229546374589 / 500000000000 : ℝ) (229546374597 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b1969 (by norm_num) (by norm_num)

lemma b1971 : Encl e1971 (57273227243 / 500000000000 : ℝ) (27965443 / 244140625 : ℝ) := by
  exact Encl.sub b1966 b1970 (by norm_num) (by norm_num)

lemma b1972 : Encl e1972 (689723357 / 250000000000 : ℝ) (689723359 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1959 b1971 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1973 : Encl e1973 (11934541937 / 500000000000 : ℝ) (11934541961 / 500000000000 : ℝ) := by
  exact Encl.sub b1957 b1947 (by norm_num) (by norm_num)

lemma b1974 : Encl e1974 (276315702789 / 200000000000 : ℝ) (1381578513953 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1964 (by norm_num) (by norm_num)

lemma b1975 : Encl e1975 (334521860927 / 500000000000 : ℝ) (33452186093 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b1938 b1974 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1976 : Encl e1976 (55952437719 / 125000000000 : ℝ) (447619501761 / 1000000000000 : ℝ) := by
  exact Encl.pow b1975 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1977 : Encl e1977 (180952437719 / 125000000000 : ℝ) (1447619501761 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1976 (by norm_num) (by norm_num)

lemma b1978 : Encl e1978 (1203170603759 / 1000000000000 : ℝ) (300792650941 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1977 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1979 : Encl e1979 (2203170603759 / 1000000000000 : ℝ) (550792650941 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1978 (by norm_num) (by norm_num)

lemma b1980 : Encl e1980 (151836566971 / 500000000000 : ℝ) (151836566973 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1975 b1979 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1981 : Encl e1981 (1179292904367 / 1000000000000 : ℝ) (589646452193 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e1938) (a := (151836566971 / 500000000000 : ℝ)) (b := (151836566973 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (924336431009 / 1000000000000 : ℝ) by norm_num).trans b1938.1
        exact b1938.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1938) (151836566971 / 500000000000 : ℝ) (151836566973 / 500000000000 : ℝ) from b1980) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1982 : Encl e1982 (601439381227 / 1000000000000 : ℝ) (601439381237 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1981 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1983 : Encl e1983 (226462425597 / 500000000000 : ℝ) (113231212799 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1938 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1984 : Encl e1984 (172826391647 / 1000000000000 : ℝ) (43206597913 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1983 b1964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1985 : Encl e1985 (17144519583 / 40000000000 : ℝ) (42861298959 / 100000000000 : ℝ) := by
  exact Encl.sub b1982 b1984 (by norm_num) (by norm_num)

lemma b1986 : Encl e1986 (76315702789 / 4000000000 : ℝ) (381578513953 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1987 : Encl e1987 (24224016741 / 500000000000 : ℝ) (12112008371 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1938 b1986 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1988 : Encl e1988 (380164956091 / 1000000000000 : ℝ) (95041239027 / 250000000000 : ℝ) := by
  exact Encl.sub b1985 b1987 (by norm_num) (by norm_num)

lemma b1989 : Encl e1989 (102318883679 / 1000000000000 : ℝ) (102318883711 / 1000000000000 : ℝ) := by
  exact Encl.sub b1988 b1918 (by norm_num) (by norm_num)

lemma b1990 : Encl e1990 (76320563 / 31250000000 : ℝ) (2442258023 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1973 b1989 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1991 : Encl e1991 (1300287861 / 250000000000 : ℝ) (5201151459 / 1000000000000 : ℝ) := by
  exact Encl.add b1972 b1990 (by norm_num) (by norm_num)

lemma b1992 : Encl e1992 (65406887599 / 1000000000000 : ℝ) (65406887603 / 1000000000000 : ℝ) := by
  exact Encl.sub b1938 b1871 (by norm_num) (by norm_num)

lemma b1993 : Encl e1993 (4969995931 / 62500000000 : ℝ) (19879983783 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1991 b1992 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1994 : Encl e1994 (-1332956659 / 12500000000 : ℝ) (-53318266223 / 500000000000 : ℝ) := by
  exact Encl.add b1936 b1993 (by norm_num) (by norm_num)

lemma b1995 : Encl e1995 (698322501809 / 1000000000000 : ℝ) (139664500367 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1996 : Encl e1996 (31420422813 / 40000000000 : ℝ) (785510570327 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1997 : Encl e1997 (1392281235299 / 1000000000000 : ℝ) (174035154413 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1996 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1998 : Encl e1998 (154256714023 / 250000000000 : ℝ) (19282089253 / 31250000000 : ℝ) := by
  exact Encl.pow b1996 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1999 : Encl e1999 (484611759541 / 1000000000000 : ℝ) (242305879773 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2000 : Encl e2000 (1484611759541 / 1000000000000 : ℝ) (742305879773 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1999 (by norm_num) (by norm_num)

lemma b2001 : Encl e2001 (304611613323 / 250000000000 : ℝ) (243689290659 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2002 : Encl e2002 (339284026627 / 200000000000 : ℝ) (848210066573 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1997 b2001 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2003 : Encl e2003 (484611759541 / 500000000000 : ℝ) (96922351909 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2004 : Encl e2004 (145439322809 / 200000000000 : ℝ) (45449788379 / 62500000000 : ℝ) := by
  exact Encl.sub b2002 b2003 (by norm_num) (by norm_num)

lemma b2005 : Encl e2005 (168043580717 / 250000000000 : ℝ) (84021790361 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1938 b2004 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2006 : Encl e2006 (26148178921 / 1000000000000 : ℝ) (26148178967 / 1000000000000 : ℝ) := by
  exact Encl.sub b1995 b2005 (by norm_num) (by norm_num)

lemma b2007 : Encl e2007 (146360796269 / 1000000000000 : ℝ) (36590199087 / 250000000000 : ℝ) := by
  exact Encl.sub b165 b1966 (by norm_num) (by norm_num)

lemma b2008 : Encl e2008 (3827068287 / 1000000000000 : ℝ) (3827068297 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2006 b2007 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2009 : Encl e2009 (10818708159 / 500000000000 : ℝ) (10818708181 / 500000000000 : ℝ) := by
  exact Encl.sub b2004 b1957 (by norm_num) (by norm_num)

lemma b2010 : Encl e2010 (34996953351 / 250000000000 : ℝ) (8749238347 / 62500000000 : ℝ) := by
  exact Encl.sub b183 b1988 (by norm_num) (by norm_num)

lemma b2011 : Encl e2011 (1514487299 / 500000000000 : ℝ) (189310913 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2009 b2010 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2012 : Encl e2012 (1371208577 / 200000000000 : ℝ) (1371208581 / 200000000000 : ℝ) := by
  exact Encl.add b2008 b2011 (by norm_num) (by norm_num)

lemma b2013 : Encl e2013 (65406887599 / 1000000000000 : ℝ) (32703443801 / 500000000000 : ℝ) := by
  exact Encl.sub b4 b1938 (by norm_num) (by norm_num)

lemma b2014 : Encl e2014 (20964284149 / 200000000000 : ℝ) (104821421057 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2012 b2013 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2015 : Encl e2015 (-72604479 / 40000000000 : ℝ) (-1815111389 / 1000000000000 : ℝ) := by
  exact Encl.add b1994 b2014 (by norm_num) (by norm_num)

lemma b2016 : Encl e2016 (47619047619 / 62500000000 : ℝ) (152380952381 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2017 : Encl e2017 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2016 (by norm_num) (by norm_num)

lemma b2018 : Encl e2018 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b2017 b5 (by norm_num) (by norm_num)

lemma b2019 : Encl e2019 (63 / 25 : ℝ) (63 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2020 : Encl e2020 (920307213471 / 500000000000 : ℝ) (368122885389 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2019 b1880 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2021 : Encl e2021 (146471442187 / 250000000000 : ℝ) (93741723 / 160000000 : ℝ) := by
  exact Encl.div_nonneg b2020 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2022 : Encl e2022 (66893970641 / 250000000000 : ℝ) (267575882567 / 1000000000000 : ℝ) := by
  exact Encl.add b2018 b2021 (by norm_num) (by norm_num)

lemma b2023 : Encl e2023 (3969 / 1250 : ℝ) (3969 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b1874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2024 : Encl e2024 (2319174177947 / 1000000000000 : ℝ) (2319174177951 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2023 b1880 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2025 : Encl e2025 (341297926971 / 62500000000 : ℝ) (5460766831541 / 1000000000000 : ℝ) := by
  exact Encl.add b0 b2024 (by norm_num) (by norm_num)

lemma b2026 : Encl e2026 (2336828370149 / 1000000000000 : ℝ) (2336828370151 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2025 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2027 : Encl e2027 (297534229013 / 200000000000 : ℝ) (1487671145069 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2026 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2028 : Encl e2028 (250047 / 125000 : ℝ) (250047 / 125000 : ℝ) := by
  exact Encl.pow b1869 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2029 : Encl e2029 (16753149 / 62500000 : ℝ) (16753149 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2028 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2030 : Encl e2030 (16753149 / 62500000 : ℝ) (16753149 / 62500000 : ℝ) := by
  exact Encl.min b2029 b941 (by norm_num) (by norm_num)

lemma b2031 : Encl e2031 (66893970641 / 125000000000 : ℝ) (267575882567 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2022 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2032 : Encl e2032 (50259447 / 31250000 : ℝ) (50259447 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b2030 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2033 : Encl e2033 (2213165435859 / 1000000000000 : ℝ) (2213165435871 / 1000000000000 : ℝ) := by
  exact Encl.pow b2027 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2034 : Encl e2034 (28475512557 / 8000000000 : ℝ) (711887813929 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2032 b2033 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2035 : Encl e2035 (952420050487 / 1000000000000 : ℝ) (119052506313 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b2034 b2022 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2036 : Encl e2036 (340150018031 / 100000000000 : ℝ) (850375045093 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2035 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2037 : Encl e2037 (440150018031 / 100000000000 : ℝ) (1100375045093 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2036 (by norm_num) (by norm_num)

lemma b2038 : Encl e2038 (419595051463 / 200000000000 : ℝ) (2097975257331 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2037 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2039 : Encl e2039 (619595051463 / 200000000000 : ℝ) (3097975257331 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2038 (by norm_num) (by norm_num)

lemma b2040 : Encl e2040 (86371213563 / 500000000000 : ℝ) (172742427129 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2031 b2039 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2041 : Encl e2041 (1241207303 / 500000000000 : ℝ) (2482414607 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2030 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

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

lemma b2042 : Encl e2042 (18966691087 / 200000000000 : ℝ) (94833455441 / 1000000000000 : ℝ) := by
  exact Encl.sub b2022 b2040 (by norm_num) (by norm_num)

lemma b2043 : Encl e2043 (7968281141 / 125000000000 : ℝ) (63746249133 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2042 b2027 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2044 : Encl e2044 (4063584277 / 1000000000000 : ℝ) (4063584279 / 1000000000000 : ℝ) := by
  exact Encl.pow b2043 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2045 : Encl e2045 (1137803597 / 1000000000000 : ℝ) (1137803599 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2044 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2046 : Encl e2046 (5154624719 / 1000000000000 : ℝ) (64432809 / 12500000000 : ℝ) := by
  exact Encl.pow b2040 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2047 : Encl e2047 (276339827 / 200000000000 : ℝ) (21589049 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b2030 b2046 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2048 : Encl e2048 (629875683 / 250000000000 : ℝ) (503900547 / 200000000000 : ℝ) := by
  exact Encl.add b2045 b2047 (by norm_num) (by norm_num)

lemma b2049 : Encl e2049 (1241207303 / 500000000000 : ℝ) (2482414607 / 1000000000000 : ℝ) := by
  exact Encl.min b2041 b2048 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_126 : Encl (twoChordBaseline (63 / 50 : ℝ)) (-72604479 / 40000000000 : ℝ) (-1815111389 / 1000000000000 : ℝ) := by
  exact b2015

lemma gain_enclosure_126 : Encl (gain (63 / 50 : ℝ)) (1241207303 / 500000000000 : ℝ) (2482414607 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2049

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

lemma baseline_lower_126 : (-72604479 / 40000000000 : ℝ) ≤ baseline (63 / 50 : ℝ) :=
  (baseline_enclosure_126).1.trans (twoChordBaseline_le_of_range (h := (63 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_126_oai : (667302631 / 1000000000000 : ℝ) ≤ baseline (63 / 50 : ℝ) + gain (63 / 50 : ℝ) := by
  have hb := baseline_lower_126
  have hg := (gain_enclosure_126).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_126_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_126_oai

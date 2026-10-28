-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_150
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:45:25.368038+00:00
-- url     : https://prove2.me/submissions/32e3cefa-2189-494c-a81c-833c3b9a2bd0

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
lemma b2857 : Encl e2857 (3 / 2 : ℝ) (3 / 2 : ℝ) := by
  exact Encl.exact (3 / 2 : ℝ)

lemma b2858 : Encl e2858 (19098593171 / 40000000000 : ℝ) (119366207319 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2857 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2859 : Encl e2859 (147 / 100 : ℝ) (147 / 100 : ℝ) := by
  exact Encl.mul_nonneg b8 b2857 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2860 : Encl e2860 (46791553269 / 100000000000 : ℝ) (467915532691 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2859 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2861 : Encl e2861 (9 / 4 : ℝ) (9 / 4 : ℝ) := by
  exact Encl.pow b2857 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2862 : Encl e2862 (9 : ℝ) (9 : ℝ) := by
  exact Encl.mul_nonneg b17 b2861 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2863 : Encl e2863 (1432394487827 / 500000000000 : ℝ) (572957795131 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2862 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2864 : Encl e2864 (1932394487827 / 500000000000 : ℝ) (772957795131 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2863 (by norm_num) (by norm_num)

lemma b2865 : Encl e2865 (1965906654867 / 1000000000000 : ℝ) (1965906654869 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2864 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2866 : Encl e2866 (2965906654867 / 1000000000000 : ℝ) (2965906654869 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2865 (by norm_num) (by norm_num)

lemma b2867 : Encl e2867 (337165027887 / 500000000000 : ℝ) (21072814243 / 31250000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2866 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2868 : Encl e2868 (1475096997 / 7812500000 : ℝ) (94406207809 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2867 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2869 : Encl e2869 (328363974153 / 500000000000 : ℝ) (656727948309 / 1000000000000 : ℝ) := by
  exact Encl.add b2860 b2868 (by norm_num) (by norm_num)

lemma b2870 : Encl e2870 (-171636025847 / 500000000000 : ℝ) (-343272051691 / 1000000000000 : ℝ) := by
  exact Encl.sub b2869 b5 (by norm_num) (by norm_num)

lemma b2871 : Encl e2871 (279252680319 / 200000000000 : ℝ) (349065850399 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2861 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2872 : Encl e2872 (113986331597 / 500000000000 : ℝ) (56993165799 / 250000000000 : ℝ) := by
  exact Encl.pow b2858 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2873 : Encl e2873 (193006834201 / 250000000000 : ℝ) (386013668403 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2872 (by norm_num) (by norm_num)

lemma b2874 : Encl e2874 (878650861721 / 1000000000000 : ℝ) (878650861723 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2873 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2875 : Encl e2875 (-211984195057 / 1000000000000 : ℝ) (-105992097527 / 500000000000 : ℝ) := by
  exact Encl.sub b29 b2874 (by norm_num) (by norm_num)

lemma b2876 : Encl e2876 (339171242377 / 500000000000 : ℝ) (678342484759 / 1000000000000 : ℝ) := by
  exact Encl.pow b2874 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2877 : Encl e2877 (14132135099 / 62500000000 : ℝ) (226114161587 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2876 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2878 : Encl e2878 (14129966527 / 1000000000000 : ℝ) (14129966533 / 1000000000000 : ℝ) := by
  exact Encl.add b2875 b2877 (by norm_num) (by norm_num)

lemma b2879 : Encl e2879 (3461841799 / 250000000000 : ℝ) (13847367203 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2878 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2880 : Encl e2880 (259457622049 / 1000000000000 : ℝ) (64864405513 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2872 b2874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2881 : Encl e2881 (-1740542377951 / 1000000000000 : ℝ) (-435135594487 / 250000000000 : ℝ) := by
  exact Encl.sub b2880 b23 (by norm_num) (by norm_num)

lemma b2882 : Encl e2882 (878650861721 / 500000000000 : ℝ) (878650861723 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2883 : Encl e2883 (16759345491 / 1000000000000 : ℝ) (8379672749 / 500000000000 : ℝ) := by
  exact Encl.add b2881 b2882 (by norm_num) (by norm_num)

lemma b2884 : Encl e2884 (335186909 / 1000000000000 : ℝ) (33518691 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2883 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2885 : Encl e2885 (6756090143 / 500000000000 : ℝ) (6756090147 / 500000000000 : ℝ) := by
  exact Encl.sub b2879 b2884 (by norm_num) (by norm_num)

lemma b2886 : Encl e2886 (18866562809 / 1000000000000 : ℝ) (18866562821 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2871 b2885 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2887 : Encl e2887 (-64881097777 / 200000000000 : ℝ) (-32440548887 / 100000000000 : ℝ) := by
  exact Encl.add b2870 b2886 (by norm_num) (by norm_num)

lemma b2888 : Encl e2888 (1878650861721 / 1000000000000 : ℝ) (1878650861723 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2874 (by norm_num) (by norm_num)

lemma b2889 : Encl e2889 (31769130111 / 125000000000 : ℝ) (25415304089 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2858 b2888 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2890 : Encl e2890 (252319407 / 3906250000 : ℝ) (32296884097 / 500000000000 : ℝ) := by
  exact Encl.pow b2889 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2891 : Encl e2891 (4158569407 / 3906250000 : ℝ) (532296884097 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2890 (by norm_num) (by norm_num)

lemma b2892 : Encl e2892 (1031791533301 / 1000000000000 : ℝ) (1031791533303 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2891 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2893 : Encl e2893 (2031791533301 / 1000000000000 : ℝ) (2031791533303 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2892 (by norm_num) (by norm_num)

lemma b2894 : Encl e2894 (5003525937 / 40000000000 : ℝ) (125088148427 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2889 b2893 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2895 : Encl e2895 (497767143601 / 1000000000000 : ℝ) (49776714361 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e2858) (a := (5003525937 / 40000000000 : ℝ)) (b := (125088148427 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (19098593171 / 40000000000 : ℝ) by norm_num).trans b2858.1
        exact b2858.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2858) (5003525937 / 40000000000 : ℝ) (125088148427 / 1000000000000 : ℝ) from b2894) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2896 : Encl e2896 (63465310809 / 250000000000 : ℝ) (126930621621 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2895 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2897 : Encl e2897 (29244720793 / 125000000000 : ℝ) (116978883173 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2858 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2898 : Encl e2898 (51391798251 / 250000000000 : ℝ) (205567193007 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2897 b2874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2899 : Encl e2899 (48294050229 / 1000000000000 : ℝ) (24147025119 / 500000000000 : ℝ) := by
  exact Encl.sub b2896 b2898 (by norm_num) (by norm_num)

lemma b2900 : Encl e2900 (878650861721 / 20000000000 : ℝ) (878650861723 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2901 : Encl e2901 (5434067729 / 500000000000 : ℝ) (10868135459 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2858 b2900 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2902 : Encl e2902 (3742591477 / 100000000000 : ℝ) (1871295739 / 50000000000 : ℝ) := by
  exact Encl.sub b2899 b2901 (by norm_num) (by norm_num)

lemma b2903 : Encl e2903 (120681713683 / 250000000000 : ℝ) (482726854873 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b2902 (by norm_num) (by norm_num)

lemma b2904 : Encl e2904 (160908951577 / 500000000000 : ℝ) (321817903249 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2903 b2857 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2905 : Encl e2905 (-2587585731 / 1000000000000 : ℝ) (-2587585621 / 1000000000000 : ℝ) := by
  exact Encl.add b2887 b2904 (by norm_num) (by norm_num)

lemma b2906 : Encl e2906 (16 / 25 : ℝ) (16 / 25 : ℝ) := by
  exact Encl.div_nonneg b924 b2857 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2907 : Encl e2907 (16 / 25 : ℝ) (16 / 25 : ℝ) := by
  exact Encl.min b7 b2906 (by norm_num) (by norm_num)

lemma b2908 : Encl e2908 (-9 / 25 : ℝ) (-9 / 25 : ℝ) := by
  exact Encl.sub b2907 b5 (by norm_num) (by norm_num)

lemma b2909 : Encl e2909 (3 : ℝ) (3 : ℝ) := by
  exact Encl.mul_nonneg b23 b2857 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2910 : Encl e2910 (1011495083661 / 500000000000 : ℝ) (63218442729 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b2909 b2867 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2911 : Encl e2911 (643937769911 / 1000000000000 : ℝ) (321968884957 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2910 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2912 : Encl e2912 (283937769911 / 1000000000000 : ℝ) (141968884957 / 500000000000 : ℝ) := by
  exact Encl.add b2908 b2911 (by norm_num) (by norm_num)

lemma b2913 : Encl e2913 (9 / 2 : ℝ) (9 / 2 : ℝ) := by
  exact Encl.mul_nonneg b23 b2861 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2914 : Encl e2914 (3034485250983 / 1000000000000 : ℝ) (189655328187 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2913 b2867 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2915 : Encl e2915 (1544019476143 / 250000000000 : ℝ) (3088038952291 / 500000000000 : ℝ) := by
  exact Encl.add b0 b2914 (by norm_num) (by norm_num)

lemma b2916 : Encl e2916 (621292901163 / 250000000000 : ℝ) (497034320931 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2915 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2917 : Encl e2917 (791054690623 / 500000000000 : ℝ) (1582109381251 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2916 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2918 : Encl e2918 (27 / 8 : ℝ) (27 / 8 : ℝ) := by
  exact Encl.pow b2857 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2919 : Encl e2919 (1809 / 4000 : ℝ) (1809 / 4000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2918 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2920 : Encl e2920 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b2919 b941 (by norm_num) (by norm_num)

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

lemma b2921 : Encl e2921 (283937769911 / 500000000000 : ℝ) (141968884957 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2912 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2922 : Encl e2922 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b2920 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2923 : Encl e2923 (1251535047113 / 500000000000 : ℝ) (2503070094243 / 1000000000000 : ℝ) := by
  exact Encl.pow b2917 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2924 : Encl e2924 (675828925441 / 125000000000 : ℝ) (1081326280713 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2922 b2923 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2925 : Encl e2925 (191893357931 / 125000000000 : ℝ) (383786715869 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2924 b2912 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2926 : Encl e2926 (5482667369457 / 1000000000000 : ℝ) (2741333684779 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2925 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2927 : Encl e2927 (6482667369457 / 1000000000000 : ℝ) (3241333684779 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2926 (by norm_num) (by norm_num)

lemma b2928 : Encl e2928 (2546108279209 / 1000000000000 : ℝ) (2546108279229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2927 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2929 : Encl e2929 (3546108279209 / 1000000000000 : ℝ) (3546108279229 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2928 (by norm_num) (by norm_num)

lemma b2930 : Encl e2930 (80070248157 / 500000000000 : ℝ) (80070248159 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2921 b2929 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2931 : Encl e2931 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b2920 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2932 : Encl e2932 (123797273593 / 1000000000000 : ℝ) (4835831 / 39062500 : ℝ) := by
  exact Encl.sub b2912 b2930 (by norm_num) (by norm_num)

lemma b2933 : Encl e2933 (39124119691 / 500000000000 : ℝ) (78248239387 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2932 b2917 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2934 : Encl e2934 (3061393483 / 500000000000 : ℝ) (765348371 / 125000000000 : ℝ) := by
  exact Encl.pow b2933 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2935 : Encl e2935 (34287607 / 20000000000 : ℝ) (26787193 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2934 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2936 : Encl e2936 (2053399797 / 500000000000 : ℝ) (821359919 / 200000000000 : ℝ) := by
  exact Encl.pow b2930 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2937 : Encl e2937 (1478447853 / 1000000000000 : ℝ) (295689571 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2920 b2936 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2938 : Encl e2938 (3192828203 / 1000000000000 : ℝ) (3192828207 / 1000000000000 : ℝ) := by
  exact Encl.add b2935 b2937 (by norm_num) (by norm_num)

lemma b2939 : Encl e2939 (3192828203 / 1000000000000 : ℝ) (3192828207 / 1000000000000 : ℝ) := by
  exact Encl.min b2931 b2938 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_150 : Encl (linearBaseline (3 / 2 : ℝ)) (-2587585731 / 1000000000000 : ℝ) (-2587585621 / 1000000000000 : ℝ) := by
  exact b2905

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

lemma gain_enclosure_150 : Encl (gain (3 / 2 : ℝ)) (3192828203 / 1000000000000 : ℝ) (3192828207 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2939

lemma baseline_lower_150 : (-2587585731 / 1000000000000 : ℝ) ≤ baseline (3 / 2 : ℝ) :=
  (baseline_enclosure_150).1.trans ((linearBaseline_eq_of_range (h := (3 / 2 : ℝ)) (by norm_num) (by norm_num)).le)

lemma combined_lower_150_oai : (75655309 / 125000000000 : ℝ) ≤ baseline (3 / 2 : ℝ) + gain (3 / 2 : ℝ) := by
  have hb := baseline_lower_150
  have hg := (gain_enclosure_150).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_150_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_150_oai

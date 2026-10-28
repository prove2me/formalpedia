-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_130
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:42:02.578994+00:00
-- url     : https://prove2.me/submissions/531fd6dc-3180-4f1a-b406-1659d88fee27

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

lemma b2050 : Encl e2050 (13 / 10 : ℝ) (13 / 10 : ℝ) := by
  exact Encl.exact (13 / 10 : ℝ)

lemma b2051 : Encl e2051 (206901426019 / 500000000000 : ℝ) (413802852039 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2050 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2052 : Encl e2052 (22154928699 / 25000000000 : ℝ) (886197147963 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2050 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2053 : Encl e2053 (637 / 500 : ℝ) (637 / 500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2054 : Encl e2054 (202763397499 / 500000000000 : ℝ) (405526794999 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2053 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2055 : Encl e2055 (169 / 100 : ℝ) (169 / 100 : ℝ) := by
  exact Encl.pow b2050 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2056 : Encl e2056 (169 / 25 : ℝ) (169 / 25 : ℝ) := by
  exact Encl.mul_nonneg b17 b2055 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2057 : Encl e2057 (1075887415301 / 500000000000 : ℝ) (2151774830603 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2056 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2058 : Encl e2058 (1575887415301 / 500000000000 : ℝ) (3151774830603 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2057 (by norm_num) (by norm_num)

lemma b2059 : Encl e2059 (1775323866397 / 1000000000000 : ℝ) (1775323866399 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2058 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2060 : Encl e2060 (2775323866397 / 1000000000000 : ℝ) (2775323866399 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2059 (by norm_num) (by norm_num)

lemma b2061 : Encl e2061 (720636616221 / 1000000000000 : ℝ) (360318308111 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2060 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2062 : Encl e2062 (201778252541 / 1000000000000 : ℝ) (201778252543 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2061 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2063 : Encl e2063 (607305047539 / 1000000000000 : ℝ) (303652523771 / 500000000000 : ℝ) := by
  exact Encl.add b2054 b2062 (by norm_num) (by norm_num)

lemma b2064 : Encl e2064 (-392694952461 / 1000000000000 : ℝ) (-196347476229 / 500000000000 : ℝ) := by
  exact Encl.sub b2063 b5 (by norm_num) (by norm_num)

lemma b2065 : Encl e2065 (929465282127 / 500000000000 : ℝ) (371786112851 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2055 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2066 : Encl e2066 (85616400177 / 500000000000 : ℝ) (42808200089 / 250000000000 : ℝ) := by
  exact Encl.pow b2051 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2067 : Encl e2067 (207191799911 / 250000000000 : ℝ) (414383599823 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2066 (by norm_num) (by norm_num)

lemma b2068 : Encl e2068 (910366519399 / 1000000000000 : ℝ) (910366519401 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2067 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2069 : Encl e2069 (-48739970547 / 200000000000 : ℝ) (-60924963183 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b2068 (by norm_num) (by norm_num)

lemma b2070 : Encl e2070 (75448191093 / 100000000000 : ℝ) (94310238867 / 125000000000 : ℝ) := by
  exact Encl.pow b2068 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2071 : Encl e2071 (25149397031 / 100000000000 : ℝ) (31436746289 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b2070 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2072 : Encl e2072 (311764703 / 40000000000 : ℝ) (389705879 / 50000000000 : ℝ) := by
  exact Encl.add b2069 b2071 (by norm_num) (by norm_num)

lemma b2073 : Encl e2073 (7638235223 / 1000000000000 : ℝ) (7638235229 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2072 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2074 : Encl e2074 (47023038717 / 250000000000 : ℝ) (188092154871 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2066 b2068 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2075 : Encl e2075 (-452976961283 / 250000000000 : ℝ) (-1811907845129 / 1000000000000 : ℝ) := by
  exact Encl.sub b2074 b23 (by norm_num) (by norm_num)

lemma b2076 : Encl e2076 (910366519399 / 500000000000 : ℝ) (910366519401 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2068 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2077 : Encl e2077 (4412596833 / 500000000000 : ℝ) (8825193673 / 1000000000000 : ℝ) := by
  exact Encl.add b2075 b2076 (by norm_num) (by norm_num)

lemma b2078 : Encl e2078 (176503873 / 1000000000000 : ℝ) (88251937 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2077 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2079 : Encl e2079 (7461731349 / 1000000000000 : ℝ) (1865432839 / 250000000000 : ℝ) := by
  exact Encl.sub b2073 b2078 (by norm_num) (by norm_num)

lemma b2080 : Encl e2080 (6935420233 / 500000000000 : ℝ) (86692753 / 6250000000 : ℝ) := by
  exact Encl.mul_nonneg b2065 b2079 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2081 : Encl e2081 (-75764822399 / 200000000000 : ℝ) (-189412055989 / 500000000000 : ℝ) := by
  exact Encl.add b2064 b2080 (by norm_num) (by norm_num)

lemma b2082 : Encl e2082 (196336346263 / 250000000000 : ℝ) (392672692529 / 500000000000 : ℝ) := by
  exact Encl.pow b2052 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2083 : Encl e2083 (107327307471 / 500000000000 : ℝ) (53663653737 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b2082 (by norm_num) (by norm_num)

lemma b2084 : Encl e2084 (463308336793 / 1000000000000 : ℝ) (579135421 / 1250000000 : ℝ) := by
  exact Encl.sqrt b2083 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2085 : Encl e2085 (1463308336793 / 1000000000000 : ℝ) (1829135421 / 1250000000 : ℝ) := by
  exact Encl.add b5 b2084 (by norm_num) (by norm_num)

lemma b2086 : Encl e2086 (605612040657 / 1000000000000 : ℝ) (605612040663 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2052 b2085 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2087 : Encl e2087 (91691485947 / 250000000000 : ℝ) (366765943797 / 1000000000000 : ℝ) := by
  exact Encl.pow b2086 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2088 : Encl e2088 (341691485947 / 250000000000 : ℝ) (1366765943797 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2087 (by norm_num) (by norm_num)

lemma b2089 : Encl e2089 (23381753089 / 20000000000 : ℝ) (233817530891 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2088 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2090 : Encl e2090 (43381753089 / 20000000000 : ℝ) (433817530891 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2089 (by norm_num) (by norm_num)

lemma b2091 : Encl e2091 (279201275897 / 1000000000000 : ℝ) (279201275901 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2086 b2090 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2092 : Encl e2092 (217814314373 / 200000000000 : ℝ) (1089071571881 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2052) (a := (279201275897 / 1000000000000 : ℝ)) (b := (279201275901 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (22154928699 / 25000000000 : ℝ) by norm_num).trans b2052.1
        exact b2052.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2052) (279201275897 / 1000000000000 : ℝ) (279201275901 / 1000000000000 : ℝ) from b2091) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2093 : Encl e2093 (555426501651 / 1000000000000 : ℝ) (27771325083 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2092 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2094 : Encl e2094 (173694641 / 400000000 : ℝ) (217118301251 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2052 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2095 : Encl e2095 (100592719039 / 500000000000 : ℝ) (201185438083 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2094 b2084 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2096 : Encl e2096 (22140066473 / 62500000000 : ℝ) (177120531791 / 500000000000 : ℝ) := by
  exact Encl.sub b2093 b2095 (by norm_num) (by norm_num)

lemma b2097 : Encl e2097 (463308336793 / 20000000000 : ℝ) (579135421 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2084 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2098 : Encl e2098 (19127589071 / 500000000000 : ℝ) (1195474317 / 31250000000 : ℝ) := by
  exact Encl.div_nonneg b2052 b2097 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2099 : Encl e2099 (19749117839 / 62500000000 : ℝ) (246863973 / 781250000 : ℝ) := by
  exact Encl.sub b2096 b2098 (by norm_num) (by norm_num)

lemma b2100 : Encl e2100 (1910366519399 / 1000000000000 : ℝ) (1910366519401 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2068 (by norm_num) (by norm_num)

lemma b2101 : Encl e2101 (216609141667 / 1000000000000 : ℝ) (216609141669 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2051 b2100 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2102 : Encl e2102 (46919520253 / 1000000000000 : ℝ) (9383904051 / 200000000000 : ℝ) := by
  exact Encl.pow b2101 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2103 : Encl e2103 (1046919520253 / 1000000000000 : ℝ) (209383904051 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2102 (by norm_num) (by norm_num)

lemma b2104 : Encl e2104 (1023190852311 / 1000000000000 : ℝ) (1023190852313 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2103 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2105 : Encl e2105 (2023190852311 / 1000000000000 : ℝ) (2023190852313 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2104 (by norm_num) (by norm_num)

lemma b2106 : Encl e2106 (21412625647 / 200000000000 : ℝ) (53531564119 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2101 b2105 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2107 : Encl e2107 (213313695887 / 500000000000 : ℝ) (426627391787 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2051) (a := (21412625647 / 200000000000 : ℝ)) (b := (53531564119 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (206901426019 / 500000000000 : ℝ) by norm_num).trans b2051.1
        exact b2051.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2051) (21412625647 / 200000000000 : ℝ) (53531564119 / 500000000000 : ℝ) from b2106) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2108 : Encl e2108 (54394992451 / 250000000000 : ℝ) (54394992453 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2107 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2109 : Encl e2109 (101381698749 / 500000000000 : ℝ) (81105359 / 400000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2051 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2110 : Encl e2110 (184589008441 / 1000000000000 : ℝ) (46147252111 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2109 b2068 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2111 : Encl e2111 (412387017 / 12500000000 : ℝ) (32990961371 / 1000000000000 : ℝ) := by
  exact Encl.sub b2108 b2110 (by norm_num) (by norm_num)

lemma b2112 : Encl e2112 (910366519399 / 20000000000 : ℝ) (910366519401 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2068 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2113 : Encl e2113 (1818181329 / 200000000000 : ℝ) (4545453323 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2051 b2112 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2114 : Encl e2114 (11950027357 / 500000000000 : ℝ) (11950027363 / 500000000000 : ℝ) := by
  exact Encl.sub b2111 b2113 (by norm_num) (by norm_num)

lemma b2115 : Encl e2115 (146042915349 / 500000000000 : ℝ) (146042915363 / 500000000000 : ℝ) := by
  exact Encl.sub b2099 b2114 (by norm_num) (by norm_num)

lemma b2116 : Encl e2116 (224681408229 / 1000000000000 : ℝ) (224681408251 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2115 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2117 : Encl e2117 (-77071351883 / 500000000000 : ℝ) (-154142703727 / 1000000000000 : ℝ) := by
  exact Encl.add b2081 b2116 (by norm_num) (by norm_num)

lemma b2118 : Encl e2118 (187594046657 / 100000000000 : ℝ) (937970233287 / 500000000000 : ℝ) := by
  exact Encl.add b2052 b4 (by norm_num) (by norm_num)

lemma b2119 : Encl e2119 (187594046657 / 200000000000 : ℝ) (937970233287 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2118 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2120 : Encl e2120 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2052 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2121 : Encl e2121 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2120 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2122 : Encl e2122 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b2120 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2123 : Encl e2123 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2122 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2124 : Encl e2124 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2123 (by norm_num) (by norm_num)

lemma b2125 : Encl e2125 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2124 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2126 : Encl e2126 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2121 b2125 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2127 : Encl e2127 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2122 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2128 : Encl e2128 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b2126 b2127 (by norm_num) (by norm_num)

lemma b2129 : Encl e2129 (639405035073 / 1000000000000 : ℝ) (639405035097 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2119 b2128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2130 : Encl e2130 (144303112813 / 200000000000 : ℝ) (721515564067 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2119 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2131 : Encl e2131 (639426520007 / 500000000000 : ℝ) (63942652001 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2130 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2132 : Encl e2132 (130146177297 / 250000000000 : ℝ) (520584709191 / 1000000000000 : ℝ) := by
  exact Encl.pow b2130 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2133 : Encl e2133 (51108284311 / 125000000000 : ℝ) (102216568623 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2132 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2134 : Encl e2134 (176108284311 / 125000000000 : ℝ) (352216568623 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2133 (by norm_num) (by norm_num)

lemma b2135 : Encl e2135 (74184795509 / 62500000000 : ℝ) (1186956728147 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2134 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2136 : Encl e2136 (189742902519 / 125000000000 : ℝ) (1517943220163 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2131 b2135 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2137 : Encl e2137 (817732548977 / 1000000000000 : ℝ) (817732548983 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2132 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2138 : Encl e2138 (700210671169 / 1000000000000 : ℝ) (350105335593 / 500000000000 : ℝ) := by
  exact Encl.sub b2136 b2137 (by norm_num) (by norm_num)

lemma b2139 : Encl e2139 (620524699761 / 1000000000000 : ℝ) (620524699779 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2052 b2138 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2140 : Encl e2140 (9440167647 / 500000000000 : ℝ) (2360041917 / 125000000000 : ℝ) := by
  exact Encl.sub b2129 b2139 (by norm_num) (by norm_num)

lemma b2141 : Encl e2141 (13746689977 / 15625000000 : ℝ) (879788158533 / 1000000000000 : ℝ) := by
  exact Encl.pow b2119 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2142 : Encl e2142 (862192395357 / 1000000000000 : ℝ) (862192395363 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2141 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2143 : Encl e2143 (137807604637 / 1000000000000 : ℝ) (137807604643 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2142 (by norm_num) (by norm_num)

lemma b2144 : Encl e2144 (120211841467 / 1000000000000 : ℝ) (1878310023 / 15625000000 : ℝ) := by
  exact Encl.sub b5 b2141 (by norm_num) (by norm_num)

lemma b2145 : Encl e2145 (173357896753 / 500000000000 : ℝ) (173357896757 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2144 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2146 : Encl e2146 (198732805391 / 500000000000 : ℝ) (39746561081 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2143 b2145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2147 : Encl e2147 (60253438919 / 100000000000 : ℝ) (301267194609 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2146 (by norm_num) (by norm_num)

lemma b2148 : Encl e2148 (15392769547 / 20000000000 : ℝ) (769638477357 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2082 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2149 : Encl e2149 (230361522643 / 1000000000000 : ℝ) (4607230453 / 20000000000 : ℝ) := by
  exact Encl.sub b5 b2148 (by norm_num) (by norm_num)

lemma b2150 : Encl e2150 (9944199331 / 20000000000 : ℝ) (248604983287 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2149 b2084 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2151 : Encl e2151 (251395016713 / 500000000000 : ℝ) (10055800669 / 20000000000 : ℝ) := by
  exact Encl.sub b5 b2150 (by norm_num) (by norm_num)

lemma b2152 : Encl e2152 (4987217787 / 50000000000 : ℝ) (6234022237 / 62500000000 : ℝ) := by
  exact Encl.sub b2147 b2151 (by norm_num) (by norm_num)

lemma b2153 : Encl e2153 (11770043 / 6250000000 : ℝ) (941603443 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2140 b2152 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2154 : Encl e2154 (18520557341 / 1000000000000 : ℝ) (18520557381 / 1000000000000 : ℝ) := by
  exact Encl.sub b2138 b2128 (by norm_num) (by norm_num)

lemma b2155 : Encl e2155 (673357896753 / 500000000000 : ℝ) (673357896757 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2145 (by norm_num) (by norm_num)

lemma b2156 : Encl e2156 (348243570693 / 500000000000 : ℝ) (696487141393 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2119 b2155 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2157 : Encl e2157 (121273584529 / 250000000000 : ℝ) (242547169063 / 500000000000 : ℝ) := by
  exact Encl.pow b2156 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2158 : Encl e2158 (371273584529 / 250000000000 : ℝ) (742547169063 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2157 (by norm_num) (by norm_num)

lemma b2159 : Encl e2159 (609322233739 / 500000000000 : ℝ) (1218644467483 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2158 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2160 : Encl e2160 (1109322233739 / 500000000000 : ℝ) (2218644467483 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2159 (by norm_num) (by norm_num)

lemma b2161 : Encl e2161 (313924629021 / 1000000000000 : ℝ) (156962314513 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2156 b2160 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2162 : Encl e2162 (7604555603 / 6250000000 : ℝ) (152091112063 / 125000000000 : ℝ) := by
  apply Encl.arcsin (z := e2119) (a := (313924629021 / 1000000000000 : ℝ)) (b := (156962314513 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (187594046657 / 200000000000 : ℝ) by norm_num).trans b2119.1
        exact b2119.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2119) (313924629021 / 1000000000000 : ℝ) (156962314513 / 500000000000 : ℝ) from b2161) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2163 : Encl e2163 (155132934301 / 250000000000 : ℝ) (310265868609 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2162 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2164 : Encl e2164 (459605414309 / 1000000000000 : ℝ) (459605414311 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2119 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2165 : Encl e2165 (159352455921 / 1000000000000 : ℝ) (159352455927 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2164 b2145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2166 : Encl e2166 (461179281277 / 1000000000000 : ℝ) (461179281297 / 1000000000000 : ℝ) := by
  exact Encl.sub b2163 b2165 (by norm_num) (by norm_num)

lemma b2167 : Encl e2167 (173357896753 / 10000000000 : ℝ) (173357896757 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2168 : Encl e2168 (6763249979 / 125000000000 : ℝ) (27052999917 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2119 b2167 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2169 : Encl e2169 (407073281443 / 1000000000000 : ℝ) (81414656293 / 200000000000 : ℝ) := by
  exact Encl.sub b2166 b2168 (by norm_num) (by norm_num)

lemma b2170 : Encl e2170 (91087396003 / 1000000000000 : ℝ) (91087396041 / 1000000000000 : ℝ) := by
  exact Encl.sub b2169 b2099 (by norm_num) (by norm_num)

lemma b2171 : Encl e2171 (84349467 / 50000000000 : ℝ) (843494673 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2154 b2170 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2172 : Encl e2172 (178509811 / 50000000000 : ℝ) (446274529 / 125000000000 : ℝ) := by
  exact Encl.add b2153 b2171 (by norm_num) (by norm_num)

lemma b2173 : Encl e2173 (25886542661 / 500000000000 : ℝ) (51773085327 / 1000000000000 : ℝ) := by
  exact Encl.sub b2119 b2052 (by norm_num) (by norm_num)

lemma b2174 : Encl e2174 (68958536997 / 1000000000000 : ℝ) (68958537237 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2172 b2173 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2175 : Encl e2175 (-85184166769 / 1000000000000 : ℝ) (-8518416649 / 100000000000 : ℝ) := by
  exact Encl.add b2117 b2174 (by norm_num) (by norm_num)

lemma b2176 : Encl e2176 (5414287761 / 7812500000 : ℝ) (693028833427 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b2138 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2177 : Encl e2177 (152268202863 / 200000000000 : ℝ) (761341014317 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2178 : Encl e2178 (674720906337 / 500000000000 : ℝ) (1349441812679 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2177 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2179 : Encl e2179 (289820070039 / 500000000000 : ℝ) (289820070041 / 500000000000 : ℝ) := by
  exact Encl.pow b2177 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2180 : Encl e2180 (56906037681 / 125000000000 : ℝ) (455248301453 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2179 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2181 : Encl e2181 (181906037681 / 125000000000 : ℝ) (1455248301453 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2180 (by norm_num) (by norm_num)

lemma b2182 : Encl e2182 (301584182013 / 250000000000 : ℝ) (241267345611 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2181 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2183 : Encl e2183 (1627881220997 / 1000000000000 : ℝ) (101742576313 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2178 b2182 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2184 : Encl e2184 (56906037681 / 62500000000 : ℝ) (113812075363 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2179 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2185 : Encl e2185 (717384618093 / 1000000000000 : ℝ) (5604567329 / 7812500000 : ℝ) := by
  exact Encl.sub b2183 b2184 (by norm_num) (by norm_num)

lemma b2186 : Encl e2186 (672885417587 / 1000000000000 : ℝ) (84110677201 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b2119 b2185 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2187 : Encl e2187 (100717079 / 5000000000 : ℝ) (125896349 / 6250000000 : ℝ) := by
  exact Encl.sub b2176 b2186 (by norm_num) (by norm_num)

lemma b2188 : Encl e2188 (117465610757 / 1000000000000 : ℝ) (58732805419 / 500000000000 : ℝ) := by
  exact Encl.sub b165 b2147 (by norm_num) (by norm_num)

lemma b2189 : Encl e2189 (2366158639 / 1000000000000 : ℝ) (2366158647 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2187 b2188 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2190 : Encl e2190 (17173946907 / 1000000000000 : ℝ) (17173946943 / 1000000000000 : ℝ) := by
  exact Encl.sub b2185 b2138 (by norm_num) (by norm_num)

lemma b2191 : Encl e2191 (113079488047 / 1000000000000 : ℝ) (565397441 / 5000000000 : ℝ) := by
  exact Encl.sub b183 b2169 (by norm_num) (by norm_num)

lemma b2192 : Encl e2192 (1942021123 / 1000000000000 : ℝ) (1942021131 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2190 b2191 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2193 : Encl e2193 (2154089881 / 500000000000 : ℝ) (2154089889 / 500000000000 : ℝ) := by
  exact Encl.add b2189 b2192 (by norm_num) (by norm_num)

lemma b2194 : Encl e2194 (51773085323 / 1000000000000 : ℝ) (25886542663 / 500000000000 : ℝ) := by
  exact Encl.sub b4 b2119 (by norm_num) (by norm_num)

lemma b2195 : Encl e2195 (16642545967 / 200000000000 : ℝ) (1664254603 / 20000000000 : ℝ) := by
  exact Encl.div_nonneg b2193 b2194 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2196 : Encl e2196 (-985718467 / 500000000000 : ℝ) (-98571817 / 50000000000 : ℝ) := by
  exact Encl.add b2175 b2195 (by norm_num) (by norm_num)

lemma b2197 : Encl e2197 (738461538461 / 1000000000000 : ℝ) (369230769231 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2198 : Encl e2198 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2197 (by norm_num) (by norm_num)

lemma b2199 : Encl e2199 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b2198 b5 (by norm_num) (by norm_num)

lemma b2200 : Encl e2200 (13 / 5 : ℝ) (13 / 5 : ℝ) := by
  exact Encl.mul_nonneg b23 b2050 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2201 : Encl e2201 (936827601087 / 500000000000 : ℝ) (936827601089 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2200 b2061 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2202 : Encl e2202 (596402974151 / 1000000000000 : ℝ) (596402974153 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2201 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2203 : Encl e2203 (278093087967 / 1000000000000 : ℝ) (27809308797 / 100000000000 : ℝ) := by
  exact Encl.add b2199 b2202 (by norm_num) (by norm_num)

lemma b2204 : Encl e2204 (169 / 50 : ℝ) (169 / 50 : ℝ) := by
  exact Encl.mul_nonneg b23 b2055 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2205 : Encl e2205 (1217875881413 / 500000000000 : ℝ) (2435751762831 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2204 b2061 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2206 : Encl e2206 (1115468883283 / 200000000000 : ℝ) (5577344416421 / 1000000000000 : ℝ) := by
  exact Encl.add b0 b2205 (by norm_num) (by norm_num)

lemma b2207 : Encl e2207 (1180820098111 / 500000000000 : ℝ) (94465607849 / 40000000000 : ℝ) := by
  exact Encl.sqrt b2206 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2208 : Encl e2208 (1503466844131 / 1000000000000 : ℝ) (187933355517 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2207 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2209 : Encl e2209 (2197 / 1000 : ℝ) (2197 / 1000 : ℝ) := by
  exact Encl.pow b2050 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2210 : Encl e2210 (147199 / 500000 : ℝ) (147199 / 500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2209 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2211 : Encl e2211 (147199 / 500000 : ℝ) (147199 / 500000 : ℝ) := by
  exact Encl.min b2210 b941 (by norm_num) (by norm_num)

lemma b2212 : Encl e2212 (278093087967 / 500000000000 : ℝ) (27809308797 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2203 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2213 : Encl e2213 (441597 / 250000 : ℝ) (441597 / 250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b2211 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2214 : Encl e2214 (2260412551401 / 1000000000000 : ℝ) (2260412551417 / 1000000000000 : ℝ) := by
  exact Encl.pow b2208 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2215 : Encl e2215 (998191401461 / 250000000000 : ℝ) (3992765605873 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2213 b2214 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2216 : Encl e2216 (1110360516857 / 1000000000000 : ℝ) (555180258439 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2215 b2203 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2217 : Encl e2217 (3965573274489 / 1000000000000 : ℝ) (793114654913 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2216 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2218 : Encl e2218 (4965573274489 / 1000000000000 : ℝ) (993114654913 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2217 (by norm_num) (by norm_num)

lemma b2219 : Encl e2219 (1114178315451 / 500000000000 : ℝ) (55708915773 / 25000000000 : ℝ) := by
  exact Encl.sqrt b2218 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2220 : Encl e2220 (1614178315451 / 500000000000 : ℝ) (80708915773 / 25000000000 : ℝ) := by
  exact Encl.add b5 b2219 (by norm_num) (by norm_num)

lemma b2221 : Encl e2221 (21535189553 / 125000000000 : ℝ) (43070379107 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2212 b2220 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2222 : Encl e2222 (1363209939 / 500000000000 : ℝ) (1363209939 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2211 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2223 : Encl e2223 (105811571539 / 1000000000000 : ℝ) (52905785773 / 500000000000 : ℝ) := by
  exact Encl.sub b2203 b2221 (by norm_num) (by norm_num)

lemma b2224 : Encl e2224 (70378387093 / 1000000000000 : ℝ) (70378387099 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2223 b2208 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2225 : Encl e2225 (4953117369 / 1000000000000 : ℝ) (4953117371 / 1000000000000 : ℝ) := by
  exact Encl.pow b2224 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2226 : Encl e2226 (1386872863 / 1000000000000 : ℝ) (43339777 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2225 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2227 : Encl e2227 (5113474061 / 1000000000000 : ℝ) (5113474063 / 1000000000000 : ℝ) := by
  exact Encl.pow b2221 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2228 : Encl e2228 (188174567 / 125000000000 : ℝ) (752698269 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2211 b2227 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2229 : Encl e2229 (2892269399 / 1000000000000 : ℝ) (1446134701 / 500000000000 : ℝ) := by
  exact Encl.add b2226 b2228 (by norm_num) (by norm_num)

lemma b2230 : Encl e2230 (1363209939 / 500000000000 : ℝ) (1363209939 / 500000000000 : ℝ) := by
  exact Encl.min b2222 b2229 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_130 : Encl (twoChordBaseline (13 / 10 : ℝ)) (-985718467 / 500000000000 : ℝ) (-98571817 / 50000000000 : ℝ) := by
  exact b2196

lemma gain_enclosure_130 : Encl (gain (13 / 10 : ℝ)) (1363209939 / 500000000000 : ℝ) (1363209939 / 500000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2230

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

lemma baseline_lower_130 : (-985718467 / 500000000000 : ℝ) ≤ baseline (13 / 10 : ℝ) :=
  (baseline_enclosure_130).1.trans (twoChordBaseline_le_of_range (h := (13 / 10 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_130_oai : (23593217 / 31250000000 : ℝ) ≤ baseline (13 / 10 : ℝ) + gain (13 / 10 : ℝ) := by
  have hb := baseline_lower_130
  have hg := (gain_enclosure_130).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_130_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_130_oai

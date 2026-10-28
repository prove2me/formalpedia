-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_122
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:40:32.991144+00:00
-- url     : https://prove2.me/submissions/2ec24e8f-1e73-4a42-87a1-a26b42fc1988

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
lemma b1688 : Encl e1688 (61 / 50 : ℝ) (61 / 50 : ℝ) := by
  exact Encl.exact (61 / 50 : ℝ)

lemma b1689 : Encl e1689 (48542257643 / 125000000000 : ℝ) (77667612229 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1688 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1690 : Encl e1690 (166332387771 / 200000000000 : ℝ) (831661938857 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1688 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1691 : Encl e1691 (2989 / 2500 : ℝ) (2989 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1692 : Encl e1692 (380571299921 / 1000000000000 : ℝ) (190285649961 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1691 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1693 : Encl e1693 (3721 / 2500 : ℝ) (3721 / 2500 : ℝ) := by
  exact Encl.pow b1688 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1694 : Encl e1694 (3721 / 625 : ℝ) (3721 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b1693 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1695 : Encl e1695 (1895089738383 / 1000000000000 : ℝ) (118443108649 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b1694 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1696 : Encl e1696 (2895089738383 / 1000000000000 : ℝ) (180943108649 / 62500000000 : ℝ) := by
  exact Encl.add b5 b1695 (by norm_num) (by norm_num)

lemma b1697 : Encl e1697 (212687040419 / 125000000000 : ℝ) (850748161677 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1696 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1698 : Encl e1698 (337687040419 / 125000000000 : ℝ) (1350748161677 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1697 (by norm_num) (by norm_num)

lemma b1699 : Encl e1699 (740330454167 / 1000000000000 : ℝ) (92541306771 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b1698 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1700 : Encl e1700 (103646263583 / 500000000000 : ℝ) (3238945737 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1699 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1701 : Encl e1701 (587863827087 / 1000000000000 : ℝ) (58786382709 / 100000000000 : ℝ) := by
  exact Encl.add b1692 b1700 (by norm_num) (by norm_num)

lemma b1702 : Encl e1702 (-412136172913 / 1000000000000 : ℝ) (-41213617291 / 100000000000 : ℝ) := by
  exact Encl.sub b1701 b5 (by norm_num) (by norm_num)

lemma b1703 : Encl e1703 (263839748521 / 125000000000 : ℝ) (2110717988169 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b1693 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1704 : Encl e1704 (150806449733 / 1000000000000 : ℝ) (75403224867 / 500000000000 : ℝ) := by
  exact Encl.pow b1689 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1705 : Encl e1705 (424596775133 / 500000000000 : ℝ) (849193550267 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1704 (by norm_num) (by norm_num)

lemma b1706 : Encl e1706 (921516983167 / 1000000000000 : ℝ) (7199351431 / 7812500000 : ℝ) := by
  exact Encl.sqrt b1705 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1707 : Encl e1707 (-127425158251 / 500000000000 : ℝ) (-509700633 / 2000000000 : ℝ) := by
  exact Encl.sub b29 b1706 (by norm_num) (by norm_num)

lemma b1708 : Encl e1708 (156509255713 / 200000000000 : ℝ) (97818284821 / 125000000000 : ℝ) := by
  exact Encl.pow b1706 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1709 : Encl e1709 (260848759521 / 1000000000000 : ℝ) (260848759523 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1708 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1710 : Encl e1710 (5998443019 / 1000000000000 : ℝ) (5998443023 / 1000000000000 : ℝ) := by
  exact Encl.add b1707 b1709 (by norm_num) (by norm_num)

lemma b1711 : Encl e1711 (2939237079 / 500000000000 : ℝ) (5878474163 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1710 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1712 : Encl e1712 (81825106041 / 500000000000 : ℝ) (40912553021 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1704 b1706 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1713 : Encl e1713 (-918174893959 / 500000000000 : ℝ) (-459087446979 / 250000000000 : ℝ) := by
  exact Encl.sub b1712 b23 (by norm_num) (by norm_num)

lemma b1714 : Encl e1714 (921516983167 / 500000000000 : ℝ) (7199351431 / 3906250000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1706 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1715 : Encl e1715 (417761151 / 62500000000 : ℝ) (334208921 / 50000000000 : ℝ) := by
  exact Encl.add b1713 b1714 (by norm_num) (by norm_num)

lemma b1716 : Encl e1716 (8355223 / 62500000000 : ℝ) (133683569 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1715 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1717 : Encl e1717 (5744790589 / 1000000000000 : ℝ) (1148958119 / 200000000000 : ℝ) := by
  exact Encl.sub b1711 b1716 (by norm_num) (by norm_num)

lemma b1718 : Encl e1718 (6062816417 / 500000000000 : ℝ) (757852053 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b1703 b1717 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1719 : Encl e1719 (-400010540079 / 1000000000000 : ℝ) (-200005270031 / 500000000000 : ℝ) := by
  exact Encl.add b1702 b1718 (by norm_num) (by norm_num)

lemma b1720 : Encl e1720 (34583079027 / 50000000000 : ℝ) (2701803049 / 3906250000 : ℝ) := by
  exact Encl.pow b1690 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1721 : Encl e1721 (1204446951 / 3906250000 : ℝ) (15416920973 / 50000000000 : ℝ) := by
  exact Encl.sub b5 b1720 (by norm_num) (by norm_num)

lemma b1722 : Encl e1722 (6941028601 / 12500000000 : ℝ) (111056457617 / 200000000000 : ℝ) := by
  exact Encl.sqrt b1721 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1723 : Encl e1723 (19441028601 / 12500000000 : ℝ) (311056457617 / 200000000000 : ℝ) := by
  exact Encl.add b5 b1722 (by norm_num) (by norm_num)

lemma b1724 : Encl e1724 (267366877777 / 500000000000 : ℝ) (267366877779 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1690 b1723 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1725 : Encl e1725 (17871261833 / 62500000000 : ℝ) (142970094667 / 500000000000 : ℝ) := by
  exact Encl.pow b1724 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1726 : Encl e1726 (80371261833 / 62500000000 : ℝ) (642970094667 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1725 (by norm_num) (by norm_num)

lemma b1727 : Encl e1727 (566996514391 / 500000000000 : ℝ) (566996514393 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1726 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1728 : Encl e1728 (1066996514391 / 500000000000 : ℝ) (1066996514393 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1727 (by norm_num) (by norm_num)

lemma b1729 : Encl e1729 (250578960821 / 1000000000000 : ℝ) (10023158433 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b1724 b1728 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1730 : Encl e1730 (982093972619 / 1000000000000 : ℝ) (245523493159 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e1690) (a := (250578960821 / 1000000000000 : ℝ)) (b := (10023158433 / 40000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (166332387771 / 200000000000 : ℝ) by norm_num).trans b1690.1
        exact b1690.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1690) (250578960821 / 1000000000000 : ℝ) (10023158433 / 40000000000 : ℝ) from b1729) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1731 : Encl e1731 (100173585207 / 200000000000 : ℝ) (100173585209 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1730 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1732 : Encl e1732 (203757175019 / 500000000000 : ℝ) (10187858751 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1690 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1733 : Encl e1733 (113142750357 / 500000000000 : ℝ) (113142750359 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1732 b1722 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1734 : Encl e1734 (274582425317 / 1000000000000 : ℝ) (274582425331 / 1000000000000 : ℝ) := by
  exact Encl.sub b1731 b1733 (by norm_num) (by norm_num)

lemma b1735 : Encl e1735 (6941028601 / 250000000 : ℝ) (111056457617 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1722 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1736 : Encl e1736 (29954563893 / 1000000000000 : ℝ) (14977281947 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1690 b1735 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1737 : Encl e1737 (244627861423 / 1000000000000 : ℝ) (122313930719 / 500000000000 : ℝ) := by
  exact Encl.sub b1734 b1736 (by norm_num) (by norm_num)

lemma b1738 : Encl e1738 (1921516983167 / 1000000000000 : ℝ) (15011851431 / 7812500000 : ℝ) := by
  exact Encl.add b5 b1706 (by norm_num) (by norm_num)

lemma b1739 : Encl e1739 (202099728779 / 1000000000000 : ℝ) (202099728781 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1689 b1738 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1740 : Encl e1740 (10211075093 / 250000000000 : ℝ) (20422150187 / 500000000000 : ℝ) := by
  exact Encl.pow b1739 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1741 : Encl e1741 (260211075093 / 250000000000 : ℝ) (520422150187 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1740 (by norm_num) (by norm_num)

lemma b1742 : Encl e1742 (255054442763 / 250000000000 : ℝ) (510108885527 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1741 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1743 : Encl e1743 (505054442763 / 250000000000 : ℝ) (1010108885527 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1742 (by norm_num) (by norm_num)

lemma b1744 : Encl e1744 (100038585777 / 1000000000000 : ℝ) (100038585779 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1739 b1743 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1745 : Encl e1745 (398827424339 / 1000000000000 : ℝ) (99706856087 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e1689) (a := (100038585777 / 1000000000000 : ℝ)) (b := (100038585779 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (48542257643 / 125000000000 : ℝ) by norm_num).trans b1689.1
        exact b1689.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1689) (100038585777 / 1000000000000 : ℝ) (100038585779 / 1000000000000 : ℝ) from b1744) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1746 : Encl e1746 (50850496603 / 250000000000 : ℝ) (101700993209 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1745 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1747 : Encl e1747 (4757141249 / 25000000000 : ℝ) (95142824981 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1689 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1748 : Encl e1748 (175351458091 / 1000000000000 : ℝ) (87675729047 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1747 b1706 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1749 : Encl e1749 (14025264159 / 500000000000 : ℝ) (28050528327 / 1000000000000 : ℝ) := by
  exact Encl.sub b1746 b1748 (by norm_num) (by norm_num)

lemma b1750 : Encl e1750 (921516983167 / 20000000000 : ℝ) (7199351431 / 156250000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1706 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1751 : Encl e1751 (2107058623 / 250000000000 : ℝ) (8428234493 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1689 b1750 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1752 : Encl e1752 (784891753 / 40000000000 : ℝ) (3924458767 / 200000000000 : ℝ) := by
  exact Encl.sub b1749 b1751 (by norm_num) (by norm_num)

lemma b1753 : Encl e1753 (56251391897 / 250000000000 : ℝ) (225005567613 / 1000000000000 : ℝ) := by
  exact Encl.sub b1737 b1752 (by norm_num) (by norm_num)

lemma b1754 : Encl e1754 (11526924569 / 62500000000 : ℝ) (92215396563 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1753 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1755 : Encl e1755 (-8623189879 / 40000000000 : ℝ) (-26947468367 / 125000000000 : ℝ) := by
  exact Encl.add b1719 b1754 (by norm_num) (by norm_num)

lemma b1756 : Encl e1756 (364281051493 / 200000000000 : ℝ) (455351314367 / 250000000000 : ℝ) := by
  exact Encl.add b1690 b4 (by norm_num) (by norm_num)

lemma b1757 : Encl e1757 (227675657183 / 250000000000 : ℝ) (455351314367 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1756 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1758 : Encl e1758 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1690 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1759 : Encl e1759 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1758 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1760 : Encl e1760 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1758 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1761 : Encl e1761 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1760 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1762 : Encl e1762 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1761 (by norm_num) (by norm_num)

lemma b1763 : Encl e1763 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1762 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1764 : Encl e1764 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1759 b1763 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1765 : Encl e1765 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1760 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1766 : Encl e1766 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1764 b1765 (by norm_num) (by norm_num)

lemma b1767 : Encl e1767 (310408489311 / 500000000000 : ℝ) (310408489323 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1757 b1766 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1768 : Encl e1768 (373238782267 / 500000000000 : ℝ) (746477564537 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1757 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1769 : Encl e1769 (82693564617 / 62500000000 : ℝ) (1323097033879 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1768 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1770 : Encl e1770 (34826797147 / 62500000000 : ℝ) (278614377179 / 500000000000 : ℝ) := by
  exact Encl.pow b1768 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1771 : Encl e1771 (21882322013 / 50000000000 : ℝ) (218823220133 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1770 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1772 : Encl e1772 (71882322013 / 50000000000 : ℝ) (718823220133 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1771 (by norm_num) (by norm_num)

lemma b1773 : Encl e1773 (599509474541 / 500000000000 : ℝ) (599509474543 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1772 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1774 : Encl e1774 (793209207543 / 500000000000 : ℝ) (1586418415101 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1769 b1773 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1775 : Encl e1775 (21882322013 / 25000000000 : ℝ) (875292880531 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1770 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1776 : Encl e1776 (142225106911 / 200000000000 : ℝ) (711125534581 / 1000000000000 : ℝ) := by
  exact Encl.sub b1774 b1775 (by norm_num) (by norm_num)

lemma b1777 : Encl e1777 (591416040837 / 1000000000000 : ℝ) (591416040861 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1690 b1776 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1778 : Encl e1778 (29400937761 / 1000000000000 : ℝ) (29400937809 / 1000000000000 : ℝ) := by
  exact Encl.sub b1767 b1777 (by norm_num) (by norm_num)

lemma b1779 : Encl e1779 (829379277979 / 1000000000000 : ℝ) (25918102437 / 31250000000 : ℝ) := by
  exact Encl.pow b1757 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1780 : Encl e1780 (812791692419 / 1000000000000 : ℝ) (32511667697 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1779 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1781 : Encl e1781 (7488332303 / 40000000000 : ℝ) (187208307581 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1780 (by norm_num) (by norm_num)

lemma b1782 : Encl e1782 (5331897563 / 31250000000 : ℝ) (170620722021 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1779 (by norm_num) (by norm_num)

lemma b1783 : Encl e1783 (206531306353 / 500000000000 : ℝ) (413062612713 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1782 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1784 : Encl e1784 (453220170049 / 1000000000000 : ℝ) (453220170073 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1781 b1783 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1785 : Encl e1785 (546779829927 / 1000000000000 : ℝ) (546779829951 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1784 (by norm_num) (by norm_num)

lemma b1786 : Encl e1786 (677828348929 / 1000000000000 : ℝ) (338914174467 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1720 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1787 : Encl e1787 (161085825533 / 500000000000 : ℝ) (322171651071 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1786 (by norm_num) (by norm_num)

lemma b1788 : Encl e1788 (580194358759 / 1000000000000 : ℝ) (290097179387 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1787 b1722 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1789 : Encl e1789 (209902820613 / 500000000000 : ℝ) (419805641241 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1788 (by norm_num) (by norm_num)

lemma b1790 : Encl e1790 (63487094343 / 500000000000 : ℝ) (5078967549 / 40000000000 : ℝ) := by
  exact Encl.sub b1785 b1789 (by norm_num) (by norm_num)

lemma b1791 : Encl e1791 (1866580109 / 500000000000 : ℝ) (3733160227 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1778 b1790 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1792 : Encl e1792 (29435420727 / 1000000000000 : ℝ) (3679427597 / 125000000000 : ℝ) := by
  exact Encl.sub b1776 b1766 (by norm_num) (by norm_num)

lemma b1793 : Encl e1793 (706531306353 / 500000000000 : ℝ) (1413062612713 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1783 (by norm_num) (by norm_num)

lemma b1794 : Encl e1794 (644488517733 / 1000000000000 : ℝ) (644488517739 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1757 b1793 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1795 : Encl e1795 (415365449489 / 1000000000000 : ℝ) (207682724749 / 500000000000 : ℝ) := by
  exact Encl.pow b1794 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1796 : Encl e1796 (1415365449489 / 1000000000000 : ℝ) (707682724749 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1795 (by norm_num) (by norm_num)

lemma b1797 : Encl e1797 (1189691325297 / 1000000000000 : ℝ) (594845662651 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1796 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1798 : Encl e1798 (2189691325297 / 1000000000000 : ℝ) (1094845662651 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1797 (by norm_num) (by norm_num)

lemma b1799 : Encl e1799 (147164239609 / 500000000000 : ℝ) (147164239611 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1794 b1798 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1800 : Encl e1800 (1144981907199 / 1000000000000 : ℝ) (71561369201 / 62500000000 : ℝ) := by
  apply Encl.arcsin (z := e1757) (a := (147164239609 / 500000000000 : ℝ)) (b := (147164239611 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (227675657183 / 250000000000 : ℝ) by norm_num).trans b1757.1
        exact b1757.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1757) (147164239609 / 500000000000 : ℝ) (147164239611 / 500000000000 : ℝ) from b1799) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1801 : Encl e1801 (583940772671 / 1000000000000 : ℝ) (583940772681 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1800 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1802 : Encl e1802 (223122144039 / 500000000000 : ℝ) (5578053601 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1757 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1803 : Encl e1803 (92163415769 / 500000000000 : ℝ) (184326831543 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1802 b1783 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1804 : Encl e1804 (49951742641 / 125000000000 : ℝ) (399613941143 / 1000000000000 : ℝ) := by
  exact Encl.sub b1801 b1803 (by norm_num) (by norm_num)

lemma b1805 : Encl e1805 (206531306353 / 10000000000 : ℝ) (413062612713 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1783 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1806 : Encl e1806 (44095137187 / 1000000000000 : ℝ) (44095137189 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1757 b1805 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1807 : Encl e1807 (355518803939 / 1000000000000 : ℝ) (88879700989 / 250000000000 : ℝ) := by
  exact Encl.sub b1804 b1806 (by norm_num) (by norm_num)

lemma b1808 : Encl e1808 (110890942501 / 1000000000000 : ℝ) (110890942533 / 1000000000000 : ℝ) := by
  exact Encl.sub b1807 b1737 (by norm_num) (by norm_num)

lemma b1809 : Encl e1809 (3264121547 / 1000000000000 : ℝ) (1632060777 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1792 b1808 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1810 : Encl e1810 (1399456353 / 200000000000 : ℝ) (6997281781 / 1000000000000 : ℝ) := by
  exact Encl.add b1791 b1809 (by norm_num) (by norm_num)

lemma b1811 : Encl e1811 (632325519 / 8000000000 : ℝ) (79040689879 / 1000000000000 : ℝ) := by
  exact Encl.sub b1757 b1690 (by norm_num) (by norm_num)

lemma b1812 : Encl e1812 (44263794861 / 500000000000 : ℝ) (8852758993 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1810 b1811 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1813 : Encl e1813 (-127052157253 / 1000000000000 : ℝ) (-63526078503 / 500000000000 : ℝ) := by
  exact Encl.add b1755 b1812 (by norm_num) (by norm_num)

lemma b1814 : Encl e1814 (351915873259 / 500000000000 : ℝ) (351915873273 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1776 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1815 : Encl e1815 (405632507627 / 500000000000 : ℝ) (162253003051 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1816 : Encl e1816 (1437929800391 / 1000000000000 : ℝ) (287585960079 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1815 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1817 : Encl e1817 (26326036999 / 40000000000 : ℝ) (658150924977 / 1000000000000 : ℝ) := by
  exact Encl.pow b1815 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1818 : Encl e1818 (516910527713 / 1000000000000 : ℝ) (129227631929 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1817 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1819 : Encl e1819 (1516910527713 / 1000000000000 : ℝ) (379227631929 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1818 (by norm_num) (by norm_num)

lemma b1820 : Encl e1820 (246325843363 / 200000000000 : ℝ) (1231629216817 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1819 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

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
lemma b1821 : Encl e1821 (177099635389 / 100000000000 : ℝ) (1770996353899 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1816 b1820 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1822 : Encl e1822 (516910527713 / 500000000000 : ℝ) (1033821055431 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1817 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1823 : Encl e1823 (737175298459 / 1000000000000 : ℝ) (737175298473 / 1000000000000 : ℝ) := by
  exact Encl.sub b1821 b1822 (by norm_num) (by norm_num)

lemma b1824 : Encl e1824 (335673741071 / 500000000000 : ℝ) (335673741079 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1757 b1823 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1825 : Encl e1825 (812106609 / 25000000000 : ℝ) (8121066101 / 250000000000 : ℝ) := by
  exact Encl.sub b1814 b1824 (by norm_num) (by norm_num)

lemma b1826 : Encl e1826 (21652521253 / 125000000000 : ℝ) (173220170101 / 1000000000000 : ℝ) := by
  exact Encl.sub b165 b1785 (by norm_num) (by norm_num)

lemma b1827 : Encl e1827 (1125385959 / 200000000000 : ℝ) (2813464903 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1825 b1826 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1828 : Encl e1828 (13024881939 / 500000000000 : ℝ) (13024881959 / 500000000000 : ℝ) := by
  exact Encl.sub b1823 b1776 (by norm_num) (by norm_num)

lemma b1829 : Encl e1829 (41158491389 / 250000000000 : ℝ) (20579245713 / 125000000000 : ℝ) := by
  exact Encl.sub b183 b1807 (by norm_num) (by norm_num)

lemma b1830 : Encl e1830 (4288675929 / 1000000000000 : ℝ) (214433797 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b1828 b1829 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1831 : Encl e1831 (2478901431 / 250000000000 : ℝ) (4957802873 / 500000000000 : ℝ) := by
  exact Encl.add b1827 b1830 (by norm_num) (by norm_num)

lemma b1832 : Encl e1832 (19760172469 / 250000000000 : ℝ) (79040689879 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b1757 (by norm_num) (by norm_num)

lemma b1833 : Encl e1833 (62724691163 / 500000000000 : ℝ) (12544938261 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1831 b1832 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1834 : Encl e1834 (-1602774927 / 1000000000000 : ℝ) (-400693599 / 250000000000 : ℝ) := by
  exact Encl.add b1813 b1833 (by norm_num) (by norm_num)

lemma b1835 : Encl e1835 (786885245901 / 1000000000000 : ℝ) (393442622951 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1836 : Encl e1836 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b1835 (by norm_num) (by norm_num)

lemma b1837 : Encl e1837 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b1836 b5 (by norm_num) (by norm_num)

lemma b1838 : Encl e1838 (61 / 25 : ℝ) (61 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1839 : Encl e1839 (1806406308167 / 1000000000000 : ℝ) (180640630817 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1838 b1699 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1840 : Encl e1840 (287498493177 / 500000000000 : ℝ) (143749246589 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1839 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1841 : Encl e1841 (25668710017 / 100000000000 : ℝ) (256687100173 / 1000000000000 : ℝ) := by
  exact Encl.add b1837 b1840 (by norm_num) (by norm_num)

lemma b1842 : Encl e1842 (3721 / 1250 : ℝ) (3721 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b1693 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1843 : Encl e1843 (550953923991 / 250000000000 : ℝ) (68869240499 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b1842 b1699 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1844 : Encl e1844 (5345408349553 / 1000000000000 : ℝ) (2672704174779 / 500000000000 : ℝ) := by
  exact Encl.add b0 b1843 (by norm_num) (by norm_num)

lemma b1845 : Encl e1845 (2312013916383 / 1000000000000 : ℝ) (1156006958193 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1844 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1846 : Encl e1846 (1471873773157 / 1000000000000 : ℝ) (735936886581 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b1845 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1847 : Encl e1847 (226981 / 125000 : ℝ) (226981 / 125000 : ℝ) := by
  exact Encl.pow b1688 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1848 : Encl e1848 (15207727 / 62500000 : ℝ) (15207727 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b1847 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1849 : Encl e1849 (15207727 / 62500000 : ℝ) (15207727 / 62500000 : ℝ) := by
  exact Encl.min b1848 b941 (by norm_num) (by norm_num)

lemma b1850 : Encl e1850 (25668710017 / 50000000000 : ℝ) (256687100173 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1841 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1851 : Encl e1851 (45623181 / 31250000 : ℝ) (45623181 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b1849 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1852 : Encl e1852 (2166412404107 / 1000000000000 : ℝ) (2166412404123 / 1000000000000 : ℝ) := by
  exact Encl.pow b1846 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1853 : Encl e1853 (3162836007463 / 1000000000000 : ℝ) (3162836007487 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1851 b1852 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1854 : Encl e1854 (202964800767 / 250000000000 : ℝ) (162371840617 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1853 b1841 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1855 : Encl e1855 (1449748576907 / 500000000000 : ℝ) (23195977231 / 8000000000 : ℝ) := by
  exact Encl.div_nonneg b1854 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1856 : Encl e1856 (1949748576907 / 500000000000 : ℝ) (31195977231 / 8000000000 : ℝ) := by
  exact Encl.add b5 b1855 (by norm_num) (by norm_num)

lemma b1857 : Encl e1857 (1974714448677 / 1000000000000 : ℝ) (1974714448693 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1856 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1858 : Encl e1858 (2974714448677 / 1000000000000 : ℝ) (2974714448693 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1857 (by norm_num) (by norm_num)

lemma b1859 : Encl e1859 (86289660603 / 500000000000 : ℝ) (17257932121 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1850 b1858 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1860 : Encl e1860 (450684031 / 200000000000 : ℝ) (563355039 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1849 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1861 : Encl e1861 (1051347237 / 12500000000 : ℝ) (84107778967 / 1000000000000 : ℝ) := by
  exact Encl.sub b1841 b1859 (by norm_num) (by norm_num)

lemma b1862 : Encl e1862 (3571458559 / 62500000000 : ℝ) (1142866739 / 20000000000 : ℝ) := by
  exact Encl.div_nonneg b1861 b1846 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1863 : Encl e1863 (3265360957 / 1000000000000 : ℝ) (1632680479 / 500000000000 : ℝ) := by
  exact Encl.pow b1862 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1864 : Encl e1864 (914301067 / 1000000000000 : ℝ) (914301069 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1863 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1865 : Encl e1865 (2570018643 / 500000000000 : ℝ) (5140037287 / 1000000000000 : ℝ) := by
  exact Encl.pow b1859 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1866 : Encl e1866 (1250692541 / 1000000000000 : ℝ) (625346271 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1849 b1865 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1867 : Encl e1867 (270624201 / 125000000000 : ℝ) (2164993611 / 1000000000000 : ℝ) := by
  exact Encl.add b1864 b1866 (by norm_num) (by norm_num)

lemma b1868 : Encl e1868 (270624201 / 125000000000 : ℝ) (2164993611 / 1000000000000 : ℝ) := by
  exact Encl.min b1860 b1867 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_122 : Encl (twoChordBaseline (61 / 50 : ℝ)) (-1602774927 / 1000000000000 : ℝ) (-400693599 / 250000000000 : ℝ) := by
  exact b1834

lemma gain_enclosure_122 : Encl (gain (61 / 50 : ℝ)) (270624201 / 125000000000 : ℝ) (2164993611 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b1868

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

lemma baseline_lower_122 : (-1602774927 / 1000000000000 : ℝ) ≤ baseline (61 / 50 : ℝ) :=
  (baseline_enclosure_122).1.trans (twoChordBaseline_le_of_range (h := (61 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_122_oai : (562218681 / 1000000000000 : ℝ) ≤ baseline (61 / 50 : ℝ) + gain (61 / 50 : ℝ) := by
  have hb := baseline_lower_122
  have hg := (gain_enclosure_122).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_122_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_122_oai

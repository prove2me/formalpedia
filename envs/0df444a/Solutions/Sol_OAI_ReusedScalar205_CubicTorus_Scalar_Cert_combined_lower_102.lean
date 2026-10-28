-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_102
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:37:54.149922+00:00
-- url     : https://prove2.me/submissions/05c5b055-d0ce-4b6c-9196-9845f322a3f2

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
lemma b777 : Encl e777 (51 / 50 : ℝ) (51 / 50 : ℝ) := by
  exact Encl.exact (51 / 50 : ℝ)

lemma b778 : Encl e778 (324676083907 / 1000000000000 : ℝ) (81169020977 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b777 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b779 : Encl e779 (173830979023 / 250000000000 : ℝ) (347661958047 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b777 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b780 : Encl e780 (2499 / 2500 : ℝ) (2499 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b781 : Encl e781 (318182562229 / 1000000000000 : ℝ) (31818256223 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b780 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b782 : Encl e782 (2601 / 2500 : ℝ) (2601 / 2500 : ℝ) := by
  exact Encl.pow b777 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b783 : Encl e783 (2601 / 625 : ℝ) (2601 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b782 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b784 : Encl e784 (662339211171 / 500000000000 : ℝ) (1324678422343 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b783 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b785 : Encl e785 (1162339211171 / 500000000000 : ℝ) (2324678422343 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b784 (by norm_num) (by norm_num)

lemma b786 : Encl e786 (1524689615083 / 1000000000000 : ℝ) (381172403771 / 250000000000 : ℝ) := by
  exact Encl.sqrt b785 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b787 : Encl e787 (2524689615083 / 1000000000000 : ℝ) (631172403771 / 250000000000 : ℝ) := by
  exact Encl.add b5 b786 (by norm_num) (by norm_num)

lemma b788 : Encl e788 (158435317201 / 200000000000 : ℝ) (396088293003 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b787 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b789 : Encl e789 (221809444081 / 1000000000000 : ℝ) (110904722041 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b788 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b790 : Encl e790 (53999200631 / 100000000000 : ℝ) (67499000789 / 125000000000 : ℝ) := by
  exact Encl.add b781 b789 (by norm_num) (by norm_num)

lemma b791 : Encl e791 (-46000799369 / 100000000000 : ℝ) (-57500999211 / 125000000000 : ℝ) := by
  exact Encl.sub b790 b5 (by norm_num) (by norm_num)

lemma b792 : Encl e792 (3019600781997 / 1000000000000 : ℝ) (1509800390999 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b782 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b793 : Encl e793 (105414559461 / 1000000000000 : ℝ) (52707279731 / 500000000000 : ℝ) := by
  exact Encl.pow b778 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b794 : Encl e794 (447292720269 / 500000000000 : ℝ) (894585440539 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b793 (by norm_num) (by norm_num)

lemma b795 : Encl e795 (945825269559 / 1000000000000 : ℝ) (945825269561 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b794 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b796 : Encl e796 (-55831720579 / 200000000000 : ℝ) (-69789650723 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b795 (by norm_num) (by norm_num)

lemma b797 : Encl e797 (423060757719 / 500000000000 : ℝ) (169224303089 / 200000000000 : ℝ) := by
  exact Encl.pow b795 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b798 : Encl e798 (141020252573 / 500000000000 : ℝ) (282040505149 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b797 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b799 : Encl e799 (2881902251 / 1000000000000 : ℝ) (2881902257 / 1000000000000 : ℝ) := by
  exact Encl.add b796 b798 (by norm_num) (by norm_num)

lemma b800 : Encl e800 (564852841 / 200000000000 : ℝ) (706066053 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b799 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b801 : Encl e801 (111452466807 / 1000000000000 : ℝ) (111452466809 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b793 b795 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b802 : Encl e802 (-1888547533193 / 1000000000000 : ℝ) (-1888547533191 / 1000000000000 : ℝ) := by
  exact Encl.sub b801 b23 (by norm_num) (by norm_num)

lemma b803 : Encl e803 (945825269559 / 500000000000 : ℝ) (945825269561 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b795 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b804 : Encl e804 (124120237 / 40000000000 : ℝ) (3103005931 / 1000000000000 : ℝ) := by
  exact Encl.add b802 b803 (by norm_num) (by norm_num)

lemma b805 : Encl e805 (31030059 / 500000000000 : ℝ) (62060119 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b804 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b806 : Encl e806 (1381102043 / 500000000000 : ℝ) (1381102047 / 500000000000 : ℝ) := by
  exact Encl.sub b800 b805 (by norm_num) (by norm_num)

lemma b807 : Encl e807 (4170376809 / 500000000000 : ℝ) (8340753643 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b792 b806 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b808 : Encl e808 (-56458405009 / 125000000000 : ℝ) (-90333448009 / 200000000000 : ℝ) := by
  exact Encl.add b791 b807 (by norm_num) (by norm_num)

lemma b809 : Encl e809 (483475348289 / 1000000000000 : ℝ) (483475348293 / 1000000000000 : ℝ) := by
  exact Encl.pow b779 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b810 : Encl e810 (516524651707 / 1000000000000 : ℝ) (516524651711 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b809 (by norm_num) (by norm_num)

lemma b811 : Encl e811 (2807408183 / 3906250000 : ℝ) (718696494851 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b810 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b812 : Encl e812 (6713658183 / 3906250000 : ℝ) (1718696494851 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b811 (by norm_num) (by norm_num)

lemma b813 : Encl e813 (202282345421 / 500000000000 : ℝ) (80912938169 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b779 b812 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b814 : Encl e814 (40918147269 / 250000000000 : ℝ) (163672589079 / 1000000000000 : ℝ) := by
  exact Encl.pow b813 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b815 : Encl e815 (290918147269 / 250000000000 : ℝ) (1163672589079 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b814 (by norm_num) (by norm_num)

lemma b816 : Encl e816 (1078736570751 / 1000000000000 : ℝ) (1078736570753 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b815 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b817 : Encl e817 (2078736570751 / 1000000000000 : ℝ) (2078736570753 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b816 (by norm_num) (by norm_num)

lemma b818 : Encl e818 (194620471171 / 1000000000000 : ℝ) (97310235587 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b813 b817 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b819 : Encl e819 (768870502009 / 1000000000000 : ℝ) (768870502021 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e779) (a := (194620471171 / 1000000000000 : ℝ)) (b := (97310235587 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (173830979023 / 250000000000 : ℝ) by norm_num).trans b779.1
        exact b779.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e779) (194620471171 / 1000000000000 : ℝ) (97310235587 / 500000000000 : ℝ) from b818) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b820 : Encl e820 (49015494503 / 125000000000 : ℝ) (392123956031 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b819 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b821 : Encl e821 (68141743777 / 200000000000 : ℝ) (340708718887 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b779 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b822 : Encl e822 (122433081013 / 500000000000 : ℝ) (24486616203 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b821 b811 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b823 : Encl e823 (73628896997 / 500000000000 : ℝ) (29451558801 / 200000000000 : ℝ) := by
  exact Encl.sub b820 b822 (by norm_num) (by norm_num)

lemma b824 : Encl e824 (2807408183 / 78125000 : ℝ) (718696494851 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b811 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b825 : Encl e825 (4837396043 / 250000000000 : ℝ) (19349584173 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b779 b824 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b826 : Encl e826 (127908209821 / 1000000000000 : ℝ) (127908209833 / 1000000000000 : ℝ) := by
  exact Encl.sub b823 b825 (by norm_num) (by norm_num)

lemma b827 : Encl e827 (1945825269559 / 1000000000000 : ℝ) (1945825269561 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b795 (by norm_num) (by norm_num)

lemma b828 : Encl e828 (10428611223 / 62500000000 : ℝ) (16685777957 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b778 b827 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b829 : Encl e829 (13920759301 / 500000000000 : ℝ) (6960379651 / 250000000000 : ℝ) := by
  exact Encl.pow b828 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b830 : Encl e830 (513920759301 / 500000000000 : ℝ) (256960379651 / 250000000000 : ℝ) := by
  exact Encl.add b5 b829 (by norm_num) (by norm_num)

lemma b831 : Encl e831 (1013825191343 / 1000000000000 : ℝ) (202765038269 / 200000000000 : ℝ) := by
  exact Encl.sqrt b830 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b832 : Encl e832 (2013825191343 / 1000000000000 : ℝ) (402765038269 / 200000000000 : ℝ) := by
  exact Encl.add b5 b831 (by norm_num) (by norm_num)

lemma b833 : Encl e833 (82856138797 / 1000000000000 : ℝ) (82856138799 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b828 b832 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b834 : Encl e834 (330669238673 / 1000000000000 : ℝ) (165334619341 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e778) (a := (82856138797 / 1000000000000 : ℝ)) (b := (82856138799 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (324676083907 / 1000000000000 : ℝ) by norm_num).trans b778.1
        exact b778.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e778) (82856138797 / 1000000000000 : ℝ) (82856138799 / 1000000000000 : ℝ) from b833) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b835 : Encl e835 (168641311723 / 1000000000000 : ℝ) (10540081983 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b834 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b836 : Encl e836 (79545640557 / 500000000000 : ℝ) (31818256223 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b778 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b837 : Encl e837 (37618138461 / 250000000000 : ℝ) (75236276923 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b836 b795 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b838 : Encl e838 (18168757877 / 1000000000000 : ℝ) (4542189471 / 250000000000 : ℝ) := by
  exact Encl.sub b835 b837 (by norm_num) (by norm_num)

lemma b839 : Encl e839 (945825269559 / 20000000000 : ℝ) (945825269561 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b795 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b840 : Encl e840 (68654559 / 10000000000 : ℝ) (6865455901 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b778 b839 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b841 : Encl e841 (1412912747 / 125000000000 : ℝ) (353228187 / 31250000000 : ℝ) := by
  exact Encl.sub b838 b840 (by norm_num) (by norm_num)

lemma b842 : Encl e842 (116604907837 / 1000000000000 : ℝ) (116604907857 / 1000000000000 : ℝ) := by
  exact Encl.sub b826 b841 (by norm_num) (by norm_num)

lemma b843 : Encl e843 (22863707419 / 200000000000 : ℝ) (22863707423 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b842 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b844 : Encl e844 (-337348702977 / 1000000000000 : ℝ) (-33734870293 / 100000000000 : ℝ) := by
  exact Encl.add b808 b843 (by norm_num) (by norm_num)

lemma b845 : Encl e845 (842533617351 / 500000000000 : ℝ) (337013446941 / 200000000000 : ℝ) := by
  exact Encl.add b779 b4 (by norm_num) (by norm_num)

lemma b846 : Encl e846 (842533617351 / 1000000000000 : ℝ) (842533617353 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b845 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b847 : Encl e847 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b779 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b848 : Encl e848 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b847 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b849 : Encl e849 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b847 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b850 : Encl e850 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b849 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b851 : Encl e851 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b850 (by norm_num) (by norm_num)

lemma b852 : Encl e852 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b851 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b853 : Encl e853 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b848 b852 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b854 : Encl e854 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b849 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b855 : Encl e855 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b853 b854 (by norm_num) (by norm_num)

lemma b856 : Encl e856 (71793354687 / 125000000000 : ℝ) (287173418759 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b846 b855 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b857 : Encl e857 (103251668793 / 125000000000 : ℝ) (826013350347 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b846 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b858 : Encl e858 (366017635929 / 250000000000 : ℝ) (1464070543723 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b857 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b859 : Encl e859 (341149027473 / 500000000000 : ℝ) (85287256869 / 125000000000 : ℝ) := by
  exact Encl.pow b857 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b860 : Encl e860 (535875639243 / 1000000000000 : ℝ) (2143502557 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b859 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b861 : Encl e861 (1535875639243 / 1000000000000 : ℝ) (6143502557 / 4000000000 : ℝ) := by
  exact Encl.add b5 b860 (by norm_num) (by norm_num)

lemma b862 : Encl e862 (1239304498193 / 1000000000000 : ℝ) (1239304498197 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b861 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b863 : Encl e863 (1814429210499 / 1000000000000 : ℝ) (907214605257 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b858 b862 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b864 : Encl e864 (1071751278487 / 1000000000000 : ℝ) (535875639249 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b859 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b865 : Encl e865 (742677932001 / 1000000000000 : ℝ) (742677932027 / 1000000000000 : ℝ) := by
  exact Encl.sub b863 b864 (by norm_num) (by norm_num)

lemma b866 : Encl e866 (258200864037 / 500000000000 : ℝ) (258200864047 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b779 b865 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b867 : Encl e867 (28972554701 / 500000000000 : ℝ) (14486277361 / 250000000000 : ℝ) := by
  exact Encl.sub b856 b866 (by norm_num) (by norm_num)

lemma b868 : Encl e868 (354931448183 / 500000000000 : ℝ) (70986289637 / 100000000000 : ℝ) := by
  exact Encl.pow b846 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b869 : Encl e869 (347832819219 / 500000000000 : ℝ) (695665638443 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b868 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b870 : Encl e870 (304334361557 / 1000000000000 : ℝ) (152167180781 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b869 (by norm_num) (by norm_num)

lemma b871 : Encl e871 (29013710363 / 100000000000 : ℝ) (145068551817 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b868 (by norm_num) (by norm_num)

lemma b872 : Encl e872 (134660940799 / 250000000000 : ℝ) (5260193 / 9765625 : ℝ) := by
  exact Encl.sqrt b871 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b873 : Encl e873 (282500589767 / 500000000000 : ℝ) (565001179549 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b870 b872 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b874 : Encl e874 (434998820451 / 1000000000000 : ℝ) (217499410233 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b873 (by norm_num) (by norm_num)

lemma b875 : Encl e875 (473805841323 / 1000000000000 : ℝ) (29612865083 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b809 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b876 : Encl e876 (32887134917 / 62500000000 : ℝ) (526194158677 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b875 (by norm_num) (by norm_num)

lemma b877 : Encl e877 (146430144697 / 200000000000 : ℝ) (91518840437 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b876 b811 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b878 : Encl e878 (33481159563 / 125000000000 : ℝ) (53569855303 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b877 (by norm_num) (by norm_num)

lemma b879 : Encl e879 (326463953 / 1953125000 : ℝ) (83574771981 / 500000000000 : ℝ) := by
  exact Encl.sub b874 b878 (by norm_num) (by norm_num)

lemma b880 : Encl e880 (9685498609 / 1000000000000 : ℝ) (9685498619 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b867 b879 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b881 : Encl e881 (60987818173 / 1000000000000 : ℝ) (30493909111 / 500000000000 : ℝ) := by
  exact Encl.sub b865 b855 (by norm_num) (by norm_num)

lemma b882 : Encl e882 (384660940799 / 250000000000 : ℝ) (15025818 / 9765625 : ℝ) := by
  exact Encl.add b5 b872 (by norm_num) (by norm_num)

lemma b883 : Encl e883 (547581992337 / 1000000000000 : ℝ) (547581992341 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b846 b882 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b884 : Encl e884 (299846038331 / 1000000000000 : ℝ) (299846038337 / 1000000000000 : ℝ) := by
  exact Encl.pow b883 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b885 : Encl e885 (1299846038331 / 1000000000000 : ℝ) (1299846038337 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b884 (by norm_num) (by norm_num)

lemma b886 : Encl e886 (1140107906441 / 1000000000000 : ℝ) (228021581289 / 200000000000 : ℝ) := by
  exact Encl.sqrt b885 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b887 : Encl e887 (2140107906441 / 1000000000000 : ℝ) (428021581289 / 200000000000 : ℝ) := by
  exact Encl.add b5 b886 (by norm_num) (by norm_num)

lemma b888 : Encl e888 (127933266983 / 500000000000 : ℝ) (25586653397 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b883 b887 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b889 : Encl e889 (500984879807 / 500000000000 : ℝ) (100196975963 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e846) (a := (127933266983 / 500000000000 : ℝ)) (b := (25586653397 / 100000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (842533617351 / 1000000000000 : ℝ) by norm_num).trans b846.1
        exact b846.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e846) (127933266983 / 500000000000 : ℝ) (25586653397 / 100000000000 : ℝ) from b888) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b890 : Encl e890 (511004577403 / 1000000000000 : ℝ) (127751144353 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b889 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b891 : Encl e891 (412841472501 / 1000000000000 : ℝ) (412841472503 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b846 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b892 : Encl e892 (222374484351 / 1000000000000 : ℝ) (44474896871 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b891 b872 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b893 : Encl e893 (36078761631 / 125000000000 : ℝ) (288630093061 / 1000000000000 : ℝ) := by
  exact Encl.sub b890 b892 (by norm_num) (by norm_num)

lemma b894 : Encl e894 (134660940799 / 5000000000 : ℝ) (10520386 / 390625 : ℝ) := by
  exact Encl.mul_nonneg b43 b872 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b895 : Encl e895 (31283518901 / 1000000000000 : ℝ) (15641759451 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b846 b894 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b896 : Encl e896 (128673287073 / 500000000000 : ℝ) (3216832177 / 12500000000 : ℝ) := by
  exact Encl.sub b893 b895 (by norm_num) (by norm_num)

lemma b897 : Encl e897 (129438364313 / 1000000000000 : ℝ) (129438364339 / 1000000000000 : ℝ) := by
  exact Encl.sub b896 b826 (by norm_num) (by norm_num)

lemma b898 : Encl e898 (7894163427 / 1000000000000 : ℝ) (1973540859 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b881 b897 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b899 : Encl e899 (4394915509 / 250000000000 : ℝ) (3515932411 / 200000000000 : ℝ) := by
  exact Encl.add b880 b898 (by norm_num) (by norm_num)

lemma b900 : Encl e900 (147209701257 / 1000000000000 : ℝ) (147209701261 / 1000000000000 : ℝ) := by
  exact Encl.sub b846 b779 (by norm_num) (by norm_num)

lemma b901 : Encl e901 (119419181517 / 1000000000000 : ℝ) (2388383633 / 20000000000 : ℝ) := by
  exact Encl.div_nonneg b899 b900 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b902 : Encl e902 (-10896476073 / 50000000000 : ℝ) (-340514877 / 1562500000 : ℝ) := by
  exact Encl.add b844 b901 (by norm_num) (by norm_num)

lemma b903 : Encl e903 (735060521077 / 1000000000000 : ℝ) (45941282569 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b865 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b904 : Encl e904 (121292073359 / 125000000000 : ℝ) (485168293437 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b905 : Encl e905 (68795072803 / 40000000000 : ℝ) (21498460251 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b904 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b906 : Encl e906 (470776545911 / 500000000000 : ℝ) (941553091827 / 1000000000000 : ℝ) := by
  exact Encl.pow b904 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b907 : Encl e907 (739494069057 / 1000000000000 : ℝ) (739494069063 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b906 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b908 : Encl e908 (1739494069057 / 1000000000000 : ℝ) (1739494069063 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b907 (by norm_num) (by norm_num)

lemma b909 : Encl e909 (164862351157 / 125000000000 : ℝ) (1318898809259 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b908 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b910 : Encl e910 (2268343490063 / 1000000000000 : ℝ) (567085872519 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b905 b909 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b911 : Encl e911 (295797627623 / 200000000000 : ℝ) (2366381021 / 1600000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b906 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b912 : Encl e912 (394677675969 / 500000000000 : ℝ) (789355351961 / 1000000000000 : ℝ) := by
  exact Encl.sub b910 b911 (by norm_num) (by norm_num)

lemma b913 : Encl e913 (665058420043 / 1000000000000 : ℝ) (133011684013 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b846 b912 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b914 : Encl e914 (17500525253 / 250000000000 : ℝ) (70002101061 / 1000000000000 : ℝ) := by
  exact Encl.sub b903 b913 (by norm_num) (by norm_num)

lemma b915 : Encl e915 (285001179509 / 1000000000000 : ℝ) (285001179577 / 1000000000000 : ℝ) := by
  exact Encl.sub b165 b874 (by norm_num) (by norm_num)

lemma b916 : Encl e916 (4987670339 / 250000000000 : ℝ) (623458793 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b914 b915 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b917 : Encl e917 (46677419911 / 1000000000000 : ℝ) (1166935499 / 25000000000 : ℝ) := by
  exact Encl.sub b912 b865 (by norm_num) (by norm_num)

lemma b918 : Encl e918 (32850774419 / 125000000000 : ℝ) (262806195497 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b896 (by norm_num) (by norm_num)

lemma b919 : Encl e919 (2453423027 / 200000000000 : ℝ) (3066778789 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b917 b918 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b920 : Encl e920 (32217796491 / 1000000000000 : ℝ) (8054449133 / 250000000000 : ℝ) := by
  exact Encl.add b916 b919 (by norm_num) (by norm_num)

lemma b921 : Encl e921 (147209701257 / 1000000000000 : ℝ) (7360485063 / 50000000000 : ℝ) := by
  exact Encl.sub b4 b846 (by norm_num) (by norm_num)

lemma b922 : Encl e922 (218856476273 / 1000000000000 : ℝ) (218856476557 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b920 b921 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b923 : Encl e923 (926954813 / 1000000000000 : ℝ) (926955277 / 1000000000000 : ℝ) := by
  exact Encl.add b902 b922 (by norm_num) (by norm_num)

lemma b924 : Encl e924 (24 / 25 : ℝ) (24 / 25 : ℝ) := by
  exact Encl.exact (24 / 25 : ℝ)

lemma b925 : Encl e925 (235294117647 / 250000000000 : ℝ) (941176470589 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b926 : Encl e926 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b925 (by norm_num) (by norm_num)

lemma b927 : Encl e927 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b926 b5 (by norm_num) (by norm_num)

lemma b928 : Encl e928 (51 / 25 : ℝ) (51 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b929 : Encl e929 (32320804709 / 20000000000 : ℝ) (1616040235453 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b928 b788 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b930 : Encl e930 (257200791707 / 500000000000 : ℝ) (64300197927 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b929 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b931 : Encl e931 (19609169723 / 100000000000 : ℝ) (196091697233 / 1000000000000 : ℝ) := by
  exact Encl.add b927 b930 (by norm_num) (by norm_num)

lemma b932 : Encl e932 (636619772367 / 1000000000000 : ℝ) (39788735773 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b23 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b933 : Encl e933 (2601 / 1250 : ℝ) (2601 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b782 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b934 : Encl e934 (1648361040159 / 1000000000000 : ℝ) (824180520081 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b933 b788 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b935 : Encl e935 (1197488423437 / 250000000000 : ℝ) (598744211719 / 125000000000 : ℝ) := by
  exact Encl.add b0 b934 (by norm_num) (by norm_num)

lemma b936 : Encl e936 (437719256773 / 200000000000 : ℝ) (1094298141933 / 500000000000 : ℝ) := by
  exact Encl.sqrt b935 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b937 : Encl e937 (1393303668037 / 1000000000000 : ℝ) (1393303668041 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b936 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b938 : Encl e938 (132651 / 125000 : ℝ) (132651 / 125000 : ℝ) := by
  exact Encl.pow b777 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b939 : Encl e939 (67 / 500 : ℝ) (67 / 500 : ℝ) := by
  exact Encl.exact (67 / 500 : ℝ)

lemma b940 : Encl e940 (8887617 / 62500000 : ℝ) (8887617 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b938 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b941 : Encl e941 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.exact (9 / 25 : ℝ)

lemma b942 : Encl e942 (8887617 / 62500000 : ℝ) (8887617 / 62500000 : ℝ) := by
  exact Encl.min b940 b941 (by norm_num) (by norm_num)

lemma b943 : Encl e943 (19609169723 / 50000000000 : ℝ) (196091697233 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b931 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

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

lemma b945 : Encl e945 (26662851 / 31250000 : ℝ) (26662851 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b942 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b946 : Encl e946 (388259022273 / 200000000000 : ℝ) (1941295111377 / 1000000000000 : ℝ) := by
  exact Encl.pow b937 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b947 : Encl e947 (1656334793643 / 1000000000000 : ℝ) (828167396827 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b945 b946 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b948 : Encl e948 (162396750433 / 500000000000 : ℝ) (162396750437 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b947 b931 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b949 : Encl e949 (1159976788807 / 1000000000000 : ℝ) (289994197209 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b948 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b950 : Encl e950 (2159976788807 / 1000000000000 : ℝ) (539994197209 / 250000000000 : ℝ) := by
  exact Encl.add b5 b949 (by norm_num) (by norm_num)

lemma b951 : Encl e951 (18371074363 / 12500000000 : ℝ) (1469685949051 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b950 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b952 : Encl e952 (30871074363 / 12500000000 : ℝ) (2469685949051 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b951 (by norm_num) (by norm_num)

lemma b953 : Encl e953 (1270391143 / 8000000000 : ℝ) (158798892879 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b943 b952 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b954 : Encl e954 (9261 / 1000000 : ℝ) (9261 / 1000000 : ℝ) := by
  exact Encl.pow b10 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b955 : Encl e955 (82308221 / 62500000000 : ℝ) (1316931537 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b942 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b956 : Encl e956 (37292804351 / 1000000000000 : ℝ) (18646402179 / 500000000000 : ℝ) := by
  exact Encl.sub b931 b953 (by norm_num) (by norm_num)

lemma b957 : Encl e957 (26765740453 / 1000000000000 : ℝ) (26765740459 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b956 b937 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b958 : Encl e958 (716404861 / 1000000000000 : ℝ) (716404863 / 1000000000000 : ℝ) := by
  exact Encl.pow b957 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b959 : Encl e959 (200593361 / 1000000000000 : ℝ) (100296681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b958 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b960 : Encl e960 (1001111429 / 250000000000 : ℝ) (4004445717 / 1000000000000 : ℝ) := by
  exact Encl.pow b953 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b961 : Encl e961 (569439677 / 1000000000000 : ℝ) (284719839 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b942 b960 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b962 : Encl e962 (385016519 / 500000000000 : ℝ) (9625413 / 12500000000 : ℝ) := by
  exact Encl.add b959 b961 (by norm_num) (by norm_num)

lemma b963 : Encl e963 (385016519 / 500000000000 : ℝ) (9625413 / 12500000000 : ℝ) := by
  exact Encl.min b955 b962 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_102 : Encl (twoChordBaseline (51 / 50 : ℝ)) (926954813 / 1000000000000 : ℝ) (926955277 / 1000000000000 : ℝ) := by
  exact b923

lemma gain_enclosure_102 : Encl (gain (51 / 50 : ℝ)) (385016519 / 500000000000 : ℝ) (9625413 / 12500000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b963

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

lemma baseline_lower_102 : (926954813 / 1000000000000 : ℝ) ≤ baseline (51 / 50 : ℝ) :=
  (baseline_enclosure_102).1.trans (twoChordBaseline_le_of_range (h := (51 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_102_oai : (1696987851 / 1000000000000 : ℝ) ≤ baseline (51 / 50 : ℝ) + gain (51 / 50 : ℝ) := by
  have hb := baseline_lower_102
  have hg := (gain_enclosure_102).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_102_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_102_oai

-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_106
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:38:17.129834+00:00
-- url     : https://prove2.me/submissions/3b826a5f-e22d-4547-958e-4953de29c564

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

lemma b964 : Encl e964 (53 / 50 : ℝ) (53 / 50 : ℝ) := by
  exact Encl.exact (53 / 50 : ℝ)

lemma b965 : Encl e965 (168704239677 / 500000000000 : ℝ) (67481695871 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b964 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b966 : Encl e966 (180647880161 / 250000000000 : ℝ) (722591520647 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b964 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b967 : Encl e967 (2597 / 2500 : ℝ) (2597 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b968 : Encl e968 (330660309767 / 1000000000000 : ℝ) (41332538721 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b967 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b969 : Encl e969 (2809 / 2500 : ℝ) (2809 / 2500 : ℝ) := by
  exact Encl.pow b964 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b970 : Encl e970 (2809 / 625 : ℝ) (2809 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b969 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b971 : Encl e971 (89413247029 / 62500000000 : ℝ) (286122390493 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b970 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b972 : Encl e972 (151913247029 / 62500000000 : ℝ) (486122390493 / 200000000000 : ℝ) := by
  exact Encl.add b5 b971 (by norm_num) (by norm_num)

lemma b973 : Encl e973 (15590419983 / 10000000000 : ℝ) (1559041998301 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b972 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b974 : Encl e974 (25590419983 / 10000000000 : ℝ) (2559041998301 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b973 (by norm_num) (by norm_num)

lemma b975 : Encl e975 (195385617091 / 250000000000 : ℝ) (156308493673 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b974 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b976 : Encl e976 (218831891141 / 1000000000000 : ℝ) (218831891143 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b975 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b977 : Encl e977 (137373050227 / 250000000000 : ℝ) (549492200911 / 1000000000000 : ℝ) := by
  exact Encl.add b968 b976 (by norm_num) (by norm_num)

lemma b978 : Encl e978 (-112626949773 / 250000000000 : ℝ) (-450507799089 / 1000000000000 : ℝ) := by
  exact Encl.sub b977 b5 (by norm_num) (by norm_num)

lemma b979 : Encl e979 (2796006277669 / 1000000000000 : ℝ) (279600627767 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b969 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b980 : Encl e980 (113844481939 / 1000000000000 : ℝ) (113844481941 / 1000000000000 : ℝ) := by
  exact Encl.pow b965 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b981 : Encl e981 (886155518059 / 1000000000000 : ℝ) (886155518061 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b980 (by norm_num) (by norm_num)

lemma b982 : Encl e982 (941358336691 / 1000000000000 : ℝ) (941358336693 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b981 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b983 : Encl e983 (-274691670027 / 1000000000000 : ℝ) (-34336458753 / 125000000000 : ℝ) := by
  exact Encl.sub b29 b982 (by norm_num) (by norm_num)

lemma b984 : Encl e984 (52136867783 / 62500000000 : ℝ) (417094942267 / 500000000000 : ℝ) := by
  exact Encl.pow b982 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b985 : Encl e985 (139031647421 / 500000000000 : ℝ) (55612658969 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b984 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b986 : Encl e986 (674324963 / 200000000000 : ℝ) (3371624821 / 1000000000000 : ℝ) := by
  exact Encl.add b983 b985 (by norm_num) (by norm_num)

lemma b987 : Encl e987 (1652096159 / 500000000000 : ℝ) (132167693 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b986 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b988 : Encl e988 (12093639319 / 100000000000 : ℝ) (120936393193 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b980 b982 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b989 : Encl e989 (-187906360681 / 100000000000 : ℝ) (-1879063606807 / 1000000000000 : ℝ) := by
  exact Encl.sub b988 b23 (by norm_num) (by norm_num)

lemma b990 : Encl e990 (941358336691 / 500000000000 : ℝ) (941358336693 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b982 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b991 : Encl e991 (913266643 / 250000000000 : ℝ) (3653066579 / 1000000000000 : ℝ) := by
  exact Encl.add b989 b990 (by norm_num) (by norm_num)

lemma b992 : Encl e992 (73061331 / 1000000000000 : ℝ) (18265333 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b991 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b993 : Encl e993 (1615565493 / 500000000000 : ℝ) (1615565497 / 500000000000 : ℝ) := by
  exact Encl.sub b987 b992 (by norm_num) (by norm_num)

lemma b994 : Encl e994 (225856563 / 25000000000 : ℝ) (564641409 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b979 b993 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b995 : Encl e995 (-110368384143 / 250000000000 : ℝ) (-88294707309 / 200000000000 : ℝ) := by
  exact Encl.add b978 b994 (by norm_num) (by norm_num)

lemma b996 : Encl e996 (261069252853 / 500000000000 : ℝ) (522138505711 / 1000000000000 : ℝ) := by
  exact Encl.pow b966 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b997 : Encl e997 (477861494289 / 1000000000000 : ℝ) (238930747147 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b996 (by norm_num) (by norm_num)

lemma b998 : Encl e998 (138255053331 / 200000000000 : ℝ) (691275266659 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b997 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b999 : Encl e999 (338255053331 / 200000000000 : ℝ) (1691275266659 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b998 (by norm_num) (by norm_num)

lemma b1000 : Encl e1000 (1668931831 / 3906250000 : ℝ) (21362327437 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b966 b999 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1001 : Encl e1001 (91269806703 / 500000000000 : ℝ) (182539613411 / 1000000000000 : ℝ) := by
  exact Encl.pow b1000 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1002 : Encl e1002 (591269806703 / 500000000000 : ℝ) (1182539613411 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1001 (by norm_num) (by norm_num)

lemma b1003 : Encl e1003 (1087446372657 / 1000000000000 : ℝ) (54372318633 / 50000000000 : ℝ) := by
  exact Encl.sqrt b1002 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1004 : Encl e1004 (2087446372657 / 1000000000000 : ℝ) (104372318633 / 50000000000 : ℝ) := by
  exact Encl.add b5 b1003 (by norm_num) (by norm_num)

lemma b1005 : Encl e1005 (204674263411 / 1000000000000 : ℝ) (40934852683 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1000 b1004 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1006 : Encl e1006 (807543909073 / 1000000000000 : ℝ) (807543909089 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e966) (a := (204674263411 / 1000000000000 : ℝ)) (b := (40934852683 / 200000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (180647880161 / 250000000000 : ℝ) by norm_num).trans b966.1
        exact b966.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e966) (204674263411 / 1000000000000 : ℝ) (40934852683 / 200000000000 : ℝ) from b1005) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1007 : Encl e1007 (411847393627 / 1000000000000 : ℝ) (102961848409 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1006 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1008 : Encl e1008 (70813969023 / 200000000000 : ℝ) (177034922559 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b966 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1009 : Encl e1009 (61189931649 / 250000000000 : ℝ) (1223798633 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b1008 b998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1010 : Encl e1010 (167087667027 / 1000000000000 : ℝ) (1044297919 / 6250000000 : ℝ) := by
  exact Encl.sub b1007 b1009 (by norm_num) (by norm_num)

lemma b1011 : Encl e1011 (138255053331 / 4000000000 : ℝ) (691275266659 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1012 : Encl e1012 (10453021473 / 500000000000 : ℝ) (5226510737 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b966 b1011 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1013 : Encl e1013 (146181624079 / 1000000000000 : ℝ) (73090812047 / 500000000000 : ℝ) := by
  exact Encl.sub b1010 b1012 (by norm_num) (by norm_num)

lemma b1014 : Encl e1014 (1941358336691 / 1000000000000 : ℝ) (1941358336693 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b982 (by norm_num) (by norm_num)

lemma b1015 : Encl e1015 (86900103133 / 500000000000 : ℝ) (173800206267 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b965 b1014 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1016 : Encl e1016 (15103255849 / 500000000000 : ℝ) (30206511699 / 1000000000000 : ℝ) := by
  exact Encl.pow b1015 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1017 : Encl e1017 (515103255849 / 500000000000 : ℝ) (1030206511699 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1016 (by norm_num) (by norm_num)

lemma b1018 : Encl e1018 (1014990892421 / 1000000000000 : ℝ) (507495446211 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1017 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1019 : Encl e1019 (2014990892421 / 1000000000000 : ℝ) (1007495446211 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1018 (by norm_num) (by norm_num)

lemma b1020 : Encl e1020 (43126796979 / 500000000000 : ℝ) (2156339849 / 25000000000 : ℝ) := by
  exact Encl.div_nonneg b1015 b1019 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1021 : Encl e1021 (344162575749 / 1000000000000 : ℝ) (172081287879 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e965) (a := (43126796979 / 500000000000 : ℝ)) (b := (2156339849 / 25000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (168704239677 / 500000000000 : ℝ) by norm_num).trans b965.1
        exact b965.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e965) (43126796979 / 500000000000 : ℝ) (2156339849 / 25000000000 : ℝ) from b1020) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1022 : Encl e1022 (175522913631 / 1000000000000 : ℝ) (175522913637 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1021 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1023 : Encl e1023 (165330154883 / 1000000000000 : ℝ) (41332538721 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b965 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1024 : Encl e1024 (31126983921 / 200000000000 : ℝ) (155634919607 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1023 b982 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1025 : Encl e1025 (2485999253 / 125000000000 : ℝ) (1242999627 / 62500000000 : ℝ) := by
  exact Encl.sub b1022 b1024 (by norm_num) (by norm_num)

lemma b1026 : Encl e1026 (941358336691 / 20000000000 : ℝ) (941358336693 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b982 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1027 : Encl e1027 (1792136247 / 250000000000 : ℝ) (7168544989 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b965 b1026 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1028 : Encl e1028 (2543889807 / 200000000000 : ℝ) (3179862261 / 250000000000 : ℝ) := by
  exact Encl.sub b1025 b1027 (by norm_num) (by norm_num)

lemma b1029 : Encl e1029 (26692435007 / 200000000000 : ℝ) (133462175059 / 1000000000000 : ℝ) := by
  exact Encl.sub b1013 b1028 (by norm_num) (by norm_num)

lemma b1030 : Encl e1030 (125907712297 / 1000000000000 : ℝ) (393461601 / 3125000000 : ℝ) := by
  exact Encl.div_nonneg b1029 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1031 : Encl e1031 (-12622632971 / 40000000000 : ℝ) (-12622632969 / 40000000000 : ℝ) := by
  exact Encl.add b995 b1030 (by norm_num) (by norm_num)

lemma b1032 : Encl e1032 (856167419627 / 500000000000 : ℝ) (856167419629 / 500000000000 : ℝ) := by
  exact Encl.add b966 b4 (by norm_num) (by norm_num)

lemma b1033 : Encl e1033 (856167419627 / 1000000000000 : ℝ) (856167419629 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1032 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1034 : Encl e1034 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b966 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1035 : Encl e1035 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1034 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1036 : Encl e1036 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1034 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1037 : Encl e1037 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1036 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1038 : Encl e1038 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1037 (by norm_num) (by norm_num)

lemma b1039 : Encl e1039 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1038 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1040 : Encl e1040 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1035 b1039 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1041 : Encl e1041 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1036 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1042 : Encl e1042 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1040 b1041 (by norm_num) (by norm_num)

lemma b1043 : Encl e1043 (583640865721 / 1000000000000 : ℝ) (583640865743 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1033 b1042 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1044 : Encl e1044 (161541022571 / 200000000000 : ℝ) (403852556429 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1033 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1045 : Encl e1045 (57264801507 / 40000000000 : ℝ) (715810018841 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1044 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1046 : Encl e1046 (163096887333 / 250000000000 : ℝ) (652387549337 / 1000000000000 : ℝ) := by
  exact Encl.pow b1044 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1047 : Encl e1047 (128095995767 / 250000000000 : ℝ) (256191991537 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1046 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1048 : Encl e1048 (378095995767 / 250000000000 : ℝ) (756191991537 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1047 (by norm_num) (by norm_num)

lemma b1049 : Encl e1049 (122979021913 / 100000000000 : ℝ) (1229790219133 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1048 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1050 : Encl e1050 (1760592319843 / 1000000000000 : ℝ) (1760592319857 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1045 b1049 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1051 : Encl e1051 (128095995767 / 125000000000 : ℝ) (512383983073 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1046 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1052 : Encl e1052 (735824353697 / 1000000000000 : ℝ) (735824353721 / 1000000000000 : ℝ) := by
  exact Encl.sub b1050 b1051 (by norm_num) (by norm_num)

lemma b1053 : Encl e1053 (66462554833 / 125000000000 : ℝ) (106340087737 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b966 b1052 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1054 : Encl e1054 (12985106759 / 250000000000 : ℝ) (51940427079 / 1000000000000 : ℝ) := by
  exact Encl.sub b1043 b1053 (by norm_num) (by norm_num)

lemma b1055 : Encl e1055 (73302265043 / 100000000000 : ℝ) (146604530087 / 200000000000 : ℝ) := by
  exact Encl.pow b1033 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1056 : Encl e1056 (718362197421 / 1000000000000 : ℝ) (718362197427 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1055 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1057 : Encl e1057 (281637802573 / 1000000000000 : ℝ) (281637802579 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1056 (by norm_num) (by norm_num)

lemma b1058 : Encl e1058 (53395469913 / 200000000000 : ℝ) (26697734957 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b1055 (by norm_num) (by norm_num)

lemma b1059 : Encl e1059 (10333970187 / 20000000000 : ℝ) (129174627339 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1058 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1060 : Encl e1060 (272535915503 / 500000000000 : ℝ) (21802873241 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b1057 b1059 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1061 : Encl e1061 (18197126759 / 40000000000 : ℝ) (227464084497 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b1060 (by norm_num) (by norm_num)

lemma b1062 : Encl e1062 (511695735591 / 1000000000000 : ℝ) (511695735597 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b996 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1063 : Encl e1063 (488304264403 / 1000000000000 : ℝ) (488304264409 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1062 (by norm_num) (by norm_num)

lemma b1064 : Encl e1064 (353190898007 / 500000000000 : ℝ) (176595449007 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1063 b998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1065 : Encl e1065 (73404550993 / 250000000000 : ℝ) (146809101993 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b1064 (by norm_num) (by norm_num)

lemma b1066 : Encl e1066 (161309964989 / 1000000000000 : ℝ) (80654982511 / 500000000000 : ℝ) := by
  exact Encl.sub b1061 b1065 (by norm_num) (by norm_num)

lemma b1067 : Encl e1067 (4189254233 / 500000000000 : ℝ) (2094627119 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1054 b1066 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1068 : Encl e1068 (54134239869 / 1000000000000 : ℝ) (13533559979 / 250000000000 : ℝ) := by
  exact Encl.sub b1052 b1042 (by norm_num) (by norm_num)

lemma b1069 : Encl e1069 (30333970187 / 20000000000 : ℝ) (379174627339 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1059 (by norm_num) (by norm_num)

lemma b1070 : Encl e1070 (282247069653 / 500000000000 : ℝ) (564494139311 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1033 b1069 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1071 : Encl e1071 (31865363331 / 100000000000 : ℝ) (318653633317 / 1000000000000 : ℝ) := by
  exact Encl.pow b1070 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1072 : Encl e1072 (131865363331 / 100000000000 : ℝ) (1318653633317 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1071 (by norm_num) (by norm_num)

lemma b1073 : Encl e1073 (1148326448929 / 1000000000000 : ℝ) (1148326448933 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1072 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1074 : Encl e1074 (2148326448929 / 1000000000000 : ℝ) (2148326448933 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1073 (by norm_num) (by norm_num)

lemma b1075 : Encl e1075 (3284499311 / 12500000000 : ℝ) (262759944883 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1070 b1074 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1076 : Encl e1076 (256951502631 / 250000000000 : ℝ) (128475751317 / 125000000000 : ℝ) := by
  apply Encl.arcsin (z := e1033) (a := (3284499311 / 12500000000 : ℝ)) (b := (262759944883 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (856167419627 / 1000000000000 : ℝ) by norm_num).trans b1033.1
        exact b1033.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1033) (3284499311 / 12500000000 : ℝ) (262759944883 / 1000000000000 : ℝ) from b1075) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1077 : Encl e1077 (524181065367 / 1000000000000 : ℝ) (262090532687 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1076 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1078 : Encl e1078 (419522035617 / 1000000000000 : ℝ) (419522035619 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1033 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1079 : Encl e1079 (108383205221 / 500000000000 : ℝ) (216766410447 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1078 b1059 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1080 : Encl e1080 (7685366373 / 25000000000 : ℝ) (76853663733 / 250000000000 : ℝ) := by
  exact Encl.sub b1077 b1079 (by norm_num) (by norm_num)

lemma b1081 : Encl e1081 (10333970187 / 400000000 : ℝ) (129174627339 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1059 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1082 : Encl e1082 (33139922183 / 1000000000000 : ℝ) (6627984437 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1033 b1081 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1083 : Encl e1083 (54854946547 / 200000000000 : ℝ) (274274732749 / 1000000000000 : ℝ) := by
  exact Encl.sub b1080 b1082 (by norm_num) (by norm_num)

lemma b1084 : Encl e1084 (128093108641 / 1000000000000 : ℝ) (12809310867 / 100000000000 : ℝ) := by
  exact Encl.sub b1083 b1013 (by norm_num) (by norm_num)

lemma b1085 : Encl e1085 (1733555767 / 250000000000 : ℝ) (6934223077 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1068 b1084 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1086 : Encl e1086 (7656365767 / 500000000000 : ℝ) (15312731553 / 1000000000000 : ℝ) := by
  exact Encl.add b1067 b1085 (by norm_num) (by norm_num)

lemma b1087 : Encl e1087 (6678794949 / 50000000000 : ℝ) (26715179797 / 200000000000 : ℝ) := by
  exact Encl.sub b1033 b966 (by norm_num) (by norm_num)

lemma b1088 : Encl e1088 (22927386827 / 200000000000 : ℝ) (57318467141 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1086 b1087 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1089 : Encl e1089 (-10046444507 / 50000000000 : ℝ) (-200928889943 / 1000000000000 : ℝ) := by
  exact Encl.add b1031 b1088 (by norm_num) (by norm_num)

lemma b1090 : Encl e1090 (364138618871 / 500000000000 : ℝ) (728277237767 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1052 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1091 : Encl e1091 (116715013987 / 125000000000 : ℝ) (466860055949 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1092 : Encl e1092 (1654975807997 / 1000000000000 : ℝ) (827487904001 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1091 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1093 : Encl e1093 (871833247359 / 1000000000000 : ℝ) (871833247363 / 1000000000000 : ℝ) := by
  exact Encl.pow b1091 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1094 : Encl e1094 (21398007227 / 31250000000 : ℝ) (684736231269 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1093 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1095 : Encl e1095 (52648007227 / 31250000000 : ℝ) (1684736231269 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1094 (by norm_num) (by norm_num)

lemma b1096 : Encl e1096 (1297973894677 / 1000000000000 : ℝ) (32449347367 / 25000000000 : ℝ) := by
  exact Encl.sqrt b1095 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1097 : Encl e1097 (1074057697551 / 500000000000 : ℝ) (1074057697557 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1092 b1096 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1098 : Encl e1098 (21398007227 / 15625000000 : ℝ) (171184057817 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1093 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1099 : Encl e1099 (389321466283 / 500000000000 : ℝ) (389321466293 / 500000000000 : ℝ) := by
  exact Encl.sub b1097 b1098 (by norm_num) (by norm_num)

lemma b1100 : Encl e1100 (133329742077 / 200000000000 : ℝ) (133329742081 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1033 b1099 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1101 : Encl e1101 (61628527337 / 1000000000000 : ℝ) (30814263691 / 500000000000 : ℝ) := by
  exact Encl.sub b1090 b1100 (by norm_num) (by norm_num)

lemma b1102 : Encl e1102 (265071830981 / 1000000000000 : ℝ) (265071831053 / 1000000000000 : ℝ) := by
  exact Encl.sub b165 b1061 (by norm_num) (by norm_num)

lemma b1103 : Encl e1103 (16335986581 / 1000000000000 : ℝ) (16335986599 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1101 b1102 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1104 : Encl e1104 (8563715769 / 200000000000 : ℝ) (42818578889 / 1000000000000 : ℝ) := by
  exact Encl.sub b1099 b1052 (by norm_num) (by norm_num)

lemma b1105 : Encl e1105 (245878036763 / 1000000000000 : ℝ) (61469509227 / 250000000000 : ℝ) := by
  exact Encl.sub b183 b1083 (by norm_num) (by norm_num)

lemma b1106 : Encl e1106 (10528148103 / 1000000000000 : ℝ) (10528148121 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1104 b1105 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1107 : Encl e1107 (6716033671 / 250000000000 : ℝ) (83950421 / 3125000000 : ℝ) := by
  exact Encl.add b1103 b1106 (by norm_num) (by norm_num)

lemma b1108 : Encl e1108 (133575898981 / 1000000000000 : ℝ) (16696987373 / 125000000000 : ℝ) := by
  exact Encl.sub b4 b1033 (by norm_num) (by norm_num)

lemma b1109 : Encl e1109 (50278783239 / 250000000000 : ℝ) (201115133231 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1107 b1108 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1110 : Encl e1110 (727511 / 3906250000 : ℝ) (23280411 / 125000000000 : ℝ) := by
  exact Encl.add b1089 b1109 (by norm_num) (by norm_num)

lemma b1111 : Encl e1111 (452830188679 / 500000000000 : ℝ) (905660377359 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1112 : Encl e1112 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b1111 (by norm_num) (by norm_num)

lemma b1113 : Encl e1113 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b1112 b5 (by norm_num) (by norm_num)

lemma b1114 : Encl e1114 (53 / 25 : ℝ) (53 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1115 : Encl e1115 (1656870032931 / 1000000000000 : ℝ) (828435016467 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1114 b975 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1116 : Encl e1116 (527398111603 / 1000000000000 : ℝ) (105479622321 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1115 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1117 : Encl e1117 (209088225419 / 1000000000000 : ℝ) (104544112711 / 500000000000 : ℝ) := by
  exact Encl.add b1113 b1116 (by norm_num) (by norm_num)

lemma b1118 : Encl e1118 (2809 / 1250 : ℝ) (2809 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b969 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1119 : Encl e1119 (1756282234907 / 1000000000000 : ℝ) (175628223491 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1118 b975 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1120 : Encl e1120 (306117180531 / 62500000000 : ℝ) (9795749777 / 2000000000 : ℝ) := by
  exact Encl.add b0 b1119 (by norm_num) (by norm_num)

lemma b1121 : Encl e1121 (2213114296301 / 1000000000000 : ℝ) (2213114296303 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1120 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1122 : Encl e1122 (1408912319533 / 1000000000000 : ℝ) (1408912319537 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b1121 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1123 : Encl e1123 (148877 / 125000 : ℝ) (148877 / 125000 : ℝ) := by
  exact Encl.pow b964 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1124 : Encl e1124 (9974759 / 62500000 : ℝ) (9974759 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b1123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1125 : Encl e1125 (9974759 / 62500000 : ℝ) (9974759 / 62500000 : ℝ) := by
  exact Encl.min b1124 b941 (by norm_num) (by norm_num)

lemma b1126 : Encl e1126 (209088225419 / 500000000000 : ℝ) (104544112711 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1117 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1127 : Encl e1127 (29924277 / 31250000 : ℝ) (29924277 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b1125 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1128 : Encl e1128 (1985033924131 / 1000000000000 : ℝ) (124064620259 / 62500000000 : ℝ) := by
  exact Encl.pow b1122 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1129 : Encl e1129 (950411280001 / 500000000000 : ℝ) (118801410001 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b1127 b1128 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1130 : Encl e1130 (397439615907 / 1000000000000 : ℝ) (99359903979 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1129 b1117 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1131 : Encl e1131 (1419427199667 / 1000000000000 : ℝ) (14194271997 / 10000000000 : ℝ) := by
  exact Encl.div_nonneg b1130 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1132 : Encl e1132 (2419427199667 / 1000000000000 : ℝ) (24194271997 / 10000000000 : ℝ) := by
  exact Encl.add b5 b1131 (by norm_num) (by norm_num)

lemma b1133 : Encl e1133 (311090160543 / 200000000000 : ℝ) (777725401363 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1132 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1134 : Encl e1134 (511090160543 / 200000000000 : ℝ) (1277725401363 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1133 (by norm_num) (by norm_num)

lemma b1135 : Encl e1135 (163640971053 / 1000000000000 : ℝ) (163640971057 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1126 b1134 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1136 : Encl e1136 (1478019889 / 1000000000000 : ℝ) (147801989 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1125 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1137 : Encl e1137 (22723627181 / 500000000000 : ℝ) (45447254369 / 1000000000000 : ℝ) := by
  exact Encl.sub b1117 b1135 (by norm_num) (by norm_num)

lemma b1138 : Encl e1138 (32256978473 / 1000000000000 : ℝ) (32256978479 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1137 b1122 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1139 : Encl e1139 (52025633 / 50000000000 : ℝ) (1040512661 / 1000000000000 : ℝ) := by
  exact Encl.pow b1138 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1140 : Encl e1140 (36417943 / 125000000000 : ℝ) (145671773 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1139 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1141 : Encl e1141 (876407609 / 200000000000 : ℝ) (4382038047 / 1000000000000 : ℝ) := by
  exact Encl.pow b1135 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1142 : Encl e1142 (349678187 / 500000000000 : ℝ) (87419547 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1125 b1141 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1143 : Encl e1143 (495349959 / 500000000000 : ℝ) (495349961 / 500000000000 : ℝ) := by
  exact Encl.add b1140 b1142 (by norm_num) (by norm_num)

lemma b1144 : Encl e1144 (495349959 / 500000000000 : ℝ) (495349961 / 500000000000 : ℝ) := by
  exact Encl.min b1136 b1143 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_106 : Encl (twoChordBaseline (53 / 50 : ℝ)) (727511 / 3906250000 : ℝ) (23280411 / 125000000000 : ℝ) := by
  exact b1110

lemma gain_enclosure_106 : Encl (gain (53 / 50 : ℝ)) (495349959 / 500000000000 : ℝ) (495349961 / 500000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b1144

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

lemma baseline_lower_106 : (727511 / 3906250000 : ℝ) ≤ baseline (53 / 50 : ℝ) :=
  (baseline_enclosure_106).1.trans (twoChordBaseline_le_of_range (h := (53 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_106_oai : (588471367 / 500000000000 : ℝ) ≤ baseline (53 / 50 : ℝ) + gain (53 / 50 : ℝ) := by
  have hb := baseline_lower_106
  have hg := (gain_enclosure_106).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_106_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_106_oai

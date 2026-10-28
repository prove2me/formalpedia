-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_138
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:43:32.863981+00:00
-- url     : https://prove2.me/submissions/97a148ec-480d-4846-a8ef-f44ee9e819ed

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
lemma b2412 : Encl e2412 (69 / 50 : ℝ) (69 / 50 : ℝ) := by
  exact Encl.exact (69 / 50 : ℝ)

lemma b2413 : Encl e2413 (439267642933 / 1000000000000 : ℝ) (219633821467 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2412 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2414 : Encl e2414 (470366178533 / 500000000000 : ℝ) (235183089267 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2412 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2415 : Encl e2415 (3381 / 2500 : ℝ) (3381 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2416 : Encl e2416 (215241145037 / 500000000000 : ℝ) (17219291603 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b2415 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2417 : Encl e2417 (4761 / 2500 : ℝ) (4761 / 2500 : ℝ) := by
  exact Encl.pow b2412 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2418 : Encl e2418 (4761 / 625 : ℝ) (4761 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b2417 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2419 : Encl e2419 (2424757388993 / 1000000000000 : ℝ) (1212378694497 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2418 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2420 : Encl e2420 (3424757388993 / 1000000000000 : ℝ) (1712378694497 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2419 (by norm_num) (by norm_num)

lemma b2421 : Encl e2421 (462652501141 / 250000000000 : ℝ) (370122000913 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2420 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2422 : Encl e2422 (712652501141 / 250000000000 : ℝ) (570122000913 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2421 (by norm_num) (by norm_num)

lemma b2423 : Encl e2423 (701604216921 / 1000000000000 : ℝ) (350802108461 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2422 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2424 : Encl e2424 (196449180737 / 1000000000000 : ℝ) (196449180739 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2423 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2425 : Encl e2425 (626931470811 / 1000000000000 : ℝ) (313465735407 / 500000000000 : ℝ) := by
  exact Encl.add b2416 b2424 (by norm_num) (by norm_num)

lemma b2426 : Encl e2426 (-373068529189 / 1000000000000 : ℝ) (-186534264593 / 500000000000 : ℝ) := by
  exact Encl.sub b2425 b5 (by norm_num) (by norm_num)

lemma b2427 : Encl e2427 (824824788277 / 500000000000 : ℝ) (329929915311 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2417 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2428 : Encl e2428 (192956062127 / 1000000000000 : ℝ) (192956062129 / 1000000000000 : ℝ) := by
  exact Encl.pow b2413 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2429 : Encl e2429 (807043937871 / 1000000000000 : ℝ) (807043937873 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2428 (by norm_num) (by norm_num)

lemma b2430 : Encl e2430 (112294530273 / 125000000000 : ℝ) (449178121093 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2429 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2431 : Encl e2431 (-1448059847 / 6250000000 : ℝ) (-231689575517 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b2430 (by norm_num) (by norm_num)

lemma b2432 : Encl e2432 (725012959303 / 1000000000000 : ℝ) (181253239827 / 250000000000 : ℝ) := by
  exact Encl.pow b2430 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2433 : Encl e2433 (120835493217 / 500000000000 : ℝ) (60417746609 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2432 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2434 : Encl e2434 (4990705457 / 500000000000 : ℝ) (9981410919 / 1000000000000 : ℝ) := by
  exact Encl.add b2431 b2433 (by norm_num) (by norm_num)

lemma b2435 : Encl e2435 (1956356539 / 200000000000 : ℝ) (9781782701 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2434 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2436 : Encl e2436 (214787912707 / 1000000000000 : ℝ) (214787912711 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2428 b2430 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2437 : Encl e2437 (-1785212087293 / 1000000000000 : ℝ) (-1785212087289 / 1000000000000 : ℝ) := by
  exact Encl.sub b2436 b23 (by norm_num) (by norm_num)

lemma b2438 : Encl e2438 (112294530273 / 62500000000 : ℝ) (449178121093 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2430 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2439 : Encl e2439 (460015883 / 40000000000 : ℝ) (11500397083 / 1000000000000 : ℝ) := by
  exact Encl.add b2437 b2438 (by norm_num) (by norm_num)

lemma b2440 : Encl e2440 (230007941 / 1000000000000 : ℝ) (115003971 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2439 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2441 : Encl e2441 (9551774753 / 1000000000000 : ℝ) (238794369 / 25000000000 : ℝ) := by
  exact Encl.sub b2435 b2440 (by norm_num) (by norm_num)

lemma b2442 : Encl e2442 (1969635147 / 125000000000 : ℝ) (15757081189 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2427 b2441 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2443 : Encl e2443 (-357311448013 / 1000000000000 : ℝ) (-357311447997 / 1000000000000 : ℝ) := by
  exact Encl.add b2426 b2442 (by norm_num) (by norm_num)

lemma b2444 : Encl e2444 (88497736763 / 100000000000 : ℝ) (176995473527 / 200000000000 : ℝ) := by
  exact Encl.pow b2414 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2445 : Encl e2445 (23004526473 / 200000000000 : ℝ) (11502263237 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b2444 (by norm_num) (by norm_num)

lemma b2446 : Encl e2446 (84787466779 / 250000000000 : ℝ) (84787466781 / 250000000000 : ℝ) := by
  exact Encl.sqrt b2445 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2447 : Encl e2447 (334787466779 / 250000000000 : ℝ) (334787466781 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2446 (by norm_num) (by norm_num)

lemma b2448 : Encl e2448 (702484748093 / 1000000000000 : ℝ) (7024847481 / 10000000000 : ℝ) := by
  exact Encl.div_nonneg b2414 b2447 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2449 : Encl e2449 (493484821303 / 1000000000000 : ℝ) (246742410657 / 500000000000 : ℝ) := by
  exact Encl.pow b2448 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2450 : Encl e2450 (1493484821303 / 1000000000000 : ℝ) (746742410657 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2449 (by norm_num) (by norm_num)

lemma b2451 : Encl e2451 (611041083173 / 500000000000 : ℝ) (76380135397 / 62500000000 : ℝ) := by
  exact Encl.sqrt b2450 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2452 : Encl e2452 (1111041083173 / 500000000000 : ℝ) (138880135397 / 62500000000 : ℝ) := by
  exact Encl.add b5 b2451 (by norm_num) (by norm_num)

lemma b2453 : Encl e2453 (316138061287 / 1000000000000 : ℝ) (79034515323 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2448 b2452 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2454 : Encl e2454 (1224783269243 / 1000000000000 : ℝ) (1224783269269 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2414) (a := (316138061287 / 1000000000000 : ℝ)) (b := (79034515323 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (470366178533 / 500000000000 : ℝ) by norm_num).trans b2414.1
        exact b2414.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2414) (316138061287 / 1000000000000 : ℝ) (79034515323 / 250000000000 : ℝ) from b2453) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2455 : Encl e2455 (624639467313 / 1000000000000 : ℝ) (9759991677 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2454 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2456 : Encl e2456 (230479427481 / 500000000000 : ℝ) (115239713741 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2414 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2457 : Encl e2457 (78167067203 / 500000000000 : ℝ) (156334134411 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2456 b2446 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2458 : Encl e2458 (234152666451 / 500000000000 : ℝ) (234152666461 / 500000000000 : ℝ) := by
  exact Encl.sub b2455 b2457 (by norm_num) (by norm_num)

lemma b2459 : Encl e2459 (84787466779 / 5000000000 : ℝ) (84787466781 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2446 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2460 : Encl e2460 (55475908927 / 1000000000000 : ℝ) (55475908929 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2414 b2459 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2461 : Encl e2461 (412829423973 / 1000000000000 : ℝ) (82565884799 / 200000000000 : ℝ) := by
  exact Encl.sub b2458 b2460 (by norm_num) (by norm_num)

lemma b2462 : Encl e2462 (237294530273 / 125000000000 : ℝ) (949178121093 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2430 (by norm_num) (by norm_num)

lemma b2463 : Encl e2463 (115696841607 / 500000000000 : ℝ) (14462105201 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b2413 b2462 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2464 : Encl e2464 (53543036631 / 1000000000000 : ℝ) (53543036633 / 1000000000000 : ℝ) := by
  exact Encl.pow b2463 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2465 : Encl e2465 (1053543036631 / 1000000000000 : ℝ) (1053543036633 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2464 (by norm_num) (by norm_num)

lemma b2466 : Encl e2466 (513211222751 / 500000000000 : ℝ) (16037850711 / 15625000000 : ℝ) := by
  exact Encl.sqrt b2465 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2467 : Encl e2467 (1013211222751 / 500000000000 : ℝ) (31662850711 / 15625000000 : ℝ) := by
  exact Encl.add b5 b2466 (by norm_num) (by norm_num)

lemma b2468 : Encl e2468 (114188274871 / 1000000000000 : ℝ) (57094137437 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2463 b2467 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2469 : Encl e2469 (227391645883 / 500000000000 : ℝ) (454783291779 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2413) (a := (114188274871 / 1000000000000 : ℝ)) (b := (57094137437 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (439267642933 / 1000000000000 : ℝ) by norm_num).trans b2413.1
        exact b2413.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2413) (114188274871 / 1000000000000 : ℝ) (57094137437 / 500000000000 : ℝ) from b2468) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2470 : Encl e2470 (579848697 / 2500000000 : ℝ) (28992434851 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2469 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2471 : Encl e2471 (215241145037 / 1000000000000 : ℝ) (107620572519 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2413 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2472 : Encl e2472 (96681613109 / 500000000000 : ℝ) (193363226221 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2471 b2430 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2473 : Encl e2473 (38576252579 / 1000000000000 : ℝ) (3857625259 / 100000000000 : ℝ) := by
  exact Encl.sub b2470 b2472 (by norm_num) (by norm_num)

lemma b2474 : Encl e2474 (112294530273 / 2500000000 : ℝ) (449178121093 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2430 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2475 : Encl e2475 (9779364183 / 1000000000000 : ℝ) (1222420523 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b2413 b2474 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2476 : Encl e2476 (5759377679 / 200000000000 : ℝ) (28796888407 / 1000000000000 : ℝ) := by
  exact Encl.sub b2473 b2475 (by norm_num) (by norm_num)

lemma b2477 : Encl e2477 (192016267783 / 500000000000 : ℝ) (960081339 / 2500000000 : ℝ) := by
  exact Encl.sub b2461 b2476 (by norm_num) (by norm_num)

lemma b2478 : Encl e2478 (139142223031 / 500000000000 : ℝ) (278284446087 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2477 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2479 : Encl e2479 (-79027001951 / 1000000000000 : ℝ) (-7902700191 / 100000000000 : ℝ) := by
  exact Encl.add b2443 b2478 (by norm_num) (by norm_num)

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures2480To2700
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

lemma b2480 : Encl e2480 (482618918919 / 250000000000 : ℝ) (1930475675679 / 1000000000000 : ℝ) := by
  exact Encl.add b2414 b4 (by norm_num) (by norm_num)

lemma b2481 : Encl e2481 (482618918919 / 500000000000 : ℝ) (12065472973 / 12500000000 : ℝ) := by
  exact Encl.div_nonneg b2480 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2482 : Encl e2482 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2414 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2483 : Encl e2483 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2482 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2484 : Encl e2484 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b2482 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2485 : Encl e2485 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2486 : Encl e2486 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2485 (by norm_num) (by norm_num)

lemma b2487 : Encl e2487 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2486 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2488 : Encl e2488 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2483 b2487 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2489 : Encl e2489 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2490 : Encl e2490 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b2488 b2489 (by norm_num) (by norm_num)

lemma b2491 : Encl e2491 (164498272881 / 250000000000 : ℝ) (657993091549 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2481 b2490 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2492 : Encl e2492 (349723854289 / 500000000000 : ℝ) (34972385429 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b2481 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2493 : Encl e2493 (49589551383 / 40000000000 : ℝ) (61986939229 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2492 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2494 : Encl e2494 (97845419407 / 200000000000 : ℝ) (244613548519 / 500000000000 : ℝ) := by
  exact Encl.pow b2492 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2495 : Encl e2495 (76847612699 / 200000000000 : ℝ) (384238063499 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2494 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2496 : Encl e2496 (276847612699 / 200000000000 : ℝ) (1384238063499 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2495 (by norm_num) (by norm_num)

lemma b2497 : Encl e2497 (588268234629 / 500000000000 : ℝ) (1176536469261 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2496 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2498 : Encl e2498 (729298946203 / 500000000000 : ℝ) (22790592069 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b2493 b2497 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2499 : Encl e2499 (76847612699 / 100000000000 : ℝ) (192119031749 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2494 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2500 : Encl e2500 (69012176541 / 100000000000 : ℝ) (345060882713 / 500000000000 : ℝ) := by
  exact Encl.sub b2498 b2499 (by norm_num) (by norm_num)

lemma b2501 : Encl e2501 (162304968759 / 250000000000 : ℝ) (324609937527 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2414 b2500 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2502 : Encl e2502 (877321647 / 100000000000 : ℝ) (8773216513 / 1000000000000 : ℝ) := by
  exact Encl.sub b2491 b2501 (by norm_num) (by norm_num)

lemma b2503 : Encl e2503 (465842041797 / 500000000000 : ℝ) (931684083599 / 1000000000000 : ℝ) := by
  exact Encl.pow b2481 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2504 : Encl e2504 (456525200961 / 500000000000 : ℝ) (114131300241 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2503 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2505 : Encl e2505 (10868699759 / 125000000000 : ℝ) (43474799039 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2504 (by norm_num) (by norm_num)

lemma b2506 : Encl e2506 (68315916401 / 1000000000000 : ℝ) (34157958203 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2503 (by norm_num) (by norm_num)

lemma b2507 : Encl e2507 (261373136341 / 1000000000000 : ℝ) (8167910511 / 31250000000 : ℝ) := by
  exact Encl.sqrt b2506 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2508 : Encl e2508 (83166157859 / 250000000000 : ℝ) (166332315737 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2505 b2507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2509 : Encl e2509 (333667684263 / 500000000000 : ℝ) (166833842141 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b2508 (by norm_num) (by norm_num)

lemma b2510 : Encl e2510 (867277820277 / 1000000000000 : ℝ) (867277820283 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2444 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2511 : Encl e2511 (132722179717 / 1000000000000 : ℝ) (132722179723 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2510 (by norm_num) (by norm_num)

lemma b2512 : Encl e2512 (48917231209 / 125000000000 : ℝ) (3913378497 / 10000000000 : ℝ) := by
  exact Encl.div_nonneg b2511 b2446 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2513 : Encl e2513 (6086621503 / 10000000000 : ℝ) (76082768791 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b2512 (by norm_num) (by norm_num)

lemma b2514 : Encl e2514 (29336609099 / 500000000000 : ℝ) (7334152283 / 125000000000 : ℝ) := by
  exact Encl.sub b2509 b2513 (by norm_num) (by norm_num)

lemma b2515 : Encl e2515 (128688211 / 250000000000 : ℝ) (32172053 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2502 b2514 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2516 : Encl e2516 (4215825791 / 500000000000 : ℝ) (8431651621 / 1000000000000 : ℝ) := by
  exact Encl.sub b2500 b2490 (by norm_num) (by norm_num)

lemma b2517 : Encl e2517 (1261373136341 / 1000000000000 : ℝ) (39417910511 / 31250000000 : ℝ) := by
  exact Encl.add b5 b2507 (by norm_num) (by norm_num)

lemma b2518 : Encl e2518 (382613918919 / 500000000000 : ℝ) (765227837847 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2481 b2517 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2519 : Encl e2519 (292786821901 / 500000000000 : ℝ) (73196705477 / 125000000000 : ℝ) := by
  exact Encl.pow b2518 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2520 : Encl e2520 (792786821901 / 500000000000 : ℝ) (198196705477 / 125000000000 : ℝ) := by
  exact Encl.add b5 b2519 (by norm_num) (by norm_num)

lemma b2521 : Encl e2521 (1259195633649 / 1000000000000 : ℝ) (157399454207 / 125000000000 : ℝ) := by
  exact Encl.sqrt b2520 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2522 : Encl e2522 (2259195633649 / 1000000000000 : ℝ) (282399454207 / 125000000000 : ℝ) := by
  exact Encl.add b5 b2521 (by norm_num) (by norm_num)

lemma b2523 : Encl e2523 (338716942631 / 1000000000000 : ℝ) (338716942637 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2518 b2522 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2524 : Encl e2524 (326587952167 / 250000000000 : ℝ) (326587952179 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e2481) (a := (338716942631 / 1000000000000 : ℝ)) (b := (338716942637 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (482618918919 / 500000000000 : ℝ) by norm_num).trans b2481.1
        exact b2481.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2481) (338716942631 / 1000000000000 : ℝ) (338716942637 / 1000000000000 : ℝ) from b2523) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2525 : Encl e2525 (33311971121 / 50000000000 : ℝ) (333119711223 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2524 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2526 : Encl e2526 (23648327027 / 50000000000 : ℝ) (236483270271 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2481 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2527 : Encl e2527 (24724149617 / 200000000000 : ℝ) (30905187023 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2526 b2507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2528 : Encl e2528 (67827334291 / 125000000000 : ℝ) (542618674361 / 1000000000000 : ℝ) := by
  exact Encl.sub b2525 b2527 (by norm_num) (by norm_num)

lemma b2529 : Encl e2529 (261373136341 / 20000000000 : ℝ) (8167910511 / 625000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2530 : Encl e2530 (14771798683 / 200000000000 : ℝ) (73858993419 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2481 b2529 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2531 : Encl e2531 (468759680909 / 1000000000000 : ℝ) (234379840473 / 500000000000 : ℝ) := by
  exact Encl.sub b2528 b2530 (by norm_num) (by norm_num)

lemma b2532 : Encl e2532 (27965128457 / 500000000000 : ℝ) (55930256973 / 1000000000000 : ℝ) := by
  exact Encl.sub b2531 b2461 (by norm_num) (by norm_num)

lemma b2533 : Encl e2533 (471584439 / 1000000000000 : ℝ) (235792221 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2516 b2532 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2534 : Encl e2534 (986337283 / 1000000000000 : ℝ) (98633729 / 100000000000 : ℝ) := by
  exact Encl.add b2515 b2533 (by norm_num) (by norm_num)

lemma b2535 : Encl e2535 (2450548077 / 100000000000 : ℝ) (12252740387 / 500000000000 : ℝ) := by
  exact Encl.sub b2481 b2414 (by norm_num) (by norm_num)

lemma b2536 : Encl e2536 (40249660559 / 1000000000000 : ℝ) (10062415213 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2534 b2535 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2537 : Encl e2537 (-2423583837 / 62500000000 : ℝ) (-19388670529 / 500000000000 : ℝ) := by
  exact Encl.add b2479 b2536 (by norm_num) (by norm_num)

lemma b2538 : Encl e2538 (683043406341 / 1000000000000 : ℝ) (683043406359 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b2500 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2539 : Encl e2539 (35860265167 / 50000000000 : ℝ) (358602651671 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2540 : Encl e2540 (635606650897 / 500000000000 : ℝ) (1271213301799 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2539 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2541 : Encl e2541 (514383447139 / 1000000000000 : ℝ) (257191723571 / 500000000000 : ℝ) := by
  exact Encl.pow b2539 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2542 : Encl e2542 (50499476833 / 125000000000 : ℝ) (100998953667 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2543 : Encl e2543 (175499476833 / 125000000000 : ℝ) (350998953667 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2542 (by norm_num) (by norm_num)

lemma b2544 : Encl e2544 (59245164669 / 50000000000 : ℝ) (1184903293383 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2543 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2545 : Encl e2545 (376566206971 / 250000000000 : ℝ) (753132413947 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2540 b2544 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2546 : Encl e2546 (807991629329 / 1000000000000 : ℝ) (161598325867 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2547 : Encl e2547 (698273198549 / 1000000000000 : ℝ) (139654639713 / 200000000000 : ℝ) := by
  exact Encl.sub b2545 b2546 (by norm_num) (by norm_num)

lemma b2548 : Encl e2548 (673999712387 / 1000000000000 : ℝ) (134799942481 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2481 b2547 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2549 : Encl e2549 (565230871 / 62500000000 : ℝ) (2260923493 / 250000000000 : ℝ) := by
  exact Encl.sub b2538 b2548 (by norm_num) (by norm_num)

lemma b2550 : Encl e2550 (52664631411 / 1000000000000 : ℝ) (26332315751 / 500000000000 : ℝ) := by
  exact Encl.sub b165 b2509 (by norm_num) (by norm_num)

lemma b2551 : Encl e2551 (476282807 / 1000000000000 : ℝ) (476282811 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2549 b2550 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2552 : Encl e2552 (8151433123 / 1000000000000 : ℝ) (1630286631 / 200000000000 : ℝ) := by
  exact Encl.sub b2547 b2500 (by norm_num) (by norm_num)

lemma b2553 : Encl e2553 (25696544283 / 500000000000 : ℝ) (25696544367 / 500000000000 : ℝ) := by
  exact Encl.sub b183 b2531 (by norm_num) (by norm_num)

lemma b2554 : Encl e2554 (104731831 / 250000000000 : ℝ) (13091479 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b2552 b2553 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2555 : Encl e2555 (895210131 / 1000000000000 : ℝ) (895210139 / 1000000000000 : ℝ) := by
  exact Encl.add b2551 b2554 (by norm_num) (by norm_num)

lemma b2556 : Encl e2556 (2450548077 / 100000000000 : ℝ) (24505480773 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b2481 (by norm_num) (by norm_num)

lemma b2557 : Encl e2557 (2283188553 / 62500000000 : ℝ) (1826550859 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b2555 b2556 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2558 : Encl e2558 (-35098821 / 15625000000 : ℝ) (-1123161939 / 500000000000 : ℝ) := by
  exact Encl.add b2537 b2557 (by norm_num) (by norm_num)

lemma b2559 : Encl e2559 (695652173913 / 1000000000000 : ℝ) (347826086957 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2560 : Encl e2560 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2559 (by norm_num) (by norm_num)

lemma b2561 : Encl e2561 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b2560 b5 (by norm_num) (by norm_num)

lemma b2562 : Encl e2562 (69 / 25 : ℝ) (69 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2563 : Encl e2563 (1936427638701 / 1000000000000 : ℝ) (387285527741 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2562 b2423 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2564 : Encl e2564 (308192030639 / 500000000000 : ℝ) (3852400383 / 6250000000 : ℝ) := by
  exact Encl.div_nonneg b2563 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2565 : Encl e2565 (149037087547 / 500000000000 : ℝ) (298074175097 / 1000000000000 : ℝ) := by
  exact Encl.add b2561 b2564 (by norm_num) (by norm_num)

lemma b2566 : Encl e2566 (4761 / 1250 : ℝ) (4761 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b2417 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2567 : Encl e2567 (83508441919 / 31250000000 : ℝ) (2672270141413 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2566 b2423 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2568 : Encl e2568 (5813862794997 / 1000000000000 : ℝ) (5813862795003 / 1000000000000 : ℝ) := by
  exact Encl.add b0 b2567 (by norm_num) (by norm_num)

lemma b2569 : Encl e2569 (12055976521 / 5000000000 : ℝ) (1205597652101 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2568 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2570 : Encl e2570 (383753651423 / 250000000000 : ℝ) (11992301607 / 7812500000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2569 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2571 : Encl e2571 (328509 / 125000 : ℝ) (328509 / 125000 : ℝ) := by
  exact Encl.pow b2412 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2572 : Encl e2572 (22010103 / 62500000 : ℝ) (22010103 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2571 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2573 : Encl e2573 (22010103 / 62500000 : ℝ) (22010103 / 62500000 : ℝ) := by
  exact Encl.min b2572 b941 (by norm_num) (by norm_num)

lemma b2574 : Encl e2574 (149037087547 / 250000000000 : ℝ) (298074175097 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2565 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2575 : Encl e2575 (66030309 / 31250000 : ℝ) (66030309 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b2573 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2576 : Encl e2576 (2356269839687 / 1000000000000 : ℝ) (2356269839701 / 1000000000000 : ℝ) := by
  exact Encl.pow b2570 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2577 : Encl e2577 (4978727219261 / 1000000000000 : ℝ) (4978727219291 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2575 b2576 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2578 : Encl e2578 (1484030008899 / 1000000000000 : ℝ) (371007502231 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2577 b2565 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2579 : Encl e2579 (5300107174639 / 1000000000000 : ℝ) (5300107174729 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2578 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2580 : Encl e2580 (6300107174639 / 1000000000000 : ℝ) (6300107174729 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2579 (by norm_num) (by norm_num)

lemma b2581 : Encl e2581 (251000142921 / 100000000000 : ℝ) (2510001429229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2580 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2582 : Encl e2582 (351000142921 / 100000000000 : ℝ) (3510001429229 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2581 (by norm_num) (by norm_num)

lemma b2583 : Encl e2583 (169842765653 / 1000000000000 : ℝ) (169842765657 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2574 b2582 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2584 : Encl e2584 (1630684511 / 500000000000 : ℝ) (3261369023 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2573 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2585 : Encl e2585 (128231409437 / 1000000000000 : ℝ) (32057852361 / 250000000000 : ℝ) := by
  exact Encl.sub b2565 b2583 (by norm_num) (by norm_num)

lemma b2586 : Encl e2586 (83537582613 / 1000000000000 : ℝ) (83537582619 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2585 b2570 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2587 : Encl e2587 (1744631927 / 250000000000 : ℝ) (697852771 / 100000000000 : ℝ) := by
  exact Encl.pow b2586 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2588 : Encl e2588 (976993879 / 500000000000 : ℝ) (1953987759 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2587 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2589 : Encl e2589 (2449690193 / 500000000000 : ℝ) (1224845097 / 250000000000 : ℝ) := by
  exact Encl.pow b2583 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2590 : Encl e2590 (172537387 / 100000000000 : ℝ) (107835867 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2573 b2589 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2591 : Encl e2591 (919840407 / 250000000000 : ℝ) (3679361631 / 1000000000000 : ℝ) := by
  exact Encl.add b2588 b2590 (by norm_num) (by norm_num)

lemma b2592 : Encl e2592 (1630684511 / 500000000000 : ℝ) (3261369023 / 1000000000000 : ℝ) := by
  exact Encl.min b2584 b2591 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_138 : Encl (twoChordBaseline (69 / 50 : ℝ)) (-35098821 / 15625000000 : ℝ) (-1123161939 / 500000000000 : ℝ) := by
  exact b2558

lemma gain_enclosure_138 : Encl (gain (69 / 50 : ℝ)) (1630684511 / 500000000000 : ℝ) (3261369023 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2592

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

lemma baseline_lower_138 : (-35098821 / 15625000000 : ℝ) ≤ baseline (69 / 50 : ℝ) :=
  (baseline_enclosure_138).1.trans (twoChordBaseline_le_of_range (h := (69 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_138_oai : (507522239 / 500000000000 : ℝ) ≤ baseline (69 / 50 : ℝ) + gain (69 / 50 : ℝ) := by
  have hb := baseline_lower_138
  have hg := (gain_enclosure_138).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_138_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_138_oai

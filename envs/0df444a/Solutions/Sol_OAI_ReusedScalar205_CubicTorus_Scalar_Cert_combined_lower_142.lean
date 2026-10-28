-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_142
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:43:34.240992+00:00
-- url     : https://prove2.me/submissions/083c3909-91ea-4222-87fb-8a8be967a8cb

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

lemma b2593 : Encl e2593 (71 / 50 : ℝ) (71 / 50 : ℝ) := by
  exact Encl.exact (71 / 50 : ℝ)

lemma b2594 : Encl e2594 (22600001919 / 50000000000 : ℝ) (452000038381 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2593 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2595 : Encl e2595 (483999980809 / 500000000000 : ℝ) (967999961621 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2593 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2596 : Encl e2596 (3479 / 2500 : ℝ) (3479 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2597 : Encl e2597 (442960037613 / 1000000000000 : ℝ) (221480018807 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2596 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2598 : Encl e2598 (5041 / 2500 : ℝ) (5041 / 2500 : ℝ) := by
  exact Encl.pow b2593 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2599 : Encl e2599 (5041 / 625 : ℝ) (5041 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b2598 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2600 : Encl e2600 (2567360218003 / 1000000000000 : ℝ) (641840054501 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2599 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2601 : Encl e2601 (3567360218003 / 1000000000000 : ℝ) (891840054501 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2600 (by norm_num) (by norm_num)

lemma b2602 : Encl e2602 (236093209149 / 125000000000 : ℝ) (1888745673193 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2601 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2603 : Encl e2603 (361093209149 / 125000000000 : ℝ) (2888745673193 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2602 (by norm_num) (by norm_num)

lemma b2604 : Encl e2604 (69234201493 / 100000000000 : ℝ) (692342014931 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2603 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2605 : Encl e2605 (9692788209 / 50000000000 : ℝ) (193855764181 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2604 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2606 : Encl e2606 (636815801793 / 1000000000000 : ℝ) (127363160359 / 200000000000 : ℝ) := by
  exact Encl.add b2597 b2605 (by norm_num) (by norm_num)

lemma b2607 : Encl e2607 (-363184198207 / 1000000000000 : ℝ) (-72636839641 / 200000000000 : ℝ) := by
  exact Encl.sub b2606 b5 (by norm_num) (by norm_num)

lemma b2608 : Encl e2608 (1558020558217 / 1000000000000 : ℝ) (779010279109 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2598 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2609 : Encl e2609 (40860806939 / 200000000000 : ℝ) (204304034697 / 1000000000000 : ℝ) := by
  exact Encl.pow b2594 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2610 : Encl e2610 (795695965303 / 1000000000000 : ℝ) (159139193061 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b2609 (by norm_num) (by norm_num)

lemma b2611 : Encl e2611 (89201791759 / 100000000000 : ℝ) (111502239699 / 125000000000 : ℝ) := by
  exact Encl.sqrt b2610 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2612 : Encl e2612 (-112675625463 / 500000000000 : ℝ) (-225351250923 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b2611 (by norm_num) (by norm_num)

lemma b2613 : Encl e2613 (709775058003 / 1000000000000 : ℝ) (88721882251 / 125000000000 : ℝ) := by
  exact Encl.pow b2611 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2614 : Encl e2614 (236591686001 / 1000000000000 : ℝ) (236591686003 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2613 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2615 : Encl e2615 (449617403 / 40000000000 : ℝ) (281010877 / 25000000000 : ℝ) := by
  exact Encl.add b2612 b2614 (by norm_num) (by norm_num)

lemma b2616 : Encl e2616 (11015626373 / 1000000000000 : ℝ) (11015626379 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2615 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2617 : Encl e2617 (229035797001 / 1000000000000 : ℝ) (57258949251 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2609 b2611 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2618 : Encl e2618 (-1770964202999 / 1000000000000 : ℝ) (-442741050749 / 250000000000 : ℝ) := by
  exact Encl.sub b2617 b23 (by norm_num) (by norm_num)

lemma b2619 : Encl e2619 (89201791759 / 50000000000 : ℝ) (111502239699 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2611 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2620 : Encl e2620 (13071632181 / 1000000000000 : ℝ) (3267908047 / 250000000000 : ℝ) := by
  exact Encl.add b2618 b2619 (by norm_num) (by norm_num)

lemma b2621 : Encl e2621 (261432643 / 1000000000000 : ℝ) (65358161 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2620 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2622 : Encl e2622 (10754193729 / 1000000000000 : ℝ) (1344274217 / 125000000000 : ℝ) := by
  exact Encl.sub b2616 b2621 (by norm_num) (by norm_num)

lemma b2623 : Encl e2623 (4188813729 / 250000000000 : ℝ) (1047203433 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2608 b2622 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2624 : Encl e2624 (-346428943291 / 1000000000000 : ℝ) (-346428943277 / 1000000000000 : ℝ) := by
  exact Encl.add b2607 b2623 (by norm_num) (by norm_num)

lemma b2625 : Encl e2625 (234255981423 / 250000000000 : ℝ) (937023925699 / 1000000000000 : ℝ) := by
  exact Encl.pow b2595 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2626 : Encl e2626 (62976074301 / 1000000000000 : ℝ) (15744018577 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b2625 (by norm_num) (by norm_num)

lemma b2627 : Encl e2627 (250950342301 / 1000000000000 : ℝ) (50190068463 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2626 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2628 : Encl e2628 (1250950342301 / 1000000000000 : ℝ) (250190068463 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2627 (by norm_num) (by norm_num)

lemma b2629 : Encl e2629 (386905830261 / 500000000000 : ℝ) (386905830267 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2595 b2628 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2630 : Encl e2630 (598784485959 / 1000000000000 : ℝ) (598784485979 / 1000000000000 : ℝ) := by
  exact Encl.pow b2629 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2631 : Encl e2631 (1598784485959 / 1000000000000 : ℝ) (1598784485979 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2630 (by norm_num) (by norm_num)

lemma b2632 : Encl e2632 (632215249333 / 500000000000 : ℝ) (50577219947 / 40000000000 : ℝ) := by
  exact Encl.sqrt b2631 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2633 : Encl e2633 (1132215249333 / 500000000000 : ℝ) (90577219947 / 40000000000 : ℝ) := by
  exact Encl.add b5 b2632 (by norm_num) (by norm_num)

lemma b2634 : Encl e2634 (170862311953 / 500000000000 : ℝ) (170862311957 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2629 b2633 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2635 : Encl e2635 (1317134437737 / 1000000000000 : ℝ) (658567218899 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e2595) (a := (170862311953 / 500000000000 : ℝ)) (b := (170862311957 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (483999980809 / 500000000000 : ℝ) by norm_num).trans b2595.1
        exact b2595.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2595) (170862311953 / 500000000000 : ℝ) (170862311957 / 500000000000 : ℝ) from b2634) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2636 : Encl e2636 (134347712649 / 200000000000 : ℝ) (671738563277 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2635 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2637 : Encl e2637 (59289997649 / 125000000000 : ℝ) (94863996239 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2595 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2638 : Encl e2638 (2975769041 / 25000000000 : ℝ) (7439422603 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2637 b2627 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2639 : Encl e2639 (552707801597 / 1000000000000 : ℝ) (552707801637 / 1000000000000 : ℝ) := by
  exact Encl.sub b2636 b2638 (by norm_num) (by norm_num)

lemma b2640 : Encl e2640 (250950342301 / 20000000000 : ℝ) (50190068463 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2627 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2641 : Encl e2641 (77146733707 / 1000000000000 : ℝ) (4821670857 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b2595 b2640 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2642 : Encl e2642 (95112213577 / 200000000000 : ℝ) (47556106793 / 100000000000 : ℝ) := by
  exact Encl.sub b2639 b2641 (by norm_num) (by norm_num)

lemma b2643 : Encl e2643 (189201791759 / 100000000000 : ℝ) (236502239699 / 125000000000 : ℝ) := by
  exact Encl.add b5 b2611 (by norm_num) (by norm_num)

lemma b2644 : Encl e2644 (119449196061 / 500000000000 : ℝ) (59724598031 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2594 b2643 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2645 : Encl e2645 (28536220879 / 500000000000 : ℝ) (356702761 / 6250000000 : ℝ) := by
  exact Encl.pow b2644 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2646 : Encl e2646 (528536220879 / 500000000000 : ℝ) (6606702761 / 6250000000 : ℝ) := by
  exact Encl.add b5 b2645 (by norm_num) (by norm_num)

lemma b2647 : Encl e2647 (128517535389 / 125000000000 : ℝ) (514070141557 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2646 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2648 : Encl e2648 (253517535389 / 125000000000 : ℝ) (1014070141557 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2647 (by norm_num) (by norm_num)

lemma b2649 : Encl e2649 (29447962021 / 250000000000 : ℝ) (58895924043 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2644 b2648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2650 : Encl e2650 (234503109563 / 500000000000 : ℝ) (93801243827 / 200000000000 : ℝ) := by
  apply Encl.arcsin (z := e2594) (a := (29447962021 / 250000000000 : ℝ)) (b := (58895924043 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (22600001919 / 50000000000 : ℝ) by norm_num).trans b2594.1
        exact b2594.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2594) (29447962021 / 250000000000 : ℝ) (58895924043 / 500000000000 : ℝ) from b2649) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2651 : Encl e2651 (119596585877 / 500000000000 : ℝ) (239193171759 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2650 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2652 : Encl e2652 (110740009403 / 500000000000 : ℝ) (221480018807 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2594 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2653 : Encl e2653 (197564145163 / 1000000000000 : ℝ) (39512829033 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2652 b2611 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2654 : Encl e2654 (41629026589 / 1000000000000 : ℝ) (10407256649 / 250000000000 : ℝ) := by
  exact Encl.sub b2651 b2653 (by norm_num) (by norm_num)

lemma b2655 : Encl e2655 (89201791759 / 2000000000 : ℝ) (111502239699 / 2500000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2611 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2656 : Encl e2656 (253358161 / 25000000000 : ℝ) (10134326441 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2594 b2655 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2657 : Encl e2657 (7873675037 / 250000000000 : ℝ) (7873675039 / 250000000000 : ℝ) := by
  exact Encl.sub b2654 b2656 (by norm_num) (by norm_num)

lemma b2658 : Encl e2658 (444066367729 / 1000000000000 : ℝ) (222033183891 / 500000000000 : ℝ) := by
  exact Encl.sub b2642 b2657 (by norm_num) (by norm_num)

lemma b2659 : Encl e2659 (12508911767 / 40000000000 : ℝ) (312722794213 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2658 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2660 : Encl e2660 (-8426537279 / 250000000000 : ℝ) (-4213268633 / 125000000000 : ℝ) := by
  exact Encl.add b2624 b2659 (by norm_num) (by norm_num)

lemma b2661 : Encl e2661 (489435820057 / 250000000000 : ℝ) (244717910029 / 125000000000 : ℝ) := by
  exact Encl.add b2595 b4 (by norm_num) (by norm_num)

lemma b2662 : Encl e2662 (489435820057 / 500000000000 : ℝ) (244717910029 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2661 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2663 : Encl e2663 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2595 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2664 : Encl e2664 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2663 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2665 : Encl e2665 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b2663 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2666 : Encl e2666 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2665 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2667 : Encl e2667 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2666 (by norm_num) (by norm_num)

lemma b2668 : Encl e2668 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2667 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2669 : Encl e2669 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2664 b2668 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2670 : Encl e2670 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2665 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2671 : Encl e2671 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b2669 b2670 (by norm_num) (by norm_num)

lemma b2672 : Encl e2672 (667287119749 / 1000000000000 : ℝ) (333643559887 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2662 b2671 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2673 : Encl e2673 (86168278179 / 125000000000 : ℝ) (344673112717 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2662 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2674 : Encl e2674 (1221834371873 / 1000000000000 : ℝ) (1221834371879 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2673 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2675 : Encl e2675 (475198218517 / 1000000000000 : ℝ) (475198218521 / 1000000000000 : ℝ) := by
  exact Encl.pow b2673 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2676 : Encl e2676 (46652476009 / 125000000000 : ℝ) (373219808077 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2675 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2677 : Encl e2677 (171652476009 / 125000000000 : ℝ) (1373219808077 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2676 (by norm_num) (by norm_num)

lemma b2678 : Encl e2678 (292961154429 / 250000000000 : ℝ) (29296115443 / 25000000000 : ℝ) := by
  exact Encl.sqrt b2677 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2679 : Encl e2679 (1431800032419 / 1000000000000 : ℝ) (89487502027 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2674 b2678 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2680 : Encl e2680 (149287923229 / 200000000000 : ℝ) (746439616153 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2675 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2681 : Encl e2681 (342680208133 / 500000000000 : ℝ) (685360416287 / 1000000000000 : ℝ) := by
  exact Encl.sub b2679 b2680 (by norm_num) (by norm_num)

lemma b2682 : Encl e2682 (663428856639 / 1000000000000 : ℝ) (663428856663 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2595 b2681 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2683 : Encl e2683 (1929131543 / 500000000000 : ℝ) (771652627 / 200000000000 : ℝ) := by
  exact Encl.sub b2672 b2682 (by norm_num) (by norm_num)

lemma b2684 : Encl e2684 (958189687819 / 1000000000000 : ℝ) (59886855489 / 62500000000 : ℝ) := by
  exact Encl.pow b2662 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2685 : Encl e2685 (469512947031 / 500000000000 : ℝ) (234756473517 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2684 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2686 : Encl e2686 (15243526483 / 250000000000 : ℝ) (30487052969 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2685 (by norm_num) (by norm_num)

lemma b2687 : Encl e2687 (2613144511 / 62500000000 : ℝ) (41810312181 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2684 (by norm_num) (by norm_num)

lemma b2688 : Encl e2688 (102237850349 / 500000000000 : ℝ) (204475700711 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2687 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2689 : Encl e2689 (298197319877 / 1000000000000 : ℝ) (149098659963 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2686 b2688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2690 : Encl e2690 (350901340037 / 500000000000 : ℝ) (701802680123 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2689 (by norm_num) (by norm_num)

lemma b2691 : Encl e2691 (459141723589 / 500000000000 : ℝ) (459141723593 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2625 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2692 : Encl e2692 (40858276407 / 500000000000 : ℝ) (40858276411 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2691 (by norm_num) (by norm_num)

lemma b2693 : Encl e2693 (325628377551 / 1000000000000 : ℝ) (162814188801 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2692 b2627 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2694 : Encl e2694 (337185811199 / 500000000000 : ℝ) (674371622449 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2693 (by norm_num) (by norm_num)

lemma b2695 : Encl e2695 (219448461 / 8000000000 : ℝ) (1097242309 / 40000000000 : ℝ) := by
  exact Encl.sub b2690 b2694 (by norm_num) (by norm_num)

lemma b2696 : Encl e2696 (105836237 / 1000000000000 : ℝ) (105836239 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2683 b2695 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2697 : Encl e2697 (1835151219 / 500000000000 : ℝ) (1835151241 / 500000000000 : ℝ) := by
  exact Encl.sub b2681 b2671 (by norm_num) (by norm_num)

lemma b2698 : Encl e2698 (602237850349 / 500000000000 : ℝ) (1204475700711 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2688 (by norm_num) (by norm_num)

lemma b2699 : Encl e2699 (812695216297 / 1000000000000 : ℝ) (203173804077 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2662 b2698 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

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
lemma b2700 : Encl e2700 (20639797331 / 31250000000 : ℝ) (66047351461 / 100000000000 : ℝ) := by
  exact Encl.pow b2699 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2701 : Encl e2701 (51889797331 / 31250000000 : ℝ) (166047351461 / 100000000000 : ℝ) := by
  exact Encl.add b5 b2700 (by norm_num) (by norm_num)

lemma b2702 : Encl e2702 (1288593618869 / 1000000000000 : ℝ) (1288593618877 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2701 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2703 : Encl e2703 (2288593618869 / 1000000000000 : ℝ) (2288593618877 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2702 (by norm_num) (by norm_num)

lemma b2704 : Encl e2704 (22194176633 / 62500000000 : ℝ) (71021365227 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2699 b2703 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2705 : Encl e2705 (272973653087 / 200000000000 : ℝ) (136486826553 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e2662) (a := (22194176633 / 62500000000 : ℝ)) (b := (71021365227 / 200000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (489435820057 / 500000000000 : ℝ) by norm_num).trans b2662.1
        exact b2662.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2662) (22194176633 / 62500000000 : ℝ) (71021365227 / 200000000000 : ℝ) from b2704) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b2706 : Encl e2706 (696082815371 / 1000000000000 : ℝ) (696082815421 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2705 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2707 : Encl e2707 (95929420731 / 200000000000 : ℝ) (479647103657 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2662 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2708 : Encl e2708 (98076177607 / 1000000000000 : ℝ) (19615235523 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2707 b2688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2709 : Encl e2709 (149501659439 / 250000000000 : ℝ) (299003318907 / 500000000000 : ℝ) := by
  exact Encl.sub b2706 b2708 (by norm_num) (by norm_num)

lemma b2710 : Encl e2710 (102237850349 / 10000000000 : ℝ) (204475700711 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2711 : Encl e2711 (748004253 / 7812500000 : ℝ) (95744544391 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2662 b2710 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2712 : Encl e2712 (100452418673 / 200000000000 : ℝ) (50226209343 / 100000000000 : ℝ) := by
  exact Encl.sub b2709 b2711 (by norm_num) (by norm_num)

lemma b2713 : Encl e2713 (5340205087 / 200000000000 : ℝ) (5340205109 / 200000000000 : ℝ) := by
  exact Encl.sub b2712 b2642 (by norm_num) (by norm_num)

lemma b2714 : Encl e2714 (49000419 / 500000000000 : ℝ) (98000841 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2697 b2713 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2715 : Encl e2715 (8153483 / 40000000000 : ℝ) (5095927 / 25000000000 : ℝ) := by
  exact Encl.add b2696 b2714 (by norm_num) (by norm_num)

lemma b2716 : Encl e2716 (10871678493 / 1000000000000 : ℝ) (5435839249 / 500000000000 : ℝ) := by
  exact Encl.sub b2662 b2595 (by norm_num) (by norm_num)

lemma b2717 : Encl e2717 (9374682807 / 500000000000 : ℝ) (18749366083 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2715 b2716 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2718 : Encl e2718 (-7478391751 / 500000000000 : ℝ) (-14956782981 / 1000000000000 : ℝ) := by
  exact Encl.add b2660 b2717 (by norm_num) (by norm_num)

lemma b2719 : Encl e2719 (678330892839 / 1000000000000 : ℝ) (678330892861 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b2681 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2720 : Encl e2720 (697002337049 / 1000000000000 : ℝ) (13940046741 / 20000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2721 : Encl e2721 (154425559549 / 125000000000 : ℝ) (247080895279 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2720 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2722 : Encl e2722 (485812257851 / 1000000000000 : ℝ) (242906128927 / 500000000000 : ℝ) := by
  exact Encl.pow b2720 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2723 : Encl e2723 (381556055071 / 1000000000000 : ℝ) (15262242203 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2722 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2724 : Encl e2724 (1381556055071 / 1000000000000 : ℝ) (55262242203 / 40000000000 : ℝ) := by
  exact Encl.add b5 b2723 (by norm_num) (by norm_num)

lemma b2725 : Encl e2725 (587698063437 / 500000000000 : ℝ) (293849031719 / 250000000000 : ℝ) := by
  exact Encl.sqrt b2724 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2726 : Encl e2726 (1452089636673 / 1000000000000 : ℝ) (36302240917 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b2721 b2725 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2727 : Encl e2727 (763112110143 / 1000000000000 : ℝ) (15262242203 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2722 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2728 : Encl e2728 (688977526523 / 1000000000000 : ℝ) (688977526537 / 1000000000000 : ℝ) := by
  exact Encl.sub b2726 b2727 (by norm_num) (by norm_num)

lemma b2729 : Encl e2729 (674420561389 / 1000000000000 : ℝ) (134884112281 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2662 b2728 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2730 : Encl e2730 (1955165717 / 500000000000 : ℝ) (244395717 / 62500000000 : ℝ) := by
  exact Encl.sub b2719 b2729 (by norm_num) (by norm_num)

lemma b2731 : Encl e2731 (4549329963 / 250000000000 : ℝ) (9098659977 / 500000000000 : ℝ) := by
  exact Encl.sub b165 b2690 (by norm_num) (by norm_num)

lemma b2732 : Encl e2732 (71157551 / 1000000000000 : ℝ) (71157553 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2730 b2731 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2733 : Encl e2733 (904277559 / 250000000000 : ℝ) (3617110271 / 1000000000000 : ℝ) := by
  exact Encl.sub b2728 b2681 (by norm_num) (by norm_num)

lemma b2734 : Encl e2734 (8945338041 / 500000000000 : ℝ) (8945338139 / 500000000000 : ℝ) := by
  exact Encl.sub b183 b2712 (by norm_num) (by norm_num)

lemma b2735 : Encl e2735 (64712547 / 1000000000000 : ℝ) (64712549 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2733 b2734 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2736 : Encl e2736 (67935049 / 500000000000 : ℝ) (67935051 / 500000000000 : ℝ) := by
  exact Encl.add b2732 b2735 (by norm_num) (by norm_num)

lemma b2737 : Encl e2737 (5435839247 / 500000000000 : ℝ) (10871678497 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b2662 (by norm_num) (by norm_num)

lemma b2738 : Encl e2738 (12497619207 / 1000000000000 : ℝ) (12497619579 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2736 b2737 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2739 : Encl e2739 (-491832859 / 200000000000 : ℝ) (-1229581701 / 500000000000 : ℝ) := by
  exact Encl.add b2718 b2738 (by norm_num) (by norm_num)

lemma b2740 : Encl e2740 (169014084507 / 250000000000 : ℝ) (676056338029 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2741 : Encl e2741 (169014084507 / 250000000000 : ℝ) (676056338029 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2740 (by norm_num) (by norm_num)

lemma b2742 : Encl e2742 (-80985915493 / 250000000000 : ℝ) (-323943661971 / 1000000000000 : ℝ) := by
  exact Encl.sub b2741 b5 (by norm_num) (by norm_num)

lemma b2743 : Encl e2743 (71 / 25 : ℝ) (71 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2744 : Encl e2744 (1966251322401 / 1000000000000 : ℝ) (393250264481 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2743 b2604 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2745 : Encl e2745 (312938617321 / 500000000000 : ℝ) (156469308661 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2744 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2746 : Encl e2746 (30193357267 / 100000000000 : ℝ) (301933572673 / 1000000000000 : ℝ) := by
  exact Encl.add b2742 b2745 (by norm_num) (by norm_num)

lemma b2747 : Encl e2747 (5041 / 1250 : ℝ) (5041 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b2598 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2748 : Encl e2748 (2792076877809 / 1000000000000 : ℝ) (1396038438907 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2747 b2604 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2749 : Encl e2749 (2966834765699 / 500000000000 : ℝ) (1483417382851 / 250000000000 : ℝ) := by
  exact Encl.add b0 b2748 (by norm_num) (by norm_num)

lemma b2750 : Encl e2750 (121795623191 / 50000000000 : ℝ) (2435912463823 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2749 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2751 : Encl e2751 (1550750038223 / 1000000000000 : ℝ) (387687509557 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2750 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2752 : Encl e2752 (357911 / 125000 : ℝ) (357911 / 125000 : ℝ) := by
  exact Encl.pow b2593 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2753 : Encl e2753 (23980037 / 62500000 : ℝ) (23980037 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2752 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2754 : Encl e2754 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b2753 b941 (by norm_num) (by norm_num)

lemma b2755 : Encl e2755 (30193357267 / 50000000000 : ℝ) (301933572673 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2746 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2756 : Encl e2756 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b2754 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2757 : Encl e2757 (300603210131 / 125000000000 : ℝ) (480965136213 / 200000000000 : ℝ) := by
  exact Encl.pow b2751 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2758 : Encl e2758 (5194423471063 / 1000000000000 : ℝ) (5194423471101 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2756 b2757 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2759 : Encl e2759 (784185418289 / 500000000000 : ℝ) (1568370836607 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2758 b2746 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2760 : Encl e2760 (112026488327 / 20000000000 : ℝ) (2800662208227 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2759 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2761 : Encl e2761 (132026488327 / 20000000000 : ℝ) (3300662208227 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2760 (by norm_num) (by norm_num)

lemma b2762 : Encl e2762 (513860853397 / 200000000000 : ℝ) (1284652133503 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2761 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2763 : Encl e2763 (713860853397 / 200000000000 : ℝ) (1784652133503 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2762 (by norm_num) (by norm_num)

lemma b2764 : Encl e2764 (84591715943 / 500000000000 : ℝ) (16918343189 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2755 b2763 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2765 : Encl e2765 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b2754 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2766 : Encl e2766 (6637507039 / 50000000000 : ℝ) (132750140787 / 1000000000000 : ℝ) := by
  exact Encl.sub b2746 b2764 (by norm_num) (by norm_num)

lemma b2767 : Encl e2767 (85603828797 / 1000000000000 : ℝ) (85603828803 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2766 b2751 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2768 : Encl e2768 (458000969 / 62500000000 : ℝ) (3664007753 / 500000000000 : ℝ) := by
  exact Encl.pow b2767 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b2769 : Encl e2769 (2051844341 / 1000000000000 : ℝ) (1025922171 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2768 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2770 : Encl e2770 (4842543059 / 1000000000000 : ℝ) (242127153 / 50000000000 : ℝ) := by
  exact Encl.pow b2764 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b2771 : Encl e2771 (1743315501 / 1000000000000 : ℝ) (871657751 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2754 b2770 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b2772 : Encl e2772 (1897579921 / 500000000000 : ℝ) (948789961 / 250000000000 : ℝ) := by
  exact Encl.add b2769 b2771 (by norm_num) (by norm_num)

lemma b2773 : Encl e2773 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.min b2765 b2772 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_142 : Encl (twoChordBaseline (71 / 50 : ℝ)) (-491832859 / 200000000000 : ℝ) (-1229581701 / 500000000000 : ℝ) := by
  exact b2739

lemma gain_enclosure_142 : Encl (gain (71 / 50 : ℝ)) (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2773

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

lemma baseline_lower_142 : (-491832859 / 200000000000 : ℝ) ≤ baseline (71 / 50 : ℝ) :=
  (baseline_enclosure_142).1.trans (twoChordBaseline_le_of_range (h := (71 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_142_oai : (174959141 / 200000000000 : ℝ) ≤ baseline (71 / 50 : ℝ) + gain (71 / 50 : ℝ) := by
  have hb := baseline_lower_142
  have hg := (gain_enclosure_142).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_142_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_142_oai

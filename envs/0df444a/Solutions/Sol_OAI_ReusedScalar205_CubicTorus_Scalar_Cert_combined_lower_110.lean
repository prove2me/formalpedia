-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_110
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:38:18.413176+00:00
-- url     : https://prove2.me/submissions/058ea33d-9867-4b6f-a3fa-f0657bdd1e3a

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

lemma b1145 : Encl e1145 (11 / 10 : ℝ) (11 / 10 : ℝ) := by
  exact Encl.exact (11 / 10 : ℝ)

lemma b1146 : Encl e1146 (175070437401 / 500000000000 : ℝ) (350140874803 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1145 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1147 : Encl e1147 (749859125197 / 1000000000000 : ℝ) (749859125199 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1145 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1148 : Encl e1148 (539 / 500 : ℝ) (539 / 500 : ℝ) := by
  exact Encl.mul_nonneg b8 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1149 : Encl e1149 (171569028653 / 500000000000 : ℝ) (343138057307 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1148 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1150 : Encl e1150 (121 / 100 : ℝ) (121 / 100 : ℝ) := by
  exact Encl.pow b1145 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1151 : Encl e1151 (121 / 25 : ℝ) (121 / 25 : ℝ) := by
  exact Encl.mul_nonneg b17 b1150 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1152 : Encl e1152 (1540619849129 / 1000000000000 : ℝ) (154061984913 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1151 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1153 : Encl e1153 (2540619849129 / 1000000000000 : ℝ) (254061984913 / 100000000000 : ℝ) := by
  exact Encl.add b5 b1152 (by norm_num) (by norm_num)

lemma b1154 : Encl e1154 (318786439431 / 200000000000 : ℝ) (398483049289 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1153 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1155 : Encl e1155 (518786439431 / 200000000000 : ℝ) (648483049289 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1154 (by norm_num) (by norm_num)

lemma b1156 : Encl e1156 (12047346509 / 15625000000 : ℝ) (771030176577 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b1155 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1157 : Encl e1157 (215888449441 / 1000000000000 : ℝ) (107944224721 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1156 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1158 : Encl e1158 (559026506747 / 1000000000000 : ℝ) (559026506749 / 1000000000000 : ℝ) := by
  exact Encl.add b1149 b1157 (by norm_num) (by norm_num)

lemma b1159 : Encl e1159 (-440973493253 / 1000000000000 : ℝ) (-440973493251 / 1000000000000 : ℝ) := by
  exact Encl.sub b1158 b5 (by norm_num) (by norm_num)

lemma b1160 : Encl e1160 (51927151299 / 20000000000 : ℝ) (2596357564951 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b1150 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1161 : Encl e1161 (122598632207 / 1000000000000 : ℝ) (7662414513 / 62500000000 : ℝ) := by
  exact Encl.pow b1146 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1162 : Encl e1162 (54837585487 / 62500000000 : ℝ) (877401367793 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1161 (by norm_num) (by norm_num)

lemma b1163 : Encl e1163 (468348526151 / 500000000000 : ℝ) (936697052303 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1162 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1164 : Encl e1164 (-270030385637 / 1000000000000 : ℝ) (-54006077127 / 200000000000 : ℝ) := by
  exact Encl.sub b29 b1163 (by norm_num) (by norm_num)

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures1165To1383
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

lemma b1165 : Encl e1165 (164371854979 / 200000000000 : ℝ) (821859274899 / 1000000000000 : ℝ) := by
  exact Encl.pow b1163 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1166 : Encl e1166 (273953091631 / 1000000000000 : ℝ) (273953091633 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1165 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1167 : Encl e1167 (1961352997 / 500000000000 : ℝ) (1961352999 / 500000000000 : ℝ) := by
  exact Encl.add b1164 b1166 (by norm_num) (by norm_num)

lemma b1168 : Encl e1168 (1922125937 / 500000000000 : ℝ) (3844251879 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1167 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1169 : Encl e1169 (65441986769 / 500000000000 : ℝ) (6544198677 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b1161 b1163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1170 : Encl e1170 (-934558013231 / 500000000000 : ℝ) (-93455801323 / 50000000000 : ℝ) := by
  exact Encl.sub b1169 b23 (by norm_num) (by norm_num)

lemma b1171 : Encl e1171 (468348526151 / 250000000000 : ℝ) (936697052303 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1172 : Encl e1172 (2139039071 / 500000000000 : ℝ) (2139039073 / 500000000000 : ℝ) := by
  exact Encl.add b1170 b1171 (by norm_num) (by norm_num)

lemma b1173 : Encl e1173 (42780781 / 500000000000 : ℝ) (85561563 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1172 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1174 : Encl e1174 (3758690311 / 1000000000000 : ℝ) (3758690317 / 1000000000000 : ℝ) := by
  exact Encl.sub b1168 b1173 (by norm_num) (by norm_num)

lemma b1175 : Encl e1175 (9758904023 / 1000000000000 : ℝ) (9758904039 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1160 b1174 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1176 : Encl e1176 (-43121458923 / 100000000000 : ℝ) (-107803647303 / 250000000000 : ℝ) := by
  exact Encl.add b1159 b1175 (by norm_num) (by norm_num)

lemma b1177 : Encl e1177 (562288707641 / 1000000000000 : ℝ) (112457741529 / 200000000000 : ℝ) := by
  exact Encl.pow b1147 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1178 : Encl e1178 (87542258471 / 200000000000 : ℝ) (437711292359 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1177 (by norm_num) (by norm_num)

lemma b1179 : Encl e1179 (661597530493 / 1000000000000 : ℝ) (661597530497 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1178 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1180 : Encl e1180 (1661597530493 / 1000000000000 : ℝ) (1661597530497 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1179 (by norm_num) (by norm_num)

lemma b1181 : Encl e1181 (451288059493 / 1000000000000 : ℝ) (56411007437 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1147 b1180 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1182 : Encl e1182 (19888761 / 97656250 : ℝ) (50915228161 / 250000000000 : ℝ) := by
  exact Encl.pow b1181 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1183 : Encl e1183 (117545011 / 97656250 : ℝ) (300915228161 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1182 (by norm_num) (by norm_num)

lemma b1184 : Encl e1184 (1097114812879 / 1000000000000 : ℝ) (548557406441 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1183 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1185 : Encl e1185 (2097114812879 / 1000000000000 : ℝ) (1048557406441 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1184 (by norm_num) (by norm_num)

lemma b1186 : Encl e1186 (43038946339 / 200000000000 : ℝ) (107597365849 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1181 b1185 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1187 : Encl e1187 (211962280501 / 250000000000 : ℝ) (847849122017 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e1147) (a := (43038946339 / 200000000000 : ℝ)) (b := (107597365849 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (749859125197 / 1000000000000 : ℝ) by norm_num).trans b1147.1
        exact b1147.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1147) (43038946339 / 200000000000 : ℝ) (107597365849 / 500000000000 : ℝ) from b1186) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1188 : Encl e1188 (216201526111 / 500000000000 : ℝ) (432403052229 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1187 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1189 : Encl e1189 (183715485673 / 500000000000 : ℝ) (91857742837 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1147 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1190 : Encl e1190 (243091423269 / 1000000000000 : ℝ) (30386427909 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1189 b1179 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1191 : Encl e1191 (3786232579 / 20000000000 : ℝ) (1183197681 / 6250000000 : ℝ) := by
  exact Encl.sub b1188 b1190 (by norm_num) (by norm_num)

lemma b1192 : Encl e1192 (661597530493 / 20000000000 : ℝ) (661597530497 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1179 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1193 : Encl e1193 (11334067777 / 500000000000 : ℝ) (4533627111 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1147 b1192 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1194 : Encl e1194 (33328698679 / 200000000000 : ℝ) (83321746703 / 500000000000 : ℝ) := by
  exact Encl.sub b1191 b1193 (by norm_num) (by norm_num)

lemma b1195 : Encl e1195 (968348526151 / 500000000000 : ℝ) (1936697052303 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1163 (by norm_num) (by norm_num)

lemma b1196 : Encl e1196 (3615855917 / 20000000000 : ℝ) (45198198963 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1146 b1195 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1197 : Encl e1197 (32686035031 / 1000000000000 : ℝ) (4085754379 / 125000000000 : ℝ) := by
  exact Encl.pow b1196 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1198 : Encl e1198 (1032686035031 / 1000000000000 : ℝ) (129085754379 / 125000000000 : ℝ) := by
  exact Encl.add b5 b1197 (by norm_num) (by norm_num)

lemma b1199 : Encl e1199 (31756612793 / 31250000000 : ℝ) (1016211609377 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1198 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1200 : Encl e1200 (63006612793 / 31250000000 : ℝ) (2016211609377 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1199 (by norm_num) (by norm_num)

lemma b1201 : Encl e1201 (89669554033 / 1000000000000 : ℝ) (17933910807 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1196 b1200 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1202 : Encl e1202 (8943037367 / 25000000000 : ℝ) (357721494689 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e1146) (a := (89669554033 / 1000000000000 : ℝ)) (b := (17933910807 / 200000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (175070437401 / 500000000000 : ℝ) by norm_num).trans b1146.1
        exact b1146.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1146) (89669554033 / 1000000000000 : ℝ) (17933910807 / 200000000000 : ℝ) from b1201) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1203 : Encl e1203 (91218981143 / 500000000000 : ℝ) (45609490573 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1202 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1204 : Encl e1204 (42892257163 / 250000000000 : ℝ) (85784514327 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1146 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1205 : Encl e1205 (40177050851 / 250000000000 : ℝ) (160708203407 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1204 b1163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1206 : Encl e1206 (21729758879 / 1000000000000 : ℝ) (2716219861 / 125000000000 : ℝ) := by
  exact Encl.sub b1203 b1205 (by norm_num) (by norm_num)

lemma b1207 : Encl e1207 (468348526151 / 10000000000 : ℝ) (936697052303 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1163 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1208 : Encl e1208 (3738037543 / 500000000000 : ℝ) (7476075087 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1146 b1207 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1209 : Encl e1209 (890855237 / 62500000000 : ℝ) (7126841901 / 500000000000 : ℝ) := by
  exact Encl.sub b1206 b1208 (by norm_num) (by norm_num)

lemma b1210 : Encl e1210 (152389809593 / 1000000000000 : ℝ) (76194904807 / 500000000000 : ℝ) := by
  exact Encl.sub b1194 b1209 (by norm_num) (by norm_num)

lemma b1211 : Encl e1211 (138536190539 / 1000000000000 : ℝ) (138536190559 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1210 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1212 : Encl e1212 (-292678398691 / 1000000000000 : ℝ) (-292678398653 / 1000000000000 : ℝ) := by
  exact Encl.add b1176 b1211 (by norm_num) (by norm_num)

lemma b1213 : Encl e1213 (1739602443807 / 1000000000000 : ℝ) (173960244381 / 100000000000 : ℝ) := by
  exact Encl.add b1147 b4 (by norm_num) (by norm_num)

lemma b1214 : Encl e1214 (869801221903 / 1000000000000 : ℝ) (173960244381 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1213 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1215 : Encl e1215 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1147 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1216 : Encl e1216 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1215 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1217 : Encl e1217 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1215 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1218 : Encl e1218 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1217 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1219 : Encl e1219 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1218 (by norm_num) (by norm_num)

lemma b1220 : Encl e1220 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1219 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1221 : Encl e1221 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1216 b1220 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1222 : Encl e1222 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1217 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1223 : Encl e1223 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1221 b1222 (by norm_num) (by norm_num)

lemma b1224 : Encl e1224 (296467446973 / 500000000000 : ℝ) (592934893969 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1214 b1223 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1225 : Encl e1225 (197682095887 / 250000000000 : ℝ) (15814567671 / 20000000000 : ℝ) := by
  exact Encl.div_nonneg b1214 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1226 : Encl e1226 (1401529568439 / 1000000000000 : ℝ) (350382392111 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1225 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1227 : Encl e1227 (156312844137 / 250000000000 : ℝ) (78156422069 / 125000000000 : ℝ) := by
  exact Encl.pow b1225 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1228 : Encl e1228 (245535641401 / 500000000000 : ℝ) (491071282807 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1227 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1229 : Encl e1229 (745535641401 / 500000000000 : ℝ) (1491071282807 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1228 (by norm_num) (by norm_num)

lemma b1230 : Encl e1230 (61054714863 / 50000000000 : ℝ) (1221094297263 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1229 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1231 : Encl e1231 (855699881731 / 500000000000 : ℝ) (1711399763473 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1226 b1230 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1232 : Encl e1232 (245535641401 / 250000000000 : ℝ) (245535641403 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1227 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1233 : Encl e1233 (14585143957 / 20000000000 : ℝ) (729257197869 / 1000000000000 : ℝ) := by
  exact Encl.sub b1231 b1232 (by norm_num) (by norm_num)

lemma b1234 : Encl e1234 (546840164423 / 1000000000000 : ℝ) (13671004111 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b1147 b1233 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1235 : Encl e1235 (23047364753 / 500000000000 : ℝ) (23047364773 / 500000000000 : ℝ) := by
  exact Encl.sub b1224 b1234 (by norm_num) (by norm_num)

lemma b1236 : Encl e1236 (756554165623 / 1000000000000 : ℝ) (189138541407 / 250000000000 : ℝ) := by
  exact Encl.pow b1214 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1237 : Encl e1237 (74142308231 / 100000000000 : ℝ) (185355770579 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1236 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1238 : Encl e1238 (64644229421 / 250000000000 : ℝ) (25857691769 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b1237 (by norm_num) (by norm_num)

lemma b1239 : Encl e1239 (60861458593 / 250000000000 : ℝ) (243445834377 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1236 (by norm_num) (by norm_num)

lemma b1240 : Encl e1240 (493402304789 / 1000000000000 : ℝ) (98680460959 / 200000000000 : ℝ) := by
  exact Encl.sqrt b1239 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1241 : Encl e1241 (65508641521 / 125000000000 : ℝ) (131017283047 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1238 b1240 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1242 : Encl e1242 (118982716953 / 250000000000 : ℝ) (59491358479 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b1241 (by norm_num) (by norm_num)

lemma b1243 : Encl e1243 (34440183343 / 62500000000 : ℝ) (551042933493 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1177 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1244 : Encl e1244 (448957066507 / 1000000000000 : ℝ) (28059816657 / 62500000000 : ℝ) := by
  exact Encl.sub b5 b1243 (by norm_num) (by norm_num)

lemma b1245 : Encl e1245 (135719087757 / 200000000000 : ℝ) (339297719399 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1244 b1179 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1246 : Encl e1246 (160702280601 / 500000000000 : ℝ) (64280912243 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b1245 (by norm_num) (by norm_num)

lemma b1247 : Encl e1247 (154526306597 / 1000000000000 : ℝ) (15452630663 / 100000000000 : ℝ) := by
  exact Encl.sub b1242 b1246 (by norm_num) (by norm_num)

lemma b1248 : Encl e1248 (445178019 / 62500000000 : ℝ) (890356039 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1235 b1247 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1249 : Encl e1249 (23783542011 / 500000000000 : ℝ) (1486471377 / 31250000000 : ℝ) := by
  exact Encl.sub b1233 b1223 (by norm_num) (by norm_num)

lemma b1250 : Encl e1250 (1493402304789 / 1000000000000 : ℝ) (298680460959 / 200000000000 : ℝ) := by
  exact Encl.add b5 b1240 (by norm_num) (by norm_num)

lemma b1251 : Encl e1251 (582429275159 / 1000000000000 : ℝ) (582429275163 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1214 b1250 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1252 : Encl e1252 (169611930281 / 500000000000 : ℝ) (339223860567 / 1000000000000 : ℝ) := by
  exact Encl.pow b1251 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1253 : Encl e1253 (669611930281 / 500000000000 : ℝ) (1339223860567 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1252 (by norm_num) (by norm_num)

lemma b1254 : Encl e1254 (36164012517 / 31250000000 : ℝ) (1157248400547 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1253 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1255 : Encl e1255 (67414012517 / 31250000000 : ℝ) (2157248400547 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1254 (by norm_num) (by norm_num)

lemma b1256 : Encl e1256 (269987116463 / 1000000000000 : ℝ) (134993558233 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1251 b1255 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1257 : Encl e1257 (1054799305119 / 1000000000000 : ℝ) (263699826283 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e1214) (a := (269987116463 / 1000000000000 : ℝ)) (b := (134993558233 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (869801221903 / 1000000000000 : ℝ) by norm_num).trans b1214.1
        exact b1214.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1214) (269987116463 / 1000000000000 : ℝ) (134993558233 / 500000000000 : ℝ) from b1256) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b1258 : Encl e1258 (53794764561 / 100000000000 : ℝ) (268973822809 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1257 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1259 : Encl e1259 (106550649683 / 250000000000 : ℝ) (213101299367 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1214 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1260 : Encl e1260 (210289344521 / 1000000000000 : ℝ) (8411573781 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b1259 b1240 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1261 : Encl e1261 (65531660217 / 200000000000 : ℝ) (327658301097 / 1000000000000 : ℝ) := by
  exact Encl.sub b1258 b1260 (by norm_num) (by norm_num)

lemma b1262 : Encl e1262 (493402304789 / 20000000000 : ℝ) (98680460959 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1240 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1263 : Encl e1263 (35257282483 / 1000000000000 : ℝ) (8814320621 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1214 b1262 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1264 : Encl e1264 (292401018601 / 1000000000000 : ℝ) (146200509307 / 500000000000 : ℝ) := by
  exact Encl.sub b1261 b1263 (by norm_num) (by norm_num)

lemma b1265 : Encl e1265 (25151505039 / 200000000000 : ℝ) (125757525219 / 1000000000000 : ℝ) := by
  exact Encl.sub b1264 b1194 (by norm_num) (by norm_num)

lemma b1266 : Encl e1266 (5981918767 / 1000000000000 : ℝ) (2990959387 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1249 b1265 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1267 : Encl e1267 (13104767071 / 1000000000000 : ℝ) (6552383543 / 500000000000 : ℝ) := by
  exact Encl.add b1248 b1266 (by norm_num) (by norm_num)

lemma b1268 : Encl e1268 (1874095261 / 15625000000 : ℝ) (29985524177 / 250000000000 : ℝ) := by
  exact Encl.sub b1214 b1147 (by norm_num) (by norm_num)

lemma b1269 : Encl e1269 (109259112777 / 1000000000000 : ℝ) (109259112907 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1267 b1268 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1270 : Encl e1270 (-91709642957 / 500000000000 : ℝ) (-91709642873 / 500000000000 : ℝ) := by
  exact Encl.add b1212 b1269 (by norm_num) (by norm_num)

lemma b1271 : Encl e1271 (9022217989 / 12500000000 : ℝ) (36088871957 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1233 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1272 : Encl e1272 (899766653281 / 1000000000000 : ℝ) (899766653283 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1273 : Encl e1273 (1594794869523 / 1000000000000 : ℝ) (1594794869529 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1272 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1274 : Encl e1274 (202395007589 / 250000000000 : ℝ) (809580030361 / 1000000000000 : ℝ) := by
  exact Encl.pow b1272 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1275 : Encl e1275 (158960667241 / 250000000000 : ℝ) (63584266897 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1274 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1276 : Encl e1276 (408960667241 / 250000000000 : ℝ) (163584266897 / 100000000000 : ℝ) := by
  exact Encl.add b5 b1275 (by norm_num) (by norm_num)

lemma b1277 : Encl e1277 (39968770389 / 31250000000 : ℝ) (1279000652451 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1276 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1278 : Encl e1278 (25496795983 / 12500000000 : ℝ) (1019871839327 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1273 b1277 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1279 : Encl e1279 (158960667241 / 125000000000 : ℝ) (635842668969 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1274 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1280 : Encl e1280 (384029170351 / 500000000000 : ℝ) (384029170363 / 500000000000 : ℝ) := by
  exact Encl.sub b1278 b1279 (by norm_num) (by norm_num)

lemma b1281 : Encl e1281 (133611616647 / 200000000000 : ℝ) (334029041629 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1214 b1280 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1282 : Encl e1282 (26859677931 / 500000000000 : ℝ) (10743871181 / 200000000000 : ℝ) := by
  exact Encl.sub b1271 b1281 (by norm_num) (by norm_num)

lemma b1283 : Encl e1283 (244069132143 / 1000000000000 : ℝ) (30508641527 / 125000000000 : ℝ) := by
  exact Encl.sub b165 b1242 (by norm_num) (by norm_num)

lemma b1284 : Encl e1284 (3277809141 / 250000000000 : ℝ) (13111236579 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1282 b1283 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1285 : Encl e1285 (38801142833 / 1000000000000 : ℝ) (9700285719 / 250000000000 : ℝ) := by
  exact Encl.sub b1280 b1233 (by norm_num) (by norm_num)

lemma b1286 : Encl e1286 (113875875449 / 500000000000 : ℝ) (113875875521 / 500000000000 : ℝ) := by
  exact Encl.sub b183 b1264 (by norm_num) (by norm_num)

lemma b1287 : Encl e1287 (8837028217 / 1000000000000 : ℝ) (8837028233 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1285 b1286 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1288 : Encl e1288 (21948264781 / 1000000000000 : ℝ) (5487066203 / 250000000000 : ℝ) := by
  exact Encl.add b1284 b1287 (by norm_num) (by norm_num)

lemma b1289 : Encl e1289 (23988419341 / 200000000000 : ℝ) (29985524177 / 250000000000 : ℝ) := by
  exact Encl.sub b4 b1214 (by norm_num) (by norm_num)

lemma b1290 : Encl e1290 (91495252223 / 500000000000 : ℝ) (18299050471 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1288 b1289 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1291 : Encl e1291 (-107195367 / 250000000000 : ℝ) (-107195259 / 250000000000 : ℝ) := by
  exact Encl.add b1270 b1290 (by norm_num) (by norm_num)

lemma b1292 : Encl e1292 (872727272727 / 1000000000000 : ℝ) (109090909091 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1293 : Encl e1293 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b1292 (by norm_num) (by norm_num)

lemma b1294 : Encl e1294 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b1293 b5 (by norm_num) (by norm_num)

lemma b1295 : Encl e1295 (11 / 5 : ℝ) (11 / 5 : ℝ) := by
  exact Encl.mul_nonneg b23 b1145 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1296 : Encl e1296 (1696266388467 / 1000000000000 : ℝ) (169626638847 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1295 b1156 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1297 : Encl e1297 (10798767221 / 20000000000 : ℝ) (134984590263 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1296 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1298 : Encl e1298 (110814237433 / 500000000000 : ℝ) (221628474869 / 1000000000000 : ℝ) := by
  exact Encl.add b1294 b1297 (by norm_num) (by norm_num)

lemma b1299 : Encl e1299 (121 / 50 : ℝ) (121 / 50 : ℝ) := by
  exact Encl.mul_nonneg b23 b1150 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1300 : Encl e1300 (1865893027313 / 1000000000000 : ℝ) (1865893027317 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1299 b1156 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1301 : Encl e1301 (2503742840451 / 500000000000 : ℝ) (5007485680907 / 1000000000000 : ℝ) := by
  exact Encl.add b0 b1300 (by norm_num) (by norm_num)

lemma b1302 : Encl e1302 (69929412519 / 31250000000 : ℝ) (223774120061 / 100000000000 : ℝ) := by
  exact Encl.sqrt b1301 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1303 : Encl e1303 (1424590293747 / 1000000000000 : ℝ) (1424590293751 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b1302 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1304 : Encl e1304 (1331 / 1000 : ℝ) (1331 / 1000 : ℝ) := by
  exact Encl.pow b1145 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1305 : Encl e1305 (89177 / 500000 : ℝ) (89177 / 500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b1304 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1306 : Encl e1306 (89177 / 500000 : ℝ) (89177 / 500000 : ℝ) := by
  exact Encl.min b1305 b941 (by norm_num) (by norm_num)

lemma b1307 : Encl e1307 (110814237433 / 250000000000 : ℝ) (221628474869 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1298 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1308 : Encl e1308 (267531 / 250000 : ℝ) (267531 / 250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b1306 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1309 : Encl e1309 (1014728752519 / 500000000000 : ℝ) (40589150101 / 20000000000 : ℝ) := by
  exact Encl.pow b1303 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1310 : Encl e1310 (2171771183121 / 1000000000000 : ℝ) (434354236627 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1308 b1309 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1311 : Encl e1311 (481326335073 / 1000000000000 : ℝ) (481326335083 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1310 b1298 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1312 : Encl e1312 (85951131263 / 50000000000 : ℝ) (1719022625297 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1311 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1313 : Encl e1313 (135951131263 / 50000000000 : ℝ) (2719022625297 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1312 (by norm_num) (by norm_num)

lemma b1314 : Encl e1314 (824472956691 / 500000000000 : ℝ) (824472956697 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1313 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1315 : Encl e1315 (1324472956691 / 500000000000 : ℝ) (1324472956697 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1314 (by norm_num) (by norm_num)

lemma b1316 : Encl e1316 (167333333417 / 1000000000000 : ℝ) (167333333421 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1307 b1315 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1317 : Encl e1317 (825868197 / 500000000000 : ℝ) (825868197 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1306 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1318 : Encl e1318 (10859028289 / 200000000000 : ℝ) (13573785363 / 250000000000 : ℝ) := by
  exact Encl.sub b1298 b1316 (by norm_num) (by norm_num)

lemma b1319 : Encl e1319 (1905640579 / 50000000000 : ℝ) (19056405793 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1318 b1303 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1320 : Encl e1320 (726293203 / 500000000000 : ℝ) (1452586407 / 1000000000000 : ℝ) := by
  exact Encl.pow b1319 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b1321 : Encl e1321 (406724193 / 1000000000000 : ℝ) (203362097 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1320 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1322 : Encl e1322 (468540771 / 100000000000 : ℝ) (146418991 / 31250000000 : ℝ) := by
  exact Encl.pow b1316 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b1323 : Encl e1323 (417830603 / 500000000000 : ℝ) (104457651 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1306 b1322 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b1324 : Encl e1324 (1242385399 / 1000000000000 : ℝ) (621192701 / 500000000000 : ℝ) := by
  exact Encl.add b1321 b1323 (by norm_num) (by norm_num)

lemma b1325 : Encl e1325 (1242385399 / 1000000000000 : ℝ) (621192701 / 500000000000 : ℝ) := by
  exact Encl.min b1317 b1324 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_110 : Encl (twoChordBaseline (11 / 10 : ℝ)) (-107195367 / 250000000000 : ℝ) (-107195259 / 250000000000 : ℝ) := by
  exact b1291

lemma gain_enclosure_110 : Encl (gain (11 / 10 : ℝ)) (1242385399 / 1000000000000 : ℝ) (621192701 / 500000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b1325

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

lemma baseline_lower_110 : (-107195367 / 250000000000 : ℝ) ≤ baseline (11 / 10 : ℝ) :=
  (baseline_enclosure_110).1.trans (twoChordBaseline_le_of_range (h := (11 / 10 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_110_oai : (813603931 / 1000000000000 : ℝ) ≤ baseline (11 / 10 : ℝ) + gain (11 / 10 : ℝ) := by
  have hb := baseline_lower_110
  have hg := (gain_enclosure_110).1
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_110_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_110_oai

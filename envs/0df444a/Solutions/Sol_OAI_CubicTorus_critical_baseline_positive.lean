-- Prove2me | solution 1 for OAI.CubicTorus.critical_baseline_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:59:14.842204+00:00
-- url     : https://prove2.me/submissions/f641ba3a-2de5-4dd4-b7e8-132194b1eff9

import Mathlib
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_concaveOn_baseline_corrected
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_linearBaseline_eq_of_range

section
-- module Solutions.OAIQ079_CT.Compat
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SectionExtentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

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

end CubicTorus.Shape
end
end
end
end

end OAI
end

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

namespace CubicTorus.Scalar
open Set _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma semiconcave_chord_bound {f : ℝ → ℝ} {a b c x : ℝ} (hab : a < b) (hc : 0 ≤ c)
    (hf : ConcaveOn ℝ (Icc a b) (fun y ↦ f y - c * y ^ 2)) (hx : x ∈ Icc a b) :
    min (f a) (f b) - c * (b - a) ^ 2 / 4 ≤ f x := by
  let w := (b - x) / (b - a)
  let v := (x - a) / (b - a)
  have hd : 0 < b - a := sub_pos.2 hab
  have hw : 0 ≤ w := div_nonneg (sub_nonneg.2 hx.2) hd.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.2 hx.1) hd.le
  have hsum : w + v = 1 := by dsimp [w, v]; field_simp; ring
  have harg : w * a + v * b = x := by dsimp [w, v]; field_simp; ring
  have hcon := hf.2 (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hw hv hsum
  simp only [smul_eq_mul, harg] at hcon
  have hmin : min (f a) (f b) ≤ w * f a + v * f b := by
    have ha := mul_le_mul_of_nonneg_left (min_le_left (f a) (f b)) hw
    have hb := mul_le_mul_of_nonneg_left (min_le_right (f a) (f b)) hv
    calc
      _ = w * min (f a) (f b) + v * min (f a) (f b) := by rw [← add_mul, hsum, one_mul]
      _ ≤ _ := add_le_add ha hb
  have hcorr : w * c * a ^ 2 + v * c * b ^ 2 - c * x ^ 2 = c * (x - a) * (b - x) := by
    dsimp [w, v]
    field_simp
    ring
  have hprod : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - a - b)]
  have hprod' := mul_le_mul_of_nonneg_left hprod hc
  nlinarith only [hcon, hmin, hcorr, hprod']

end CubicTorus.Scalar

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

lemma b8 : Encl e8 (49 / 50 : ℝ) (49 / 50 : ℝ) := by
  exact Encl.exact (49 / 50 : ℝ)

lemma b9 : Encl e9 (7 / 25 : ℝ) (7 / 25 : ℝ) := by
  exact Encl.exact (7 / 25 : ℝ)

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

lemma b3106 : Encl e3106 (81 / 50 : ℝ) (81 / 50 : ℝ) := by
  exact Encl.exact (81 / 50 : ℝ)

lemma b3107 : Encl e3107 (515662015617 / 1000000000000 : ℝ) (257831007809 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3106 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3108 : Encl e3108 (3969 / 2500 : ℝ) (3969 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b3106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3109 : Encl e3109 (101069755061 / 200000000000 : ℝ) (252674387653 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3108 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3110 : Encl e3110 (6561 / 2500 : ℝ) (6561 / 2500 : ℝ) := by
  exact Encl.pow b3106 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3111 : Encl e3111 (6561 / 625 : ℝ) (6561 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b3110 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3112 : Encl e3112 (1670744930601 / 500000000000 : ℝ) (3341489861203 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3111 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3113 : Encl e3113 (2170744930601 / 500000000000 : ℝ) (4341489861203 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3112 (by norm_num) (by norm_num)

lemma b3114 : Encl e3114 (260453026631 / 125000000000 : ℝ) (2083624213049 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3113 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3115 : Encl e3115 (385453026631 / 125000000000 : ℝ) (3083624213049 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3114 (by norm_num) (by norm_num)

lemma b3116 : Encl e3116 (648587461317 / 1000000000000 : ℝ) (648587461319 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b3115 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3117 : Encl e3117 (11350280573 / 62500000000 : ℝ) (18160448917 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3118 : Encl e3118 (686953264473 / 1000000000000 : ℝ) (171738316119 / 250000000000 : ℝ) := by
  exact Encl.add b3109 b3117 (by norm_num) (by norm_num)

lemma b3119 : Encl e3119 (-313046735527 / 1000000000000 : ℝ) (-78261683881 / 250000000000 : ℝ) := by
  exact Encl.sub b3118 b5 (by norm_num) (by norm_num)

lemma b3120 : Encl e3120 (598535408777 / 500000000000 : ℝ) (239414163511 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b3110 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3121 : Encl e3121 (5318146287 / 20000000000 : ℝ) (16619207147 / 62500000000 : ℝ) := by
  exact Encl.pow b3107 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3122 : Encl e3122 (45880792853 / 62500000000 : ℝ) (14681853713 / 20000000000 : ℝ) := by
  exact Encl.sub b5 b3121 (by norm_num) (by norm_num)

lemma b3123 : Encl e3123 (428396045047 / 500000000000 : ℝ) (53549505631 / 62500000000 : ℝ) := by
  exact Encl.sqrt b3122 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3124 : Encl e3124 (-19012542343 / 100000000000 : ℝ) (-190125423427 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b3123 (by norm_num) (by norm_num)

lemma b3125 : Encl e3125 (314482403229 / 500000000000 : ℝ) (9827575101 / 15625000000 : ℝ) := by
  exact Encl.pow b3123 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b3126 : Encl e3126 (104827467743 / 500000000000 : ℝ) (3275858367 / 15625000000 : ℝ) := by
  exact Encl.div_nonneg b3125 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3127 : Encl e3127 (2441189007 / 125000000000 : ℝ) (19529512061 / 1000000000000 : ℝ) := by
  exact Encl.add b3124 b3126 (by norm_num) (by norm_num)

lemma b3128 : Encl e3128 (9569460907 / 500000000000 : ℝ) (956946091 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b3127 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3129 : Encl e3129 (62070440991 / 200000000000 : ℝ) (310352204959 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3121 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3130 : Encl e3130 (-337929559009 / 200000000000 : ℝ) (-1689647795041 / 1000000000000 : ℝ) := by
  exact Encl.sub b3129 b23 (by norm_num) (by norm_num)

lemma b3131 : Encl e3131 (428396045047 / 250000000000 : ℝ) (53549505631 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3132 : Encl e3132 (23936385143 / 1000000000000 : ℝ) (23936385151 / 1000000000000 : ℝ) := by
  exact Encl.add b3130 b3131 (by norm_num) (by norm_num)

lemma b3133 : Encl e3133 (239363851 / 500000000000 : ℝ) (59840963 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b3132 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3134 : Encl e3134 (1866019411 / 100000000000 : ℝ) (9330097059 / 500000000000 : ℝ) := by
  exact Encl.sub b3128 b3133 (by norm_num) (by norm_num)

lemma b3135 : Encl e3135 (11168786909 / 500000000000 : ℝ) (22337573829 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3120 b3134 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3136 : Encl e3136 (-290709161709 / 1000000000000 : ℝ) (-58141832339 / 200000000000 : ℝ) := by
  exact Encl.add b3119 b3135 (by norm_num) (by norm_num)

lemma b3137 : Encl e3137 (928396045047 / 500000000000 : ℝ) (116049505631 / 62500000000 : ℝ) := by
  exact Encl.add b5 b3123 (by norm_num) (by norm_num)

lemma b3138 : Encl e3138 (277716615859 / 1000000000000 : ℝ) (277716615861 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3107 b3137 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3139 : Encl e3139 (19281629681 / 250000000000 : ℝ) (38563259363 / 500000000000 : ℝ) := by
  exact Encl.pow b3138 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3140 : Encl e3140 (269281629681 / 250000000000 : ℝ) (538563259363 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3139 (by norm_num) (by norm_num)

lemma b3141 : Encl e3141 (1037847059409 / 1000000000000 : ℝ) (1037847059411 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3140 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3142 : Encl e3142 (2037847059409 / 1000000000000 : ℝ) (2037847059411 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3141 (by norm_num) (by norm_num)

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

lemma b3143 : Encl e3143 (136279420271 / 1000000000000 : ℝ) (136279420273 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3138 b3142 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3144 : Encl e3144 (541780137497 / 1000000000000 : ℝ) (270890068753 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e3107) (a := (136279420271 / 1000000000000 : ℝ)) (b := (136279420273 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (515662015617 / 1000000000000 : ℝ) by norm_num).trans b3107.1
        exact b3107.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e3107) (136279420271 / 1000000000000 : ℝ) (136279420273 / 1000000000000 : ℝ) from b3143) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b3145 : Encl e3145 (276307870123 / 1000000000000 : ℝ) (276307870129 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b3144 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3146 : Encl e3146 (63168596913 / 250000000000 : ℝ) (252674387653 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b3107 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3147 : Encl e3147 (216489416709 / 1000000000000 : ℝ) (216489416711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3146 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3148 : Encl e3148 (14954613353 / 250000000000 : ℝ) (2990922671 / 50000000000 : ℝ) := by
  exact Encl.sub b3145 b3147 (by norm_num) (by norm_num)

lemma b3149 : Encl e3149 (428396045047 / 10000000000 : ℝ) (53549505631 / 1250000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3150 : Encl e3150 (6018519797 / 500000000000 : ℝ) (2407407919 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b3107 b3149 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3151 : Encl e3151 (47781413817 / 1000000000000 : ℝ) (23890706913 / 500000000000 : ℝ) := by
  exact Encl.sub b3148 b3150 (by norm_num) (by norm_num)

lemma b3152 : Encl e3152 (236185677843 / 500000000000 : ℝ) (236185677913 / 500000000000 : ℝ) := by
  exact Encl.sub b183 b3151 (by norm_num) (by norm_num)

lemma b3153 : Encl e3153 (72896814149 / 250000000000 : ℝ) (291587256683 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3152 b3106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3154 : Encl e3154 (878094887 / 1000000000000 : ℝ) (219523747 / 250000000000 : ℝ) := by
  exact Encl.add b3136 b3153 (by norm_num) (by norm_num)

lemma b3189 : Encl e3189 (17 / 10 : ℝ) (17 / 10 : ℝ) := by
  exact Encl.exact (17 / 10 : ℝ)

lemma b3190 : Encl e3190 (33820425407 / 62500000000 : ℝ) (541126806513 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3189 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3191 : Encl e3191 (833 / 500 : ℝ) (833 / 500 : ℝ) := by
  exact Encl.mul_nonneg b8 b3189 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3192 : Encl e3192 (265152135191 / 500000000000 : ℝ) (530304270383 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3191 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3193 : Encl e3193 (289 / 100 : ℝ) (289 / 100 : ℝ) := by
  exact Encl.pow b3189 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3194 : Encl e3194 (289 / 25 : ℝ) (289 / 25 : ℝ) := by
  exact Encl.mul_nonneg b17 b3193 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3195 : Encl e3195 (919915571071 / 250000000000 : ℝ) (735932456857 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b3194 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3196 : Encl e3196 (1169915571071 / 250000000000 : ℝ) (935932456857 / 200000000000 : ℝ) := by
  exact Encl.add b5 b3195 (by norm_num) (by norm_num)

lemma b3197 : Encl e3197 (2163252709297 / 1000000000000 : ℝ) (1081626354649 / 500000000000 : ℝ) := by
  exact Encl.sqrt b3196 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3198 : Encl e3198 (3163252709297 / 1000000000000 : ℝ) (1581626354649 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3197 (by norm_num) (by norm_num)

lemma b3199 : Encl e3199 (316130291159 / 500000000000 : ℝ) (632260582319 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b3198 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3200 : Encl e3200 (177032963049 / 1000000000000 : ℝ) (3540659261 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3199 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3201 : Encl e3201 (707337233431 / 1000000000000 : ℝ) (707337233433 / 1000000000000 : ℝ) := by
  exact Encl.add b3192 b3200 (by norm_num) (by norm_num)

lemma b3202 : Encl e3202 (-292662766569 / 1000000000000 : ℝ) (-292662766567 / 1000000000000 : ℝ) := by
  exact Encl.sub b3201 b5 (by norm_num) (by norm_num)

lemma b3203 : Encl e3203 (543528140759 / 500000000000 : ℝ) (1087056281519 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b3193 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3204 : Encl e3204 (11712728829 / 40000000000 : ℝ) (292818220727 / 1000000000000 : ℝ) := by
  exact Encl.pow b3190 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3205 : Encl e3205 (707181779273 / 1000000000000 : ℝ) (28287271171 / 40000000000 : ℝ) := by
  exact Encl.sub b5 b3204 (by norm_num) (by norm_num)

lemma b3206 : Encl e3206 (4204705041 / 5000000000 : ℝ) (420470504101 / 500000000000 : ℝ) := by
  exact Encl.sqrt b3205 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3207 : Encl e3207 (-5446073173 / 31250000000 : ℝ) (-174274341533 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b3206 (by norm_num) (by norm_num)

lemma b3208 : Encl e3208 (297349079221 / 500000000000 : ℝ) (594698158447 / 1000000000000 : ℝ) := by
  exact Encl.pow b3206 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b3209 : Encl e3209 (4955817987 / 25000000000 : ℝ) (198232719483 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3208 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3210 : Encl e3210 (2994797243 / 125000000000 : ℝ) (479167559 / 20000000000 : ℝ) := by
  exact Encl.add b3207 b3209 (by norm_num) (by norm_num)

lemma b3211 : Encl e3211 (4695842077 / 200000000000 : ℝ) (23479210391 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b3210 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3212 : Encl e3212 (348203046193 / 1000000000000 : ℝ) (348203046197 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3204 b3206 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3213 : Encl e3213 (-1651796953807 / 1000000000000 : ℝ) (-1651796953803 / 1000000000000 : ℝ) := by
  exact Encl.sub b3212 b23 (by norm_num) (by norm_num)

lemma b3214 : Encl e3214 (4204705041 / 2500000000 : ℝ) (420470504101 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3206 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3215 : Encl e3215 (30085062593 / 1000000000000 : ℝ) (30085062601 / 1000000000000 : ℝ) := by
  exact Encl.add b3213 b3214 (by norm_num) (by norm_num)

lemma b3216 : Encl e3216 (601701251 / 1000000000000 : ℝ) (601701253 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3215 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3217 : Encl e3217 (5719377283 / 250000000000 : ℝ) (1143875457 / 50000000000 : ℝ) := by
  exact Encl.sub b3211 b3216 (by norm_num) (by norm_num)

lemma b3218 : Encl e3218 (24869140007 / 1000000000000 : ℝ) (24869140017 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3203 b3217 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3219 : Encl e3219 (-133896813281 / 500000000000 : ℝ) (-5355872531 / 20000000000 : ℝ) := by
  exact Encl.add b3202 b3218 (by norm_num) (by norm_num)

lemma b3220 : Encl e3220 (9204705041 / 5000000000 : ℝ) (920470504101 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3206 (by norm_num) (by norm_num)

lemma b3221 : Encl e3221 (73485082371 / 250000000000 : ℝ) (146970164743 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3190 b3220 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3222 : Encl e3222 (86400917297 / 1000000000000 : ℝ) (86400917299 / 1000000000000 : ℝ) := by
  exact Encl.pow b3221 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3223 : Encl e3223 (1086400917297 / 1000000000000 : ℝ) (1086400917299 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3222 (by norm_num) (by norm_num)

lemma b3224 : Encl e3224 (32572049303 / 31250000000 : ℝ) (521152788849 / 500000000000 : ℝ) := by
  exact Encl.sqrt b3223 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3225 : Encl e3225 (63822049303 / 31250000000 : ℝ) (1021152788849 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3224 (by norm_num) (by norm_num)

lemma b3226 : Encl e3226 (143925734079 / 1000000000000 : ℝ) (143925734081 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3221 b3225 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3227 : Encl e3227 (571776467901 / 1000000000000 : ℝ) (57177646791 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e3190) (a := (143925734079 / 1000000000000 : ℝ)) (b := (143925734081 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (33820425407 / 62500000000 : ℝ) by norm_num).trans b3190.1
        exact b3190.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e3190) (143925734079 / 1000000000000 : ℝ) (143925734081 / 1000000000000 : ℝ) from b3226) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b3228 : Encl e3228 (291605998629 / 1000000000000 : ℝ) (58321199727 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b3227 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3229 : Encl e3229 (26515213519 / 100000000000 : ℝ) (33144016899 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b3190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3230 : Encl e3230 (222977303893 / 1000000000000 : ℝ) (27872162987 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b3229 b3206 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3231 : Encl e3231 (68628694733 / 1000000000000 : ℝ) (34314347371 / 500000000000 : ℝ) := by
  exact Encl.sub b3228 b3230 (by norm_num) (by norm_num)

lemma b3232 : Encl e3232 (4204705041 / 100000000 : ℝ) (420470504101 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b3206 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3233 : Encl e3233 (3217388623 / 250000000000 : ℝ) (12869554493 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3190 b3232 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3234 : Encl e3234 (696989253 / 12500000000 : ℝ) (223036561 / 4000000000 : ℝ) := by
  exact Encl.sub b3231 b3233 (by norm_num) (by norm_num)

lemma b3235 : Encl e3235 (232196814631 / 500000000000 : ℝ) (464393629403 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b3234 (by norm_num) (by norm_num)

lemma b3236 : Encl e3236 (54634544619 / 200000000000 : ℝ) (273172723179 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3235 b3189 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3237 : Encl e3237 (5379096533 / 1000000000000 : ℝ) (5379096629 / 1000000000000 : ℝ) := by
  exact Encl.add b3219 b3236 (by norm_num) (by norm_num)

lemma b3238 : Encl e3238 (19 / 10 : ℝ) (19 / 10 : ℝ) := by
  exact Encl.exact (19 / 10 : ℝ)

lemma b3239 : Encl e3239 (604788783749 / 1000000000000 : ℝ) (483831027 / 800000000 : ℝ) := by
  exact Encl.div_nonneg b3238 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3240 : Encl e3240 (931 / 500 : ℝ) (931 / 500 : ℝ) := by
  exact Encl.mul_nonneg b8 b3238 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3241 : Encl e3241 (296346504037 / 500000000000 : ℝ) (23707720323 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b3240 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3242 : Encl e3242 (361 / 100 : ℝ) (361 / 100 : ℝ) := by
  exact Encl.pow b3238 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3243 : Encl e3243 (361 / 25 : ℝ) (361 / 25 : ℝ) := by
  exact Encl.mul_nonneg b17 b3242 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3244 : Encl e3244 (4596394756493 / 1000000000000 : ℝ) (2298197378247 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3243 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3245 : Encl e3245 (5596394756493 / 1000000000000 : ℝ) (2798197378247 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3244 (by norm_num) (by norm_num)

lemma b3246 : Encl e3246 (591417510969 / 250000000000 : ℝ) (2365670043877 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3245 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3247 : Encl e3247 (841417510969 / 250000000000 : ℝ) (3365670043877 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3246 (by norm_num) (by norm_num)

lemma b3248 : Encl e3248 (594235315383 / 1000000000000 : ℝ) (74279414423 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b3247 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3249 : Encl e3249 (166385888307 / 1000000000000 : ℝ) (41596472077 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3248 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3250 : Encl e3250 (759078896381 / 1000000000000 : ℝ) (759078896383 / 1000000000000 : ℝ) := by
  exact Encl.add b3241 b3249 (by norm_num) (by norm_num)

lemma b3251 : Encl e3251 (-240921103619 / 1000000000000 : ℝ) (-240921103617 / 1000000000000 : ℝ) := by
  exact Encl.sub b3250 b5 (by norm_num) (by norm_num)

lemma b3252 : Encl e3252 (435123636231 / 500000000000 : ℝ) (870247272463 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b3242 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3253 : Encl e3253 (91442368237 / 250000000000 : ℝ) (7315389459 / 20000000000 : ℝ) := by
  exact Encl.pow b3239 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3254 : Encl e3254 (12684610541 / 20000000000 : ℝ) (158557631763 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b3253 (by norm_num) (by norm_num)

lemma b3255 : Encl e3255 (796385915903 / 1000000000000 : ℝ) (398192957953 / 500000000000 : ℝ) := by
  exact Encl.sqrt b3254 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3256 : Encl e3256 (-3242981231 / 25000000000 : ℝ) (-32429812309 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b3255 (by norm_num) (by norm_num)

lemma b3257 : Encl e3257 (505092259177 / 1000000000000 : ℝ) (505092259183 / 1000000000000 : ℝ) := by
  exact Encl.pow b3255 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b3258 : Encl e3258 (21045510799 / 125000000000 : ℝ) (33672817279 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b3257 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3259 : Encl e3259 (1207651161 / 31250000000 : ℝ) (38644837159 / 1000000000000 : ℝ) := by
  exact Encl.add b3256 b3258 (by norm_num) (by norm_num)

lemma b3260 : Encl e3260 (4733992551 / 125000000000 : ℝ) (591749069 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b3259 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3261 : Encl e3261 (459286717209 / 1000000000000 : ℝ) (229643358607 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3253 b3255 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3262 : Encl e3262 (-1540713282791 / 1000000000000 : ℝ) (-770356641393 / 500000000000 : ℝ) := by
  exact Encl.sub b3261 b23 (by norm_num) (by norm_num)

lemma b3263 : Encl e3263 (796385915903 / 500000000000 : ℝ) (398192957953 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3255 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3264 : Encl e3264 (10411709803 / 200000000000 : ℝ) (26029274513 / 500000000000 : ℝ) := by
  exact Encl.add b3262 b3263 (by norm_num) (by norm_num)

lemma b3265 : Encl e3265 (52058549 / 50000000000 : ℝ) (1041170981 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3264 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3266 : Encl e3266 (36830769427 / 1000000000000 : ℝ) (9207692359 / 250000000000 : ℝ) := by
  exact Encl.sub b3260 b3265 (by norm_num) (by norm_num)

lemma b3267 : Encl e3267 (8012969159 / 250000000000 : ℝ) (6410375329 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b3252 b3266 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3268 : Encl e3268 (-208869226983 / 1000000000000 : ℝ) (-52217306743 / 250000000000 : ℝ) := by
  exact Encl.add b3251 b3267 (by norm_num) (by norm_num)

lemma b3269 : Encl e3269 (1796385915903 / 1000000000000 : ℝ) (898192957953 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3255 (by norm_num) (by norm_num)

lemma b3270 : Encl e3270 (67333948501 / 200000000000 : ℝ) (336669742507 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3239 b3269 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3271 : Encl e3271 (56673257759 / 500000000000 : ℝ) (354207861 / 3125000000 : ℝ) := by
  exact Encl.pow b3270 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b3272 : Encl e3272 (556673257759 / 500000000000 : ℝ) (3479207861 / 3125000000 : ℝ) := by
  exact Encl.add b5 b3271 (by norm_num) (by norm_num)

lemma b3273 : Encl e3273 (52757618301 / 50000000000 : ℝ) (527576183011 / 500000000000 : ℝ) := by
  exact Encl.sqrt b3272 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3274 : Encl e3274 (102757618301 / 50000000000 : ℝ) (1027576183011 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3273 (by norm_num) (by norm_num)

lemma b3275 : Encl e3275 (16381741231 / 100000000000 : ℝ) (20477176539 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b3270 b3274 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3276 : Encl e3276 (649500622237 / 1000000000000 : ℝ) (324750311123 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e3239) (a := (16381741231 / 100000000000 : ℝ)) (b := (20477176539 / 125000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (604788783749 / 1000000000000 : ℝ) by norm_num).trans b3239.1
        exact b3239.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e3239) (16381741231 / 100000000000 : ℝ) (20477176539 / 125000000000 : ℝ) from b3275) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b3277 : Encl e3277 (16562265867 / 50000000000 : ℝ) (165622658673 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b3276 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3278 : Encl e3278 (296346504037 / 1000000000000 : ℝ) (148173252019 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b3239 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3279 : Encl e3279 (118003091021 / 500000000000 : ℝ) (59001545511 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3278 b3255 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3280 : Encl e3280 (1488111489 / 15625000000 : ℝ) (11904891913 / 125000000000 : ℝ) := by
  exact Encl.sub b3277 b3279 (by norm_num) (by norm_num)

lemma b3281 : Encl e3281 (796385915903 / 20000000000 : ℝ) (398192957953 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b3255 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3282 : Encl e3282 (15188334491 / 1000000000000 : ℝ) (3797083623 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b3239 b3281 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3283 : Encl e3283 (20012700201 / 250000000000 : ℝ) (80050800813 / 1000000000000 : ℝ) := by
  exact Encl.sub b3280 b3282 (by norm_num) (by norm_num)

lemma b3284 : Encl e3284 (440101968699 / 1000000000000 : ℝ) (440101968839 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b3283 (by norm_num) (by norm_num)

lemma b3285 : Encl e3285 (3619259611 / 15625000000 : ℝ) (231632615179 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3284 b3238 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b3286 : Encl e3286 (22763388121 / 1000000000000 : ℝ) (22763388207 / 1000000000000 : ℝ) := by
  exact Encl.add b3268 b3285 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_162 : Encl (linearBaseline (81 / 50 : ℝ)) (878094887 / 1000000000000 : ℝ) (219523747 / 250000000000 : ℝ) := by
  exact b3154

lemma baseline_enclosure_170 : Encl (linearBaseline (17 / 10 : ℝ)) (5379096533 / 1000000000000 : ℝ) (5379096629 / 1000000000000 : ℝ) := by
  exact b3237

lemma baseline_enclosure_190 : Encl (linearBaseline (19 / 10 : ℝ)) (22763388121 / 1000000000000 : ℝ) (22763388207 / 1000000000000 : ℝ) := by
  exact b3286

lemma baseline_lower_162 : (878094887 / 1000000000000 : ℝ) ≤ baseline (81 / 50 : ℝ) :=
  (baseline_enclosure_162).1.trans ((linearBaseline_eq_of_range (h := (81 / 50 : ℝ)) (by norm_num) (by norm_num)).le)

lemma baseline_lower_170 : (5379096533 / 1000000000000 : ℝ) ≤ baseline (17 / 10 : ℝ) :=
  (baseline_enclosure_170).1.trans ((linearBaseline_eq_of_range (h := (17 / 10 : ℝ)) (by norm_num) (by norm_num)).le)

lemma baseline_lower_190 : (22763388121 / 1000000000000 : ℝ) ≤ baseline (19 / 10 : ℝ) :=
  (baseline_enclosure_190).1.trans ((linearBaseline_eq_of_range (h := (19 / 10 : ℝ)) (by norm_num) (by norm_num)).le)

end CubicTorus.Scalar.Cert

end
end
end
end ReusedScalar205

end

section

noncomputable section
open MeasureTheory Set
namespace CubicTorus

lemma unitPlanarProfile_eq_reused (v : ℝ) :
    unitPlanarProfile v=2*ReusedScalar205.CubicTorus.Scalar.planarProfile v := by
  unfold unitPlanarProfile ReusedScalar205.CubicTorus.Scalar.planarProfile
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2),
    mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)]
  ring_nf

lemma nestingBaseline_eq_reused {h : ℝ} (hh : 0<h) :
    nestingBaseline h=ReusedScalar205.CubicTorus.Scalar.baseline h := by
  have ht := Shape.t_spec hh
  have he : (∫ v in (0 : ℝ)..Shape.t h,sharpSectionWeight (2*h) v)=
      ∫ v in (0 : ℝ)..Shape.t h,
        ReusedScalar205.CubicTorus.Nesting.weight
          (h*v/ReusedScalar205.CubicTorus.Scalar.planarProfile v) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ht.1.le]
    intro v hv
    have hv1 : v<1 := hv.2.trans_lt ht.2.1
    rw [sharpSectionWeight,ite_eq_left ⟨hv.1,hv1⟩,unitPlanarProfile_eq_reused]
    have hac : 2*h*v/(2*ReusedScalar205.CubicTorus.Scalar.planarProfile v)=
        h*v/ReusedScalar205.CubicTorus.Scalar.planarProfile v := by ring
    rw [hac]
    rfl
  unfold nestingBaseline ReusedScalar205.CubicTorus.Scalar.baseline
  rw [he]
  rfl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace CubicTorus

lemma criticalCorrection_convex : ConvexOn ℝ (Ioi 0) criticalCorrection := by
  have hi : ConvexOn ℝ (Ioi (0 : ℝ)) (fun h : ℝ => h⁻¹) := by
    simpa using (strictConvexOn_zpow (m := -1) (by norm_num) (by norm_num)).convexOn
  refine ⟨convex_Ioi 0,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := mul_le_mul_of_nonneg_left (hi.2 hx hy ha hb hab) (show 0≤51*Real.pi/200 by positivity)
  simp only [smul_eq_mul] at hh ⊢
  unfold criticalCorrection
  nlinarith only [hh,hab]

lemma criticalCorrection_rational_upper {h : ℝ} (hh : 0<h) :
    criticalCorrection h≤(49/50 : ℝ)/(3141592/1000000)*h+
      (51*(3141593/1000000)/200)*h⁻¹-1 := by
  have hpl : (3141592/1000000 : ℝ)≤Real.pi := by linarith [Real.pi_gt_d6]
  have hpu : Real.pi≤(3141593/1000000 : ℝ) := by linarith [Real.pi_lt_d6]
  have hl := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤49/50) (by norm_num) hpl) hh.le
  have hr := mul_le_mul_of_nonneg_right hpu (show 0≤(51/200 : ℝ)*h⁻¹ by positivity)
  unfold criticalCorrection
  nlinarith only [hl,hr]

lemma criticalCorrection_162 : criticalCorrection (81/50)≤-1/10000 := by
  have hh := criticalCorrection_rational_upper (h := 81/50) (by norm_num)
  norm_num at hh ⊢
  linarith
lemma criticalCorrection_170 : criticalCorrection (17/10)≤31/20000 := by
  have hh := criticalCorrection_rational_upper (h := 17/10) (by norm_num)
  norm_num at hh ⊢
  linarith
lemma criticalCorrection_190 : criticalCorrection (19/10)≤717/50000 := by
  have hh := criticalCorrection_rational_upper (h := 19/10) (by norm_num)
  norm_num at hh ⊢
  linarith

lemma critical_baseline_chord {a b x l r : ℝ} (ha : 0<a) (hab : a<b)
    (hx : x∈Icc a b)
    (hl : l≤nestingBaseline a-criticalCorrection a)
    (hr : r≤nestingBaseline b-criticalCorrection b) :
    min l r-(b-a)^2/(4*a^2)≤nestingBaseline x-criticalCorrection x := by
  have hc := criticalCorrection_convex.subset (show Icc a b⊆Ioi 0 from fun y hy => ha.trans_le hy.1) (convex_Icc a b)
  have hf : ConcaveOn ℝ (Icc a b)
      (fun h => nestingBaseline h-criticalCorrection h-(1/a^2)*h^2) := by
    apply ((ReusedScalar205.CubicTorus.Scalar.concaveOn_baseline_corrected (b := b) ha).sub hc).congr
    intro y hy
    dsimp only [Pi.sub_apply]
    rw [nestingBaseline_eq_reused (ha.trans_le hy.1)]
    ring
  have hb := ReusedScalar205.CubicTorus.Scalar.semiconcave_chord_bound hab
    (show 0≤(1 : ℝ)/a^2 by positivity) hf hx
  have hm := min_le_min hl hr
  have he : (1/a^2)*(b-a)^2/4=(b-a)^2/(4*a^2) := by ring
  rw [he] at hb
  linarith

lemma critical_baseline_positive_oai {h : ℝ} (hh : h∈Icc (81/50 : ℝ) (19/10)) :
    0<nestingBaseline h-criticalCorrection h := by
  have hl : (978/1000000 : ℝ)≤nestingBaseline (81/50)-criticalCorrection (81/50) := by
    rw [nestingBaseline_eq_reused (by norm_num)]
    linarith [ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_162,criticalCorrection_162]
  have hm : (3829/1000000 : ℝ)≤nestingBaseline (17/10)-criticalCorrection (17/10) := by
    rw [nestingBaseline_eq_reused (by norm_num)]
    linarith [ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_170,criticalCorrection_170]
  have hr : (8423/1000000 : ℝ)≤nestingBaseline (19/10)-criticalCorrection (19/10) := by
    rw [nestingBaseline_eq_reused (by norm_num)]
    linarith [ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_190,criticalCorrection_190]
  by_cases hmidh : h≤17/10
  · have hb := critical_baseline_chord (by norm_num) (by norm_num) ⟨hh.1,hmidh⟩ hl hm
    have hp : (0 : ℝ) < min (978/1000000 : ℝ) (3829/1000000)-((17/10 : ℝ)-81/50)^2/(4*(81/50 : ℝ)^2) := by norm_num
    exact hp.trans_le hb
  · have hb := critical_baseline_chord (by norm_num) (by norm_num) ⟨(lt_of_not_ge hmidh).le,hh.2⟩ hm hr
    have hp : (0 : ℝ) < min (3829/1000000 : ℝ) (8423/1000000)-((19/10 : ℝ)-17/10)^2/(4*(17/10 : ℝ)^2) := by norm_num
    exact hp.trans_le hb

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.critical_baseline_positive_oai := @OAI.CubicTorus.critical_baseline_positive_oai

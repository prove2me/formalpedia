-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_84
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:36:01.047096+00:00
-- url     : https://prove2.me/submissions/38fd40cf-b2da-4e0c-a1ea-f89149c5239b

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures289To507
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

lemma b337 : Encl e337 (21 / 25 : ℝ) (21 / 25 : ℝ) := by
  exact Encl.exact (21 / 25 : ℝ)

lemma b338 : Encl e338 (133690152197 / 500000000000 : ℝ) (53476060879 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b337 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b339 : Encl e339 (114523939121 / 200000000000 : ℝ) (572619695607 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b337 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b340 : Encl e340 (1029 / 1250 : ℝ) (1029 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b8 b337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b341 : Encl e341 (131016349153 / 500000000000 : ℝ) (262032698307 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b340 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b342 : Encl e342 (441 / 625 : ℝ) (441 / 625 : ℝ) := by
  exact Encl.pow b337 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b343 : Encl e343 (1764 / 625 : ℝ) (1764 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b342 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b344 : Encl e344 (179679564553 / 200000000000 : ℝ) (449198911383 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b343 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b345 : Encl e345 (379679564553 / 200000000000 : ℝ) (949198911383 / 500000000000 : ℝ) := by
  exact Encl.add b5 b344 (by norm_num) (by norm_num)

lemma b346 : Encl e346 (86113973867 / 62500000000 : ℝ) (688911790937 / 500000000000 : ℝ) := by
  exact Encl.sqrt b345 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b347 : Encl e347 (148613973867 / 62500000000 : ℝ) (1188911790937 / 500000000000 : ℝ) := by
  exact Encl.add b5 b346 (by norm_num) (by norm_num)

lemma b348 : Encl e348 (33644211711 / 40000000000 : ℝ) (105138161597 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b347 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b349 : Encl e349 (235509481977 / 1000000000000 : ℝ) (117754740989 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b348 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b350 : Encl e350 (497542180283 / 1000000000000 : ℝ) (99508436057 / 200000000000 : ℝ) := by
  exact Encl.add b341 b349 (by norm_num) (by norm_num)

lemma b351 : Encl e351 (-502457819717 / 1000000000000 : ℝ) (-100491563943 / 200000000000 : ℝ) := by
  exact Encl.sub b350 b5 (by norm_num) (by norm_num)

lemma b352 : Encl e352 (4452370540801 / 1000000000000 : ℝ) (2226185270401 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b342 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b353 : Encl e353 (71492227177 / 1000000000000 : ℝ) (71492227179 / 1000000000000 : ℝ) := by
  exact Encl.pow b338 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b354 : Encl e354 (928507772821 / 1000000000000 : ℝ) (928507772823 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b353 (by norm_num) (by norm_num)

lemma b355 : Encl e355 (481795540873 / 500000000000 : ℝ) (240897770437 / 250000000000 : ℝ) := by
  exact Encl.sqrt b354 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b356 : Encl e356 (-148462207541 / 500000000000 : ℝ) (-296924415079 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b355 (by norm_num) (by norm_num)

lemma b357 : Encl e357 (894701809221 / 1000000000000 : ℝ) (223675452307 / 250000000000 : ℝ) := by
  exact Encl.pow b355 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b358 : Encl e358 (298233936407 / 1000000000000 : ℝ) (29823393641 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b357 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b359 : Encl e359 (52380853 / 40000000000 : ℝ) (1309521331 / 1000000000000 : ℝ) := by
  exact Encl.add b356 b358 (by norm_num) (by norm_num)

lemma b360 : Encl e360 (641665449 / 500000000000 : ℝ) (256666181 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b359 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b361 : Encl e361 (2318547921 / 31250000000 : ℝ) (2967741339 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b353 b355 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b362 : Encl e362 (-60181452079 / 31250000000 : ℝ) (-77032258661 / 40000000000 : ℝ) := by
  exact Encl.sub b361 b23 (by norm_num) (by norm_num)

lemma b363 : Encl e363 (481795540873 / 250000000000 : ℝ) (240897770437 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b355 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b364 : Encl e364 (343924241 / 250000000000 : ℝ) (1375696971 / 1000000000000 : ℝ) := by
  exact Encl.add b362 b363 (by norm_num) (by norm_num)

lemma b365 : Encl e365 (27513939 / 1000000000000 : ℝ) (1375697 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b364 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b366 : Encl e366 (627908479 / 500000000000 : ℝ) (627908483 / 500000000000 : ℝ) := by
  exact Encl.sub b360 b365 (by norm_num) (by norm_num)

lemma b367 : Encl e367 (1397840607 / 250000000000 : ℝ) (1118272493 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b352 b366 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b368 : Encl e368 (-496866457289 / 1000000000000 : ℝ) (-1987465829 / 4000000000 : ℝ) := by
  exact Encl.add b351 b367 (by norm_num) (by norm_num)

lemma b369 : Encl e369 (163946657897 / 500000000000 : ℝ) (163946657899 / 500000000000 : ℝ) := by
  exact Encl.pow b339 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b370 : Encl e370 (336053342101 / 500000000000 : ℝ) (336053342103 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b369 (by norm_num) (by norm_num)

lemma b371 : Encl e371 (409910564697 / 500000000000 : ℝ) (409910564699 / 500000000000 : ℝ) := by
  exact Encl.sqrt b370 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b372 : Encl e372 (909910564697 / 500000000000 : ℝ) (909910564699 / 500000000000 : ℝ) := by
  exact Encl.add b5 b371 (by norm_num) (by norm_num)

lemma b373 : Encl e373 (78664282763 / 250000000000 : ℝ) (62931426211 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b339 b372 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b374 : Encl e374 (99009110121 / 1000000000000 : ℝ) (24752277531 / 250000000000 : ℝ) := by
  exact Encl.pow b373 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b375 : Encl e375 (1099009110121 / 1000000000000 : ℝ) (274752277531 / 250000000000 : ℝ) := by
  exact Encl.add b5 b374 (by norm_num) (by norm_num)

lemma b376 : Encl e376 (262084088381 / 250000000000 : ℝ) (524168176763 / 500000000000 : ℝ) := by
  exact Encl.sqrt b375 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b377 : Encl e377 (512084088381 / 250000000000 : ℝ) (1024168176763 / 500000000000 : ℝ) := by
  exact Encl.add b5 b376 (by norm_num) (by norm_num)

lemma b378 : Encl e378 (153615948137 / 1000000000000 : ℝ) (7680797407 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b373 b377 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b379 : Encl e379 (304848875169 / 500000000000 : ℝ) (609697750351 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e339) (a := (153615948137 / 1000000000000 : ℝ)) (b := (7680797407 / 50000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (114523939121 / 200000000000 : ℝ) by norm_num).trans b339.1
        exact b339.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e339) (153615948137 / 1000000000000 : ℝ) (7680797407 / 50000000000 : ℝ) from b378) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b380 : Encl e380 (1214632237 / 3906250000 : ℝ) (7773646317 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b379 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b381 : Encl e381 (140291825423 / 500000000000 : ℝ) (8768239089 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b339 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b382 : Encl e382 (115014202763 / 500000000000 : ℝ) (230028405529 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b381 b371 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b383 : Encl e383 (80917447143 / 1000000000000 : ℝ) (40458723577 / 500000000000 : ℝ) := by
  exact Encl.sub b380 b382 (by norm_num) (by norm_num)

lemma b384 : Encl e384 (409910564697 / 10000000000 : ℝ) (409910564699 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b371 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b385 : Encl e385 (109135791 / 7812500000 : ℝ) (13969381249 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b339 b384 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b386 : Encl e386 (33474032947 / 500000000000 : ℝ) (33474032953 / 500000000000 : ℝ) := by
  exact Encl.sub b383 b385 (by norm_num) (by norm_num)

lemma b387 : Encl e387 (981795540873 / 500000000000 : ℝ) (490897770437 / 250000000000 : ℝ) := by
  exact Encl.add b5 b355 (by norm_num) (by norm_num)

lemma b388 : Encl e388 (34042258961 / 250000000000 : ℝ) (27233807169 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b338 b387 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b389 : Encl e389 (9271003161 / 500000000000 : ℝ) (18542006323 / 1000000000000 : ℝ) := by
  exact Encl.pow b388 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b390 : Encl e390 (509271003161 / 500000000000 : ℝ) (1018542006323 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b389 (by norm_num) (by norm_num)

lemma b391 : Encl e391 (1009228421281 / 1000000000000 : ℝ) (504614210641 / 500000000000 : ℝ) := by
  exact Encl.sqrt b390 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b392 : Encl e392 (2009228421281 / 1000000000000 : ℝ) (1004614210641 / 500000000000 : ℝ) := by
  exact Encl.add b5 b391 (by norm_num) (by norm_num)

lemma b393 : Encl e393 (3388590227 / 50000000000 : ℝ) (67771804541 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b388 b392 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b394 : Encl e394 (27067332207 / 100000000000 : ℝ) (10826932883 / 40000000000 : ℝ) := by
  apply Encl.arcsin (z := e338) (a := (3388590227 / 50000000000 : ℝ)) (b := (67771804541 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (133690152197 / 500000000000 : ℝ) by norm_num).trans b338.1
        exact b338.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e338) (3388590227 / 50000000000 : ℝ) (67771804541 / 1000000000000 : ℝ) from b393) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b395 : Encl e395 (27608678851 / 200000000000 : ℝ) (138043394259 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b394 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b396 : Encl e396 (131016349153 / 1000000000000 : ℝ) (65508174577 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b338 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b397 : Encl e397 (63123092803 / 500000000000 : ℝ) (15780773201 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b396 b355 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b398 : Encl e398 (11797208647 / 1000000000000 : ℝ) (11797208653 / 1000000000000 : ℝ) := by
  exact Encl.sub b395 b397 (by norm_num) (by norm_num)

lemma b399 : Encl e399 (481795540873 / 10000000000 : ℝ) (240897770437 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b355 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b400 : Encl e400 (2774831663 / 500000000000 : ℝ) (5549663327 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b338 b399 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b401 : Encl e401 (156188633 / 25000000000 : ℝ) (6247545327 / 1000000000000 : ℝ) := by
  exact Encl.sub b398 b400 (by norm_num) (by norm_num)

lemma b402 : Encl e402 (60700520567 / 1000000000000 : ℝ) (30350260293 / 500000000000 : ℝ) := by
  exact Encl.sub b386 b401 (by norm_num) (by norm_num)

lemma b403 : Encl e403 (18065631121 / 250000000000 : ℝ) (18065631127 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b402 b337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b404 : Encl e404 (-84920786561 / 200000000000 : ℝ) (-212301966371 / 500000000000 : ℝ) := by
  exact Encl.add b368 b403 (by norm_num) (by norm_num)

lemma b405 : Encl e405 (312472602843 / 200000000000 : ℝ) (781181507109 / 500000000000 : ℝ) := by
  exact Encl.add b339 b4 (by norm_num) (by norm_num)

lemma b406 : Encl e406 (781181507107 / 1000000000000 : ℝ) (781181507109 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b405 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b407 : Encl e407 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b339 b337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b408 : Encl e408 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b407 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b409 : Encl e409 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b407 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b410 : Encl e410 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b409 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b411 : Encl e411 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b410 (by norm_num) (by norm_num)

lemma b412 : Encl e412 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b411 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b413 : Encl e413 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b408 b412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b414 : Encl e414 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b409 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b415 : Encl e415 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b413 b414 (by norm_num) (by norm_num)

lemma b416 : Encl e416 (266261855241 / 500000000000 : ℝ) (266261855251 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b406 b415 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b417 : Encl e417 (929977984651 / 1000000000000 : ℝ) (464988992327 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b406 b337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b418 : Encl e418 (1648343060151 / 1000000000000 : ℝ) (824171530079 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b417 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b419 : Encl e419 (172971810387 / 200000000000 : ℝ) (432429525971 / 500000000000 : ℝ) := by
  exact Encl.pow b417 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b420 : Encl e420 (679258710987 / 1000000000000 : ℝ) (339629355497 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b419 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b421 : Encl e421 (1679258710987 / 1000000000000 : ℝ) (839629355497 / 500000000000 : ℝ) := by
  exact Encl.add b5 b420 (by norm_num) (by norm_num)

lemma b422 : Encl e422 (259172429937 / 200000000000 : ℝ) (161982768711 / 125000000000 : ℝ) := by
  exact Encl.sqrt b421 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b423 : Encl e423 (427205076269 / 200000000000 : ℝ) (26700317267 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b418 b422 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b424 : Encl e424 (679258710987 / 500000000000 : ℝ) (679258710993 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b419 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b425 : Encl e425 (777507959359 / 1000000000000 : ℝ) (388753979693 / 500000000000 : ℝ) := by
  exact Encl.sub b423 b424 (by norm_num) (by norm_num)

lemma b426 : Encl e426 (222608185509 / 500000000000 : ℝ) (111304092759 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b339 b425 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b427 : Encl e427 (43653669723 / 500000000000 : ℝ) (21826834871 / 250000000000 : ℝ) := by
  exact Encl.sub b416 b426 (by norm_num) (by norm_num)

lemma b428 : Encl e428 (122048909409 / 200000000000 : ℝ) (12204890941 / 20000000000 : ℝ) := by
  exact Encl.pow b406 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b429 : Encl e429 (74754957013 / 125000000000 : ℝ) (598039656109 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b428 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b430 : Encl e430 (401960343891 / 1000000000000 : ℝ) (50245042987 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b429 (by norm_num) (by norm_num)

lemma b431 : Encl e431 (7795109059 / 20000000000 : ℝ) (77951090591 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b428 (by norm_num) (by norm_num)

lemma b432 : Encl e432 (624303974799 / 1000000000000 : ℝ) (156075993701 / 250000000000 : ℝ) := by
  exact Encl.sqrt b431 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b433 : Encl e433 (321926785759 / 500000000000 : ℝ) (643853571533 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b430 b432 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b434 : Encl e434 (356146428467 / 1000000000000 : ℝ) (178073214241 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b433 (by norm_num) (by norm_num)

lemma b435 : Encl e435 (160667724739 / 500000000000 : ℝ) (321335449483 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b369 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b436 : Encl e436 (678664550517 / 1000000000000 : ℝ) (339332275261 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b435 (by norm_num) (by norm_num)

lemma b437 : Encl e437 (206955068057 / 250000000000 : ℝ) (827820272239 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b436 b371 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b438 : Encl e438 (172179727761 / 1000000000000 : ℝ) (43044931943 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b437 (by norm_num) (by norm_num)

lemma b439 : Encl e439 (36793340139 / 200000000000 : ℝ) (183966700721 / 1000000000000 : ℝ) := by
  exact Encl.sub b434 b438 (by norm_num) (by norm_num)

lemma b440 : Encl e440 (1003852699 / 62500000000 : ℝ) (8030821597 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b427 b439 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b441 : Encl e441 (95817845531 / 1000000000000 : ℝ) (95817845581 / 1000000000000 : ℝ) := by
  exact Encl.sub b425 b415 (by norm_num) (by norm_num)

lemma b442 : Encl e442 (1624303974799 / 1000000000000 : ℝ) (406075993701 / 250000000000 : ℝ) := by
  exact Encl.add b5 b432 (by norm_num) (by norm_num)

lemma b443 : Encl e443 (480933076089 / 1000000000000 : ℝ) (480933076093 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b406 b442 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b444 : Encl e444 (57824155919 / 250000000000 : ℝ) (231296623681 / 1000000000000 : ℝ) := by
  exact Encl.pow b443 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b445 : Encl e445 (307824155919 / 250000000000 : ℝ) (1231296623681 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b444 (by norm_num) (by norm_num)

lemma b446 : Encl e446 (1109638059763 / 1000000000000 : ℝ) (554819029883 / 500000000000 : ℝ) := by
  exact Encl.sqrt b445 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b447 : Encl e447 (2109638059763 / 1000000000000 : ℝ) (1054819029883 / 500000000000 : ℝ) := by
  exact Encl.add b5 b446 (by norm_num) (by norm_num)

lemma b448 : Encl e448 (227969472707 / 1000000000000 : ℝ) (22796947271 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b443 b447 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b449 : Encl e449 (896556101783 / 1000000000000 : ℝ) (179311220359 / 200000000000 : ℝ) := by
  apply Encl.arcsin (z := e406) (a := (227969472707 / 1000000000000 : ℝ)) (b := (22796947271 / 100000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (781181507107 / 1000000000000 : ℝ) by norm_num).trans b406.1
        exact b406.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e406) (227969472707 / 1000000000000 : ℝ) (22796947271 / 100000000000 : ℝ) from b448) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b450 : Encl e450 (457243611909 / 1000000000000 : ℝ) (114310902979 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b449 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b451 : Encl e451 (191389469241 / 500000000000 : ℝ) (95694734621 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b406 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b452 : Encl e452 (238970412763 / 1000000000000 : ℝ) (238970412767 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b451 b432 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b453 : Encl e453 (109136599571 / 500000000000 : ℝ) (218273199153 / 1000000000000 : ℝ) := by
  exact Encl.sub b450 b452 (by norm_num) (by norm_num)

lemma b454 : Encl e454 (624303974799 / 20000000000 : ℝ) (156075993701 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b432 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b455 : Encl e455 (25025677831 / 1000000000000 : ℝ) (3128209729 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b406 b454 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b456 : Encl e456 (19324752131 / 100000000000 : ℝ) (96623760661 / 500000000000 : ℝ) := by
  exact Encl.sub b453 b455 (by norm_num) (by norm_num)

lemma b457 : Encl e457 (31574863851 / 250000000000 : ℝ) (31574863857 / 250000000000 : ℝ) := by
  exact Encl.sub b456 b386 (by norm_num) (by norm_num)

lemma b458 : Encl e458 (3025435427 / 250000000000 : ℝ) (6050870859 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b441 b457 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b459 : Encl e459 (7040846223 / 250000000000 : ℝ) (1760211557 / 62500000000 : ℝ) := by
  exact Encl.add b440 b458 (by norm_num) (by norm_num)

lemma b460 : Encl e460 (417123623 / 2000000000 : ℝ) (13035113219 / 62500000000 : ℝ) := by
  exact Encl.sub b406 b339 (by norm_num) (by norm_num)

lemma b461 : Encl e461 (135036153977 / 1000000000000 : ℝ) (33759038519 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b459 b460 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b462 : Encl e462 (-72391944707 / 250000000000 : ℝ) (-144783889333 / 500000000000 : ℝ) := by
  exact Encl.add b404 b461 (by norm_num) (by norm_num)

lemma b463 : Encl e463 (769533307941 / 1000000000000 : ℝ) (76953330797 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b425 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b464 : Encl e464 (2301300499 / 1953125000 : ℝ) (117826585549 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b465 : Encl e465 (2088421852949 / 1000000000000 : ℝ) (417684370591 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b464 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b466 : Encl e466 (43384700819 / 31250000000 : ℝ) (694155213107 / 500000000000 : ℝ) := by
  exact Encl.pow b464 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b467 : Encl e467 (136297057371 / 125000000000 : ℝ) (43615058359 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b466 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b468 : Encl e468 (261297057371 / 125000000000 : ℝ) (83615058359 / 40000000000 : ℝ) := by
  exact Encl.add b5 b467 (by norm_num) (by norm_num)

lemma b469 : Encl e469 (722906712337 / 500000000000 : ℝ) (1445813424677 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b468 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b470 : Encl e470 (188716771961 / 62500000000 : ℝ) (94358385981 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b465 b469 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b471 : Encl e471 (2180752917937 / 1000000000000 : ℝ) (2180752917949 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b466 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b472 : Encl e472 (838715433427 / 1000000000000 : ℝ) (167743086691 / 200000000000 : ℝ) := by
  exact Encl.sub b470 b471 (by norm_num) (by norm_num)

lemma b473 : Encl e473 (327594493159 / 500000000000 : ℝ) (327594493171 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b406 b472 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b474 : Encl e474 (114344321599 / 1000000000000 : ℝ) (28586080413 / 250000000000 : ℝ) := by
  exact Encl.sub b463 b473 (by norm_num) (by norm_num)

lemma b475 : Encl e475 (363853571493 / 1000000000000 : ℝ) (363853571561 / 1000000000000 : ℝ) := by
  exact Encl.sub b165 b434 (by norm_num) (by norm_num)

lemma b476 : Encl e476 (41604589793 / 1000000000000 : ℝ) (41604589821 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b474 b475 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b477 : Encl e477 (61207474041 / 1000000000000 : ℝ) (3825467131 / 62500000000 : ℝ) := by
  exact Encl.sub b472 b425 (by norm_num) (by norm_num)

lemma b478 : Encl e478 (32690524819 / 100000000000 : ℝ) (326905248333 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b456 (by norm_num) (by norm_num)

lemma b479 : Encl e479 (5002261123 / 250000000000 : ℝ) (500226113 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b477 b478 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b480 : Encl e480 (12322726857 / 200000000000 : ℝ) (61613634341 / 1000000000000 : ℝ) := by
  exact Encl.add b476 b479 (by norm_num) (by norm_num)

lemma b481 : Encl e481 (208561811501 / 1000000000000 : ℝ) (13035113219 / 62500000000 : ℝ) := by
  exact Encl.sub b4 b406 (by norm_num) (by norm_num)

lemma b482 : Encl e482 (73855364317 / 250000000000 : ℝ) (295421457541 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b480 b481 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b483 : Encl e483 (146341961 / 25000000000 : ℝ) (46829431 / 8000000000 : ℝ) := by
  exact Encl.add b462 b482 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_84 : Encl (twoChordBaseline (21 / 25 : ℝ)) (146341961 / 25000000000 : ℝ) (46829431 / 8000000000 : ℝ) := by
  exact b483

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

lemma baseline_lower_84_oai : (146341961 / 25000000000 : ℝ) ≤ baseline (21 / 25 : ℝ) :=
  (baseline_enclosure_84).1.trans (twoChordBaseline_le_of_range (h := (21 / 25 : ℝ)) (by norm_num) (by norm_num))

end CubicTorus.Scalar.Cert

end
end
end
end ReusedScalar205

end

end

end OAI
end

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_84_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_84_oai

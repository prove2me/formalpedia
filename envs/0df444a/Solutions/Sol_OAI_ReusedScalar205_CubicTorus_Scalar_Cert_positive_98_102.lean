-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_98_102
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:49:09.697775+00:00
-- url     : https://prove2.me/submissions/8fb403d7-c064-4a9b-91e3-6ab424502580

import Mathlib
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_baseline_chord_lower
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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures508To725
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

lemma b631 : Encl e631 (15597184423 / 50000000000 : ℝ) (311943688461 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b8 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b632 : Encl e632 (668056311539 / 1000000000000 : ℝ) (668056311541 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b633 : Encl e633 (2401 / 2500 : ℝ) (2401 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b634 : Encl e634 (30570481469 / 100000000000 : ℝ) (305704814691 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b633 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b635 : Encl e635 (2401 / 2500 : ℝ) (2401 / 2500 : ℝ) := by
  exact Encl.pow b8 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b636 : Encl e636 (2401 / 625 : ℝ) (2401 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b635 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b637 : Encl e637 (1222819258763 / 1000000000000 : ℝ) (305704814691 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b636 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b638 : Encl e638 (2222819258763 / 1000000000000 : ℝ) (555704814691 / 250000000000 : ℝ) := by
  exact Encl.add b5 b637 (by norm_num) (by norm_num)

lemma b639 : Encl e639 (745456111847 / 500000000000 : ℝ) (93182013981 / 62500000000 : ℝ) := by
  exact Encl.sqrt b638 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b640 : Encl e640 (1245456111847 / 500000000000 : ℝ) (155682013981 / 62500000000 : ℝ) := by
  exact Encl.add b5 b639 (by norm_num) (by norm_num)

lemma b641 : Encl e641 (802918698207 / 1000000000000 : ℝ) (802918698209 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b640 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b642 : Encl e642 (224817235497 / 1000000000000 : ℝ) (224817235499 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b641 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b643 : Encl e643 (530522050187 / 1000000000000 : ℝ) (53052205019 / 100000000000 : ℝ) := by
  exact Encl.add b634 b642 (by norm_num) (by norm_num)

lemma b644 : Encl e644 (-469477949813 / 1000000000000 : ℝ) (-46947794981 / 100000000000 : ℝ) := by
  exact Encl.sub b643 b5 (by norm_num) (by norm_num)

lemma b645 : Encl e645 (654225875383 / 200000000000 : ℝ) (817782344229 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b635 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b646 : Encl e646 (9730886477 / 100000000000 : ℝ) (97308864771 / 1000000000000 : ℝ) := by
  exact Encl.pow b631 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b647 : Encl e647 (902691135229 / 1000000000000 : ℝ) (90269113523 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b646 (by norm_num) (by norm_num)

lemma b648 : Encl e648 (950100592163 / 1000000000000 : ℝ) (237525148041 / 250000000000 : ℝ) := by
  exact Encl.sqrt b647 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b649 : Encl e649 (-141716962749 / 500000000000 : ℝ) (-35429240687 / 125000000000 : ℝ) := by
  exact Encl.sub b29 b648 (by norm_num) (by norm_num)

lemma b650 : Encl e650 (21441184553 / 25000000000 : ℝ) (214411845531 / 250000000000 : ℝ) := by
  exact Encl.pow b648 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b651 : Encl e651 (142941230353 / 500000000000 : ℝ) (71470615177 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b650 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b652 : Encl e652 (306066901 / 125000000000 : ℝ) (612133803 / 250000000000 : ℝ) := by
  exact Encl.add b649 b651 (by norm_num) (by norm_num)

lemma b653 : Encl e653 (2399564503 / 1000000000000 : ℝ) (599891127 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b652 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b654 : Encl e654 (102419539123 / 1000000000000 : ℝ) (819356313 / 8000000000 : ℝ) := by
  exact Encl.div_nonneg b646 b648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b655 : Encl e655 (-1897580460877 / 1000000000000 : ℝ) (-15180643687 / 8000000000 : ℝ) := by
  exact Encl.sub b654 b23 (by norm_num) (by norm_num)

lemma b656 : Encl e656 (950100592163 / 500000000000 : ℝ) (237525148041 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b657 : Encl e657 (2620723449 / 1000000000000 : ℝ) (2620723453 / 1000000000000 : ℝ) := by
  exact Encl.add b655 b656 (by norm_num) (by norm_num)

lemma b658 : Encl e658 (13103617 / 250000000000 : ℝ) (5241447 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b657 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b659 : Encl e659 (2347150033 / 1000000000000 : ℝ) (58678751 / 25000000000 : ℝ) := by
  exact Encl.sub b653 b658 (by norm_num) (by norm_num)

lemma b660 : Encl e660 (29991529 / 3906250000 : ℝ) (959728931 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b645 b659 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b661 : Encl e661 (-461800118389 / 1000000000000 : ℝ) (-230900059181 / 500000000000 : ℝ) := by
  exact Encl.add b644 b660 (by norm_num) (by norm_num)

lemma b662 : Encl e662 (446299235387 / 1000000000000 : ℝ) (44629923539 / 100000000000 : ℝ) := by
  exact Encl.pow b632 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b663 : Encl e663 (55370076461 / 100000000000 : ℝ) (553700764613 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b662 (by norm_num) (by norm_num)

lemma b664 : Encl e664 (148822144133 / 200000000000 : ℝ) (186027680167 / 250000000000 : ℝ) := by
  exact Encl.sqrt b663 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b665 : Encl e665 (348822144133 / 200000000000 : ℝ) (436027680167 / 250000000000 : ℝ) := by
  exact Encl.add b5 b664 (by norm_num) (by norm_num)

lemma b666 : Encl e666 (23939718377 / 62500000000 : ℝ) (76607098807 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b632 b665 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b667 : Encl e667 (18339523711 / 125000000000 : ℝ) (146716189691 / 1000000000000 : ℝ) := by
  exact Encl.pow b666 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b668 : Encl e668 (143339523711 / 125000000000 : ℝ) (1146716189691 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b667 (by norm_num) (by norm_num)

lemma b669 : Encl e669 (535424175231 / 500000000000 : ℝ) (4183001369 / 3906250000 : ℝ) := by
  exact Encl.sqrt b668 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b670 : Encl e670 (1035424175231 / 500000000000 : ℝ) (8089251369 / 3906250000 : ℝ) := by
  exact Encl.add b5 b669 (by norm_num) (by norm_num)

lemma b671 : Encl e671 (184965496843 / 1000000000000 : ℝ) (92482748423 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b666 b670 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b672 : Encl e672 (365796809329 / 500000000000 : ℝ) (731593618671 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e632) (a := (184965496843 / 1000000000000 : ℝ)) (b := (92482748423 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (668056311539 / 1000000000000 : ℝ) by norm_num).trans b632.1
        exact b632.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e632) (184965496843 / 1000000000000 : ℝ) (92482748423 / 500000000000 : ℝ) from b671) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b673 : Encl e673 (74622549103 / 200000000000 : ℝ) (373112745523 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b672 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b674 : Encl e674 (163673796327 / 500000000000 : ℝ) (20459224541 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b632 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b675 : Encl e675 (243582853077 / 1000000000000 : ℝ) (243582853081 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b674 b664 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b676 : Encl e676 (64764946217 / 500000000000 : ℝ) (64764946223 / 500000000000 : ℝ) := by
  exact Encl.sub b673 b675 (by norm_num) (by norm_num)

lemma b677 : Encl e677 (148822144133 / 4000000000 : ℝ) (186027680167 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b664 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b678 : Encl e678 (3591166169 / 200000000000 : ℝ) (8977915423 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b632 b677 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b679 : Encl e679 (27893515397 / 250000000000 : ℝ) (111574061601 / 1000000000000 : ℝ) := by
  exact Encl.sub b676 b678 (by norm_num) (by norm_num)

lemma b680 : Encl e680 (1950100592163 / 1000000000000 : ℝ) (487525148041 / 250000000000 : ℝ) := by
  exact Encl.add b5 b648 (by norm_num) (by norm_num)

lemma b681 : Encl e681 (79981435243 / 500000000000 : ℝ) (19995358811 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b631 b680 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b682 : Encl e682 (12794059967 / 500000000000 : ℝ) (5117623987 / 200000000000 : ℝ) := by
  exact Encl.pow b681 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b683 : Encl e683 (512794059967 / 500000000000 : ℝ) (205117623987 / 200000000000 : ℝ) := by
  exact Encl.add b5 b682 (by norm_num) (by norm_num)

lemma b684 : Encl e684 (506356623323 / 500000000000 : ℝ) (126589155831 / 125000000000 : ℝ) := by
  exact Encl.sqrt b683 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b685 : Encl e685 (1006356623323 / 500000000000 : ℝ) (251589155831 / 125000000000 : ℝ) := by
  exact Encl.add b5 b684 (by norm_num) (by norm_num)

lemma b686 : Encl e686 (15895246951 / 200000000000 : ℝ) (79476234757 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b681 b685 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b687 : Encl e687 (158619059251 / 500000000000 : ℝ) (317238118511 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e631) (a := (15895246951 / 200000000000 : ℝ)) (b := (79476234757 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (15597184423 / 50000000000 : ℝ) by norm_num).trans b631.1
        exact b631.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e631) (15895246951 / 200000000000 : ℝ) (79476234757 / 1000000000000 : ℝ) from b686) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b688 : Encl e688 (40447860109 / 250000000000 : ℝ) (161791440441 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b687 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b689 : Encl e689 (30570481469 / 200000000000 : ℝ) (76426203673 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b631 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b690 : Encl e690 (36306290683 / 250000000000 : ℝ) (72612581367 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b689 b648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b691 : Encl e691 (8283138851 / 500000000000 : ℝ) (16566277709 / 1000000000000 : ℝ) := by
  exact Encl.sub b688 b690 (by norm_num) (by norm_num)

lemma b692 : Encl e692 (950100592163 / 20000000000 : ℝ) (237525148041 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b693 : Encl e693 (3283270119 / 500000000000 : ℝ) (6566540239 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b631 b692 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b694 : Encl e694 (9999737463 / 1000000000000 : ℝ) (9999737471 / 1000000000000 : ℝ) := by
  exact Encl.sub b691 b693 (by norm_num) (by norm_num)

lemma b695 : Encl e695 (101574324117 / 1000000000000 : ℝ) (50787162069 / 500000000000 : ℝ) := by
  exact Encl.sub b679 b694 (by norm_num) (by norm_num)

lemma b696 : Encl e696 (103647269507 / 1000000000000 : ℝ) (103647269529 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b695 b8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b697 : Encl e697 (-179076424441 / 500000000000 : ℝ) (-358152848833 / 1000000000000 : ℝ) := by
  exact Encl.add b661 b696 (by norm_num) (by norm_num)

lemma b698 : Encl e698 (1657799630149 / 1000000000000 : ℝ) (207224953769 / 125000000000 : ℝ) := by
  exact Encl.add b632 b4 (by norm_num) (by norm_num)

lemma b699 : Encl e699 (414449907537 / 500000000000 : ℝ) (207224953769 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b698 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b700 : Encl e700 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b632 b8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b701 : Encl e701 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b700 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b702 : Encl e702 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b700 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b703 : Encl e703 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b702 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b704 : Encl e704 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b703 (by norm_num) (by norm_num)

lemma b705 : Encl e705 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b704 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b706 : Encl e706 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b701 b705 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b707 : Encl e707 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b702 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b708 : Encl e708 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b706 b707 (by norm_num) (by norm_num)

lemma b709 : Encl e709 (56505280927 / 100000000000 : ℝ) (141263202323 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b699 b708 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b710 : Encl e710 (84581613783 / 100000000000 : ℝ) (845816137833 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b699 b8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b711 : Encl e711 (749585035327 / 500000000000 : ℝ) (1499170070661 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b710 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b712 : Encl e712 (715404939013 / 1000000000000 : ℝ) (715404939019 / 1000000000000 : ℝ) := by
  exact Encl.pow b710 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b713 : Encl e713 (112375545037 / 200000000000 : ℝ) (70234715649 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b712 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b714 : Encl e714 (312375545037 / 200000000000 : ℝ) (195234715649 / 125000000000 : ℝ) := by
  exact Encl.add b5 b713 (by norm_num) (by norm_num)

lemma b715 : Encl e715 (624875532643 / 500000000000 : ℝ) (124975106529 / 100000000000 : ℝ) := by
  exact Encl.sqrt b714 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b716 : Encl e716 (468397348211 / 250000000000 : ℝ) (93679469643 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b711 b715 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b717 : Encl e717 (1123755450371 / 1000000000000 : ℝ) (1123755450383 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b712 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b718 : Encl e718 (749833942461 / 1000000000000 : ℝ) (749833942489 / 1000000000000 : ℝ) := by
  exact Encl.sub b716 b717 (by norm_num) (by norm_num)

lemma b719 : Encl e719 (500931297867 / 1000000000000 : ℝ) (15654103059 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b632 b718 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b720 : Encl e720 (32060755691 / 500000000000 : ℝ) (2564860457 / 40000000000 : ℝ) := by
  exact Encl.sub b709 b719 (by norm_num) (by norm_num)

lemma b721 : Encl e721 (687074903429 / 1000000000000 : ℝ) (343537451717 / 500000000000 : ℝ) := by
  exact Encl.pow b699 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b722 : Encl e722 (8416667567 / 12500000000 : ℝ) (336666702683 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b721 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b723 : Encl e723 (163333297317 / 500000000000 : ℝ) (4083332433 / 12500000000 : ℝ) := by
  exact Encl.sub b5 b722 (by norm_num) (by norm_num)

lemma b724 : Encl e724 (156462548283 / 500000000000 : ℝ) (312925096571 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b721 (by norm_num) (by norm_num)

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
lemma b725 : Encl e725 (279698541543 / 500000000000 : ℝ) (139849270773 / 250000000000 : ℝ) := by
  exact Encl.sqrt b724 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b726 : Encl e726 (583961919909 / 1000000000000 : ℝ) (583961919927 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b723 b725 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b727 : Encl e727 (416038080073 / 1000000000000 : ℝ) (416038080091 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b726 (by norm_num) (by norm_num)

lemma b728 : Encl e728 (437373250679 / 1000000000000 : ℝ) (437373250683 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b662 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b729 : Encl e729 (562626749317 / 1000000000000 : ℝ) (562626749321 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b728 (by norm_num) (by norm_num)

lemma b730 : Encl e730 (189026556697 / 250000000000 : ℝ) (756106226797 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b729 b664 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b731 : Encl e731 (243893773203 / 1000000000000 : ℝ) (60973443303 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b730 (by norm_num) (by norm_num)

lemma b732 : Encl e732 (172144306861 / 1000000000000 : ℝ) (21518038361 / 125000000000 : ℝ) := by
  exact Encl.sub b727 b731 (by norm_num) (by norm_num)

lemma b733 : Encl e733 (11038153131 / 1000000000000 : ℝ) (11038153141 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b720 b732 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b734 : Encl e734 (68143828633 / 1000000000000 : ℝ) (17035957171 / 250000000000 : ℝ) := by
  exact Encl.sub b718 b708 (by norm_num) (by norm_num)

lemma b735 : Encl e735 (779698541543 / 500000000000 : ℝ) (389849270773 / 250000000000 : ℝ) := by
  exact Encl.add b5 b725 (by norm_num) (by norm_num)

lemma b736 : Encl e736 (531551472079 / 1000000000000 : ℝ) (531551472083 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b699 b735 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b737 : Encl e737 (282546967469 / 1000000000000 : ℝ) (141273483737 / 500000000000 : ℝ) := by
  exact Encl.pow b736 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b738 : Encl e738 (1282546967469 / 1000000000000 : ℝ) (641273483737 / 500000000000 : ℝ) := by
  exact Encl.add b5 b737 (by norm_num) (by norm_num)

lemma b739 : Encl e739 (70780993859 / 62500000000 : ℝ) (283123975437 / 250000000000 : ℝ) := by
  exact Encl.sqrt b738 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b740 : Encl e740 (133280993859 / 62500000000 : ℝ) (533123975437 / 250000000000 : ℝ) := by
  exact Encl.add b5 b739 (by norm_num) (by norm_num)

lemma b741 : Encl e741 (249262599587 / 1000000000000 : ℝ) (24926259959 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b736 b740 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b742 : Encl e742 (122142259441 / 125000000000 : ℝ) (48856903777 / 50000000000 : ℝ) := by
  apply Encl.arcsin (z := e699) (a := (249262599587 / 1000000000000 : ℝ)) (b := (24926259959 / 100000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (414449907537 / 500000000000 : ℝ) by norm_num).trans b699.1
        exact b699.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e699) (249262599587 / 1000000000000 : ℝ) (24926259959 / 100000000000 : ℝ) from b741) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b743 : Encl e743 (498340418519 / 1000000000000 : ℝ) (249170209263 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b742 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b744 : Encl e744 (203080454693 / 500000000000 : ℝ) (101540227347 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b699 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b745 : Encl e745 (113602613987 / 500000000000 : ℝ) (113602613989 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b744 b725 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b746 : Encl e746 (271135190541 / 1000000000000 : ℝ) (33891898819 / 125000000000 : ℝ) := by
  exact Encl.sub b743 b745 (by norm_num) (by norm_num)

lemma b747 : Encl e747 (279698541543 / 10000000000 : ℝ) (139849270773 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b725 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b748 : Encl e748 (29635471479 / 1000000000000 : ℝ) (740886787 / 25000000000 : ℝ) := by
  exact Encl.div_nonneg b699 b747 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b749 : Encl e749 (241499719061 / 1000000000000 : ℝ) (241499719073 / 1000000000000 : ℝ) := by
  exact Encl.sub b746 b748 (by norm_num) (by norm_num)

lemma b750 : Encl e750 (6496282873 / 50000000000 : ℝ) (25985131497 / 200000000000 : ℝ) := by
  exact Encl.sub b749 b679 (by norm_num) (by norm_num)

lemma b751 : Encl e751 (1106703967 / 125000000000 : ℝ) (4426815873 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b734 b750 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b752 : Encl e752 (19891784867 / 1000000000000 : ℝ) (19891784887 / 1000000000000 : ℝ) := by
  exact Encl.add b733 b751 (by norm_num) (by norm_num)

lemma b753 : Encl e753 (160843503533 / 1000000000000 : ℝ) (160843503537 / 1000000000000 : ℝ) := by
  exact Encl.sub b699 b632 (by norm_num) (by norm_num)

lemma b754 : Encl e754 (123671671093 / 1000000000000 : ℝ) (61835835611 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b752 b753 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b755 : Encl e755 (-234481177789 / 1000000000000 : ℝ) (-234481177611 / 1000000000000 : ℝ) := by
  exact Encl.add b697 b754 (by norm_num) (by norm_num)

lemma b756 : Encl e756 (742143134617 / 1000000000000 : ℝ) (742143134647 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b718 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b757 : Encl e757 (504971080923 / 500000000000 : ℝ) (126242770231 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b758 : Encl e758 (358015174791 / 200000000000 : ℝ) (44751896849 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b757 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b759 : Encl e759 (509991585137 / 500000000000 : ℝ) (1019983170279 / 1000000000000 : ℝ) := by
  exact Encl.pow b757 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b760 : Encl e760 (801092908629 / 1000000000000 : ℝ) (400546454317 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b759 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b761 : Encl e761 (1801092908629 / 1000000000000 : ℝ) (900546454317 / 500000000000 : ℝ) := by
  exact Encl.add b5 b760 (by norm_num) (by norm_num)

lemma b762 : Encl e762 (134204802769 / 100000000000 : ℝ) (1342048027693 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b761 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b763 : Encl e763 (300295974507 / 125000000000 : ℝ) (2402367796069 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b758 b762 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b764 : Encl e764 (801092908629 / 500000000000 : ℝ) (1602185817267 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b759 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b765 : Encl e765 (800181978789 / 1000000000000 : ℝ) (800181978811 / 1000000000000 : ℝ) := by
  exact Encl.sub b763 b764 (by norm_num) (by norm_num)

lemma b766 : Encl e766 (663270694243 / 1000000000000 : ℝ) (82908836783 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b699 b765 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b767 : Encl e767 (78872440353 / 1000000000000 : ℝ) (19718110101 / 250000000000 : ℝ) := by
  exact Encl.sub b756 b766 (by norm_num) (by norm_num)

lemma b768 : Encl e768 (75990479971 / 250000000000 : ℝ) (60792383991 / 200000000000 : ℝ) := by
  exact Encl.sub b165 b727 (by norm_num) (by norm_num)

lemma b769 : Encl e769 (4794843679 / 200000000000 : ℝ) (23974218417 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b767 b768 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b770 : Encl e770 (503480363 / 10000000000 : ℝ) (1006960727 / 20000000000 : ℝ) := by
  exact Encl.sub b765 b718 (by norm_num) (by norm_num)

lemma b771 : Encl e771 (278653050439 / 1000000000000 : ℝ) (139326525291 / 500000000000 : ℝ) := by
  exact Encl.sub b183 b749 (by norm_num) (by norm_num)

lemma b772 : Encl e772 (7014816949 / 500000000000 : ℝ) (21921303 / 1562500000 : ℝ) := by
  exact Encl.mul_nonneg b770 b771 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b773 : Encl e773 (38003852293 / 1000000000000 : ℝ) (38003852337 / 1000000000000 : ℝ) := by
  exact Encl.add b769 b772 (by norm_num) (by norm_num)

lemma b774 : Encl e774 (80421751767 / 500000000000 : ℝ) (160843503537 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b699 (by norm_num) (by norm_num)

lemma b775 : Encl e775 (590696103 / 2500000000 : ℝ) (236278441479 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b773 b774 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b776 : Encl e776 (1797263411 / 1000000000000 : ℝ) (449315967 / 250000000000 : ℝ) := by
  exact Encl.add b755 b775 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_98 : Encl (twoChordBaseline (49 / 50 : ℝ)) (1797263411 / 1000000000000 : ℝ) (449315967 / 250000000000 : ℝ) := by
  exact b776

lemma baseline_enclosure_102 : Encl (twoChordBaseline (51 / 50 : ℝ)) (926954813 / 1000000000000 : ℝ) (926955277 / 1000000000000 : ℝ) := by
  exact b923

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

lemma baseline_lower_98 : (1797263411 / 1000000000000 : ℝ) ≤ baseline (49 / 50 : ℝ) :=
  (baseline_enclosure_98).1.trans (twoChordBaseline_le_of_range (h := (49 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma baseline_lower_102 : (926954813 / 1000000000000 : ℝ) ≤ baseline (51 / 50 : ℝ) :=
  (baseline_enclosure_102).1.trans (twoChordBaseline_le_of_range (h := (51 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma positive_98_102_oai {h : ℝ} (hh : h ∈ Set.Icc (49 / 50 : ℝ) (51 / 50 : ℝ)) : 0 < baseline h := by
  have hb := baseline_chord_lower (by norm_num) (by norm_num) hh baseline_lower_98 baseline_lower_102
  have hp : (0 : ℝ) < min (1797263411 / 1000000000000 : ℝ) (926954813 / 1000000000000 : ℝ) - ((51 / 50 : ℝ) - (49 / 50 : ℝ)) ^ 2 / (4 * (49 / 50 : ℝ) ^ 2) := by norm_num
  exact hp.trans_le hb

end CubicTorus.Scalar.Cert

end
end
end
end ReusedScalar205

end

end

end OAI
end

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_98_102_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_98_102_oai

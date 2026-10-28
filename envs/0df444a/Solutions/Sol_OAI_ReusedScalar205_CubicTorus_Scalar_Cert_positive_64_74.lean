-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_64_74
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:47:41.719993+00:00
-- url     : https://prove2.me/submissions/42a4014e-2da2-40ea-a9a9-c3e9f952279e

import Mathlib
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_baseline_lower_64
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

lemma b190 : Encl e190 (37 / 50 : ℝ) (37 / 50 : ℝ) := by
  exact Encl.exact (37 / 50 : ℝ)

lemma b191 : Encl e191 (3680458059 / 15625000000 : ℝ) (235549315777 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b190 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b192 : Encl e192 (504450684223 / 1000000000000 : ℝ) (20178027369 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b190 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b193 : Encl e193 (1813 / 2500 : ℝ) (1813 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b194 : Encl e194 (11541916473 / 50000000000 : ℝ) (230838329461 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b193 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b195 : Encl e195 (1369 / 2500 : ℝ) (1369 / 2500 : ℝ) := by
  exact Encl.pow b190 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b196 : Encl e196 (1369 / 625 : ℝ) (1369 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b195 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b197 : Encl e197 (87153246837 / 125000000000 : ℝ) (697225974697 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b196 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b198 : Encl e198 (212153246837 / 125000000000 : ℝ) (1697225974697 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b197 (by norm_num) (by norm_num)

lemma b199 : Encl e199 (52111050263 / 40000000000 : ℝ) (20355879009 / 15625000000 : ℝ) := by
  exact Encl.sqrt b198 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b200 : Encl e200 (92111050263 / 40000000000 : ℝ) (35980879009 / 15625000000 : ℝ) := by
  exact Encl.add b5 b199 (by norm_num) (by norm_num)

lemma b201 : Encl e201 (868516858417 / 1000000000000 : ℝ) (434258429209 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b200 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b202 : Encl e202 (60796180089 / 250000000000 : ℝ) (121592360179 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b201 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b203 : Encl e203 (59252881227 / 125000000000 : ℝ) (474023049819 / 1000000000000 : ℝ) := by
  exact Encl.add b194 b202 (by norm_num) (by norm_num)

lemma b204 : Encl e204 (-65747118773 / 125000000000 : ℝ) (-525976950181 / 1000000000000 : ℝ) := by
  exact Encl.sub b203 b5 (by norm_num) (by norm_num)

lemma b205 : Encl e205 (2868510457989 / 500000000000 : ℝ) (5737020915979 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b195 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b206 : Encl e206 (27741740081 / 500000000000 : ℝ) (13870870041 / 250000000000 : ℝ) := by
  exact Encl.pow b191 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b207 : Encl e207 (236129129959 / 250000000000 : ℝ) (472258259919 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b206 (by norm_num) (by norm_num)

lemma b208 : Encl e208 (971862397583 / 1000000000000 : ℝ) (194372479517 / 200000000000 : ℝ) := by
  exact Encl.sqrt b207 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b209 : Encl e209 (-305195730919 / 1000000000000 : ℝ) (-76298932729 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b208 (by norm_num) (by norm_num)

lemma b210 : Encl e210 (229485022381 / 250000000000 : ℝ) (917940089531 / 1000000000000 : ℝ) := by
  exact Encl.pow b208 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b211 : Encl e211 (305980029841 / 1000000000000 : ℝ) (76495007461 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b210 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b212 : Encl e212 (392149461 / 500000000000 : ℝ) (49018683 / 62500000000 : ℝ) := by
  exact Encl.add b209 b211 (by norm_num) (by norm_num)

lemma b213 : Encl e213 (768612943 / 1000000000000 : ℝ) (15372259 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b212 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b214 : Encl e214 (57089851711 / 1000000000000 : ℝ) (28544925857 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b206 b208 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b215 : Encl e215 (-1942910148289 / 1000000000000 : ℝ) (-971455074143 / 500000000000 : ℝ) := by
  exact Encl.sub b214 b23 (by norm_num) (by norm_num)

lemma b216 : Encl e216 (971862397583 / 500000000000 : ℝ) (194372479517 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b208 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b217 : Encl e217 (814646877 / 1000000000000 : ℝ) (203661721 / 250000000000 : ℝ) := by
  exact Encl.add b215 b216 (by norm_num) (by norm_num)

lemma b218 : Encl e218 (16292937 / 1000000000000 : ℝ) (8146469 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b217 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b219 : Encl e219 (150464001 / 200000000000 : ℝ) (752320013 / 1000000000000 : ℝ) := by
  exact Encl.sub b213 b218 (by norm_num) (by norm_num)

lemma b220 : Encl e220 (1079018901 / 250000000000 : ℝ) (4316075651 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b205 b219 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b221 : Encl e221 (-26083043729 / 50000000000 : ℝ) (-52166087453 / 100000000000 : ℝ) := by
  exact Encl.add b204 b220 (by norm_num) (by norm_num)

lemma b222 : Encl e222 (254470492813 / 1000000000000 : ℝ) (15904405801 / 62500000000 : ℝ) := by
  exact Encl.pow b192 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b223 : Encl e223 (46595594199 / 62500000000 : ℝ) (745529507187 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b222 (by norm_num) (by norm_num)

lemma b224 : Encl e224 (431720252937 / 500000000000 : ℝ) (215860126469 / 250000000000 : ℝ) := by
  exact Encl.sqrt b223 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b225 : Encl e225 (931720252937 / 500000000000 : ℝ) (465860126469 / 250000000000 : ℝ) := by
  exact Encl.add b5 b224 (by norm_num) (by norm_num)

lemma b226 : Encl e226 (270709304983 / 1000000000000 : ℝ) (54141860997 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b192 b225 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b227 : Encl e227 (18320881951 / 250000000000 : ℝ) (36641763903 / 500000000000 : ℝ) := by
  exact Encl.pow b226 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b228 : Encl e228 (268320881951 / 250000000000 : ℝ) (536641763903 / 500000000000 : ℝ) := by
  exact Encl.add b5 b227 (by norm_num) (by norm_num)

lemma b229 : Encl e229 (517996990291 / 500000000000 : ℝ) (129499247573 / 125000000000 : ℝ) := by
  exact Encl.sqrt b228 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b230 : Encl e230 (1017996990291 / 500000000000 : ℝ) (254499247573 / 125000000000 : ℝ) := by
  exact Encl.add b5 b229 (by norm_num) (by norm_num)

lemma b231 : Encl e231 (132961741323 / 1000000000000 : ℝ) (5318469653 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b226 b230 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b232 : Encl e232 (264372826437 / 500000000000 : ℝ) (528745652883 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e192) (a := (132961741323 / 1000000000000 : ℝ)) (b := (5318469653 / 40000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (504450684223 / 1000000000000 : ℝ) by norm_num).trans b192.1
        exact b192.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e192) (132961741323 / 1000000000000 : ℝ) (5318469653 / 40000000000 : ℝ) from b231) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b233 : Encl e233 (53932056593 / 200000000000 : ℝ) (269660282971 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b232 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b234 : Encl e234 (247180835269 / 1000000000000 : ℝ) (247180835271 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b192 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b235 : Encl e235 (213425945447 / 1000000000000 : ℝ) (4268518909 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b234 b224 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b236 : Encl e236 (11246867503 / 200000000000 : ℝ) (14058584381 / 250000000000 : ℝ) := by
  exact Encl.sub b233 b235 (by norm_num) (by norm_num)

lemma b237 : Encl e237 (431720252937 / 10000000000 : ℝ) (215860126469 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b224 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b238 : Encl e238 (2921166431 / 250000000000 : ℝ) (467386629 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b192 b237 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b239 : Encl e239 (4454967179 / 100000000000 : ℝ) (222748359 / 5000000000 : ℝ) := by
  exact Encl.sub b236 b238 (by norm_num) (by norm_num)

lemma b240 : Encl e240 (1971862397583 / 1000000000000 : ℝ) (394372479517 / 200000000000 : ℝ) := by
  exact Encl.add b5 b208 (by norm_num) (by norm_num)

lemma b241 : Encl e241 (59727625027 / 500000000000 : ℝ) (23891050011 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b191 b240 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b242 : Encl e242 (2853911353 / 200000000000 : ℝ) (7134778383 / 500000000000 : ℝ) := by
  exact Encl.pow b241 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b243 : Encl e243 (202853911353 / 200000000000 : ℝ) (507134778383 / 500000000000 : ℝ) := by
  exact Encl.add b5 b242 (by norm_num) (by norm_num)

lemma b244 : Encl e244 (201421901169 / 200000000000 : ℝ) (1007109505847 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b243 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b245 : Encl e245 (401421901169 / 200000000000 : ℝ) (2007109505847 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b244 (by norm_num) (by norm_num)

lemma b246 : Encl e246 (29758030069 / 500000000000 : ℝ) (59516060139 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b241 b245 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b247 : Encl e247 (59445937279 / 250000000000 : ℝ) (237783749121 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e191) (a := (29758030069 / 500000000000 : ℝ)) (b := (59516060139 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (3680458059 / 15625000000 : ℝ) by norm_num).trans b191.1
        exact b191.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e191) (29758030069 / 500000000000 : ℝ) (59516060139 / 1000000000000 : ℝ) from b246) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b248 : Encl e248 (121269712049 / 1000000000000 : ℝ) (30317428013 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b247 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b249 : Encl e249 (11541916473 / 100000000000 : ℝ) (115419164731 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b191 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b250 : Encl e250 (112171546161 / 1000000000000 : ℝ) (112171546163 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b249 b208 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b251 : Encl e251 (4549082943 / 500000000000 : ℝ) (9098165891 / 1000000000000 : ℝ) := by
  exact Encl.sub b248 b250 (by norm_num) (by norm_num)

lemma b252 : Encl e252 (971862397583 / 20000000000 : ℝ) (194372479517 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b208 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b253 : Encl e253 (969475993 / 200000000000 : ℝ) (2423689983 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b191 b252 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b254 : Encl e254 (6641853 / 1562500000 : ℝ) (2125392963 / 500000000000 : ℝ) := by
  exact Encl.sub b251 b253 (by norm_num) (by norm_num)

lemma b255 : Encl e255 (5037360733 / 125000000000 : ℝ) (1007472147 / 25000000000 : ℝ) := by
  exact Encl.sub b239 b254 (by norm_num) (by norm_num)

lemma b256 : Encl e256 (5445795387 / 100000000000 : ℝ) (13614488473 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b255 b190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b257 : Encl e257 (-46720292071 / 100000000000 : ℝ) (-233601460319 / 500000000000 : ℝ) := by
  exact Encl.add b221 b256 (by norm_num) (by norm_num)

lemma b258 : Encl e258 (1494194002833 / 1000000000000 : ℝ) (373548500709 / 250000000000 : ℝ) := by
  exact Encl.add b192 b4 (by norm_num) (by norm_num)

lemma b259 : Encl e259 (93387125177 / 125000000000 : ℝ) (373548500709 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b258 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b260 : Encl e260 (340845056907 / 500000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b192 b190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b261 : Encl e261 (1208264267353 / 1000000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b260 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b262 : Encl e262 (464701411271 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b260 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b263 : Encl e263 (18248781747 / 50000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b262 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b264 : Encl e264 (68248781747 / 50000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b263 (by norm_num) (by norm_num)

lemma b265 : Encl e265 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b264 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b266 : Encl e266 (282328276739 / 200000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b261 b265 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b267 : Encl e267 (18248781747 / 25000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b262 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b268 : Encl e268 (681690113803 / 1000000000000 : ℝ) (681690113831 / 1000000000000 : ℝ) := by
  exact Encl.sub b266 b267 (by norm_num) (by norm_num)

lemma b269 : Encl e269 (509288639917 / 1000000000000 : ℝ) (25464431997 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b259 b268 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b270 : Encl e270 (504795271227 / 500000000000 : ℝ) (1009590542457 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b259 b190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b271 : Encl e271 (1789452644809 / 1000000000000 : ℝ) (1789452644817 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b270 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b272 : Encl e272 (254818265853 / 250000000000 : ℝ) (1019273063419 / 1000000000000 : ℝ) := by
  exact Encl.pow b270 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b273 : Encl e273 (800535192003 / 1000000000000 : ℝ) (800535192011 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b272 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b274 : Encl e274 (1800535192003 / 1000000000000 : ℝ) (1800535192011 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b273 (by norm_num) (by norm_num)

lemma b275 : Encl e275 (1341840225959 / 1000000000000 : ℝ) (1341840225963 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b274 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b276 : Encl e276 (2401159541253 / 1000000000000 : ℝ) (300144942659 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b271 b275 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b277 : Encl e277 (1601070384007 / 1000000000000 : ℝ) (80053519201 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b272 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b278 : Encl e278 (800089157233 / 1000000000000 : ℝ) (160017831453 / 200000000000 : ℝ) := by
  exact Encl.sub b276 b277 (by norm_num) (by norm_num)

lemma b279 : Encl e279 (80721104561 / 200000000000 : ℝ) (50450690353 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b192 b278 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b280 : Encl e280 (105683117093 / 1000000000000 : ℝ) (21136623427 / 200000000000 : ℝ) := by
  exact Encl.sub b269 b279 (by norm_num) (by norm_num)

lemma b281 : Encl e281 (139538482381 / 250000000000 : ℝ) (69769241191 / 125000000000 : ℝ) := by
  exact Encl.pow b259 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b282 : Encl e282 (546990850933 / 1000000000000 : ℝ) (273495425469 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b281 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b283 : Encl e283 (226504574531 / 500000000000 : ℝ) (453009149067 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b282 (by norm_num) (by norm_num)

lemma b284 : Encl e284 (55230758809 / 125000000000 : ℝ) (110461517619 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b281 (by norm_num) (by norm_num)

lemma b285 : Encl e285 (664715029521 / 1000000000000 : ℝ) (26588601181 / 40000000000 : ℝ) := by
  exact Encl.sqrt b284 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b286 : Encl e286 (681508810453 / 1000000000000 : ℝ) (136301762093 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b283 b285 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b287 : Encl e287 (63698237907 / 200000000000 : ℝ) (318491189547 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b286 (by norm_num) (by norm_num)

lemma b288 : Encl e288 (62345270739 / 250000000000 : ℝ) (3117263537 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b222 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

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

lemma b289 : Encl e289 (9382736463 / 12500000000 : ℝ) (187654729261 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b288 (by norm_num) (by norm_num)

lemma b290 : Encl e290 (869334843491 / 1000000000000 : ℝ) (869334843499 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b289 b224 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b291 : Encl e291 (130665156501 / 1000000000000 : ℝ) (130665156509 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b290 (by norm_num) (by norm_num)

lemma b292 : Encl e292 (93913016513 / 500000000000 : ℝ) (93913016523 / 500000000000 : ℝ) := by
  exact Encl.sub b287 b291 (by norm_num) (by norm_num)

lemma b293 : Encl e293 (19850040641 / 1000000000000 : ℝ) (4962510163 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b280 b292 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b294 : Encl e294 (59199521701 / 500000000000 : ℝ) (59199521731 / 500000000000 : ℝ) := by
  exact Encl.sub b278 b268 (by norm_num) (by norm_num)

lemma b295 : Encl e295 (1664715029521 / 1000000000000 : ℝ) (66588601181 / 40000000000 : ℝ) := by
  exact Encl.add b5 b285 (by norm_num) (by norm_num)

lemma b296 : Encl e296 (448783718633 / 1000000000000 : ℝ) (448783718637 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b259 b295 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b297 : Encl e297 (20140682611 / 100000000000 : ℝ) (100703413057 / 500000000000 : ℝ) := by
  exact Encl.pow b296 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b298 : Encl e298 (120140682611 / 100000000000 : ℝ) (600703413057 / 500000000000 : ℝ) := by
  exact Encl.add b5 b297 (by norm_num) (by norm_num)

lemma b299 : Encl e299 (1096087052249 / 1000000000000 : ℝ) (274021763063 / 250000000000 : ℝ) := by
  exact Encl.sqrt b298 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b300 : Encl e300 (2096087052249 / 1000000000000 : ℝ) (524021763063 / 250000000000 : ℝ) := by
  exact Encl.add b5 b299 (by norm_num) (by norm_num)

lemma b301 : Encl e301 (214105477227 / 1000000000000 : ℝ) (21410547723 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b296 b300 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b302 : Encl e302 (421842005297 / 500000000000 : ℝ) (843684010607 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e259) (a := (214105477227 / 1000000000000 : ℝ)) (b := (21410547723 / 100000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (93387125177 / 125000000000 : ℝ) by norm_num).trans b259.1
        exact b259.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e259) (214105477227 / 1000000000000 : ℝ) (21410547723 / 100000000000 : ℝ) from b301) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b303 : Encl e303 (215139422701 / 500000000000 : ℝ) (43027884541 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b302 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b304 : Encl e304 (366077530693 / 1000000000000 : ℝ) (73215506139 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b259 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b305 : Encl e305 (243337236621 / 1000000000000 : ℝ) (1946697893 / 8000000000 : ℝ) := by
  exact Encl.mul_nonneg b304 b285 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b306 : Encl e306 (186941608777 / 1000000000000 : ℝ) (186941608789 / 1000000000000 : ℝ) := by
  exact Encl.sub b303 b305 (by norm_num) (by norm_num)

lemma b307 : Encl e307 (664715029521 / 20000000000 : ℝ) (26588601181 / 800000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b285 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b308 : Encl e308 (11239357743 / 500000000000 : ℝ) (22478715487 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b259 b307 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b309 : Encl e309 (16446289329 / 100000000000 : ℝ) (164462893303 / 1000000000000 : ℝ) := by
  exact Encl.sub b306 b308 (by norm_num) (by norm_num)

lemma b310 : Encl e310 (11991322149 / 100000000000 : ℝ) (119913221513 / 1000000000000 : ℝ) := by
  exact Encl.sub b309 b239 (by norm_num) (by norm_num)

lemma b311 : Encl e311 (2839522143 / 200000000000 : ℝ) (7098805363 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b294 b310 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b312 : Encl e312 (8511912839 / 250000000000 : ℝ) (17023825689 / 500000000000 : ℝ) := by
  exact Encl.add b293 b311 (by norm_num) (by norm_num)

lemma b313 : Encl e313 (242646317191 / 1000000000000 : ℝ) (48529263439 / 200000000000 : ℝ) := by
  exact Encl.sub b259 b192 (by norm_num) (by norm_num)

lemma b314 : Encl e314 (2192469099 / 15625000000 : ℝ) (14031802243 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b312 b313 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b315 : Encl e315 (-163442449187 / 500000000000 : ℝ) (-10215153069 / 31250000000 : ℝ) := by
  exact Encl.add b257 b314 (by norm_num) (by norm_num)

lemma b316 : Encl e316 (791882897663 / 1000000000000 : ℝ) (791882897697 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b278 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b317 : Encl e317 (668745485547 / 500000000000 : ℝ) (167186371387 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b318 : Encl e318 (1185320511133 / 500000000000 : ℝ) (37041265973 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b317 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b319 : Encl e319 (1788882097757 / 1000000000000 : ℝ) (447220524441 / 250000000000 : ℝ) := by
  exact Encl.pow b317 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b320 : Encl e320 (10976443079 / 7812500000 : ℝ) (35124617853 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b319 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b321 : Encl e321 (18788943079 / 7812500000 : ℝ) (60124617853 / 25000000000 : ℝ) := by
  exact Encl.add b5 b320 (by norm_num) (by norm_num)

lemma b322 : Encl e322 (1550801313551 / 1000000000000 : ℝ) (775400656777 / 500000000000 : ℝ) := by
  exact Encl.sqrt b321 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b323 : Encl e323 (3676393211287 / 1000000000000 : ℝ) (735278642261 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b318 b322 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b324 : Encl e324 (10976443079 / 3906250000 : ℝ) (1404984714119 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b319 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b325 : Encl e325 (866423783049 / 1000000000000 : ℝ) (866423783081 / 1000000000000 : ℝ) := by
  exact Encl.sub b323 b324 (by norm_num) (by norm_num)

lemma b326 : Encl e326 (647302610271 / 1000000000000 : ℝ) (323651305149 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b259 b325 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b327 : Encl e327 (28916057473 / 200000000000 : ℝ) (72290143713 / 500000000000 : ℝ) := by
  exact Encl.sub b316 b326 (by norm_num) (by norm_num)

lemma b328 : Encl e328 (100377202607 / 250000000000 : ℝ) (401508810493 / 1000000000000 : ℝ) := by
  exact Encl.sub b165 b287 (by norm_num) (by norm_num)

lemma b329 : Encl e329 (58050259191 / 1000000000000 : ℝ) (29025129613 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b327 b328 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b330 : Encl e330 (8291828223 / 125000000000 : ℝ) (8291828231 / 125000000000 : ℝ) := by
  exact Encl.sub b325 b278 (by norm_num) (by norm_num)

lemma b331 : Encl e331 (355689876209 / 1000000000000 : ℝ) (355689876353 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b309 (by norm_num) (by norm_num)

lemma b332 : Encl e332 (23594554833 / 1000000000000 : ℝ) (11797277433 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b330 b331 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b333 : Encl e333 (10205601753 / 125000000000 : ℝ) (20411203523 / 250000000000 : ℝ) := by
  exact Encl.add b329 b332 (by norm_num) (by norm_num)

lemma b334 : Encl e334 (30330789649 / 125000000000 : ℝ) (48529263439 / 200000000000 : ℝ) := by
  exact Encl.sub b4 b259 (by norm_num) (by norm_num)

lemma b335 : Encl e335 (336476625599 / 1000000000000 : ℝ) (67295325177 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b333 b334 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b336 : Encl e336 (383669089 / 40000000000 : ℝ) (9591727677 / 1000000000000 : ℝ) := by
  exact Encl.add b315 b335 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_74 : Encl (twoChordBaseline (37 / 50 : ℝ)) (383669089 / 40000000000 : ℝ) (9591727677 / 1000000000000 : ℝ) := by
  exact b336

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

lemma baseline_lower_74 : (383669089 / 40000000000 : ℝ) ≤ baseline (37 / 50 : ℝ) :=
  (baseline_enclosure_74).1.trans (twoChordBaseline_le_of_range (h := (37 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma positive_64_74_oai {h : ℝ} (hh : h ∈ Set.Icc (16 / 25 : ℝ) (37 / 50 : ℝ)) : 0 < baseline h := by
  have hb := baseline_chord_lower (by norm_num) (by norm_num) hh baseline_lower_64 baseline_lower_74
  have hp : (0 : ℝ) < min (6874889409 / 500000000000 : ℝ) (383669089 / 40000000000 : ℝ) - ((37 / 50 : ℝ) - (16 / 25 : ℝ)) ^ 2 / (4 * (16 / 25 : ℝ) ^ 2) := by norm_num
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

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_64_74_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_64_74_oai

-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_92
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:36:45.805416+00:00
-- url     : https://prove2.me/submissions/76afc247-d93b-4c91-9cf9-85cb0ccaf039

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

lemma b484 : Encl e484 (23 / 25 : ℝ) (23 / 25 : ℝ) := by
  exact Encl.exact (23 / 25 : ℝ)

lemma b485 : Encl e485 (292845095289 / 1000000000000 : ℝ) (29284509529 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b484 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b486 : Encl e486 (62715490471 / 100000000000 : ℝ) (78394363089 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b484 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b487 : Encl e487 (1127 / 1250 : ℝ) (1127 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b8 b484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b488 : Encl e488 (286988193383 / 1000000000000 : ℝ) (35873524173 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b487 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b489 : Encl e489 (529 / 625 : ℝ) (529 / 625 : ℝ) := by
  exact Encl.pow b484 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b490 : Encl e490 (2116 / 625 : ℝ) (2116 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b489 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b491 : Encl e491 (1077669950663 / 1000000000000 : ℝ) (134708743833 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b490 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b492 : Encl e492 (2077669950663 / 1000000000000 : ℝ) (259708743833 / 125000000000 : ℝ) := by
  exact Encl.add b5 b491 (by norm_num) (by norm_num)

lemma b493 : Encl e493 (720706242283 / 500000000000 : ℝ) (1441412484567 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b492 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b494 : Encl e494 (1220706242283 / 500000000000 : ℝ) (2441412484567 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b493 (by norm_num) (by norm_num)

lemma b495 : Encl e495 (819197908031 / 1000000000000 : ℝ) (819197908033 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b494 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b496 : Encl e496 (28671926781 / 125000000000 : ℝ) (917501657 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b495 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b497 : Encl e497 (516363607631 / 1000000000000 : ℝ) (258181803817 / 500000000000 : ℝ) := by
  exact Encl.add b488 b496 (by norm_num) (by norm_num)

lemma b498 : Encl e498 (-483636392369 / 1000000000000 : ℝ) (-241818196183 / 500000000000 : ℝ) := by
  exact Encl.sub b497 b5 (by norm_num) (by norm_num)

lemma b499 : Encl e499 (1855855773623 / 500000000000 : ℝ) (3711711547247 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b489 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b500 : Encl e500 (42879124917 / 500000000000 : ℝ) (21439562459 / 250000000000 : ℝ) := by
  exact Encl.pow b485 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b501 : Encl e501 (228560437541 / 250000000000 : ℝ) (457120875083 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b500 (by norm_num) (by norm_num)

lemma b502 : Encl e502 (956159897801 / 1000000000000 : ℝ) (956159897803 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b501 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b503 : Encl e503 (-289493231137 / 1000000000000 : ℝ) (-144746615567 / 500000000000 : ℝ) := by
  exact Encl.sub b29 b502 (by norm_num) (by norm_num)

lemma b504 : Encl e504 (874161298401 / 1000000000000 : ℝ) (874161298407 / 1000000000000 : ℝ) := by
  exact Encl.pow b502 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b505 : Encl e505 (291387099467 / 1000000000000 : ℝ) (291387099469 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b504 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b506 : Encl e506 (189386833 / 100000000000 : ℝ) (378773667 / 200000000000 : ℝ) := by
  exact Encl.add b503 b505 (by norm_num) (by norm_num)

lemma b507 : Encl e507 (1855990963 / 1000000000000 : ℝ) (1855990969 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b506 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

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

lemma b508 : Encl e508 (17938056183 / 200000000000 : ℝ) (44845140459 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b500 b502 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b509 : Encl e509 (-382061943817 / 200000000000 : ℝ) (-955154859541 / 500000000000 : ℝ) := by
  exact Encl.sub b508 b23 (by norm_num) (by norm_num)

lemma b510 : Encl e510 (956159897801 / 500000000000 : ℝ) (956159897803 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b502 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b511 : Encl e511 (2010076517 / 1000000000000 : ℝ) (502519131 / 250000000000 : ℝ) := by
  exact Encl.add b509 b510 (by norm_num) (by norm_num)

lemma b512 : Encl e512 (4020153 / 100000000000 : ℝ) (40201531 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b511 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b513 : Encl e513 (226973679 / 125000000000 : ℝ) (1815789439 / 1000000000000 : ℝ) := by
  exact Encl.sub b507 b512 (by norm_num) (by norm_num)

lemma b514 : Encl e514 (3369843301 / 500000000000 : ℝ) (6739686629 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b499 b513 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b515 : Encl e515 (-476896705767 / 1000000000000 : ℝ) (-476896705737 / 1000000000000 : ℝ) := by
  exact Encl.add b498 b514 (by norm_num) (by norm_num)

lemma b516 : Encl e516 (393323274501 / 1000000000000 : ℝ) (78664654901 / 200000000000 : ℝ) := by
  exact Encl.pow b486 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b517 : Encl e517 (121335345099 / 200000000000 : ℝ) (606676725499 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b516 (by norm_num) (by norm_num)

lemma b518 : Encl e518 (389447276757 / 500000000000 : ℝ) (389447276759 / 500000000000 : ℝ) := by
  exact Encl.sqrt b517 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b519 : Encl e519 (889447276757 / 500000000000 : ℝ) (889447276759 / 500000000000 : ℝ) := by
  exact Encl.add b5 b518 (by norm_num) (by norm_num)

lemma b520 : Encl e520 (88138291203 / 250000000000 : ℝ) (70510632963 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b486 b519 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b521 : Encl e521 (62146867009 / 500000000000 : ℝ) (62146867011 / 500000000000 : ℝ) := by
  exact Encl.pow b520 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b522 : Encl e522 (562146867009 / 500000000000 : ℝ) (562146867011 / 500000000000 : ℝ) := by
  exact Encl.add b5 b521 (by norm_num) (by norm_num)

lemma b523 : Encl e523 (265081795633 / 250000000000 : ℝ) (212065436507 / 200000000000 : ℝ) := by
  exact Encl.sqrt b522 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b524 : Encl e524 (515081795633 / 250000000000 : ℝ) (412065436507 / 200000000000 : ℝ) := by
  exact Encl.add b5 b523 (by norm_num) (by norm_num)

lemma b525 : Encl e525 (85557567701 / 500000000000 : ℝ) (42778783851 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b520 b524 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b526 : Encl e526 (16947377027 / 25000000000 : ℝ) (5296055321 / 7812500000 : ℝ) := by
  apply Encl.arcsin (z := e486) (a := (85557567701 / 500000000000 : ℝ)) (b := (42778783851 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (62715490471 / 100000000000 : ℝ) by norm_num).trans b486.1
        exact b486.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e486) (85557567701 / 500000000000 : ℝ) (42778783851 / 250000000000 : ℝ) from b525) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b527 : Encl e527 (6914529827 / 20000000000 : ℝ) (69145298271 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b526 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b528 : Encl e528 (307305903307 / 1000000000000 : ℝ) (307305903309 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b486 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b529 : Encl e529 (59839723587 / 250000000000 : ℝ) (14959930897 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b528 b518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b530 : Encl e530 (53183798499 / 500000000000 : ℝ) (106367597007 / 1000000000000 : ℝ) := by
  exact Encl.sub b527 b529 (by norm_num) (by norm_num)

lemma b531 : Encl e531 (389447276757 / 10000000000 : ℝ) (389447276759 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b532 : Encl e532 (1610371781 / 100000000000 : ℝ) (16103717811 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b486 b531 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b533 : Encl e533 (90263879187 / 1000000000000 : ℝ) (90263879197 / 1000000000000 : ℝ) := by
  exact Encl.sub b530 b532 (by norm_num) (by norm_num)

lemma b534 : Encl e534 (1956159897801 / 1000000000000 : ℝ) (1956159897803 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b502 (by norm_num) (by norm_num)

lemma b535 : Encl e535 (5988162739 / 40000000000 : ℝ) (37426017119 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b485 b534 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b536 : Encl e536 (22411308117 / 1000000000000 : ℝ) (22411308119 / 1000000000000 : ℝ) := by
  exact Encl.pow b535 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b537 : Encl e537 (1022411308117 / 1000000000000 : ℝ) (1022411308119 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b536 (by norm_num) (by norm_num)

lemma b538 : Encl e538 (1011143564543 / 1000000000000 : ℝ) (202228712909 / 200000000000 : ℝ) := by
  exact Encl.sqrt b537 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b539 : Encl e539 (2011143564543 / 1000000000000 : ℝ) (402228712909 / 200000000000 : ℝ) := by
  exact Encl.add b5 b538 (by norm_num) (by norm_num)

lemma b540 : Encl e540 (74437285887 / 1000000000000 : ℝ) (74437285889 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b535 b539 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b541 : Encl e541 (297201030933 / 1000000000000 : ℝ) (148600515471 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e485) (a := (74437285887 / 1000000000000 : ℝ)) (b := (74437285889 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (292845095289 / 1000000000000 : ℝ) by norm_num).trans b485.1
        exact b485.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e485) (74437285887 / 1000000000000 : ℝ) (74437285889 / 1000000000000 : ℝ) from b540) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b542 : Encl e542 (6062901031 / 40000000000 : ℝ) (151572525781 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b543 : Encl e543 (143494096691 / 1000000000000 : ℝ) (143494096693 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b485 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b544 : Encl e544 (137203300827 / 1000000000000 : ℝ) (13720330083 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b543 b502 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b545 : Encl e545 (2873844989 / 200000000000 : ℝ) (7184612477 / 500000000000 : ℝ) := by
  exact Encl.sub b542 b544 (by norm_num) (by norm_num)

lemma b546 : Encl e546 (956159897801 / 20000000000 : ℝ) (956159897803 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b502 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b547 : Encl e547 (382840119 / 62500000000 : ℝ) (1225088381 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b485 b546 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b548 : Encl e548 (12880911 / 1562500000 : ℝ) (164875661 / 20000000000 : ℝ) := by
  exact Encl.sub b545 b547 (by norm_num) (by norm_num)

lemma b549 : Encl e549 (82020096137 / 1000000000000 : ℝ) (82020096157 / 1000000000000 : ℝ) := by
  exact Encl.sub b533 b548 (by norm_num) (by norm_num)

lemma b550 : Encl e550 (89152278409 / 1000000000000 : ℝ) (2786008701 / 31250000000 : ℝ) := by
  exact Encl.div_nonneg b549 b484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b551 : Encl e551 (-193872213679 / 500000000000 : ℝ) (-77548885461 / 200000000000 : ℝ) := by
  exact Encl.add b515 b550 (by norm_num) (by norm_num)

lemma b552 : Encl e552 (40422455583 / 25000000000 : ℝ) (1616898223323 / 1000000000000 : ℝ) := by
  exact Encl.add b486 b4 (by norm_num) (by norm_num)

lemma b553 : Encl e553 (40422455583 / 50000000000 : ℝ) (404224555831 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b552 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b554 : Encl e554 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b486 b484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b555 : Encl e555 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b554 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b556 : Encl e556 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b554 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b557 : Encl e557 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b556 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b558 : Encl e558 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b557 (by norm_num) (by norm_num)

lemma b559 : Encl e559 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b558 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b560 : Encl e560 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b555 b559 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b561 : Encl e561 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b556 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b562 : Encl e562 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b560 b561 (by norm_num) (by norm_num)

lemma b563 : Encl e563 (551111766933 / 1000000000000 : ℝ) (275555883477 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b553 b562 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b564 : Encl e564 (878749034413 / 1000000000000 : ℝ) (54921814651 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b553 b484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b565 : Encl e565 (194692763753 / 125000000000 : ℝ) (1557542110031 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b564 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b566 : Encl e566 (772199865481 / 1000000000000 : ℝ) (48262491593 / 62500000000 : ℝ) := by
  exact Encl.pow b564 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b567 : Encl e567 (151621089031 / 250000000000 : ℝ) (606484356131 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b566 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b568 : Encl e568 (401621089031 / 250000000000 : ℝ) (1606484356131 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b567 (by norm_num) (by norm_num)

lemma b569 : Encl e569 (1267471639179 / 1000000000000 : ℝ) (1267471639183 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b568 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b570 : Encl e570 (987070225641 / 500000000000 : ℝ) (987070225649 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b565 b569 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b571 : Encl e571 (151621089031 / 125000000000 : ℝ) (1212968712261 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b566 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b572 : Encl e572 (761171739021 / 1000000000000 : ℝ) (15223434781 / 20000000000 : ℝ) := by
  exact Encl.sub b570 b571 (by norm_num) (by norm_num)

lemma b573 : Encl e573 (477372589453 / 1000000000000 : ℝ) (238686294737 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b486 b572 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b574 : Encl e574 (73739177459 / 1000000000000 : ℝ) (73739177501 / 1000000000000 : ℝ) := by
  exact Encl.sub b563 b573 (by norm_num) (by norm_num)

lemma b575 : Encl e575 (653589966143 / 1000000000000 : ℝ) (163397491537 / 250000000000 : ℝ) := by
  exact Encl.pow b553 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b576 : Encl e576 (32025908341 / 50000000000 : ℝ) (320259083413 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b575 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b577 : Encl e577 (179740916587 / 500000000000 : ℝ) (17974091659 / 50000000000 : ℝ) := by
  exact Encl.sub b5 b576 (by norm_num) (by norm_num)

lemma b578 : Encl e578 (86602508463 / 250000000000 : ℝ) (346410033857 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b575 (by norm_num) (by norm_num)

lemma b579 : Encl e579 (23542643313 / 40000000000 : ℝ) (58856608283 / 100000000000 : ℝ) := by
  exact Encl.sqrt b578 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b580 : Encl e580 (3817347827 / 6250000000 : ℝ) (38173478271 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b577 b579 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b581 : Encl e581 (24326521729 / 62500000000 : ℝ) (2432652173 / 6250000000 : ℝ) := by
  exact Encl.sub b5 b580 (by norm_num) (by norm_num)

lemma b582 : Encl e582 (38545680901 / 100000000000 : ℝ) (77091361803 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b516 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b583 : Encl e583 (122908638197 / 200000000000 : ℝ) (61454319099 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b582 (by norm_num) (by norm_num)

lemma b584 : Encl e584 (9862425989 / 12500000000 : ℝ) (197248519783 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b583 b518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b585 : Encl e585 (52751480217 / 250000000000 : ℝ) (2637574011 / 12500000000 : ℝ) := by
  exact Encl.sub b5 b584 (by norm_num) (by norm_num)

lemma b586 : Encl e586 (5569325837 / 31250000000 : ℝ) (44554606703 / 250000000000 : ℝ) := by
  exact Encl.sub b581 b585 (by norm_num) (by norm_num)

lemma b587 : Encl e587 (13141680199 / 1000000000000 : ℝ) (13141680209 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b574 b586 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b588 : Encl e588 (79481625193 / 1000000000000 : ℝ) (15896325049 / 200000000000 : ℝ) := by
  exact Encl.sub b572 b562 (by norm_num) (by norm_num)

lemma b589 : Encl e589 (63542643313 / 40000000000 : ℝ) (158856608283 / 100000000000 : ℝ) := by
  exact Encl.add b5 b579 (by norm_num) (by norm_num)

lemma b590 : Encl e590 (50891752027 / 100000000000 : ℝ) (254458760137 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b553 b589 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b591 : Encl e591 (258997042437 / 1000000000000 : ℝ) (129498521221 / 500000000000 : ℝ) := by
  exact Encl.pow b590 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b592 : Encl e592 (1258997042437 / 1000000000000 : ℝ) (629498521221 / 500000000000 : ℝ) := by
  exact Encl.add b5 b591 (by norm_num) (by norm_num)

lemma b593 : Encl e593 (561025187143 / 500000000000 : ℝ) (1122050374289 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b592 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b594 : Encl e594 (1061025187143 / 500000000000 : ℝ) (2122050374289 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b593 (by norm_num) (by norm_num)

lemma b595 : Encl e595 (239823486961 / 1000000000000 : ℝ) (59955871741 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b590 b594 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b596 : Encl e596 (941512297663 / 1000000000000 : ℝ) (235378074419 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e553) (a := (239823486961 / 1000000000000 : ℝ)) (b := (59955871741 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (40422455583 / 50000000000 : ℝ) by norm_num).trans b553.1
        exact b553.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e553) (239823486961 / 1000000000000 : ℝ) (59955871741 / 250000000000 : ℝ) from b595) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b597 : Encl e597 (3751338061 / 7812500000 : ℝ) (96034254363 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b596 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b598 : Encl e598 (396140064713 / 1000000000000 : ℝ) (79228012943 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b553 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b599 : Encl e599 (116577303069 / 500000000000 : ℝ) (116577303071 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b598 b579 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b600 : Encl e600 (123508332833 / 500000000000 : ℝ) (247016665677 / 1000000000000 : ℝ) := by
  exact Encl.sub b597 b599 (by norm_num) (by norm_num)

lemma b601 : Encl e601 (23542643313 / 800000000 : ℝ) (58856608283 / 2000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b579 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b602 : Encl e602 (2747182127 / 100000000000 : ℝ) (27471821271 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b553 b601 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b603 : Encl e603 (43908968879 / 200000000000 : ℝ) (219544844407 / 1000000000000 : ℝ) := by
  exact Encl.sub b600 b602 (by norm_num) (by norm_num)

lemma b604 : Encl e604 (64640482599 / 500000000000 : ℝ) (6464048261 / 50000000000 : ℝ) := by
  exact Encl.sub b603 b533 (by norm_num) (by norm_num)

lemma b605 : Encl e605 (513773061 / 50000000000 : ℝ) (10275461229 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b588 b604 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b606 : Encl e606 (23417141419 / 1000000000000 : ℝ) (11708570719 / 500000000000 : ℝ) := by
  exact Encl.add b587 b605 (by norm_num) (by norm_num)

lemma b607 : Encl e607 (45323551737 / 250000000000 : ℝ) (22661775869 / 125000000000 : ℝ) := by
  exact Encl.sub b553 b486 (by norm_num) (by norm_num)

lemma b608 : Encl e608 (129166517853 / 1000000000000 : ℝ) (64583258981 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b606 b607 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b609 : Encl e609 (-51715581901 / 200000000000 : ℝ) (-258577909343 / 1000000000000 : ℝ) := by
  exact Encl.add b551 b608 (by norm_num) (by norm_num)

lemma b610 : Encl e610 (75336464301 / 100000000000 : ℝ) (753364643041 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b572 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b611 : Encl e611 (107580795501 / 100000000000 : ℝ) (268951988753 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b612 : Encl e612 (1906819952691 / 1000000000000 : ℝ) (1906819952697 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b611 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b613 : Encl e613 (578681378031 / 500000000000 : ℝ) (289340689017 / 250000000000 : ℝ) := by
  exact Encl.pow b611 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b614 : Encl e614 (181798116599 / 200000000000 : ℝ) (454495291501 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b613 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b615 : Encl e615 (381798116599 / 200000000000 : ℝ) (954495291501 / 500000000000 : ℝ) := by
  exact Encl.add b5 b614 (by norm_num) (by norm_num)

lemma b616 : Encl e616 (1381662253589 / 1000000000000 : ℝ) (1381662253593 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b615 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b617 : Encl e617 (2634581153023 / 1000000000000 : ℝ) (32932264413 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b612 b616 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b618 : Encl e618 (181798116599 / 100000000000 : ℝ) (1817981166001 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b613 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b619 : Encl e619 (408299993511 / 500000000000 : ℝ) (16331999741 / 20000000000 : ℝ) := by
  exact Encl.sub b617 b618 (by norm_num) (by norm_num)

lemma b620 : Encl e620 (660179534089 / 1000000000000 : ℝ) (330089767057 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b553 b619 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b621 : Encl e621 (2912034653 / 31250000000 : ℝ) (11648138619 / 125000000000 : ℝ) := by
  exact Encl.sub b610 b620 (by norm_num) (by norm_num)

lemma b622 : Encl e622 (66155130459 / 200000000000 : ℝ) (82693913091 / 250000000000 : ℝ) := by
  exact Encl.sub b165 b581 (by norm_num) (by norm_num)

lemma b623 : Encl e623 (30823365179 / 1000000000000 : ℝ) (6164673041 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b621 b622 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b624 : Encl e624 (13857061993 / 250000000000 : ℝ) (55428248029 / 1000000000000 : ℝ) := by
  exact Encl.sub b619 b572 (by norm_num) (by norm_num)

lemma b625 : Encl e625 (60121585021 / 200000000000 : ℝ) (293562427 / 976562500 : ℝ) := by
  exact Encl.sub b183 b603 (by norm_num) (by norm_num)

lemma b626 : Encl e626 (3332434123 / 200000000000 : ℝ) (16662170641 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b624 b625 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b627 : Encl e627 (23742767897 / 500000000000 : ℝ) (23742767923 / 500000000000 : ℝ) := by
  exact Encl.add b623 b626 (by norm_num) (by norm_num)

lemma b628 : Encl e628 (45323551737 / 250000000000 : ℝ) (181294206951 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b553 (by norm_num) (by norm_num)

lemma b629 : Encl e629 (52385055863 / 200000000000 : ℝ) (32740659951 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b627 b628 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b630 : Encl e630 (334736981 / 100000000000 : ℝ) (669474053 / 200000000000 : ℝ) := by
  exact Encl.add b609 b629 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_92 : Encl (twoChordBaseline (23 / 25 : ℝ)) (334736981 / 100000000000 : ℝ) (669474053 / 200000000000 : ℝ) := by
  exact b630

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

lemma baseline_lower_92_oai : (334736981 / 100000000000 : ℝ) ≤ baseline (23 / 25 : ℝ) :=
  (baseline_enclosure_92).1.trans (twoChordBaseline_le_of_range (h := (23 / 25 : ℝ)) (by norm_num) (by norm_num))

end CubicTorus.Scalar.Cert

end
end
end
end ReusedScalar205

end

end

end OAI
end

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_92_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_92_oai

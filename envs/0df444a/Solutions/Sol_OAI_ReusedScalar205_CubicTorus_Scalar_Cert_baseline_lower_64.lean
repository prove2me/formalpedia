-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_64
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:35:16.348151+00:00
-- url     : https://prove2.me/submissions/979ee0d6-757a-48bf-9f19-3d156cd8827f

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

lemma b11 : Encl e11 (16 / 25 : ℝ) (16 / 25 : ℝ) := by
  exact Encl.exact (16 / 25 : ℝ)

lemma b12 : Encl e12 (203718327157 / 1000000000000 : ℝ) (101859163579 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b11 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b13 : Encl e13 (218140836421 / 500000000000 : ℝ) (436281672843 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b11 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b14 : Encl e14 (392 / 625 : ℝ) (392 / 625 : ℝ) := by
  exact Encl.mul_nonneg b8 b11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b15 : Encl e15 (99821980307 / 500000000000 : ℝ) (39928792123 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b14 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b16 : Encl e16 (256 / 625 : ℝ) (256 / 625 : ℝ) := by
  exact Encl.pow b11 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b17 : Encl e17 (4 : ℝ) (4 : ℝ) := by
  exact Encl.exact (4 : ℝ)

lemma b18 : Encl e18 (1024 / 625 : ℝ) (1024 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b19 : Encl e19 (521518917523 / 1000000000000 : ℝ) (130379729381 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b18 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b20 : Encl e20 (1521518917523 / 1000000000000 : ℝ) (380379729381 / 250000000000 : ℝ) := by
  exact Encl.add b5 b19 (by norm_num) (by norm_num)

lemma b21 : Encl e21 (1233498649177 / 1000000000000 : ℝ) (1233498649179 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b22 : Encl e22 (2233498649177 / 1000000000000 : ℝ) (2233498649179 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b21 (by norm_num) (by norm_num)

lemma b23 : Encl e23 (2 : ℝ) (2 : ℝ) := by
  exact Encl.exact (2 : ℝ)

lemma b24 : Encl e24 (895456104589 / 1000000000000 : ℝ) (895456104591 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b25 : Encl e25 (62681927321 / 250000000000 : ℝ) (125363854643 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b26 : Encl e26 (225185834949 / 500000000000 : ℝ) (450371669901 / 1000000000000 : ℝ) := by
  exact Encl.add b15 b25 (by norm_num) (by norm_num)

lemma b27 : Encl e27 (-274814165051 / 500000000000 : ℝ) (-549628330099 / 1000000000000 : ℝ) := by
  exact Encl.sub b26 b5 (by norm_num) (by norm_num)

lemma b28 : Encl e28 (1917475984857 / 250000000000 : ℝ) (7669903939429 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b29 : Encl e29 (2 / 3 : ℝ) (2 / 3 : ℝ) := by
  exact Encl.exact (2 / 3 : ℝ)

lemma b30 : Encl e30 (41501156819 / 1000000000000 : ℝ) (41501156821 / 1000000000000 : ℝ) := by
  exact Encl.pow b12 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b31 : Encl e31 (958498843179 / 1000000000000 : ℝ) (958498843181 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b30 (by norm_num) (by norm_num)

lemma b32 : Encl e32 (39161181661 / 40000000000 : ℝ) (979029541527 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b33 : Encl e33 (-312362874861 / 1000000000000 : ℝ) (-156181437429 / 500000000000 : ℝ) := by
  exact Encl.sub b29 b32 (by norm_num) (by norm_num)

lemma b34 : Encl e34 (938398682989 / 1000000000000 : ℝ) (234599670749 / 250000000000 : ℝ) := by
  exact Encl.pow b32 (by norm_num) 3 (by norm_num) (by norm_num)

lemma b35 : Encl e35 (3 : ℝ) (3 : ℝ) := by
  exact Encl.exact (3 : ℝ)

lemma b36 : Encl e36 (78199890249 / 250000000000 : ℝ) (312799560999 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b34 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b37 : Encl e37 (87337227 / 200000000000 : ℝ) (436686141 / 1000000000000 : ℝ) := by
  exact Encl.add b33 b36 (by norm_num) (by norm_num)

lemma b38 : Encl e38 (106988103 / 250000000000 : ℝ) (427952419 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b39 : Encl e39 (21195048289 / 500000000000 : ℝ) (21195048291 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b30 b32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b40 : Encl e40 (-978804951711 / 500000000000 : ℝ) (-978804951709 / 500000000000 : ℝ) := by
  exact Encl.sub b39 b23 (by norm_num) (by norm_num)

lemma b41 : Encl e41 (39161181661 / 20000000000 : ℝ) (979029541527 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b42 : Encl e42 (112294907 / 250000000000 : ℝ) (112294909 / 250000000000 : ℝ) := by
  exact Encl.add b40 b41 (by norm_num) (by norm_num)

lemma b43 : Encl e43 (50 : ℝ) (50 : ℝ) := by
  exact Encl.exact (50 : ℝ)

lemma b44 : Encl e44 (1122949 / 125000000000 : ℝ) (8983593 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b42 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b45 : Encl e45 (418968819 / 1000000000000 : ℝ) (418968827 / 1000000000000 : ℝ) := by
  exact Encl.sub b38 b44 (by norm_num) (by norm_num)

lemma b46 : Encl e46 (642690119 / 200000000000 : ℝ) (3213450657 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b28 b45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b47 : Encl e47 (-546414879507 / 1000000000000 : ℝ) (-273207439721 / 500000000000 : ℝ) := by
  exact Encl.add b27 b46 (by norm_num) (by norm_num)

lemma b48 : Encl e48 (190341698057 / 1000000000000 : ℝ) (190341698059 / 1000000000000 : ℝ) := by
  exact Encl.pow b13 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b49 : Encl e49 (809658301941 / 1000000000000 : ℝ) (809658301943 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b48 (by norm_num) (by norm_num)

lemma b50 : Encl e50 (22495253693 / 25000000000 : ℝ) (449905073861 / 500000000000 : ℝ) := by
  exact Encl.sqrt b49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b51 : Encl e51 (47495253693 / 25000000000 : ℝ) (949905073861 / 500000000000 : ℝ) := by
  exact Encl.add b5 b50 (by norm_num) (by norm_num)

lemma b52 : Encl e52 (57411219927 / 250000000000 : ℝ) (229644879709 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b13 b51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b53 : Encl e53 (6592096347 / 125000000000 : ℝ) (52736770777 / 1000000000000 : ℝ) := by
  exact Encl.pow b52 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b54 : Encl e54 (131592096347 / 125000000000 : ℝ) (1052736770777 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b53 (by norm_num) (by norm_num)

lemma b55 : Encl e55 (12825370187 / 12500000000 : ℝ) (1026029614961 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b56 : Encl e56 (25325370187 / 12500000000 : ℝ) (2026029614961 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b55 (by norm_num) (by norm_num)

lemma b57 : Encl e57 (28336811813 / 250000000000 : ℝ) (56673623627 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b52 b56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b58 : Encl e58 (14108192723 / 31250000000 : ℝ) (56432770893 / 125000000000 : ℝ) := by
  apply Encl.arcsin (z := e13) (a := (28336811813 / 250000000000 : ℝ)) (b := (56673623627 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (218140836421 / 500000000000 : ℝ) by norm_num).trans b13.1
        exact b13.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e13) (28336811813 / 250000000000 : ℝ) (56673623627 / 500000000000 : ℝ) from b57) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b59 : Encl e59 (51 / 100 : ℝ) (51 / 100 : ℝ) := by
  exact Encl.exact (51 / 100 : ℝ)

lemma b60 : Encl e60 (230245705239 / 1000000000000 : ℝ) (57561426311 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b61 : Encl e61 (49 / 100 : ℝ) (49 / 100 : ℝ) := by
  exact Encl.exact (49 / 100 : ℝ)

lemma b62 : Encl e62 (53444504923 / 250000000000 : ℝ) (106889009847 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b63 : Encl e63 (96179815739 / 500000000000 : ℝ) (192359631481 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b62 b50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b64 : Encl e64 (18943036879 / 500000000000 : ℝ) (18943036883 / 500000000000 : ℝ) := by
  exact Encl.sub b60 b63 (by norm_num) (by norm_num)

lemma b65 : Encl e65 (22495253693 / 500000000 : ℝ) (449905073861 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b66 : Encl e66 (9697193879 / 1000000000000 : ℝ) (242429847 / 25000000000 : ℝ) := by
  exact Encl.div_nonneg b13 b65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b67 : Encl e67 (14094439939 / 500000000000 : ℝ) (28188879887 / 1000000000000 : ℝ) := by
  exact Encl.sub b64 b66 (by norm_num) (by norm_num)

lemma b68 : Encl e68 (79161181661 / 40000000000 : ℝ) (1979029541527 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b32 (by norm_num) (by norm_num)

lemma b69 : Encl e69 (2573462433 / 25000000000 : ℝ) (102938497321 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b12 b68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b70 : Encl e70 (1059633423 / 100000000000 : ℝ) (10596334231 / 1000000000000 : ℝ) := by
  exact Encl.pow b69 (by norm_num) 2 (by norm_num) (by norm_num)

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
lemma b71 : Encl e71 (101059633423 / 100000000000 : ℝ) (1010596334231 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b70 (by norm_num) (by norm_num)

lemma b72 : Encl e72 (10052842057 / 10000000000 : ℝ) (1005284205701 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b71 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b73 : Encl e73 (20052842057 / 10000000000 : ℝ) (2005284205701 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b72 (by norm_num) (by norm_num)

lemma b74 : Encl e74 (12833404989 / 250000000000 : ℝ) (51333619957 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b69 b73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b75 : Encl e75 (102577201359 / 500000000000 : ℝ) (205154402723 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e12) (a := (12833404989 / 250000000000 : ℝ)) (b := (51333619957 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (203718327157 / 1000000000000 : ℝ) by norm_num).trans b12.1
        exact b12.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e12) (12833404989 / 250000000000 : ℝ) (51333619957 / 1000000000000 : ℝ) from b74) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b76 : Encl e76 (52314372693 / 500000000000 : ℝ) (104628745389 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b75 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b77 : Encl e77 (49910990153 / 500000000000 : ℝ) (24955495077 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b78 : Encl e78 (97728667613 / 1000000000000 : ℝ) (3054020863 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b77 b32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b79 : Encl e79 (690007777 / 100000000000 : ℝ) (431254861 / 62500000000 : ℝ) := by
  exact Encl.sub b76 b78 (by norm_num) (by norm_num)

lemma b80 : Encl e80 (39161181661 / 800000000 : ℝ) (979029541527 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b81 : Encl e81 (4161637999 / 1000000000000 : ℝ) (4161638001 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b12 b80 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b82 : Encl e82 (2738439769 / 1000000000000 : ℝ) (2738439777 / 1000000000000 : ℝ) := by
  exact Encl.sub b79 b81 (by norm_num) (by norm_num)

lemma b83 : Encl e83 (25450440101 / 1000000000000 : ℝ) (12725220059 / 500000000000 : ℝ) := by
  exact Encl.sub b67 b82 (by norm_num) (by norm_num)

lemma b84 : Encl e84 (39766312657 / 1000000000000 : ℝ) (7953262537 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b83 b11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b85 : Encl e85 (-10132971337 / 20000000000 : ℝ) (-506648566757 / 1000000000000 : ℝ) := by
  exact Encl.add b47 b84 (by norm_num) (by norm_num)

lemma b86 : Encl e86 (356506247863 / 250000000000 : ℝ) (713012495727 / 500000000000 : ℝ) := by
  exact Encl.add b13 b4 (by norm_num) (by norm_num)

lemma b87 : Encl e87 (356506247863 / 500000000000 : ℝ) (713012495727 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b86 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b88 : Encl e88 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b13 b11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b89 : Encl e89 (354490770181 / 200000000000 : ℝ) (886226925453 / 500000000000 : ℝ) := by
  exact Encl.sqrt b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b90 : Encl e90 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b88 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b91 : Encl e91 (785398163397 / 1000000000000 : ℝ) (392699081699 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b92 : Encl e92 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b88 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b93 : Encl e93 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b92 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b94 : Encl e94 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b93 (by norm_num) (by norm_num)

lemma b95 : Encl e95 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b94 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b96 : Encl e96 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b90 b95 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b97 : Encl e97 (785398163397 / 500000000000 : ℝ) (314159265359 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b98 : Encl e98 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b92 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b99 : Encl e99 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b96 b98 (by norm_num) (by norm_num)

lemma b100 : Encl e100 (97210713871 / 200000000000 : ℝ) (486053569373 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b87 b99 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b101 : Encl e101 (1114082024571 / 1000000000000 : ℝ) (557041012287 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b87 b11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b102 : Encl e102 (987329487337 / 500000000000 : ℝ) (987329487341 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b101 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b103 : Encl e103 (38786836171 / 31250000000 : ℝ) (1241178757479 / 1000000000000 : ℝ) := by
  exact Encl.pow b101 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b104 : Encl e104 (194963903313 / 200000000000 : ℝ) (974819516573 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b103 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b105 : Encl e105 (394963903313 / 200000000000 : ℝ) (1974819516573 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b104 (by norm_num) (by norm_num)

lemma b106 : Encl e106 (1405282717663 / 1000000000000 : ℝ) (1405282717667 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b105 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b107 : Encl e107 (2774954130387 / 1000000000000 : ℝ) (2774954130407 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b102 b106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b108 : Encl e108 (1949639033131 / 1000000000000 : ℝ) (243704879143 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b103 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b109 : Encl e109 (825315097243 / 1000000000000 : ℝ) (206328774319 / 250000000000 : ℝ) := by
  exact Encl.sub b107 b108 (by norm_num) (by norm_num)

lemma b110 : Encl e110 (180034925623 / 500000000000 : ℝ) (360069851263 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b13 b109 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b111 : Encl e111 (31495929523 / 250000000000 : ℝ) (125983718127 / 1000000000000 : ℝ) := by
  exact Encl.sub b100 b110 (by norm_num) (by norm_num)

lemma b112 : Encl e112 (508386819061 / 1000000000000 : ℝ) (508386819063 / 1000000000000 : ℝ) := by
  exact Encl.pow b87 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b113 : Encl e113 (498219082679 / 1000000000000 : ℝ) (249109541341 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b112 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b114 : Encl e114 (250890458659 / 500000000000 : ℝ) (501780917321 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b113 (by norm_num) (by norm_num)

lemma b115 : Encl e115 (491613180937 / 1000000000000 : ℝ) (491613180939 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b112 (by norm_num) (by norm_num)

lemma b116 : Encl e116 (175287831319 / 250000000000 : ℝ) (350575662639 / 500000000000 : ℝ) := by
  exact Encl.sqrt b115 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b117 : Encl e117 (178913202909 / 250000000000 : ℝ) (178913202911 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b114 b116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b118 : Encl e118 (71086797089 / 250000000000 : ℝ) (71086797091 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b117 (by norm_num) (by norm_num)

lemma b119 : Encl e119 (37306972819 / 200000000000 : ℝ) (93267432049 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b120 : Encl e120 (406732567951 / 500000000000 : ℝ) (162693027181 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b119 (by norm_num) (by norm_num)

lemma b121 : Encl e121 (452020427843 / 500000000000 : ℝ) (226010213923 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b120 b50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b122 : Encl e122 (23989786077 / 250000000000 : ℝ) (47979572157 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b121 (by norm_num) (by norm_num)

lemma b123 : Encl e123 (94194022021 / 500000000000 : ℝ) (23548505507 / 125000000000 : ℝ) := by
  exact Encl.sub b118 b122 (by norm_num) (by norm_num)

lemma b124 : Encl e124 (2966728279 / 125000000000 : ℝ) (23733826241 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b111 b123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b125 : Encl e125 (28724996683 / 200000000000 : ℝ) (143624983471 / 1000000000000 : ℝ) := by
  exact Encl.sub b109 b99 (by norm_num) (by norm_num)

lemma b126 : Encl e126 (425287831319 / 250000000000 : ℝ) (850575662639 / 500000000000 : ℝ) := by
  exact Encl.add b5 b116 (by norm_num) (by norm_num)

lemma b127 : Encl e127 (13097976741 / 31250000000 : ℝ) (209567627857 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b87 b126 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b128 : Encl e128 (8783718129 / 50000000000 : ℝ) (175674362583 / 1000000000000 : ℝ) := by
  exact Encl.pow b127 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b129 : Encl e129 (58783718129 / 50000000000 : ℝ) (1175674362583 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b128 (by norm_num) (by norm_num)

lemma b130 : Encl e130 (542142592539 / 500000000000 : ℝ) (27107129627 / 25000000000 : ℝ) := by
  exact Encl.sqrt b129 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b131 : Encl e131 (1042142592539 / 500000000000 : ℝ) (52107129627 / 25000000000 : ℝ) := by
  exact Encl.add b5 b130 (by norm_num) (by norm_num)

lemma b132 : Encl e132 (201093045573 / 1000000000000 : ℝ) (8043721823 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b127 b131 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b133 : Encl e133 (793785375783 / 1000000000000 : ℝ) (793785375791 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e87) (a := (201093045573 / 1000000000000 : ℝ)) (b := (8043721823 / 40000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (356506247863 / 500000000000 : ℝ) by norm_num).trans b87.1
        exact b87.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e87) (201093045573 / 1000000000000 : ℝ) (8043721823 / 40000000000 : ℝ) from b132) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

lemma b134 : Encl e134 (404830541649 / 1000000000000 : ℝ) (202415270827 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b133 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b135 : Encl e135 (69875224581 / 200000000000 : ℝ) (349376122907 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b87 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b136 : Encl e136 (122482765797 / 500000000000 : ℝ) (244965531597 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b135 b116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b137 : Encl e137 (39966252513 / 250000000000 : ℝ) (7993250503 / 50000000000 : ℝ) := by
  exact Encl.sub b134 b136 (by norm_num) (by norm_num)

lemma b138 : Encl e138 (175287831319 / 5000000000 : ℝ) (350575662639 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b139 : Encl e139 (20338334109 / 1000000000000 : ℝ) (2033833411 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b87 b138 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b140 : Encl e140 (69763337971 / 500000000000 : ℝ) (139526675951 / 1000000000000 : ℝ) := by
  exact Encl.sub b137 b139 (by norm_num) (by norm_num)

lemma b141 : Encl e141 (22267559211 / 200000000000 : ℝ) (111337796073 / 1000000000000 : ℝ) := by
  exact Encl.sub b140 b67 (by norm_num) (by norm_num)

lemma b142 : Encl e142 (15990889111 / 1000000000000 : ℝ) (15990889121 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b125 b141 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b143 : Encl e143 (39724715343 / 1000000000000 : ℝ) (19862357681 / 500000000000 : ℝ) := by
  exact Encl.add b124 b142 (by norm_num) (by norm_num)

lemma b144 : Encl e144 (276730822883 / 1000000000000 : ℝ) (55346164577 / 200000000000 : ℝ) := by
  exact Encl.sub b87 b13 (by norm_num) (by norm_num)

lemma b145 : Encl e145 (71775010331 / 500000000000 : ℝ) (35887505183 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b143 b144 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b146 : Encl e146 (-90774636547 / 250000000000 : ℝ) (-14523941841 / 40000000000 : ℝ) := by
  exact Encl.add b85 b145 (by norm_num) (by norm_num)

lemma b147 : Encl e147 (204212525811 / 250000000000 : ℝ) (408425051639 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b109 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b148 : Encl e148 (48327310479 / 31250000000 : ℝ) (154647393533 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b149 : Encl e149 (685263420499 / 250000000000 : ℝ) (1370526841001 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b148 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b150 : Encl e150 (298947704081 / 125000000000 : ℝ) (149473852041 / 62500000000 : ℝ) := by
  exact Encl.pow b148 (by norm_num) 2 (by norm_num) (by norm_num)

lemma b151 : Encl e151 (375668764379 / 200000000000 : ℝ) (375668764381 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b150 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b152 : Encl e152 (575668764379 / 200000000000 : ℝ) (575668764381 / 200000000000 : ℝ) := by
  exact Encl.add b5 b151 (by norm_num) (by norm_num)

lemma b153 : Encl e153 (848284124261 / 500000000000 : ℝ) (848284124263 / 500000000000 : ℝ) := by
  exact Encl.sqrt b152 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b154 : Encl e154 (290649040273 / 62500000000 : ℝ) (465038464439 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b149 b153 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b155 : Encl e155 (3756687643791 / 1000000000000 : ℝ) (3756687643807 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b150 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b156 : Encl e156 (893697000561 / 1000000000000 : ℝ) (893697000599 / 1000000000000 : ℝ) := by
  exact Encl.sub b154 b155 (by norm_num) (by norm_num)

lemma b157 : Encl e157 (79652141099 / 125000000000 : ℝ) (637217128821 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b87 b156 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b158 : Encl e158 (179632974423 / 1000000000000 : ℝ) (89816487243 / 500000000000 : ℝ) := by
  exact Encl.sub b147 b157 (by norm_num) (by norm_num)

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

lemma b166 : Encl e166 (435652811611 / 1000000000000 : ℝ) (54456601459 / 125000000000 : ℝ) := by
  exact Encl.sub b165 b118 (by norm_num) (by norm_num)

lemma b167 : Encl e167 (15651522073 / 200000000000 : ℝ) (19564402601 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b158 b166 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b168 : Encl e168 (13676380657 / 200000000000 : ℝ) (17095475839 / 250000000000 : ℝ) := by
  exact Encl.sub b156 b109 (by norm_num) (by norm_num)

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

lemma b184 : Encl e184 (380626093561 / 1000000000000 : ℝ) (380626093701 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b140 (by norm_num) (by norm_num)

lemma b185 : Encl e185 (26027936717 / 1000000000000 : ℝ) (5205587351 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b168 b184 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b186 : Encl e186 (52142773541 / 500000000000 : ℝ) (104285547159 / 1000000000000 : ℝ) := by
  exact Encl.add b167 b185 (by norm_num) (by norm_num)

lemma b187 : Encl e187 (276730822883 / 1000000000000 : ℝ) (55346164577 / 200000000000 : ℝ) := by
  exact Encl.sub b4 b87 (by norm_num) (by norm_num)

lemma b188 : Encl e188 (188424162503 / 500000000000 : ℝ) (47106040661 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b186 b187 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma b189 : Encl e189 (6874889409 / 500000000000 : ℝ) (13749779263 / 1000000000000 : ℝ) := by
  exact Encl.add b146 b188 (by norm_num) (by norm_num)

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

lemma baseline_enclosure_64 : Encl (twoChordBaseline (16 / 25 : ℝ)) (6874889409 / 500000000000 : ℝ) (13749779263 / 1000000000000 : ℝ) := by
  exact b189

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

lemma baseline_lower_64_oai : (6874889409 / 500000000000 : ℝ) ≤ baseline (16 / 25 : ℝ) :=
  (baseline_enclosure_64).1.trans (twoChordBaseline_le_of_range (h := (16 / 25 : ℝ)) (by norm_num) (by norm_num))

end CubicTorus.Scalar.Cert

end
end
end
end ReusedScalar205

end

end

end OAI
end

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_64_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_64_oai

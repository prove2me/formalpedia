-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff12.coupled_coordinate_bounds12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:53:39.621235+00:00
-- url     : https://prove2.me/submissions/35c5fec5-a5ad-4c36-9e69-44ac7ef5b301

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Convex.Function
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalConstruction
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

end HlawkaSchatten.DiagonalConstruction

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

end HlawkaSchatten.DiagonalCutoff12

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem support12_0 (x : Fin 3 → ℝ) :
    (-183559/10000000 : ℝ)*x 0 + (52353113/100000000 : ℝ)*x 1 + (13088267/25000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(-183559/10000000 : ℝ), (52353113/100000000 : ℝ), (13088267/25000000 : ℝ)] ![(12762539781/1000000000000 : ℝ), (4936189567/10000000000 : ℝ), (493618493839/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_1 (x : Fin 3 → ℝ) :
    (25490469/50000000 : ℝ)*x 0 + (-3630807/100000000 : ℝ)*x 1 + (818017/1562500 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(25490469/50000000 : ℝ), (-3630807/100000000 : ℝ), (818017/1562500 : ℝ)] ![(119880498871/250000000000 : ℝ), (671481991/25000000000 : ℝ), (98723739911/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_2 (x : Fin 3 → ℝ) :
    (3186309/6250000 : ℝ)*x 0 + (10470617/20000000 : ℝ)*x 1 + (-907701/25000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(3186309/6250000 : ℝ), (10470617/20000000 : ℝ), (-907701/25000000 : ℝ)] ![(9590441141/20000000000 : ℝ), (493618668697/1000000000000 : ℝ), (2685925543/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_3 (x : Fin 3 → ℝ) :
    (11163367/25000000 : ℝ)*x 0 + (10127/31250 : ℝ)*x 1 + (32406453/100000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(11163367/25000000 : ℝ), (10127/31250 : ℝ), (32406453/100000000 : ℝ)] ![(25936051821/62500000000 : ℝ), (292511320327/1000000000000 : ℝ), (292511842213/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_4 (x : Fin 3 → ℝ) :
    (-6801109/100000000 : ℝ)*x 0 + (50380781/100000000 : ℝ)*x 1 + (25190377/50000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(-6801109/100000000 : ℝ), (50380781/100000000 : ℝ), (25190377/50000000 : ℝ)] ![(53266065683/1000000000000 : ℝ), (236683548737/500000000000 : ℝ), (18934672829/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_5 (x : Fin 3 → ℝ) :
    (52174851/100000000 : ℝ)*x 0 + (-18006/390625 : ℝ)*x 1 + (25190377/50000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(52174851/100000000 : ℝ), (-18006/390625 : ℝ), (25190377/50000000 : ℝ)] ![(122946418581/250000000000 : ℝ), (34847490073/1000000000000 : ℝ), (18934672829/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_6 (x : Fin 3 → ℝ) :
    (26087433/50000000 : ℝ)*x 0 + (6297593/12500000 : ℝ)*x 1 + (-460953/10000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(26087433/50000000 : ℝ), (6297593/12500000 : ℝ), (-460953/10000000 : ℝ)] ![(491785828563/1000000000000 : ℝ), (18934668729/40000000000 : ℝ), (3484744059/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_7 (x : Fin 3 → ℝ) :
    (3197887/12500000 : ℝ)*x 0 + (5235673/12500000 : ℝ)*x 1 + (4188537/10000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(3197887/12500000 : ℝ), (5235673/12500000 : ℝ), (4188537/10000000 : ℝ)] ![(56502890283/250000000000 : ℝ), (386994280883/1000000000000 : ℝ), (386994139773/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_8 (x : Fin 3 → ℝ) :
    (-2850733/50000000 : ℝ)*x 0 + (24334053/50000000 : ℝ)*x 1 + (13248553/25000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(-2850733/50000000 : ℝ), (24334053/50000000 : ℝ), (13248553/25000000 : ℝ)] ![(21971737931/500000000000 : ℝ), (28489979679/62500000000 : ℝ), (125054206691/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_9 (x : Fin 3 → ℝ) :
    (6324381/12500000 : ℝ)*x 0 + (-1651151/50000000 : ℝ)*x 1 + (52994211/100000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(6324381/12500000 : ℝ), (-1651151/50000000 : ℝ), (52994211/100000000 : ℝ)] ![(475563747461/1000000000000 : ℝ), (3027427707/125000000000 : ℝ), (500216816467/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_10 (x : Fin 3 → ℝ) :
    (3162191/6250000 : ℝ)*x 0 + (1656069/3125000 : ℝ)*x 1 + (-412787/12500000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(3162191/6250000 : ℝ), (1656069/3125000 : ℝ), (-412787/12500000 : ℝ)] ![(118890957373/250000000000 : ℝ), (62527098197/125000000000 : ℝ), (24219373651/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_11 (x : Fin 3 → ℝ) :
    (12651351/25000000 : ℝ)*x 0 + (29310737/100000000 : ℝ)*x 1 + (915961/3125000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(12651351/25000000 : ℝ), (29310737/100000000 : ℝ), (915961/3125000 : ℝ)] ![(475669937889/1000000000000 : ℝ), (131082473641/500000000000 : ℝ), (262165093643/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_12 (x : Fin 3 → ℝ) :
    (-518727/20000000 : ℝ)*x 0 + (26973583/50000000 : ℝ)*x 1 + (50184309/100000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(-518727/20000000 : ℝ), (26973583/50000000 : ℝ), (50184309/100000000 : ℝ)] ![(18608816543/1000000000000 : ℝ), (102007509113/200000000000 : ℝ), (117838406689/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_13 (x : Fin 3 → ℝ) :
    (209179/400000 : ℝ)*x 0 + (-940811/20000000 : ℝ)*x 1 + (10036861/20000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(209179/400000 : ℝ), (-940811/20000000 : ℝ), (10036861/20000000 : ℝ)] ![(246509338627/500000000000 : ℝ), (4453465331/125000000000 : ℝ), (471353585771/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_14 (x : Fin 3 → ℝ) :
    (52294741/100000000 : ℝ)*x 0 + (6273039/12500000 : ℝ)*x 1 + (-4704057/100000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(52294741/100000000 : ℝ), (6273039/12500000 : ℝ), (-4704057/100000000 : ℝ)] ![(493018584691/1000000000000 : ℝ), (94270731499/200000000000 : ℝ), (8906934793/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem support12_15 (x : Fin 3 → ℝ) :
    (11805661/50000000 : ℝ)*x 0 + (42823709/100000000 : ℝ)*x 1 + (8564747/20000000 : ℝ)*x 2 ≤ lpNorm 12 x := by
  have h := norm_support12 ![(11805661/50000000 : ℝ), (42823709/100000000 : ℝ), (8564747/20000000 : ℝ)] ![(41415340503/200000000000 : ℝ), (7929230221/20000000000 : ℝ), (9911544341/25000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ, add_assoc] using h

theorem coupled_coordinate_bounds12 (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm 12 (X 0)+lpNorm 12 (X 1)+lpNorm 12 (X 2) ≤ 3)
    (hC : lpNorm 12 (X 0+X 1+X 2) ≤ (3123/625 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-33716631/1250000 : ℝ)) :
    -(4/5 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(69/100 : ℝ) ∧
      (89/100 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ 1 := by

  have hn0 := lpNorm_nonneg (12 : ℝ) (X 0)

  have hn1 := lpNorm_nonneg (12 : ℝ) (X 1)

  have hn2 := lpNorm_nonneg (12 : ℝ) (X 2)

  have hu0 : lpNorm 12 (X 0) ≤ 3 := by linarith only [hS, hn0, hn1, hn2]

  have hl0 : -3 ≤ lpNorm 12 (X 0) := by linarith only [hn0]

  have hb00 : -3 ≤ X 0 0 ∧ X 0 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by norm_num : (1 : ℝ) ≤ 12) (X 0) 0).trans hu0
    simpa only [Real.norm_eq_abs, abs_le] using h

  have hb01 : -3 ≤ X 0 1 ∧ X 0 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by norm_num : (1 : ℝ) ≤ 12) (X 0) 1).trans hu0
    simpa only [Real.norm_eq_abs, abs_le] using h

  have hb02 : -3 ≤ X 0 2 ∧ X 0 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by norm_num : (1 : ℝ) ≤ 12) (X 0) 2).trans hu0
    simpa only [Real.norm_eq_abs, abs_le] using h

  have hu1 : lpNorm 12 (X 1) ≤ 3 := by linarith only [hS, hn0, hn1, hn2]

  have hl1 : -3 ≤ lpNorm 12 (X 1) := by linarith only [hn1]

  have hb10 : -3 ≤ X 1 0 ∧ X 1 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by norm_num : (1 : ℝ) ≤ 12) (X 1) 0).trans hu1
    simpa only [Real.norm_eq_abs, abs_le] using h

  have hb11 : -3 ≤ X 1 1 ∧ X 1 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by norm_num : (1 : ℝ) ≤ 12) (X 1) 1).trans hu1
    simpa only [Real.norm_eq_abs, abs_le] using h

  have hb12 : -3 ≤ X 1 2 ∧ X 1 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by norm_num : (1 : ℝ) ≤ 12) (X 1) 2).trans hu1
    simpa only [Real.norm_eq_abs, abs_le] using h

  have hu2 : lpNorm 12 (X 2) ≤ 3 := by linarith only [hS, hn0, hn1, hn2]

  have hl2 : -3 ≤ lpNorm 12 (X 2) := by linarith only [hn2]

  have hb20 : -3 ≤ X 2 0 ∧ X 2 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by norm_num : (1 : ℝ) ≤ 12) (X 2) 0).trans hu2
    simpa only [Real.norm_eq_abs, abs_le] using h

  have hb21 : -3 ≤ X 2 1 ∧ X 2 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by norm_num : (1 : ℝ) ≤ 12) (X 2) 1).trans hu2
    simpa only [Real.norm_eq_abs, abs_le] using h

  have hb22 : -3 ≤ X 2 2 ∧ X 2 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by norm_num : (1 : ℝ) ≤ 12) (X 2) 2).trans hu2
    simpa only [Real.norm_eq_abs, abs_le] using h

  have h25 := support12_0 (X 0)

  have h26 := support12_1 (X 1)

  have h27 := support12_2 (X 2)

  have h29 := (support12_3 (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h29

  have h30 := support12_4 (X 0)

  have h31 := support12_5 (X 1)

  have h32 := support12_6 (X 2)

  have h34 := (support12_7 (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h34

  have h35 := support12_8 (X 0)

  have h36 := support12_9 (X 1)

  have h37 := support12_10 (X 2)

  have h39 := (support12_11 (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h39

  have h40 := support12_12 (X 0)

  have h41 := support12_13 (X 1)

  have h42 := support12_14 (X 2)

  have h44 := (support12_15 (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h44

  refine ⟨?_, ?_, ?_, ?_⟩

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hS, h26, h27, h29, h30, h31, h32, h34, h35, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hS, h25, h26, h27, h29, h31, h32, h35, h36]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hS, h35, h36, h37, h39]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hS, h31, h40, h41, h42, h44]

end HlawkaSchatten.DiagonalCutoff12



theorem solution (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm 12 (X 0)+lpNorm 12 (X 1)+lpNorm 12 (X 2) ≤ 3)
    (hC : lpNorm 12 (X 0+X 1+X 2) ≤ (3123/625 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-33716631/1250000 : ℝ)) :
    -(4/5 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(69/100 : ℝ) ∧
      (89/100 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ 1 := by
  exact HlawkaSchatten.DiagonalCutoff12.coupled_coordinate_bounds12 X hS hC

#print axioms solution

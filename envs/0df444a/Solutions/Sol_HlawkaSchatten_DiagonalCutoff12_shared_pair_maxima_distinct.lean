-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff12.shared_pair_maxima_distinct
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:31:33.14048+00:00
-- url     : https://prove2.me/submissions/4e71b551-61e5-483f-8209-8276829cced0

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Convex.Function
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalConstruction
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
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
namespace HlawkaSchatten.DiagonalCutoff16
theorem upper_root_of_power {x y a : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ y^a) : x^(1/a) ≤ y := by
  have hh := Real.rpow_le_rpow hx h (one_div_nonneg.mpr ha.le)
  rw [← Real.rpow_mul hy, mul_one_div_cancel ha.ne', Real.rpow_one] at hh
  exact hh
end HlawkaSchatten.DiagonalCutoff16

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12

/- Keep the combined deficit of two overlapping pairs and their relative
   coordinate estimates. This avoids charging the entire deficit twice. -/
theorem weighted_signed_conflict
    {a b c Na Nb Nc P1 P2 T G A d s r : ℝ}
    (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (ha : |a| ≤ Na) (hb : |b| ≤ Nb) (hc : |c| ≤ Nc)
    (hcol : |a+b+c| ≤ T)
    (h1 : d*P1 ≤ s*a+s*b) (h2 : d*P2 ≤ r*a+r*c)
    (hpair : (Na+Nb-P1)+(Na+Nc-P2) ≤ G)
    (hS : Na+Nb+Nc = 3) (hmin : 3-2*A ≤ Na)
    (hmax : Na ≤ A) (hT : T ≤ A)
    (hopp : 3*(1-d)+d*G < (1+d)*(3-2*A))
    (hsame : (2-d)*A < d*(3-G)) : False := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have hcol' := abs_le.mp hcol
  have hpair' := mul_le_mul_of_nonneg_left hpair hd
  have hmin' := mul_le_mul_of_nonneg_left hmin (show 0 ≤ 1+d by linarith)
  have hmax' := mul_le_mul_of_nonneg_left hmax (sub_nonneg.mpr hd1)
  have hS' := congrArg (fun x : ℝ => d*x) hS
  rcases hs with rfl | rfl <;> rcases hr with rfl | rfl <;> nlinarith

theorem orientation_parameters12 :
    3 * (91/100 : ℝ)^12 < 1 ∧
    2 / ((1041/2500 : ℝ)*12) < 401/1000 ∧
    3*(1-(91/100 : ℝ))+(91/100)*(401/1000) <
      (1+91/100)*(3-2*(1647/1250)) ∧
    (2-(91/100 : ℝ))*(1647/1250) < (91/100)*(3-401/1000) := by
  norm_num

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff12

/- The maximum-coordinate argument follows the Apache-2.0 orientation proof
   of Ezzeri Esa, bwdaugherty and Yuxuan Xu (Prove2Me submission
   4753aff4-c621-4df6-9535-63c865f87fd0). Its relative estimate is retained. -/
theorem norm_le_three_root_max {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    lpNorm p x ≤ (3 : ℝ) ^ (1 / p) * |x i| := by
  have hsum : (∑ j, |x j| ^ p) ≤ 3 * |x i| ^ p := by
    calc
      _ ≤ ∑ _ : Fin 3, |x i| ^ p :=
        Finset.sum_le_sum fun j _ ↦ Real.rpow_le_rpow (abs_nonneg _) (hi j) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg (x i)), mul_one_div_cancel hp.ne', Real.rpow_one] at h
  simpa only [lpNorm, Real.norm_eq_abs] using h

theorem relative_coordinate12 {p : ℝ} (hp : 12 ≤ p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    (91/100 : ℝ) * lpNorm p x ≤ |x i| := by
  have hp0 : 0 < p := by linarith
  have hroot : (3 : ℝ)^(1/p) ≤ 100/91 := by
    calc
      _ ≤ (3 : ℝ)^(1/(12 : ℝ)) := Real.rpow_le_rpow_of_exponent_le
        (by norm_num) (one_div_le_one_div_of_le (by norm_num) hp)
      _ ≤ 100/91 := HlawkaSchatten.DiagonalCutoff16.upper_root_of_power
        (by norm_num : (0 : ℝ) < 12) (by norm_num) (by norm_num)
        (by norm_num [Real.rpow_natCast])
  have h := norm_le_three_root_max hp0 x i hi
  have h' := mul_le_mul_of_nonneg_right hroot (abs_nonneg (x i))
  linarith

theorem pair_main_conflict12 {p : ℝ} (hp : 12 ≤ p)
    (x y z : Fin 3 → ℝ) (i j : Fin 3) (s r : ℝ)
    (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (hS : lpNorm p x+lpNorm p y+lpNorm p z = 3)
    (hx : lpNorm p x ≤ lpNorm p (x+y+z))
    (hy : lpNorm p y ≤ lpNorm p (x+y+z))
    (hz : lpNorm p z ≤ lpNorm p (x+y+z))
    (hT : lpNorm p (x+y+z) ≤ 1647/1250)
    (hG : pairGapSum (lpNorm p) x y z ≤ 401/1000)
    (h1 : (91/100 : ℝ)*lpNorm p (x+y) ≤ s*(x i+y i))
    (h2 : (91/100 : ℝ)*lpNorm p (x+z) ≤ r*(x j+z j)) : i ≠ j := by
  intro hij
  subst j
  have hp1 : 1 ≤ p := by linarith
  have htail := pairGap_nonneg hp1 y z
  have hgap : (lpNorm p x+lpNorm p y-lpNorm p (x+y))+
      (lpNorm p x+lpNorm p z-lpNorm p (x+z)) ≤ 401/1000 := by
    dsimp only [pairGapSum, pairGap] at hG htail
    linarith
  apply weighted_signed_conflict (A := (1647/1250 : ℝ))
    (d := (91/100 : ℝ)) (G := (401/1000 : ℝ))
    (by norm_num) (by norm_num) hs hr
    (norm_apply_le_lpNorm hp1 x i) (norm_apply_le_lpNorm hp1 y i)
    (norm_apply_le_lpNorm hp1 z i)
    (show |x i+y i+z i| ≤ lpNorm p (x+y+z) from norm_apply_le_lpNorm hp1 (x+y+z) i)
    (by nlinarith [h1]) (by nlinarith [h2]) hgap hS
    (by linarith) (hx.trans hT) hT (by norm_num) (by norm_num)

theorem shared_pair_maxima_distinct {p : ℝ} (hp : 12 ≤ p)
    (x y z : Fin 3 → ℝ) (i j : Fin 3)
    (hS : lpNorm p x+lpNorm p y+lpNorm p z = 3)
    (hx : lpNorm p x ≤ lpNorm p (x+y+z))
    (hy : lpNorm p y ≤ lpNorm p (x+y+z))
    (hz : lpNorm p z ≤ lpNorm p (x+y+z))
    (hT : lpNorm p (x+y+z) ≤ 1647/1250)
    (hG : pairGapSum (lpNorm p) x y z ≤ 401/1000)
    (hi : ∀ k, |(x+y) k| ≤ |(x+y) i|)
    (hj : ∀ k, |(x+z) k| ≤ |(x+z) j|) : i ≠ j := by
  have sign_choice (a : ℝ) : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ s*a = |a| := by
    by_cases ha : 0 ≤ a
    · exact ⟨1,Or.inl rfl,by simp [abs_of_nonneg ha]⟩
    · exact ⟨-1,Or.inr rfl,by simp [abs_of_neg (lt_of_not_ge ha)]⟩
  obtain ⟨s,hs,hs'⟩ := sign_choice (x i+y i)
  obtain ⟨r,hr,hr'⟩ := sign_choice (x j+z j)
  apply pair_main_conflict12 hp x y z i j s r hs hr hS hx hy hz hT hG
  · rw [hs']
    exact relative_coordinate12 hp (x+y) i hi
  · rw [hr']
    exact relative_coordinate12 hp (x+z) j hj

end HlawkaSchatten.DiagonalCutoff12



theorem solution {p : ℝ} (hp : 12 ≤ p)
    (x y z : Fin 3 → ℝ) (i j : Fin 3)
    (hS : lpNorm p x+lpNorm p y+lpNorm p z = 3)
    (hx : lpNorm p x ≤ lpNorm p (x+y+z))
    (hy : lpNorm p y ≤ lpNorm p (x+y+z))
    (hz : lpNorm p z ≤ lpNorm p (x+y+z))
    (hT : lpNorm p (x+y+z) ≤ 1647/1250)
    (hG : pairGapSum (lpNorm p) x y z ≤ 401/1000)
    (hi : ∀ k, |(x+y) k| ≤ |(x+y) i|)
    (hj : ∀ k, |(x+z) k| ≤ |(x+z) j|) : i ≠ j := by
  exact HlawkaSchatten.DiagonalCutoff12.shared_pair_maxima_distinct hp x y z i j hS hx hy hz hT hG hi hj

#print axioms solution

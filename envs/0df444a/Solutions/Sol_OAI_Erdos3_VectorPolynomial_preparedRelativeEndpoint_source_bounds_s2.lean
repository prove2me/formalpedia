-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_source_bounds_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:45:52.538987+00:00
-- url     : https://prove2.me/submissions/ec656bde-1d72-48a7-af0b-5b65127f38f0

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B257

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastComparisonFloorPolynomialBudget
namespace OAI

section

namespace Erdos3

theorem forecastComparisonMeshPolynomial_nonneg {t grid : ℝ}
    (ht : 0 ≤ t) (hgrid : 0 ≤ grid) :
    0 ≤ forecastComparisonMeshPolynomial t grid := by
  unfold forecastComparisonMeshPolynomial
  positivity

theorem forecastJointGridMeshLog_le_comparisonPolynomial (d : ℕ)
    {t P E grid : ℝ} (ht : 0 ≤ t) (hd : (d : ℝ) ≤ 2 * t)
    (hP0 : 0 ≤ P) (hP : P ≤ grid) (hE0 : 0 ≤ E) (hE : E ≤ t) :
    forecastJointGridMeshLog d P (E + 4) ≤ forecastComparisonMeshPolynomial t grid := by
  have hmul : ((d : ℝ) + 1) * (P + (E + 4) + 5) ≤
      (2 * t + 1) * (grid + t + 9) :=
    mul_le_mul (by linarith only [hd]) (by linarith only [hP, hE])
      (by linarith only [hP0, hE0]) (by linarith only [ht])
  unfold forecastJointGridMeshLog forecastComparisonMeshPolynomial
  linarith only [hmul, hd, hP, hE]

theorem forecastJointGridAmbientLog_le_comparisonPolynomial (d : ℕ)
    {t P E V Pτ grid : ℝ} (ht : 0 ≤ t) (hd : (d : ℝ) ≤ 2 * t)
    (hP0 : 0 ≤ P) (hP : P ≤ grid) (hE0 : 0 ≤ E) (hE : E ≤ t)
    (hV : V ≤ 2 * t) (hPτ : Pτ ≤ t) :
    forecastJointGridAmbientLog d P (E + 4) V Pτ ≤
      4 * t + grid + forecastComparisonMeshPolynomial t grid + 12 := by
  have hmesh := forecastJointGridMeshLog_le_comparisonPolynomial d ht hd hP0 hP hE0 hE
  unfold forecastJointGridAmbientLog
  linarith only [hmesh, hP, hE, hV, hPτ]

theorem allocatedFixedPathSlicedAmbientFloorLog_le_comparisonPolynomial (d : ℕ)
    {t D P V cost E Pg PR source grid : ℝ}
    (ht : 0 ≤ t) (hd : (d : ℝ) ≤ 2 * t)
    (hD : D ≤ t) (hP : P ≤ source) (hV : V ≤ 2 * t)
    (hcost : cost ≤ t) (hE0 : 0 ≤ E) (hE : E ≤ t)
    (hPg0 : 0 ≤ Pg) (hPg : Pg ≤ grid) (hPR : PR ≤ t)
    (hsource : 0 ≤ source) (hgrid : 0 ≤ grid) :
    allocatedFixedPathSlicedAmbientFloorLog d D P V cost E Pg PR ≤
      forecastComparisonFloorPolynomial t source grid := by
  have hmesh := forecastJointGridMeshLog_le_comparisonPolynomial d ht hd hPg0 hPg hE0 hE
  have hfirst : D + 2 * P + V + cost + E + 32 ≤ 5 * t + 2 * source + 32 := by
    linarith only [hD, hP, hV, hcost, hE]
  have hsecond : forecastJointGridSamplerLog d Pg (E + 4) V PR + 1 ≤
      4 * t + grid + forecastComparisonMeshPolynomial t grid + 12 := by
    unfold forecastJointGridSamplerLog
    linarith only [hmesh, hPg, hE, hV, hPR]
  have hfirst0 : 0 ≤ 5 * t + 2 * source + 32 := by positivity
  have hsecond0 : 0 ≤ 4 * t + grid + forecastComparisonMeshPolynomial t grid + 12 := by
    have := forecastComparisonMeshPolynomial_nonneg ht hgrid
    positivity
  unfold allocatedFixedPathSlicedAmbientFloorLog forecastComparisonFloorPolynomial
  exact max_le (hfirst.trans (le_add_of_nonneg_right hsecond0))
    (hsecond.trans (le_add_of_nonneg_left hfirst0))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedComparisonGridPolynomialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedComparisonSourcePolynomial_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ preparedComparisonSourcePolynomial t := by
  unfold preparedComparisonSourcePolynomial
  positivity

theorem preparedComparisonGridPolynomial_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ preparedComparisonGridPolynomial m t := by
  unfold preparedComparisonGridPolynomial
  have hsource := preparedComparisonSourcePolynomial_nonneg ht
  positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSlicedForecastComparisonLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastCommonFloorExponent_mono
    {periodLog childLog cost comparisonLog periodLog' childLog' cost' comparisonLog' : ℝ}
    (hperiod : periodLog ≤ periodLog') (hchild : childLog ≤ childLog')
    (hcost : cost ≤ cost') (hcomparison : comparisonLog ≤ comparisonLog') :
    preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog ≤
      preparedSlicedForecastCommonFloorExponent periodLog' childLog' cost' comparisonLog' := by
  unfold preparedSlicedForecastCommonFloorExponent
  exact max_le_max le_rfl (max_le_max hperiod
    (max_le_max hchild (max_le_max (by linarith only [hcost]) hcomparison)))

theorem preparedSlicedForecastCommonFloor_mono
    {periodLog childLog cost comparisonLog periodLog' childLog' cost' comparisonLog' : ℝ}
    (hperiod : periodLog ≤ periodLog') (hchild : childLog ≤ childLog')
    (hcost : cost ≤ cost') (hcomparison : comparisonLog ≤ comparisonLog') :
    preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog ≤
      preparedSlicedForecastCommonFloor periodLog' childLog' cost' comparisonLog' := by
  unfold preparedSlicedForecastCommonFloor
  exact Nat.ceil_mono (Real.exp_le_exp.mpr
    (preparedSlicedForecastCommonFloorExponent_mono hperiod hchild hcost hcomparison))

theorem preparedSlicedForecastCommonFloor_mono_comparison
    (periodLog childLog cost : ℝ) {a b : ℝ} (hcomparison : a ≤ b) :
    preparedSlicedForecastCommonFloor periodLog childLog cost a ≤
      preparedSlicedForecastCommonFloor periodLog childLog cost b :=
  preparedSlicedForecastCommonFloor_mono le_rfl le_rfl le_rfl hcomparison

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteComparisonGridBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastSpatialBudget_nonneg (m M nX Jalloc : ℕ)
    (Pdim cost : ℝ) : 0 ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
  have hD := (allocatedComparisonDimension_bounds m
    (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M Jalloc))).1
  unfold preparedSlicedForecastSpatialBudget
  apply le_trans _ (le_max_left _ _)
  positivity

theorem preparedSlicedForecastSourceLog_nonneg (m M Jalloc : ℕ) (Ptest : ℝ) :
    0 ≤ preparedSlicedForecastSourceLog m M Jalloc Ptest := by
  have hcap : 0 ≤ preparedSlicedForecastPrimitiveCap :=
    zero_le_one.trans preparedSlicedForecastPrimitiveCap_one_le
  unfold preparedSlicedForecastSourceLog
  positivity

theorem preparedSlicedForecastGridLog_nonneg (m M nX Jalloc : ℕ)
    (Pdim cost gainLog Qstride Ptest : ℝ) :
    0 ≤ preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest :=
  (preparedSlicedForecastSourceLog_nonneg m M Jalloc Ptest).trans (le_max_left _ _)

theorem preparedSlicedForecastSourceLog_le_preparedComparisonSourcePolynomial
    (m M Jalloc : ℕ) {t Ptest : ℝ} (ht : 1 ≤ t)
    (hD : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t)
    (hpcap : preparedSlicedForecastPrimitiveCap ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t) :
    preparedSlicedForecastSourceLog m M Jalloc Ptest ≤
      preparedComparisonSourcePolynomial t := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hD0 := (allocatedComparisonDimension_bounds m
    (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M Jalloc))).1
  have hsq := mul_le_mul hD hD hD0 ht0
  unfold preparedSlicedForecastSourceLog preparedComparisonSourcePolynomial
  rw [max_eq_right hPtest0, pow_two]
  linarith

theorem preparedSlicedForecastGridLog_le_preparedComparisonGridPolynomial
    (m M nX Jalloc : ℕ) {t Pdim cost gainLog Qstride Ptest : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t) (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ t)
    (hD : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t)
    (hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ t)
    (hpcap : preparedSlicedForecastPrimitiveCap ≤ t)
    (hPbad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ t)
    (hcost0 : 0 ≤ cost) (hcostOne : cost + 1 ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t) :
    preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest ≤
      preparedComparisonGridPolynomial m t := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hX : (nX : ℝ) ≤ t :=
    (Nat.cast_le.mpr (Nat.le_add_right nX (m * M))).trans hDmod
  have hsource := preparedSlicedForecastSourceLog_le_preparedComparisonSourcePolynomial
    m M Jalloc ht hD hpcap hPtest0 hPtest
  have hsource0 := preparedComparisonSourcePolynomial_nonneg ht0
  have hmul : ((nX : ℝ) + 1) * (cost + 1) ≤ (t + 1) * (t + 1) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hP0 := preparedSlicedForecastSpatialBudget_nonneg m M nX Jalloc Pdim cost
  have hinner0 : 0 ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost +
      ((nX : ℝ) + 1) * (cost + 1) + 1 := by positivity
  have hinner : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost +
      ((nX : ℝ) + 1) * (cost + 1) + 1 ≤ t + (t + 1) * (t + 1) + 1 := by linarith
  have hsquare := pow_le_pow_left₀ hinner0 hinner 2
  have hcoef : 10 * (m : ℝ) + 30 ≤ 10 * t + 30 := by linarith
  have hsmooth : forecastOriginalSmoothBudget m
      (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost +
        ((nX : ℝ) + 1) * (cost + 1)) ≤
      (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 := by
    unfold forecastOriginalSmoothBudget
    exact mul_le_mul hcoef hsquare (sq_nonneg _) (by positivity)
  have hsmooth0 : 0 ≤ (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 := by
    positivity
  have hDmodTwo : ((nX + m * M + 2 : ℕ) : ℝ) ≤ t + 2 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using add_le_add hDmod (le_refl (2 : ℝ))
  have hprod : (preparedSlicedForecastBadLog m nX Qstride gainLog + (cost + 1)) *
      ((nX + m * M + 2 : ℕ) : ℝ) ≤ (2 * t) * (t + 2) :=
    mul_le_mul (by linarith) hDmodTwo (Nat.cast_nonneg _) (by positivity)
  have hmodular := mul_le_mul_of_nonneg_right hprod
    (Nat.cast_nonneg (modularRankChargeFactor m))
  have hmodular0 : 0 ≤ (2 * t) * (t + 2) * (modularRankChargeFactor m : ℝ) := by
    positivity
  unfold preparedSlicedForecastGridLog preparedComparisonGridPolynomial
  exact max_le (by linarith only [hsource, hsmooth0, hmodular0])
    (max_le (by linarith only [hsmooth, hsource0, hmodular0])
      (by linarith only [hmodular, hsource0, hsmooth0]))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedComparisonPrecisionLogBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem modularRankChargeFactor_le_preparedComparisonPower (m : ℕ) {t : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t) :
    (modularRankChargeFactor m : ℝ) ≤ (t + 10) ^ (2 * m + 3) := by
  have hbase : 1 ≤ t + 10 := by linarith
  have hbase0 : 0 ≤ t + 10 := by linarith
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm_base : (m : ℝ) ≤ t + 10 := by linarith
  have hfour : (4 : ℝ) ≤ t + 10 := by linarith
  have htwo : (2 : ℝ) ≤ t + 10 := by linarith
  have hfactorial : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by
    exact_mod_cast Nat.factorial_le_pow m
  have hfactorial_base : (m.factorial : ℝ) ≤ (t + 10) ^ m :=
    hfactorial.trans (pow_le_pow_left₀ hm0 hm_base m)
  have htwo_pow : (2 : ℝ) ^ m ≤ (t + 10) ^ m :=
    pow_le_pow_left₀ (by norm_num) htwo m
  calc
    (modularRankChargeFactor m : ℝ) =
        4 * (m : ℝ) * ((2 : ℝ) ^ m * (m.factorial : ℝ)) := by
      simp only [modularRankChargeFactor, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    _ ≤ (t + 10) * (t + 10) * ((t + 10) ^ m * (t + 10) ^ m) := by
      gcongr
    _ = (t + 10) ^ (2 * m + 2) := by
      rw [two_mul, pow_add, pow_add, pow_two]
      ring
    _ ≤ (t + 10) ^ (2 * m + 3) :=
      pow_le_pow_right₀ hbase (by omega)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedComparisonSourcePolynomial_le_square {t : ℝ} (ht : 1 ≤ t) :
    preparedComparisonSourcePolynomial t ≤ (t + 10) ^ 2 := by
  unfold preparedComparisonSourcePolynomial
  nlinarith

private theorem preparedComparisonSmoothPolynomial_le_six {t : ℝ} (ht : 1 ≤ t) :
    (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 ≤ (t + 10) ^ 6 := by
  have hcoef : 10 * t + 30 ≤ (t + 10) ^ 2 := by nlinarith [sq_nonneg t]
  have hinner : t + (t + 1) * (t + 1) + 1 ≤ (t + 10) ^ 2 := by nlinarith
  have hinner0 : 0 ≤ t + (t + 1) * (t + 1) + 1 := by positivity
  calc
    _ ≤ (t + 10) ^ 2 * ((t + 10) ^ 2) ^ 2 :=
      mul_le_mul hcoef (pow_le_pow_left₀ hinner0 hinner 2) (sq_nonneg _) (sq_nonneg _)
    _ = (t + 10) ^ 6 := by ring

theorem preparedComparisonGridPolynomial_le_power (m : ℕ) {t : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t) :
    preparedComparisonGridPolynomial m t ≤ (t + 10) ^ (2 * m + 7) := by
  let a := t + 10
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have ha3 : 3 ≤ a := by dsimp [a]; linarith
  have hsource : preparedComparisonSourcePolynomial t ≤ a ^ (2 * m + 6) :=
    (preparedComparisonSourcePolynomial_le_square ht).trans (pow_le_pow_right₀ ha (by omega))
  have hsmooth : (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 ≤
      a ^ (2 * m + 6) :=
    (preparedComparisonSmoothPolynomial_le_six ht).trans (pow_le_pow_right₀ ha (by omega))
  have hprefix : (2 * t) * (t + 2) ≤ a ^ 3 := by
    have hleft : 2 * t ≤ a ^ 2 := by dsimp [a]; nlinarith [sq_nonneg t]
    have hright : t + 2 ≤ a := by dsimp [a]; linarith
    calc
      _ ≤ a ^ 2 * a := mul_le_mul hleft hright (by positivity) (sq_nonneg _)
      _ = a ^ 3 := by ring
  have hfactor : (modularRankChargeFactor m : ℝ) ≤ a ^ (2 * m + 3) :=
    modularRankChargeFactor_le_preparedComparisonPower m ht hm
  have hmodular : (2 * t) * (t + 2) * (modularRankChargeFactor m : ℝ) ≤
      a ^ (2 * m + 6) := by
    calc
      _ ≤ a ^ 3 * a ^ (2 * m + 3) :=
        mul_le_mul hprefix hfactor (Nat.cast_nonneg _) (pow_nonneg ha0 _)
      _ = a ^ (2 * m + 6) := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ 3 * a ^ (2 * m + 6) := by
      unfold preparedComparisonGridPolynomial
      linarith only [hsource, hsmooth, hmodular]
    _ ≤ a * a ^ (2 * m + 6) := mul_le_mul_of_nonneg_right ha3 (pow_nonneg ha0 _)
    _ = a ^ (2 * m + 7) := by rw [← pow_succ']

private theorem forecastComparisonMeshPolynomial_le_power {t grid : ℝ} {e : ℕ}
    (ht : 1 ≤ t) (he : 2 ≤ e) (hgrid0 : 0 ≤ grid)
    (hgrid : grid ≤ (t + 10) ^ e) :
    forecastComparisonMeshPolynomial t grid ≤ (t + 10) ^ (e + 3) := by
  let a := t + 10
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have ha3 : 3 ≤ a := by dsimp [a]; linarith
  have haE : a ≤ a ^ e := by simpa only [pow_one] using pow_le_pow_right₀ ha (by omega : 1 ≤ e)
  have ha2E : a ^ 2 ≤ a ^ e := pow_le_pow_right₀ ha he
  have hcoef : 2 * t + 1 ≤ a ^ 2 := by dsimp [a]; nlinarith [sq_nonneg t]
  have hinside : grid + t + 9 ≤ 2 * a ^ e := by
    have : t + 9 ≤ a := by dsimp [a]; linarith
    linarith only [hgrid, this, haE]
  have hleading : (2 * t + 1) * (grid + t + 9) ≤ 2 * a ^ (e + 2) := by
    calc
      _ ≤ a ^ 2 * (2 * a ^ e) :=
        mul_le_mul hcoef hinside (by linarith) (sq_nonneg _)
      _ = 2 * a ^ (e + 2) := by rw [pow_add]; ring
  have hlow : 13 * t + 12 ≤ a ^ 2 := by dsimp [a]; nlinarith [sq_nonneg t]
  have hrest : 12 * t + 2 * grid + t + 12 ≤ 3 * a ^ e := by
    linarith only [hlow, hgrid, ha2E]
  have hrest' : 12 * t + 2 * grid + t + 12 ≤ a ^ (e + 1) := by
    calc
      _ ≤ 3 * a ^ e := hrest
      _ ≤ a * a ^ e := mul_le_mul_of_nonneg_right ha3 (pow_nonneg ha0 _)
      _ = a ^ (e + 1) := by rw [pow_succ']
  have hpow : a ^ (e + 1) ≤ a ^ (e + 2) := pow_le_pow_right₀ ha (by omega)
  calc
    _ ≤ 3 * a ^ (e + 2) := by
      unfold forecastComparisonMeshPolynomial
      linarith only [hleading, hrest', hpow]
    _ ≤ a * a ^ (e + 2) := mul_le_mul_of_nonneg_right ha3 (pow_nonneg ha0 _)
    _ = a ^ (e + 3) := by rw [← pow_succ']

theorem preparedComparisonFloorPolynomial_le_power (m : ℕ) {t : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t) :
    forecastComparisonFloorPolynomial t (preparedComparisonSourcePolynomial t)
      (preparedComparisonGridPolynomial m t) ≤ (t + 10) ^ (2 * m + 20) := by
  let a := t + 10
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have ha5 : 5 ≤ a := by dsimp [a]; linarith
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hsource : preparedComparisonSourcePolynomial t ≤ a ^ 2 :=
    preparedComparisonSourcePolynomial_le_square ht
  have hgrid : preparedComparisonGridPolynomial m t ≤ a ^ (2 * m + 7) :=
    preparedComparisonGridPolynomial_le_power m ht hm
  have hmesh : forecastComparisonMeshPolynomial t (preparedComparisonGridPolynomial m t) ≤
      a ^ (2 * m + 10) := by
    have h := forecastComparisonMeshPolynomial_le_power ht (by omega : 2 ≤ 2 * m + 7)
      (preparedComparisonGridPolynomial_nonneg m ht0) hgrid
    exact h
  have hlow : 9 * t + 44 ≤ a ^ 2 := by dsimp [a]; nlinarith [sq_nonneg t]
  have hpow2 : a ^ 2 ≤ a ^ (2 * m + 10) := pow_le_pow_right₀ ha (by omega)
  have hpowgrid : a ^ (2 * m + 7) ≤ a ^ (2 * m + 10) := pow_le_pow_right₀ ha (by omega)
  calc
    _ ≤ 5 * a ^ (2 * m + 10) := by
      unfold forecastComparisonFloorPolynomial
      linarith only [hsource, hgrid, hmesh, hlow, hpow2, hpowgrid]
    _ ≤ a * a ^ (2 * m + 10) := mul_le_mul_of_nonneg_right ha5 (pow_nonneg ha0 _)
    _ = a ^ (2 * m + 11) := by rw [← pow_succ']
    _ ≤ a ^ (2 * m + 20) := pow_le_pow_right₀ ha (by omega)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastComparisonFloorLog_le_power
    (m M nX Jalloc d : ℕ)
    {t Pdim cost pRadius gainLog Qstride Ptest Ecompare : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ t) (hd : (d : ℝ) ≤ 2 * t)
    (hD : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t)
    (hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ t)
    (hpcap : preparedSlicedForecastPrimitiveCap ≤ t)
    (hPbad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ t)
    (hcost0 : 0 ≤ cost) (hcostOne : cost + 1 ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t)
    (hE0 : 0 ≤ Ecompare) (hE : Ecompare ≤ t) (hRadius : pRadius ≤ t) :
    preparedSlicedForecastComparisonFloorLog m M nX Jalloc d
      Pdim cost pRadius gainLog Qstride Ptest (2 * Ptest) Ecompare ≤
      (t + 10) ^ (2 * m + 20) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hsource := preparedSlicedForecastSourceLog_le_preparedComparisonSourcePolynomial
    m M Jalloc ht hD hpcap hPtest0 hPtest
  have hgrid := preparedSlicedForecastGridLog_le_preparedComparisonGridPolynomial
    m M nX Jalloc ht hm hDmod hD hP hpcap hPbad hcost0 hcostOne hPtest0 hPtest
  have hgrid0 := preparedSlicedForecastGridLog_nonneg m M nX Jalloc
    Pdim cost gainLog Qstride Ptest
  have hV : 2 * Ptest ≤ 2 * t := mul_le_mul_of_nonneg_left hPtest (by norm_num)
  have hcost : cost ≤ t := by linarith only [hcostOne]
  have hfloor := allocatedFixedPathSlicedAmbientFloorLog_le_comparisonPolynomial
    d ht0 hd hD hsource hV hcost hE0 hE hgrid0 hgrid hRadius
    (preparedComparisonSourcePolynomial_nonneg ht0)
    (preparedComparisonGridPolynomial_nonneg m ht0)
  exact hfloor.trans (preparedComparisonFloorPolynomial_le_power m ht hm)

theorem preparedSlicedForecastJointGridAmbientLog_le_power
    (m M nX Jalloc d : ℕ)
    {t Pdim cost gainLog Qstride Ptest Ecompare : ℝ}
    (ht : 1 ≤ t) (hm : (m : ℝ) ≤ t)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ t) (hd : (d : ℝ) ≤ 2 * t)
    (hD : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ t)
    (hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ t)
    (hpcap : preparedSlicedForecastPrimitiveCap ≤ t)
    (hPbad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ t)
    (hcost0 : 0 ≤ cost) (hcostOne : cost + 1 ≤ t)
    (hPtest0 : 0 ≤ Ptest) (hPtest : Ptest ≤ t)
    (hE0 : 0 ≤ Ecompare) (hE : Ecompare ≤ t)
    (hTau : gainLog + (nX : ℝ) + 8 ≤ t) :
    forecastJointGridAmbientLog d
      (preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest)
      (Ecompare + 4) (2 * Ptest) (gainLog + (nX : ℝ) + 8) ≤
      (t + 10) ^ (2 * m + 20) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hgrid := preparedSlicedForecastGridLog_le_preparedComparisonGridPolynomial
    m M nX Jalloc ht hm hDmod hD hP hpcap hPbad hcost0 hcostOne hPtest0 hPtest
  have hgrid0 := preparedSlicedForecastGridLog_nonneg m M nX Jalloc
    Pdim cost gainLog Qstride Ptest
  have hV : 2 * Ptest ≤ 2 * t := mul_le_mul_of_nonneg_left hPtest (by norm_num)
  have hN := forecastJointGridAmbientLog_le_comparisonPolynomial d ht0 hd
    hgrid0 hgrid hE0 hE hV hTau
  have hsource0 := preparedComparisonSourcePolynomial_nonneg ht0
  have hfirst : 0 ≤ 5 * t + 2 * preparedComparisonSourcePolynomial t + 32 := by positivity
  exact (hN.trans (le_add_of_nonneg_left hfirst)).trans
    (preparedComparisonFloorPolynomial_le_power m ht hm)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointSourceBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedRelativeEndpointSigmaLog_eq (m M Jalloc : ℕ)
    (Ptest Ecompare cost : ℝ) :
    preparedRelativeEndpointSigmaLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare cost m =
    fixedPathSlicedPerturbationLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) +
        preparedSlicedForecastSourceLog m M Jalloc Ptest + 4) (cost + 1)
      (2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + (Ecompare + 4) + 14) m := by
  unfold preparedRelativeEndpointSigmaLog preparedRelativeEndpointCoarseLog
  change fixedPathSlicedPerturbationLog _ _ _
    (2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + Ecompare + 18) _ = _
  congr 1
  ring

theorem preparedComparisonContinuousDimension_le_two
    {X J : Type} {m M nX : ℕ} (prep : RankPreparationFamily X J m)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    {T : ℝ} (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ T) :
    (((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j) : ℕ) : ℝ) ≤ 2 * T := by
  have hI : Fintype.card (Σ j, PreparedSamplerContinuous prep j) ≤ m * M := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => by
        simpa only [PreparedSamplerContinuous, Fintype.card_fin] using
          ((prep j).rank_le_coord_card.trans (hCoord j)))
      _ = _ := by simp
  have hIdim : Fintype.card (Σ j, PreparedSamplerContinuous prep j) ≤ nX + m * M := by omega
  have hIT : (Fintype.card (Σ j, PreparedSamplerContinuous prep j) : ℝ) ≤ T :=
    (Nat.cast_le.mpr hIdim).trans hDmod
  rw [Nat.cast_add]
  linarith only [hDmod, hIT]

theorem preparedRelativeEndpoint_source_bounds_s2_oai
    {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m)
    (M nX Jalloc : ℕ) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (σ : Fin m → ℝ) (ξ : ℝ) (S : ℕ) (N : Fin nX → ℕ)
    {T K seed childLog Pdim cost pRadius gainLog Qstride Ptest Ecompare : ℝ}
    (hK : 0 ≤ K) (hT : 1 ≤ T) (hm : (m : ℝ) ≤ T)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ T)
    (hD : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ T)
    (hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ T)
    (hpcap : preparedSlicedForecastPrimitiveCap ≤ T)
    (hPbad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ T)
    (hcost : 0 ≤ cost) (hcostOne : cost + 1 ≤ T)
    (hTest : Ptest ∈ Set.Icc 0 T) (hCompare : Ecompare ∈ Set.Icc 0 T)
    (hRadius : pRadius ≤ T) (hTau : gainLog + (nX : ℝ) + 8 ≤ T)
    (hSigmaLog : preparedRelativeEndpointSigmaLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare cost m ≤ K)
    (hCoarseLog : preparedRelativeEndpointCoarseLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare ≤ K)
    (hFloorLog : (T + 10) ^ (2 * m + 20) ≤ K)
    (hσzero : ∀ j, 0 ≤ σ j) (hσK : ∀ j, σ j ≤ Real.exp (-K))
    (hξK : ξ ≤ Real.exp (-K))
    (hS : preparedRelativeEndpointMinimumScale seed 0 childLog cost
      ((T + 10) ^ (2 * m + 20)) ≤ S)
    (hN : ∀ i, Real.exp K ≤ (N i : ℝ)) :
    (∀ j, σ j ≤ 1) ∧ ξ ≤ 1 ∧
    (∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) +
        preparedSlicedForecastSourceLog m M Jalloc Ptest + 4) (cost + 1)
      (2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + (Ecompare + 4) + 14) m)) ∧
    ξ ≤ Real.exp (-(2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + (Ecompare + 4) + 14)) ∧
    preparedSlicedForecastCommonFloor 0 childLog cost
      (preparedSlicedForecastComparisonFloorLog m M nX Jalloc
        ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
        Pdim cost pRadius gainLog Qstride Ptest (2 * Ptest) Ecompare) ≤ S ∧
    (∀ i, Real.exp (forecastJointGridAmbientLog
      ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
      (preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest)
      (Ecompare + 4) (2 * Ptest) (gainLog + (nX : ℝ) + 8)) ≤ (N i : ℝ)) := by
  have hOne : Real.exp (-K) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hK)
  have hd := preparedComparisonContinuousDimension_le_two prep hCoord hDmod
  have hfloor := preparedSlicedForecastComparisonFloorLog_le_power m M nX Jalloc
    ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
    hT hm hDmod hd hD hP hpcap hPbad hcost hcostOne hTest.1 hTest.2
    hCompare.1 hCompare.2 hRadius
  have hgrid := preparedSlicedForecastJointGridAmbientLog_le_power m M nX Jalloc
    ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
    hT hm hDmod hd hD hP hpcap hPbad hcost hcostOne hTest.1 hTest.2
    hCompare.1 hCompare.2 hTau
  refine ⟨fun j => (hσK j).trans hOne, hξK.trans hOne, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [abs_of_nonneg (hσzero j)]
    apply (hσK j).trans
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    rwa [← preparedRelativeEndpointSigmaLog_eq]
  · apply hξK.trans
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    change 2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + Ecompare + 18 ≤ K at hCoarseLog
    linarith only [hCoarseLog]
  · exact (preparedSlicedForecastCommonFloor_mono_comparison 0 childLog cost hfloor).trans
      ((le_max_right _ _).trans hS)
  · intro i
    exact (Real.exp_le_exp.mpr (hgrid.trans hFloorLog)).trans (hN i)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_source_bounds_s2_oai := @OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_source_bounds_s2_oai

-- Prove2me | solution 1 for OAI.ShortEgyptian.divisor_moment_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:25:57.744891+00:00
-- url     : https://prove2.me/submissions/49a5dc8a-12f6-4cff-b94d-226a79d289c8

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/MomentAsymptotics.lean:L63-L245
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.divisor_moment_numeric. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Theorems.Thm_OAI_ShortEgyptian_divisor_moment_finite
import Theorems.Thm_OAI_ShortEgyptian_moment_band_nonpos

-- ---- from OAI.NumberTheory.ShortEgyptian.DivisorWeights ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem momentSeriesConst_nonneg (r : ℕ) : 0 ≤ momentSeriesConst r := by
  exact tsum_nonneg (fun _ => by positivity)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.SmoothBounds ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem smallSmoothConst_nonneg : 0 ≤ smallSmoothConst := by
  exact tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.MomentDecay ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem primeRecipBound_mono {T U : ℝ} (hT : 1 ≤ T) (hTU : T ≤ U) :
    primeRecipBound T ≤ primeRecipBound U := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hl := Real.log_le_log (by linarith : 0 < T) hTU
  have harg : 0 < 1+Real.log T/Real.log 2 := by positivity
  have hl' := Real.log_le_log harg (show 1+Real.log T/Real.log 2 ≤ 1+Real.log U/Real.log 2 by gcongr)
  unfold primeRecipBound
  linarith

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.MomentAsymptotics ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

open Filter Topology Asymptotics

theorem log_linear_bound (S E : ℝ) (hS : 1 ≤ S) (hE : 0 ≤ E) :
    Real.log (1+E*S/Real.log 2) ≤ Real.log S+Real.log (1+E/Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : 0 < 1+E*S/Real.log 2 := by positivity
  calc
    _ ≤ Real.log (S*(1+E/Real.log 2)) := Real.log_le_log harg (by
      have heq : S*(1+E/Real.log 2) = S+E*S/Real.log 2 := by ring
      rw [heq]
      linarith only [hS])
    _ = _ := Real.log_mul (by linarith) (by positivity)

theorem prime_exp_bound (S E : ℝ) (hS : 1 ≤ S) (hE : 0 ≤ E)
    (hl : 1 ≤ Real.log S) (hElog : Real.log (1+E/Real.log 2) ≤ Real.log S) :
    primeRecipBound (Real.exp (E*S)) ≤ 16*Real.log S := by
  unfold primeRecipBound
  rw [Real.log_exp]
  have hh := log_linear_bound S E hS hE
  linarith

theorem divisor_moment_numeric (r : ℕ) (D S v Y : ℝ) (N : ℕ)
    (hD : 1 ≤ D) (hS : 1 < S) (hl : 1 ≤ Real.log S) (hDS : D ≤ S)
    (hElog : Real.log (1+(D+1)/Real.log 2) ≤ Real.log S)
    (h2log : Real.log (1+2/Real.log 2) ≤ Real.log S)
    (h40 : 40*(1+Real.log S) ≤ S^(1/16:ℝ))
    (hpoint : 1600*(r:ℝ)*(1+Real.log S)^2 ≤ S^(1/2:ℝ))
    (hsmall : 400*(momentSeriesConst 0*smallSmoothConst)*(1+Real.log S) ≤ S^(1/2:ℝ))
    (hband : 51200*momentSeriesConst r ≤ S^(1/20:ℝ))
    (hB : 3200*(r:ℝ)*(1+Real.log (2*(D+1)*Real.log S)) ≤ Real.log S)
    (hB1 : 1+Real.log (2*(D+1)*Real.log S) ≤ Real.log S)
    (hbig : 8*(r:ℝ)*D*(1+Real.log S) ≤ S^(1/8:ℝ))
    (hpr : 128*momentSeriesConst r*(1+Real.log S) ≤ S^(1/4:ℝ))
    (hout : 4*(1+Real.log S) ≤ S^(1/4:ℝ))
    (hvlo : S/(2*Real.log S) ≤ v) (hvup : v ≤ D*S)
    (hYlo : Real.exp (v/2) ≤ Y) (hYup : Y ≤ Real.exp v) (hN : (N:ℝ) ≤ Real.exp (D*S)) :
    ∑ n ∈ Ioc N (N+⌊Y⌋₊), (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤ Y*Real.exp (S^(1/4:ℝ)) := by
  have hS0 : 0 < S := by linarith
  have hl0 : 0 < Real.log S := by linarith
  have hv : 0 < v := lt_of_lt_of_le (div_pos hS0 (by positivity)) hvlo
  have hvcoef : S ≤ 2*Real.log S*v := by simpa [mul_comm] using (div_le_iff₀ (show 0 < 2*Real.log S by positivity)).mp hvlo
  let W := (D+1)*S
  let B := 1+Real.log (W/v)
  let L := S^(7/8:ℝ)
  let z := Real.exp (Real.log S/2)
  let T := Real.exp (4*Real.log S)
  have hW0 : 0 < W := by dsimp [W]; positivity
  have hvW : v < W := by dsimp [W]; nlinarith only [hvup,hS0]
  have hBlog : B ≤ 1+Real.log (2*(D+1)*Real.log S) := by
    have hfrac : W/v ≤ 2*(D+1)*Real.log S := by
      apply (div_le_iff₀ hv).mpr
      dsimp [W]
      nlinarith only [hvcoef,hD]
    have hh := Real.log_le_log (div_pos hW0 hv) hfrac
    dsimp [B]
    linarith
  have hBbound : (r:ℝ)*B ≤ Real.log S/3200 := by
    have hh := mul_le_mul_of_nonneg_left hBlog (Nat.cast_nonneg r)
    nlinarith only [hh,hB]
  have hBle : B ≤ Real.log S := hBlog.trans hB1
  have hBpos : 0 ≤ B := by
    have hh := Real.log_nonneg ((le_div_iff₀ hv).mpr (by simpa using hvW.le))
    dsimp [B]; linarith
  have hL0 : 0 < L := Real.rpow_pos_of_pos hS0 _
  have hLle : L ≤ S := by simpa [L] using Real.rpow_le_rpow_of_exponent_le hS.le (by norm_num : (7/8:ℝ) ≤ 1)
  have hpowhalf : S^(1/2:ℝ)*S^(1/2:ℝ) = S := by rw [← Real.rpow_add hS0]; norm_num
  have hpowL : L*S^(1/8:ℝ) = S := by dsimp [L]; rw [← Real.rpow_add hS0]; norm_num
  have hpower8 : S^(1/16:ℝ) ≤ S^(1/8:ℝ) := Real.rpow_le_rpow_of_exponent_le hS.le (by norm_num)
  have h408 : 40*(Real.log S) ≤ S^(1/8:ℝ) := by linarith
  have hLv : L ≤ v/20 := by
    have hh := mul_le_mul_of_nonneg_left h408 hL0.le
    rw [hpowL] at hh
    nlinarith only [hh,hvcoef,hl0]
  have hS16 : S^(1/16:ℝ) ≤ S := by simpa using Real.rpow_le_rpow_of_exponent_le hS.le (by norm_num : (1/16:ℝ) ≤ 1)
  have hv8 : 8 ≤ v := by nlinarith only [h40,hS16,hvcoef,hl0]
  have hY4 : 4 ≤ Y := by
    have hh := Real.add_one_le_exp (v/2)
    linarith
  have hY0 : 0 < Y := by linarith
  have hYv : v/2 ≤ Real.log Y := by
    have hh := Real.log_le_log (Real.exp_pos _) hYlo
    simpa only [Real.log_exp] using hh
  have hz : 1 < z := Real.one_lt_exp_iff.mpr (by positivity)
  have hzlog : Real.log z = Real.log S/2 := Real.log_exp _
  have hzeq : z = S^(1/2:ℝ) := by rw [Real.rpow_def_of_pos hS0]; dsimp[z]; congr 1; ring
  have hTeq : T^(1/8:ℝ) = S^(1/2:ℝ) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,Real.rpow_def_of_pos hS0]; congr 1; ring
  have hpLog : Real.log (1+W/Real.log 2) ≤ 2*Real.log S := by
    have hh := log_linear_bound S (D+1) hS.le (by linarith)
    dsimp [W]; linarith
  have hPfirst : (r:ℝ)*z*Real.log (1+W/Real.log 2) ≤ v/400 := by
    have hh : 1600*(r:ℝ)*(Real.log S)^2 ≤ S^(1/2:ℝ) := by nlinarith only [hpoint,(show (0:ℝ) ≤ r from Nat.cast_nonneg r),hl]
    have hmul := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hS0.le (1/2))
    rw [hpowhalf] at hmul
    have hm : (r:ℝ)*z*Real.log (1+W/Real.log 2) ≤ 2*(r:ℝ)*z*Real.log S := by
      have hh := mul_le_mul_of_nonneg_left hpLog (by positivity : 0 ≤ (r:ℝ)*z)
      linarith
    rw [hzeq] at hm ⊢
    nlinarith only [hm,hmul,hvcoef,hl0]
  have hPsecond : (r:ℝ)*momentB v W/Real.log z ≤ v/1600 := by
    rw [hzlog]
    apply (div_le_iff₀ (by positivity : 0 < Real.log S/2)).mpr
    have hh := mul_le_mul_of_nonneg_right hBbound hv.le
    change (r:ℝ)*(B*v) ≤ _
    nlinarith only [hh]
  have hP : momentPoint r v W z ≤ v/200 := by
    unfold momentPoint
    have heq : (r:ℝ)*(z*Real.log (1+W/Real.log 2)+momentB v W/Real.log z) =
      (r:ℝ)*z*Real.log (1+W/Real.log 2)+(r:ℝ)*momentB v W/Real.log z := by ring
    rw [heq]; linarith
  have hSmall : momentSeriesConst 0*(T^(1/8:ℝ)*smallSmoothConst) ≤ v/200 := by
    rw [hTeq]
    have hc0 := mul_nonneg (momentSeriesConst_nonneg 0) smallSmoothConst_nonneg
    have hh : 400*(momentSeriesConst 0*smallSmoothConst)*Real.log S ≤ S^(1/2:ℝ) := by nlinarith only [hsmall,hc0]
    have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hS0.le (1/2))
    rw [hpowhalf] at hm
    nlinarith only [hm,hvcoef,hl0]
  have hnW : ∀ n ∈ Ioc N (N+⌊Y⌋₊), Real.log n ≤ W := by
    intro n hn
    have hn0 : 0 < n := by have hh := (mem_Ioc.mp hn).1; omega
    have hnl : (n:ℝ) ≤ (N:ℝ)+Y := by
      have hh : (n:ℝ) ≤ (N:ℝ)+(⌊Y⌋₊:ℝ) := by exact_mod_cast (mem_Ioc.mp hn).2
      linarith [Nat.floor_le hY0.le]
    have hne : (n:ℝ) ≤ 2*Real.exp (D*S) := by
      have hh := Real.exp_le_exp.mpr hvup
      linarith
    have hh := Real.log_le_log (by exact_mod_cast hn0 : (0:ℝ)<n) hne
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hh
    have hlog2 : Real.log 2 ≤ S := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)).trans (by linarith)
    dsimp [W]; linarith
  have hbands : ∀ t : ℝ, 1 ≤ t → Real.log T/2 ≤ t → t ≤ L →
      0 ≤ Real.log (v/t)/(10*t) ∧ Real.log (v/t)/(10*t) ≤ 1/2 ∧ momentBandExp r v W t ≤ 0 := by
    intro t ht htlo htup
    have ht0 : 0 < t := by linarith
    have htlo' : 2*Real.log S ≤ t := by dsimp [T] at htlo; rw [Real.log_exp] at htlo; linarith
    have hQlo : S^(1/16:ℝ) ≤ v/t := by
      apply (le_div_iff₀ ht0).mpr
      have hh1 : 2*Real.log S ≤ S^(1/16:ℝ) := by linarith
      have hh2 := mul_le_mul_of_nonneg_left hh1 (Real.rpow_nonneg hS0.le (1/16))
      have heq : S^(1/16:ℝ)*S^(1/16:ℝ) = S^(1/8:ℝ) := by rw [← Real.rpow_add hS0]; norm_num
      rw [heq] at hh2
      have hh3 := mul_le_mul_of_nonneg_left hh2 hL0.le
      rw [hpowL] at hh3
      have hh4 := mul_le_mul_of_nonneg_left htup (Real.rpow_nonneg hS0.le (1/16))
      nlinarith only [hh3,hh4,hvcoef,hl0]
    have hQup : v/t ≤ S^2 := by
      apply (div_le_iff₀ ht0).mpr
      nlinarith only [hvup,hDS,hS0,ht]
    have hC : momentSeriesConst r*primeRecipBound (Real.exp (2*S)) ≤ S^(1/20:ℝ)*Real.log S/3200 := by
      have hh := mul_le_mul_of_nonneg_left (prime_exp_bound S 2 hS.le (by norm_num) hl h2log) (momentSeriesConst_nonneg r)
      have hh' := mul_le_mul_of_nonneg_right hband hl0.le
      linarith
    exact moment_band_nonpos r S v W t hS ht0 hv htlo' (htup.trans hLle) hBbound hQlo hQup hC
  have hfin := divisor_moment_finite r N Y v W z T L hY4 hv hvW hz hYv hL0 hLv
    (by dsimp [T]; rw [Real.log_exp]; linarith) (Real.exp_pos _) hnW (by linarith) hbands
  have hR : 1 ≤ Real.sqrt Y := Real.one_le_sqrt.mpr (by linarith)
  have hRle : Real.sqrt Y ≤ Real.exp (D*S) := by
    have hh : Real.sqrt Y ≤ Y := by nlinarith only [Real.sq_sqrt hY0.le,Real.sqrt_nonneg Y,hY4]
    exact hh.trans (hYup.trans (Real.exp_le_exp.mpr hvup))
  have hED : Real.log (1+D/Real.log 2) ≤ Real.log S := by
    apply le_trans _ hElog
    apply Real.log_le_log (by positivity : 0 < 1+D/Real.log 2)
    gcongr; norm_num
  have hPrime : primeRecipBound (Real.sqrt Y) ≤ 16*Real.log S :=
    (primeRecipBound_mono hR hRle).trans (prime_exp_bound S D hS.le (by linarith) hl hED)
  have hFirst : (r:ℝ)*momentB v W/L ≤ S^(1/4:ℝ)/8 := by
    have h8 : 0 < S^(1/8:ℝ) := Real.rpow_pos_of_pos hS0 _
    have hd : (r:ℝ)*B*v ≤ (r:ℝ)*Real.log S*(D*S) := by gcongr
    have heq : (r:ℝ)*Real.log S*(D*S)/L = (r:ℝ)*D*Real.log S*S^(1/8:ℝ) := by
      apply (div_eq_iff hL0.ne').mpr
      calc _ = (r:ℝ)*D*Real.log S*(L*S^(1/8:ℝ)) := by rw [hpowL]; ring
           _ = _ := by ring
    have hm := mul_le_mul_of_nonneg_right hbig h8.le
    have heq2 : S^(1/8:ℝ)*S^(1/8:ℝ) = S^(1/4:ℝ) := by rw [← Real.rpow_add hS0]; norm_num
    rw [heq2] at hm
    have hx : (r:ℝ)*momentB v W/L ≤ (r:ℝ)*D*Real.log S*S^(1/8:ℝ) := by
      simpa only [momentB,B,mul_assoc] using (div_le_div_of_nonneg_right hd hL0.le).trans_eq heq
    have hdrop : 8*(r:ℝ)*D*Real.log S*S^(1/8:ℝ) ≤ 8*(r:ℝ)*D*(1+Real.log S)*S^(1/8:ℝ) := by gcongr; linarith
    linarith only [hx,hm,hdrop]
  have hSecond : momentSeriesConst r*primeRecipBound (Real.sqrt Y) ≤ S^(1/4:ℝ)/8 := by
    have hh := mul_le_mul_of_nonneg_left hPrime (momentSeriesConst_nonneg r)
    nlinarith only [hh,hpr,momentSeriesConst_nonneg r]
  have hExp : Real.exp ((r:ℝ)*momentB v W/L+momentSeriesConst r*primeRecipBound (Real.sqrt Y)) ≤ Real.exp (S^(1/4:ℝ)/2) := by
    apply Real.exp_le_exp.mpr
    have hh := Real.rpow_nonneg hS0.le (1/4)
    linarith
  have hSL : (⌊L⌋₊:ℝ)+1 ≤ Real.exp (S^(1/4:ℝ)/2) := by
    apply le_trans (show (⌊L⌋₊:ℝ)+1 ≤ S+1 by linarith [Nat.floor_le hL0.le])
    rw [← Real.exp_log (by linarith : 0 < S+1)]
    apply Real.exp_le_exp.mpr
    have hh := Real.log_le_log (by linarith : 0 < S+1) (show S+1 ≤ 2*S by linarith)
    rw [Real.log_mul (by norm_num) hS0.ne'] at hh
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have h4 : (4:ℝ) ≤ Real.exp (S^(1/4:ℝ)/2) := by
    have hh := Real.add_one_le_exp (S^(1/4:ℝ)/2)
    linarith
  calc
    _ ≤ _ := hfin
    _ ≤ 4*Y*Real.exp (S^(1/4:ℝ)/2) := by nlinarith only [hExp,hSL,hY0]
    _ ≤ Y*(Real.exp (S^(1/4:ℝ)/2)*Real.exp (S^(1/4:ℝ)/2)) := by
      have hh := mul_le_mul_of_nonneg_right h4 (show 0 ≤ Y*Real.exp (S^(1/4:ℝ)/2) by positivity)
      nlinarith only [hh]
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
open Filter Topology Asymptotics


theorem solution : type_of% @_root_.OAI.ShortEgyptian.divisor_moment_numeric := @_root_.OAI.ShortEgyptian.divisor_moment_numeric

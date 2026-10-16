-- Prove2me | solution 1 for OAI.ShortEgyptian.moment_band_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:22:19.401229+00:00
-- url     : https://prove2.me/submissions/374d088b-e24e-47d5-a0ca-daa4adfea198

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/MomentDecay.lean:L20-L84
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.moment_band_nonpos. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.DivisorWeights ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem momentSeriesConst_nonneg (r : ℕ) : 0 ≤ momentSeriesConst r := by
  exact tsum_nonneg (fun _ => by positivity)

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

theorem moment_band_nonpos (r : ℕ) (S v W t : ℝ)
    (hS : 1 < S) (ht : 0 < t) (hv : 0 < v) (htlo : 2*Real.log S ≤ t)
    (htup : t ≤ S) (hB : (r:ℝ)*(1+Real.log (W/v)) ≤ Real.log S/3200)
    (hQlo : S^(1/16:ℝ) ≤ v/t) (hQup : v/t ≤ S^2)
    (hC : momentSeriesConst r*primeRecipBound (Real.exp (2*S)) ≤ S^(1/20:ℝ)*Real.log S/3200) :
    0 ≤ Real.log (v/t)/(10*t) ∧ Real.log (v/t)/(10*t) ≤ 1/2 ∧ momentBandExp r v W t ≤ 0 := by
  have hS0 : 0 < S := by linarith
  have hlS : 0 < Real.log S := Real.log_pos hS
  let Q := v/t
  have hQ : 0 < Q := div_pos hv ht
  have hlQlo : Real.log S/16 ≤ Real.log Q := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hS0 _) hQlo
    rw [Real.log_rpow hS0] at hh
    dsimp [Q]
    linarith
  have hlQup : Real.log Q ≤ 2*Real.log S := by
    have hh := Real.log_le_log hQ hQup
    rw [Real.log_pow] at hh
    exact hh
  have hlQ : 0 < Real.log Q := by linarith
  have hlam0 : 0 ≤ Real.log Q/(10*t) := div_nonneg hlQ.le (by positivity)
  have hlam1 : Real.log Q/(10*t) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 10*t)).mpr
    linarith
  refine ⟨hlam0,hlam1,?_⟩
  have hE : Real.exp (2*t)^(Real.log Q/(10*t)) = Q^(1/5:ℝ) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,Real.rpow_def_of_pos hQ]
    congr 1
    field_simp
    ring
  have hpow : S^(1/20:ℝ) ≤ Q^(4/5:ℝ) := by
    calc
      _ = (S^(1/16:ℝ))^(4/5:ℝ) := by rw [← Real.rpow_mul hS0.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hS0.le _) hQlo (by norm_num)
  have hlog : Real.log S/3200 ≤ Real.log Q/200 := by linarith
  have hH := primeRecipBound_mono (Real.one_le_exp (by positivity : 0 ≤ 2*t))
    (Real.exp_le_exp.mpr (show 2*t ≤ 2*S by linarith))
  have hcoeff : momentSeriesConst r*primeRecipBound (Real.exp (2*t)) ≤ Q^(4/5:ℝ)*Real.log Q/200 := by
    calc
      _ ≤ momentSeriesConst r*primeRecipBound (Real.exp (2*S)) :=
        mul_le_mul_of_nonneg_left hH (momentSeriesConst_nonneg r)
      _ ≤ _ := hC
      _ = S^(1/20:ℝ)*(Real.log S/3200) := by ring
      _ ≤ Q^(4/5:ℝ)*(Real.log Q/200) := mul_le_mul hpow hlog (by positivity) (Real.rpow_nonneg hQ.le _)
      _ = _ := by ring
  have hpowmul : Q^(1/5:ℝ)*Q^(4/5:ℝ) = Q := by rw [← Real.rpow_add hQ]; norm_num
  have hpos : momentSeriesConst r*(Q^(1/5:ℝ)*primeRecipBound (Real.exp (2*t))) ≤ Q*Real.log Q/200 := by
    have hh := mul_le_mul_of_nonneg_left hcoeff (Real.rpow_nonneg hQ.le (1/5))
    calc
      _ = Q^(1/5:ℝ)*(momentSeriesConst r*primeRecipBound (Real.exp (2*t))) := by ring
      _ ≤ _ := hh
      _ = Q^(1/5:ℝ)*Q^(4/5:ℝ)*Real.log Q/200 := by ring
      _ = _ := by rw [hpowmul]
  have hfirst : (r:ℝ)*momentB v W/t ≤ Q*Real.log Q/200 := by
    calc
      _ = Q*((r:ℝ)*(1+Real.log (W/v))) := by unfold momentB Q; ring
      _ ≤ Q*(Real.log S/3200) := mul_le_mul_of_nonneg_left hB hQ.le
      _ ≤ Q*(Real.log Q/200) := mul_le_mul_of_nonneg_left hlog hQ.le
      _ = _ := by ring
  have hneg : (Real.log Q/(10*t))*v/5 = Q*Real.log Q/50 := by dsimp [Q]; ring
  unfold momentBandExp
  change (r:ℝ)*momentB v W/t - (Real.log Q/(10*t))*v/5 +
    momentSeriesConst r*(Real.exp (2*t)^(Real.log Q/(10*t))*primeRecipBound (Real.exp (2*t))) ≤ 0
  rw [hE,hneg]
  nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.moment_band_nonpos := @_root_.OAI.ShortEgyptian.moment_band_nonpos

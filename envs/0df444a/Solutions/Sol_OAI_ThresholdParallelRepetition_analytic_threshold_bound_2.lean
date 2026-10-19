-- Prove2me | solution 2 for OAI.ThresholdParallelRepetition.analytic_threshold_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:56:44.103415+00:00
-- url     : https://prove2.me/submissions/3ac01c16-5695-4b85-917f-fa8e57070ab4

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/ExponentialBounds.lean:L44-L99
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.analytic_threshold_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain
import Definitions.Def_OAI_Probability_EntangledGames_BlockStates
import Definitions.Def_OAI_Probability_EntangledGames_FreshStates
import Definitions.Def_OAI_Probability_EntangledGames_ExposureData
import Definitions.Def_OAI_Probability_EntangledGames_Refinement
import Definitions.Def_OAI_Probability_EntangledGames_ExposureErrors
import Definitions.Def_OAI_Probability_EntangledGames_Rounding
import Definitions.Def_OAI_Probability_EntangledGames_RepeatedModel
import Definitions.Def_OAI_Probability_EntangledGames_TestMoments
import Definitions.Def_OAI_Probability_EntangledGames_TestExtraction

-- ---- from OAI.Probability.EntangledGames.ExponentialBounds ----
namespace OAI

noncomputable section
namespace ThresholdParallelRepetition

lemma power_ratio_bound {v δ : ℝ} (hv : 0 ≤ v) (hδ : 0 < δ) (hs : v+δ ≤ 1) (T : ℕ) :
    (v+δ/2)^T/(v+δ)^T ≤ Real.exp (-(δ*(T : ℝ)/2)) := by
  have hs0 : 0 < v+δ := by linarith
  have hr0 : 0 ≤ (v+δ/2)/(v+δ) := div_nonneg (by linarith) hs0.le
  have hr : (v+δ/2)/(v+δ) ≤ Real.exp (-δ/2) := by
    have he := Real.add_one_le_exp (-δ/2)
    have hratio : (v+δ/2)/(v+δ) ≤ 1-δ/2 := by
      apply (div_le_iff₀ hs0).mpr
      nlinarith
    linarith
  rw [← div_pow]
  have hh := pow_le_pow_left₀ hr0 hr T
  rw [← Real.exp_nat_mul] at hh
  exact hh.trans_eq (by congr 1; ring)

lemma inverse_power_bound {s δ : ℝ} (hδ : 0 < δ) (hs : δ ≤ s) (T : ℕ) :
    1/s^T ≤ Real.exp ((T : ℝ)/δ) := by
  have hs0 : 0 < s := hδ.trans_le hs
  have hh := Real.log_le_sub_one_of_pos (one_div_pos.mpr hδ)
  rw [one_div, Real.log_inv] at hh
  have hlog := Real.log_le_log hδ hs
  have hl : -Real.log s ≤ 1/δ := by simpa only [one_div] using (show -Real.log s ≤ δ⁻¹ by linarith)
  have hpow := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg T : (0:ℝ) ≤ T)
  have he : 1/s^T = Real.exp (-(T : ℝ)*Real.log s) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hs0, one_div]
  rw [he]
  apply Real.exp_le_exp.mpr
  simpa only [mul_neg, neg_mul, div_eq_mul_inv, one_mul] using hpow

end ThresholdParallelRepetition

end

noncomputable section
namespace ThresholdParallelRepetition

lemma analytic_threshold_bound {v δ θ R E q : ℝ}
    (hv : 0 ≤ v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : v+δ ≤ 1)
    (hθ : 2 ≤ θ) (hδθ : 8 ≤ δ*θ)
    (hθR : θ/δ ≤ R/4) (hR : 2/δ ≤ R/4) (hE : E ≤ δ*θ/8)
    (hq : q*(v+δ)^(⌊θ⌋₊) ≤ (v+δ/2)^(⌊θ⌋₊)+Real.exp (-R)*(2/δ)) :
    q ≤ Real.exp (-E) := by
  let T := ⌊θ⌋₊
  let L := δ*θ/4
  have hθ0 : 0 ≤ θ := by linarith
  have hT : (T : ℝ) ≤ θ := Nat.floor_le hθ0
  have hT' : θ/2 ≤ (T : ℝ) := by
    have hh := Nat.lt_floor_add_one θ
    dsimp [T]; linarith
  have hs0 : 0 < v+δ := by linarith
  have hp0 : 0 < (v+δ)^T := pow_pos hs0 _
  have hq' : q ≤ (v+δ/2)^T/(v+δ)^T + Real.exp (-R)*(2/δ)/(v+δ)^T := by
    rw [← add_div]
    exact (le_div_iff₀ hp0).mpr hq
  have hfirst : (v+δ/2)^T/(v+δ)^T ≤ Real.exp (-L) := by
    apply (power_ratio_bound hv hδ hs T).trans
    apply Real.exp_le_exp.mpr
    dsimp [L]
    nlinarith
  have hTδ : (T : ℝ)/δ ≤ R/4 := (div_le_div_of_nonneg_right hT hδ.le).trans hθR
  have hfac : 2/δ ≤ Real.exp (2/δ) := by linarith [Real.add_one_le_exp (2/δ)]
  have hbad : Real.exp (-R)*(2/δ)/(v+δ)^T ≤ Real.exp (-R/2) := by
    calc
      Real.exp (-R)*(2/δ)/(v+δ)^T = Real.exp (-R)*(2/δ)*(1/(v+δ)^T) := by ring
      _ ≤ Real.exp (-R)*Real.exp (2/δ)*Real.exp ((T : ℝ)/δ) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hfac (Real.exp_pos _).le
        · exact inverse_power_bound hδ (by linarith) T
        · positivity
        · positivity
      _ = Real.exp (-R+2/δ+(T : ℝ)/δ) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-R/2) := Real.exp_le_exp.mpr (by linarith)
  have hδ2 : δ*δ ≤ 1 := by nlinarith
  have hL : L ≤ R/2 := by
    have hh : δ*θ ≤ θ/δ := by
      apply (le_div_iff₀ hδ).mpr
      nlinarith [mul_le_mul_of_nonneg_right hδ2 hθ0]
    have hR0 : 0 < R := by have := div_pos (show (0:ℝ)<2 by norm_num) hδ; linarith
    dsimp [L]; linarith
  have hqL : q ≤ 2*Real.exp (-L) := by
    have hb : Real.exp (-R)*(2/δ)/(v+δ)^T ≤ Real.exp (-L) :=
      hbad.trans (Real.exp_le_exp.mpr (by linarith))
    linarith
  have htwo : 2 ≤ Real.exp (L/2) := by
    have hh := Real.add_one_le_exp (L/2)
    dsimp [L] at *
    linarith
  calc
    q ≤ 2*Real.exp (-L) := hqL
    _ ≤ Real.exp (L/2)*Real.exp (-L) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-L/2) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-E) := by apply Real.exp_le_exp.mpr; dsimp [L]; linarith

end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition


theorem solution : type_of% @_root_.OAI.ThresholdParallelRepetition.analytic_threshold_bound := @_root_.OAI.ThresholdParallelRepetition.analytic_threshold_bound

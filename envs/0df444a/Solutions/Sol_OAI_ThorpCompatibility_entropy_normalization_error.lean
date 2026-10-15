-- Prove2me | solution 1 for OAI.ThorpCompatibility.entropy_normalization_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:59:35.68532+00:00
-- url     : https://prove2.me/submissions/ea6dd8f8-f8b3-414a-8eab-f308560dd614

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/Normalization.lean:L56-L84
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.entropy_normalization_error. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyEntries
import Definitions.Def_OAI_Probability_ThorpCompatibility_ExposureEntropy

-- ---- from OAI.Probability.ThorpCompatibility.Normalization ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma log_side_bound {m x : ℝ} (hm : 1 ≤ m) (hx : 0 < x) (hu : x ≤ 2*m) :
    1 + Real.log x ≤ 102 * m^(1/100:ℝ) := by
  have hm0 : 0 < m := by linarith
  have ht : 1 ≤ m^(1/100:ℝ) := Real.one_le_rpow hm (by norm_num)
  have hlog := Real.log_le_log hx hu
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hm0.ne'] at hlog
  have h₂ := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have hp := Real.log_le_rpow_div hm0.le (by norm_num : (0:ℝ) < 1/100)
  norm_num at hp
  linarith

lemma exposure_error_polynomial {m : ℝ} (hm : 1 ≤ m) {A D : ℕ}
    (hA0 : 0 < A) (hD0 : 0 < D) (hA : (A:ℝ) ≤ 2*m) (hD : (D:ℝ) ≤ 2*m) :
    totalExposureError A D (m^(1/100:ℝ)) (m^(1/100:ℝ)) ≤
      41820 * m * (m^(1/100:ℝ))^4 := by
  let H : ℝ := m^(1/100:ℝ)
  have hH : 1 ≤ H := Real.one_le_rpow hm (by norm_num)
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hm0 : 0 ≤ m := by linarith
  have hla := log_side_bound hm (by exact_mod_cast hA0) hA
  have hld := log_side_bound hm (by exact_mod_cast hD0) hD
  have hDlog0 : 0 ≤ 1 + Real.log (D:ℝ) := by
    have hn : 1 ≤ (D:ℝ) := by exact_mod_cast hD0
    linarith [Real.log_nonneg hn]
  have hha : (harmonic A : ℝ) ≤ 102*H := le_trans (harmonic_le_one_add_log A) hla
  have hha0 : 0 ≤ (harmonic A : ℝ) := by unfold harmonic; positivity
  have h₁ : (A:ℝ) * (1 + Real.log (D:ℝ)) ≤ 204*m*H := by
    calc
      _ ≤ (2*m)*(102*H) := mul_le_mul hA hld hDlog0 (by positivity)
      _ = _ := by ring
  have h₂ : 2 * (D:ℝ) * H * H * (1 + Real.log (D:ℝ)) * (harmonic A : ℝ) ≤
      41616*m*H^4 := by
    have hd : 2*(D:ℝ)*H^2 ≤ 4*m*H^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hD (sq_nonneg H)]
    have hprod := mul_le_mul hld hha hha0 (by positivity : 0 ≤ 102*H)
    calc
      _ = (2*(D:ℝ)*H^2)*((1+Real.log (D:ℝ))*(harmonic A : ℝ)) := by ring
      _ ≤ (4*m*H^2)*((102*H)*(102*H)) :=
        mul_le_mul hd hprod (mul_nonneg hDlog0 hha0) (by positivity)
      _ = _ := by ring
  have hp : H ≤ H^4 := by simpa using pow_le_pow_right₀ hH (by norm_num : 1 ≤ (4:ℕ))
  have h₃ := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 204*m)
  change (A:ℝ)*(1+Real.log (D:ℝ)) +
    2*(D:ℝ)*H*H*(1+Real.log (D:ℝ))*(harmonic A : ℝ) ≤ _
  nlinarith

lemma entropy_normalization_error {m : ℝ} (hm : 1 ≤ m) {A D : ℕ}
    (hA0 : 0 < A) (hD0 : 0 < D) (hA : (A:ℝ) ≤ 2*m) (hD : (D:ℝ) ≤ 2*m) :
    totalExposureError A D (m^(1/100:ℝ)) (m^(1/100:ℝ)) + 2 + 2*Real.log m ≤
      50000*m^(108/100:ℝ) := by
  have hm0 : 0 < m := by linarith
  let H : ℝ := m^(1/100:ℝ)
  have hH : 1 ≤ H := Real.one_le_rpow hm (by norm_num)
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hpoly := exposure_error_polynomial hm hA0 hD0 hA hD
  have hlog := Real.log_le_rpow_div hm0.le (by norm_num : (0:ℝ) < 1/100)
  norm_num [div_eq_mul_inv] at hlog
  have hpow : H ≤ H^4 := by simpa using pow_le_pow_right₀ hH (by norm_num : 1 ≤ (4:ℕ))
  have hmp : H^4 ≤ m*H^4 := by nlinarith [pow_nonneg hH0 4]
  have hsmall : 2 + 2*Real.log m ≤ 202*m*H^4 := by
    change Real.log m ≤ H * 100 at hlog
    nlinarith
  have heq : m*H^4 = m^(104/100:ℝ) := by
    change m*(m^(1/100:ℝ))^4 = _
    rw [← Real.rpow_mul_natCast hm0.le]
    calc
      _ = m^(1:ℝ) * m^((1/100:ℝ)*(4:ℕ)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hm0]; norm_num
  have hmono : m^(104/100:ℝ) ≤ m^(108/100:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  have hbound : totalExposureError A D H H + 2 + 2*Real.log m ≤ 42022*(m*H^4) := by
    change totalExposureError A D H H ≤ 41820*m*H^4 at hpoly
    nlinarith
  rw [heq] at hbound
  exact le_trans hbound (by nlinarith [Real.rpow_nonneg hm0.le (108/100:ℝ)])

end ThorpCompatibility

namespace ThorpCompatibility

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {m : ℝ} (hm : 1 ≤ m) {A D : ℕ}
    (hA0 : 0 < A) (hD0 : 0 < D) (hA : (A:ℝ) ≤ 2*m) (hD : (D:ℝ) ≤ 2*m) :
    totalExposureError A D (m^(1/100:ℝ)) (m^(1/100:ℝ)) + 2 + 2*Real.log m ≤
      50000*m^(108/100:ℝ) := by
  first
    | exact OAI.ThorpCompatibility.entropy_normalization_error hm hA0 hD0 hA hD
    | exact OAI.ThorpCompatibility.entropy_normalization_error
    | (apply OAI.ThorpCompatibility.entropy_normalization_error <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.entropy_normalization_error <;> assumption)

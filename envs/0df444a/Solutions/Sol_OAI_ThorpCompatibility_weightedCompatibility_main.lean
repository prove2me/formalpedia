-- Prove2me | solution 1 for OAI.ThorpCompatibility.weightedCompatibility_main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:16:56.515015+00:00
-- url     : https://prove2.me/submissions/a6e5b1be-febf-4e59-bbc4-654953b43b09

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/Main.lean:L109-L125
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ThorpCompatibility.weightedCompatibility_main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ThorpCompatibility_weightedCompatibility_main) verbatim and is proved by it.
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
import Definitions.Def_OAI_Probability_ThorpCompatibility_UniformSupport
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyColumns
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridDeficits
import Definitions.Def_OAI_Probability_ThorpCompatibility_VariationalBound
import Theorems.Thm_OAI_ThorpCompatibility_clump_exp_moment_simple
import Theorems.Thm_OAI_ThorpCompatibility_weightedCompatibility_bound

-- ---- from OAI.Probability.ThorpCompatibility.ClumpParameters ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
open Filter Topology

lemma eventual_clump_parameters :
    ∀ᶠ m : ℝ in atTop, 1 ≤ m ∧
      4 * Real.exp 3 * m ^ (1 / 400 : ℝ) ≤ m ^ (1 / 100 : ℝ) ∧
      12 * m ^ (3 : ℕ) * Real.exp (-(m ^ (1 / 100 : ℝ))) ≤ Real.log 2 := by
  have hpow : ∀ᶠ m : ℝ in atTop, 4 * Real.exp 3 ≤ m ^ (3 / 400 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 400)).eventually
      (eventually_ge_atTop (4 * Real.exp 3))
  have ht : Tendsto (fun m : ℝ => 12 * m ^ (3 : ℕ) * Real.exp (-(m ^ (1 / 100 : ℝ))))
      atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 300).comp
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100))).const_mul 12
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with m hm
    have he : (m ^ (1 / 100 : ℝ)) ^ (300 : ℕ) = m ^ (3 : ℕ) := by
      rw [← Real.rpow_mul_natCast hm]
      norm_num
    simp only [Function.comp_apply, he]
    ring
  filter_upwards [eventually_ge_atTop (1 : ℝ), hpow,
    ht.eventually_le_const (Real.log_pos (by norm_num : (1 : ℝ) < 2))] with m hm hp he
  refine ⟨hm, ?_, he⟩
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  calc
    _ ≤ m ^ (3 / 400 : ℝ) * m ^ (1 / 400 : ℝ) :=
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hm0.le _)
    _ = m ^ (1 / 100 : ℝ) := by
      rw [← Real.rpow_add hm0]
      norm_num

lemma clump_small_parameter {m : ℝ} (hm : 1 ≤ m) {A D : ℕ}
    (hA : (A : ℝ) ≤ 2*m) (hD : m/2 ≤ D)
    (hp : 4 * Real.exp 3 * m ^ (1/400 : ℝ) ≤ m ^ (1/100 : ℝ)) :
    Real.exp 2 * A * (Real.exp (1/400 * Real.log m) * (Real.exp 1 / D)) ≤
      m ^ (1/100 : ℝ) := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hD0 : (0 : ℝ) < D := by linarith
  have hratio : (A : ℝ) / D ≤ 4 := by
    apply (div_le_iff₀ hD0).mpr
    linarith
  have hexp : Real.exp (1/400 * Real.log m) = m ^ (1/400 : ℝ) := by
    rw [Real.rpow_def_of_pos hm0]
    congr 1
    ring
  calc
    _ = Real.exp 3 * ((A : ℝ) / D) * m ^ (1/400 : ℝ) := by
      rw [hexp]
      have he : Real.exp 3 = Real.exp 2 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [he]
      ring
    _ ≤ 4 * Real.exp 3 * m ^ (1/400 : ℝ) := by
      calc
        _ ≤ Real.exp 3 * 4 * m ^ (1/400 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hratio (Real.exp_pos 3).le)
            (Real.rpow_nonneg hm0.le _)
        _ = _ := by ring
    _ ≤ _ := hp

lemma clump_polynomial_parameter {m : ℝ} (hm : 1 ≤ m) {A D : ℕ}
    (hA : (A : ℝ) ≤ 2*m) (hD : (D : ℝ) ≤ 2*m) :
    (D : ℝ)^2 * (A+1) ≤ 12*m^(3:ℕ) := by
  have hd2 : (D : ℝ)^2 ≤ (2*m)^2 := pow_le_pow_left₀ (by positivity) hD 2
  have ha3 : (A : ℝ)+1 ≤ 3*m := by linarith
  calc
    _ ≤ (2*m)^2 * (3*m) := mul_le_mul hd2 ha3 (by positivity) (by positivity)
    _ = _ := by ring

lemma clump_mgf_of_parameters {m : ℝ} (hm : 1 ≤ m)
    (hp : 4 * Real.exp 3 * m ^ (1/400 : ℝ) ≤ m ^ (1/100 : ℝ))
    (he : 12 * m^(3:ℕ) * Real.exp (-(m^(1/100:ℝ))) ≤ Real.log 2)
    (A D : ℕ) (hA : (A:ℝ) ≤ 2*m) (hD : m/2 ≤ D) (hD' : (D:ℝ) ≤ 2*m) :
    uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2 := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hD0 : (0:ℝ) < D := by linarith
  have hDN : 0 < D := by exact_mod_cast hD0
  have hsmall := clump_small_parameter hm hA hD hp
  have hpoly := clump_polynomial_parameter hm hA hD'
  have h := clump_exp_moment_simple (α := Fin A) (β := Fin D)
    (m^(1/100:ℝ)) (1/400 * Real.log m)
    (Real.rpow_nonneg hm0.le _) (by simpa using hDN) (by simpa using hsmall)
  simp only [Fintype.card_fin] at h
  calc
    _ ≤ _ := h
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (le_trans
      (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le) he)
    _ = 2 := Real.exp_log (by norm_num)

lemma eventual_clump_mgf :
    ∀ᶠ m : ℝ in Filter.atTop, ∀ (A D : ℕ),
      (A : ℝ) ≤ 2*m → m/2 ≤ D → (D : ℝ) ≤ 2*m →
      uniformMean (fun r : Rows A D =>
        Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2 := by
  filter_upwards [eventual_clump_parameters] with m hm
  exact clump_mgf_of_parameters hm.1 hm.2.1 hm.2.2

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.Main ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

theorem weightedCompatibility_main : WeightedCompatibilityTheorem := by
  have hgood : ∀ᶠ m : ℝ in Filter.atTop,
      4 ≤ m ∧ 1000 ≤ Real.log m ∧ ∀ (A D : ℕ),
      (A:ℝ) ≤ 2*m → m/2 ≤ D → (D:ℝ) ≤ 2*m →
      uniformMean (fun r : Rows A D =>
        Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2 := by
    filter_upwards [Filter.eventually_ge_atTop (4:ℝ),
      Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1000:ℝ)),
      eventual_clump_mgf] with m hm hl hg
    exact ⟨hm,hl,hg⟩
  obtain ⟨b,hb⟩ := Filter.eventually_atTop.mp hgood
  refine ⟨1000,50000,max b 4, by norm_num, by norm_num, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) (le_max_right b 4)
  · intro A D n m θ hm hθ hAl hAu hDl hDu w v hw hv
    have hh := hb m (le_trans (le_max_left b 4) hm)
    exact weightedCompatibility_bound hh.1 (Real.sq_sqrt (by positivity))
      hh.2.1 hθ hAl hAu hDl hDu (hh.2.2 A D hAu hDl hDu) w v hw hv

end ThorpCompatibility

end OAI

-- ---- mission target ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution : WeightedCompatibilityTheorem := by
  first
    | exact OAI.ThorpCompatibility.weightedCompatibility_main
    | (apply OAI.ThorpCompatibility.weightedCompatibility_main <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.weightedCompatibility_main <;> assumption)

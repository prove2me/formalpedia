-- Prove2me | solution 1 for OAI.Paper320.quantitative_profile_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:42:52.456764+00:00
-- url     : https://prove2.me/submissions/a6a71054-e235-461e-a1fd-6f0e16b588a1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/QuantitativeProfiles.lean:L12-L56
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.quantitative_profile_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Theorems.Thm_OAI_Paper320_coupled_profiles_bound
import Theorems.Thm_OAI_Paper320_normalized_profiles_step

-- ---- from OAI.Combinatorics.Sensitivity.ProfileArithmetic ----
namespace OAI

/-! The four raw recurrences imply the two normalized scalar recurrences. -/

noncomputable section

namespace Paper320

theorem le_normalizedMax_zero {M s₀ s₁ : ℝ} {n : ℕ} (hM : 0 < M) :
    s₀ ≤ normalizedMax M n s₀ s₁ * M ^ n :=
  (div_le_iff₀ (pow_pos hM n)).mp (le_max_left _ _)

theorem le_normalizedMax_one {M s₀ s₁ : ℝ} {n : ℕ} (hM : 0 < M) :
    s₁ ≤ normalizedMax M n s₀ s₁ * M ^ (n + 1) :=
  (div_le_iff₀ (pow_pos hM (n + 1))).mp (le_max_right _ _)

theorem normalizedMax_le {M s₀ s₁ u : ℝ} {n : ℕ} (hM : 0 < M)
    (h₀ : s₀ ≤ u * M ^ n) (h₁ : s₁ ≤ u * M ^ (n + 1)) :
    normalizedMax M n s₀ s₁ ≤ u :=
  max_le ((div_le_iff₀ (pow_pos hM n)).mpr h₀)
    ((div_le_iff₀ (pow_pos hM (n + 1))).mpr h₁)

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.QuantitativeProfiles ----
namespace OAI

/-! Quantitative bounds for any literal profiles satisfying the four recurrences. -/

noncomputable section

namespace Paper320

theorem quantitative_profile_bounds (d L M r : ℕ) (hM : 0 < M)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2)
    (S J : ℕ → Bool → ℕ)
    (hS₀ : S 0 false ≤ L) (hS₁ : S 0 true ≤ L * M)
    (hJ₀ : J 0 false = 0) (hJ₁ : J 0 true = 0)
    (hstepS₀ : ∀ n < d, S (n + 1) false ≤ 16 * S n false + S n true + 3 * J n true)
    (hstepS₁ : ∀ n < d, S (n + 1) true ≤ M ^ 2 * S n false + r * S n true)
    (hstepJ₀ : ∀ n < d, J (n + 1) false ≤ 16 * S n false + 3 * J n true)
    (hstepJ₁ : ∀ n < d, J (n + 1) true ≤ M ^ 2 * J n false + r * S n true) :
    ∀ n ≤ d, S n false ≤ 2 * L * M ^ n ∧ S n true ≤ 2 * L * M ^ (n + 1) := by
  let ε : ℝ := ((max r 16 : ℕ) : ℝ) / M
  let u : ℕ → ℝ := fun n => normalizedMax M n (S n false) (S n true)
  let v : ℕ → ℝ := fun n => normalizedMax M n (J n false) (J n true)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hε : 0 ≤ ε := by positivity
  have hεr : (r : ℝ) / M ≤ ε := by
    apply div_le_div_of_nonneg_right _ hMr.le
    exact_mod_cast le_max_left r 16
  have hεt : (16 : ℝ) / M ≤ ε := by
    apply div_le_div_of_nonneg_right _ hMr.le
    exact_mod_cast le_max_right r 16
  have hu0 : u 0 ≤ L := by
    apply normalizedMax_le hMr
    · simpa using (show (S 0 false : ℝ) ≤ L by exact_mod_cast hS₀)
    · simpa using (show (S 0 true : ℝ) ≤ (L : ℝ) * M by exact_mod_cast hS₁)
  have hv0 : v 0 ≤ 0 := by simp [v, normalizedMax, hJ₀, hJ₁]
  have hstep (n : ℕ) (hn : n < d) :
      u (n + 1) ≤ (1 + ε) * u n + 3 * v n ∧
      v (n + 1) ≤ ε * u n + 3 * v n := by
    apply normalized_profiles_step hMr (by positivity) hεr hεt (by positivity) (by positivity)
    · exact_mod_cast hstepS₀ n hn
    · exact_mod_cast hstepS₁ n hn
    · exact_mod_cast hstepJ₀ n hn
    · exact_mod_cast hstepJ₁ n hn
  have hb := coupled_profiles_bound d u v ε L hε (by positivity) hbudget hu0 hv0
    (fun n hn => (hstep n hn).1) (fun n hn => (hstep n hn).2)
  intro n hn
  have hu := (hb n hn).1
  have hzero : (S n false : ℝ) ≤ 2 * (L : ℝ) * (M : ℝ) ^ n := by
    exact (le_normalizedMax_zero hMr).trans
      (mul_le_mul_of_nonneg_right hu (by positivity))
  have hone : (S n true : ℝ) ≤ 2 * (L : ℝ) * (M : ℝ) ^ (n + 1) := by
    exact (le_normalizedMax_one hMr).trans
      (mul_le_mul_of_nonneg_right hu (by positivity))
  exact ⟨by exact_mod_cast hzero, by exact_mod_cast hone⟩

end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320

theorem solution (d L M r : ℕ) (hM : 0 < M)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2)
    (S J : ℕ → Bool → ℕ)
    (hS₀ : S 0 false ≤ L) (hS₁ : S 0 true ≤ L * M)
    (hJ₀ : J 0 false = 0) (hJ₁ : J 0 true = 0)
    (hstepS₀ : ∀ n < d, S (n + 1) false ≤ 16 * S n false + S n true + 3 * J n true)
    (hstepS₁ : ∀ n < d, S (n + 1) true ≤ M ^ 2 * S n false + r * S n true)
    (hstepJ₀ : ∀ n < d, J (n + 1) false ≤ 16 * S n false + 3 * J n true)
    (hstepJ₁ : ∀ n < d, J (n + 1) true ≤ M ^ 2 * J n false + r * S n true) :
    ∀ n ≤ d, S n false ≤ 2 * L * M ^ n ∧ S n true ≤ 2 * L * M ^ (n + 1) := by
  first
    | exact OAI.Paper320.quantitative_profile_bounds d L M r hM hbudget S J hS₀ hS₁ hJ₀ hJ₁ hstepS₀ hstepS₁ hstepJ₀ hstepJ₁
    | exact OAI.Paper320.quantitative_profile_bounds
    | (apply OAI.Paper320.quantitative_profile_bounds <;> assumption)
    | (intros; apply OAI.Paper320.quantitative_profile_bounds <;> assumption)

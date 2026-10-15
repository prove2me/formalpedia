-- Prove2me | solution 1 for OAI.Paper320.coupled_profiles_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:40:54.07154+00:00
-- url     : https://prove2.me/submissions/aab06286-d645-4649-a076-efc0fe8a9db5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/ScalarBounds.lean:L19-L50
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.coupled_profiles_bound. The node keeps its source
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

-- ---- from OAI.Combinatorics.Sensitivity.ScalarBounds ----
namespace OAI

/-! Scalar bounds for the two coupled sensitivity profiles. -/

namespace Paper320

theorem geometric_error_le {d n : ℕ} (hn : n ≤ d) {ε L : ℝ}
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2) :
    (3 / 2 : ℝ) * ε * L * (3 ^ n - 1) ≤ L := by
  have hp : (3 : ℝ) ^ (n + 1) ≤ 3 ^ (d + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hn)
  have hb := (mul_le_mul_of_nonneg_left hp hε).trans hbudget
  have hm := mul_le_mul_of_nonneg_right hb hL
  rw [pow_succ] at hm
  nlinarith [mul_nonneg hε hL]

theorem coupled_profiles_bound (d : ℕ) (u v : ℕ → ℝ) (ε L : ℝ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2)
    (hu0 : u 0 ≤ L) (hv0 : v 0 ≤ 0)
    (hu : ∀ n < d, u (n + 1) ≤ (1 + ε) * u n + 3 * v n)
    (hv : ∀ n < d, v (n + 1) ≤ ε * u n + 3 * v n) :
    ∀ n ≤ d, u n ≤ 2 * L ∧ v n ≤ ε * L * (3 ^ n - 1) := by
  have strong : ∀ n ≤ d,
      u n ≤ L + (3 / 2 : ℝ) * ε * L * (3 ^ n - 1) ∧
        v n ≤ ε * L * (3 ^ n - 1) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa using And.intro hu0 hv0
    | succ n ih =>
        intro hn
        have hnd : n ≤ d := by omega
        obtain ⟨hun, hvn⟩ := ih hnd
        have he := geometric_error_le hnd hε hL hbudget
        have hun' : u n ≤ 2 * L := by linarith
        have heu := mul_le_mul_of_nonneg_left hun' hε
        have hnu := hu n (by omega)
        have hnv := hv n (by omega)
        constructor
        · rw [pow_succ]
          nlinarith [mul_nonneg hε hL]
        · rw [pow_succ]
          nlinarith
  intro n hn
  obtain ⟨hun, hvn⟩ := strong n hn
  have he := geometric_error_le hn hε hL hbudget
  exact ⟨by linarith, hvn⟩

end Paper320

end OAI

-- ---- platform node ----
open OAI OAI.Paper320

theorem solution (d : ℕ) (u v : ℕ → ℝ) (ε L : ℝ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2)
    (hu0 : u 0 ≤ L) (hv0 : v 0 ≤ 0)
    (hu : ∀ n < d, u (n + 1) ≤ (1 + ε) * u n + 3 * v n)
    (hv : ∀ n < d, v (n + 1) ≤ ε * u n + 3 * v n) :
    ∀ n ≤ d, u n ≤ 2 * L ∧ v n ≤ ε * L * (3 ^ n - 1) := by
  first
    | exact OAI.Paper320.coupled_profiles_bound d u v ε L hε hL hbudget hu0 hv0 hu hv
    | exact OAI.Paper320.coupled_profiles_bound
    | (apply OAI.Paper320.coupled_profiles_bound <;> assumption)
    | (intros; apply OAI.Paper320.coupled_profiles_bound <;> assumption)

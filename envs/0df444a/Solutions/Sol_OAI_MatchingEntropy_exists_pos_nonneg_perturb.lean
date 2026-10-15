-- Prove2me | solution 1 for OAI.MatchingEntropy.exists_pos_nonneg_perturb
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:37:27.350154+00:00
-- url     : https://prove2.me/submissions/6b68b18e-d797-4635-be65-f1a9a5ed2d1d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean:L188-L210
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.exists_pos_nonneg_perturb. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic

-- ---- from OAI.Combinatorics.PerfectMatching.Optimizer ----
namespace OAI

/-!
Support and first-order identities for entropy-maximizing matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- A finite nonnegative vector permits small positive motion in any direction
which does not point outwards at its zero coordinates. -/
theorem exists_pos_nonneg_perturb {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, p i = 0 → 0 ≤ v i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ p i+t*v i := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, p i ≠ 0 → 0 ≤ p i+t*v i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : p i = 0
    · exact Filter.Eventually.of_forall (fun _ h => (h hi).elim)
    · have hc : Continuous (fun t : ℝ => p i+t*v i) := by fun_prop
      have hh : {t : ℝ | 0 < p i+t*v i} ∈ 𝓝 0 :=
        (isOpen_lt continuous_const hc).mem_nhds
          (by simpa using lt_of_le_of_ne (hp i) (Ne.symm hi))
      exact Filter.Eventually.mono hh (fun t ht _ => ht.le)
  have he' := (hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioi 0)
  obtain ⟨t, ht, htp⟩ := he'.exists
  refine ⟨t, htp, fun i => ?_⟩
  by_cases hi : p i = 0
  · rw [hi, zero_add]
    exact mul_nonneg htp.le (hz i hi)
  · exact ht i hi

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, p i = 0 → 0 ≤ v i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ p i+t*v i := by
  first
    | exact OAI.MatchingEntropy.exists_pos_nonneg_perturb p v hp hz
    | exact OAI.MatchingEntropy.exists_pos_nonneg_perturb
    | (apply OAI.MatchingEntropy.exists_pos_nonneg_perturb <;> assumption)
    | (intros; apply OAI.MatchingEntropy.exists_pos_nonneg_perturb <;> assumption)

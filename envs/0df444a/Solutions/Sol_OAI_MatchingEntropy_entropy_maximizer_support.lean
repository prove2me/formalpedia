-- Prove2me | solution 1 for OAI.MatchingEntropy.entropy_maximizer_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:31:54.342484+00:00
-- url     : https://prove2.me/submissions/d1983ca8-8ecf-4b09-b90e-8e54e9315e5e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean:L56-L77
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.entropy_maximizer_support. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Theorems.Thm_OAI_MatchingEntropy_entropy_mix_zero_bonus

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

/-- Every entropy maximizer on a convex feasible set has maximal support. -/
theorem entropy_maximizer_support {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      entropy (fun i => (1-t)*p i+t*q i) ≤ entropy p) {j : ι} (hjq : 0 < q j) :
    0 < p j := by
  by_contra hj
  have hj0 : p j = 0 := le_antisymm (le_of_not_gt hj) (hp j)
  have hqp : entropy q ≤ entropy p := by simpa using hmax 1 (by constructor <;> norm_num)
  let c := (entropy p-entropy q)/(q j)+1
  have hc : 0 < c := by dsimp [c]; positivity
  let t := Real.exp (-c)
  have htp : 0 < t := Real.exp_pos _
  have ht : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨htp.le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hc.le)⟩
  have hbonus := (entropy_mix_zero_bonus hp hq hj0 ht).trans (hmax t ht)
  have hlog : Real.log t = -c := Real.log_exp _
  rw [Real.negMulLog, hlog] at hbonus
  have he : q j * c = entropy p-entropy q+q j := by
    dsimp [c]
    field_simp
  nlinarith

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      entropy (fun i => (1-t)*p i+t*q i) ≤ entropy p) {j : ι} (hjq : 0 < q j) :
    0 < p j := by
  first
    | exact OAI.MatchingEntropy.entropy_maximizer_support hp hq hmax hjq
    | exact OAI.MatchingEntropy.entropy_maximizer_support
    | (apply OAI.MatchingEntropy.entropy_maximizer_support <;> assumption)
    | (intros; apply OAI.MatchingEntropy.entropy_maximizer_support <;> assumption)

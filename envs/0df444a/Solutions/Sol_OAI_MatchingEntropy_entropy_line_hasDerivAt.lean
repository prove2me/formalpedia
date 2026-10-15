-- Prove2me | solution 1 for OAI.MatchingEntropy.entropy_line_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:34:35.433912+00:00
-- url     : https://prove2.me/submissions/807f49e7-f6a2-467d-aa15-d209fcf1cdf6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean:L131-L151
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.entropy_line_hasDerivAt. The node keeps its source
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

/-- Derivative of entropy along a line supported on the positive probabilities. -/
theorem entropy_line_hasDerivAt {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hsupp : ∀ i, p i = 0 → v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => p i+t*v i))
      (-∑ i, v i * Real.log (p i) - ∑ i, v i) 0 := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => Real.negMulLog (p i+t*v i))
      ((-Real.log (p i)-1)*v i) 0 := by
    intro i
    by_cases hi : p i = 0
    · simpa only [hi, hsupp i hi, mul_zero, add_zero, Real.negMulLog_zero] using
        (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have hp : p i+(0 : ℝ)*v i ≠ 0 := by simpa using hi
      simpa only [zero_mul, add_zero, one_mul, Function.comp_def, id_eq] using
        (Real.hasDerivAt_negMulLog hp).comp 0
          (((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (p i))
  have he : (∑ i, (-Real.log (p i)-1)*v i) =
      -∑ i, v i*Real.log (p i) - ∑ i, v i := by
    simp_rw [sub_mul, one_mul, neg_mul, mul_comm (Real.log (p _))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [← he]
  simpa only [entropy, Finset.sum_apply] using (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i))

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hsupp : ∀ i, p i = 0 → v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => p i+t*v i))
      (-∑ i, v i * Real.log (p i) - ∑ i, v i) 0 := by
  first
    | exact OAI.MatchingEntropy.entropy_line_hasDerivAt p v hsupp
    | exact OAI.MatchingEntropy.entropy_line_hasDerivAt
    | (apply OAI.MatchingEntropy.entropy_line_hasDerivAt <;> assumption)
    | (intros; apply OAI.MatchingEntropy.entropy_line_hasDerivAt <;> assumption)

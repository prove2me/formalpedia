-- Prove2me | solution 1 for OAI.MatchingEntropy.entropy_mix_zero_bonus
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:30:49.149122+00:00
-- url     : https://prove2.me/submissions/c6cb0e36-2327-42de-bb6a-239e90d5d4b6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean:L31-L54
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.entropy_mix_zero_bonus. The node keeps its source
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

/-- A zero probability gains a strict logarithmic bonus under mixing.
This is the boundary argument needed to obtain a positive entropy optimizer
on the entire face, not an assumed regularity of H. -/
theorem entropy_mix_zero_bonus {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) {j : ι} (hj : p j = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q + q j * Real.negMulLog t ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  classical
  have hterm : ∀ i, (1-t) * Real.negMulLog (p i) + t * Real.negMulLog (q i) +
      (if i=j then q j * Real.negMulLog t else 0) ≤
        Real.negMulLog ((1-t)*p i+t*q i) := by
    intro i
    by_cases hi : i=j
    · subst i
      simp only [hj, Real.negMulLog_zero, mul_zero, zero_add, ite_true,
        Real.negMulLog_mul]
      linarith
    · simp only [hi, ↓reduceIte, add_zero]
      simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
        (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, entropy] using hh

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) {j : ι} (hj : p j = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q + q j * Real.negMulLog t ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  first
    | exact OAI.MatchingEntropy.entropy_mix_zero_bonus hp hq hj ht
    | exact OAI.MatchingEntropy.entropy_mix_zero_bonus
    | (apply OAI.MatchingEntropy.entropy_mix_zero_bonus <;> assumption)
    | (intros; apply OAI.MatchingEntropy.entropy_mix_zero_bonus <;> assumption)

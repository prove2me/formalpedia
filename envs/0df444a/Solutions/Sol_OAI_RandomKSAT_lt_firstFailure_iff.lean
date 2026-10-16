-- Prove2me | solution 1 for OAI.RandomKSAT.lt_firstFailure_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:37:18.601634+00:00
-- url     : https://prove2.me/submissions/a7240c8d-8370-4d7e-988a-74436de0cc50

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FirstFailure.lean:L21-L35
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.lt_firstFailure_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance

-- ---- from OAI.Probability.SATVariance.FirstFailure ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma prefixSAT_mono {n k : ℕ} {ω : Stream n k} {m t : ℕ}
    (h : m ≤ t) : PrefixSAT ω t → PrefixSAT ω m := by
  rintro ⟨a, ha⟩
  exact ⟨a, fun i hi => ha i (hi.trans_le h)⟩

lemma lt_firstFailure_iff {n k : ℕ} (ω : Stream n k) (m : ℕ) :
    (m : ℕ∞) < firstFailure ω ↔ PrefixSAT ω m := by
  constructor
  · intro hm
    by_contra hn
    exact (not_le_of_gt hm) (sInf_le ⟨m, hn, rfl⟩)
  · intro hm
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ firstFailure ω := by
      apply le_sInf
      rintro _ ⟨t, ht, rfl⟩
      have hmt : m < t := by
        by_contra h
        exact ht (prefixSAT_mono (Nat.le_of_not_gt h) hm)
      exact ENat.natCast_le_natCast.mpr (Nat.succ_le_of_lt hmt)
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hle

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.lt_firstFailure_iff := @_root_.OAI.RandomKSAT.lt_firstFailure_iff

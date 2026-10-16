-- Prove2me | solution 1 for OAI.RandomKSAT.measurable_firstFailure
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:39:17.553462+00:00
-- url     : https://prove2.me/submissions/a5075d01-85f4-4414-a3c8-80c1316f56dc

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FirstFailure.lean:L93-L110
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.measurable_firstFailure. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Theorems.Thm_OAI_RandomKSAT_lt_firstFailure_iff

-- ---- from OAI.Probability.SATVariance.FirstFailure ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma prefixSAT_zero {n k : ℕ} (ω : Stream n k) : PrefixSAT ω 0 :=
  ⟨fun _ => false, fun _ hi => False.elim (Nat.not_lt_zero _ hi)⟩

lemma firstFailure_le_iff {n k : ℕ} (ω : Stream n k) (m : ℕ) :
    firstFailure ω ≤ m ↔ ¬ PrefixSAT ω m := by
  rw [← not_lt, lt_firstFailure_iff]

lemma firstFailure_pos {n k : ℕ} (ω : Stream n k) : 0 < firstFailure ω := by
  exact (lt_firstFailure_iff ω 0).mpr (prefixSAT_zero ω)

lemma measurableSet_prefixSAT (n k m : ℕ) :
    MeasurableSet {ω : Stream n k | PrefixSAT ω m} := by
  simp only [PrefixSAT, Set.ofPred_exists, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact (Set.toFinite {c : Clause n k | Satisfies c a}).measurableSet.preimage
    (measurable_pi_apply i)

lemma firstFailure_eq_succ_iff {n k : ℕ} (ω : Stream n k) (m : ℕ) :
    firstFailure ω = (m + 1 : ℕ) ↔ PrefixSAT ω m ∧ ¬ PrefixSAT ω (m + 1) := by
  rw [← lt_firstFailure_iff, ← firstFailure_le_iff]
  constructor
  · intro h
    rw [h]
    exact ⟨ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self m), le_rfl⟩
  · rintro ⟨h₁, h₂⟩
    apply le_antisymm h₂
    exact (ENat.natCast_add_one_le_iff).mpr h₁

lemma measurable_firstFailure (n k : ℕ) :
    Measurable (firstFailure : Stream n k → ℕ∞) := by
  apply ENat.measurable_iff.mpr
  intro m
  cases m with
  | zero =>
    have he : (firstFailure : Stream n k → ℕ∞) ⁻¹' {0} = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact ne_of_gt (firstFailure_pos ω)
    simpa only [Nat.cast_zero, he] using MeasurableSet.empty
  | succ m =>
    have he : (firstFailure : Stream n k → ℕ∞) ⁻¹' {↑(m + 1)} =
        {ω | PrefixSAT ω m} ∩ {ω | PrefixSAT ω (m + 1)}ᶜ := by
      ext ω
      exact firstFailure_eq_succ_iff ω m
    rw [he]
    exact (measurableSet_prefixSAT n k m).inter (measurableSet_prefixSAT n k (m+1)).compl

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.measurable_firstFailure := @_root_.OAI.RandomKSAT.measurable_firstFailure

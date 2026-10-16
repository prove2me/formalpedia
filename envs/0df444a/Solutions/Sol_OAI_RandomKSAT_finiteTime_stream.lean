-- Prove2me | solution 1 for OAI.RandomKSAT.finiteTime_stream
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:59:50.171771+00:00
-- url     : https://prove2.me/submissions/245c799e-7245-4969-ab0c-81b467da8051

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FiniteVariance.lean:L180-L194
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.finiteTime_stream. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Theorems.Thm_OAI_RandomKSAT_lt_firstFailure_iff
import Theorems.Thm_OAI_RandomKSAT_sum_fin_indicator_lt

-- ---- from OAI.Probability.SATVariance.FiniteVariance ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma finiteSAT_stream {n k L m : ℕ} (ω : Stream n k) (hm : m ≤ L) :
    finiteSAT (fun j : Fin L => ω j) m ↔ PrefixSAT ω m := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun j hj => ha ⟨j, hj.trans_le hm⟩ hj⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun j hj => ha j hj⟩

lemma finiteTime_stream {n k L : ℕ} (ω : Stream n k) :
    finiteTime (fun j : Fin L => ω j) = ((min (firstFailure ω) (L : ℕ∞)).toNat : ℝ) := by
  let N := (min (firstFailure ω) (L : ℕ∞)).toNat
  have htop : min (firstFailure ω) (L : ℕ∞) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (by simp))
  have hcoe : (N : ℕ∞) = min (firstFailure ω) (L : ℕ∞) := ENat.natCast_toNat htop
  have hN : N ≤ L := by
    exact_mod_cast (hcoe ▸ min_le_right (firstFailure ω) (L : ℕ∞))
  have hh (m : Fin L) : finiteSAT (fun j : Fin L => ω j) m.val ↔ m.val < N := by
    rw [finiteSAT_stream ω m.isLt.le, ← lt_firstFailure_iff]
    have hm : (m.val : ℕ∞) < (L : ℕ∞) := by exact_mod_cast m.isLt
    rw [← ENat.natCast_lt_natCast, hcoe, lt_min_iff, and_iff_left hm]
  unfold finiteTime
  simp_rw [hh]
  exact sum_fin_indicator_lt hN

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.finiteTime_stream := @_root_.OAI.RandomKSAT.finiteTime_stream

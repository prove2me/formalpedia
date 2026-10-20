-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FinitePeriod.periodic_sum_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:37:27.871752+00:00
-- url     : https://prove2.me/submissions/e18a9449-ebae-4afe-b707-6f5156c68848

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FinitePeriod.lean:L33-L57
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FinitePeriod.periodic_sum_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool

-- ---- from OAI.Combinatorics.BinaryEdit.FinitePeriod ----
namespace OAI

/-!
# Short-period detection for the finite-tree obstruction

Complete-period averaging gives the short-period detection estimate in
`prop:finite-lower`.
-/

open scoped BigOperators

namespace TreeEdit.BinaryLower.FinitePeriod

lemma sum_range_period_mul {f : ℕ → ℝ} {q : ℕ}
    (hperiod : Function.Periodic f q) (n : ℕ) :
    ∑ s ∈ Finset.range (n * q), f s =
      (n : ℝ) * ∑ s ∈ Finset.range q, f s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hshift : (∑ s ∈ Finset.range q, f (n * q + s)) =
          ∑ s ∈ Finset.range q, f s := by
        apply Finset.sum_congr rfl
        intro s hs
        simpa [Nat.add_comm] using hperiod.nat_mul n s
      rw [hshift]
      push_cast
      ring

/-- Full periods occupy at least half of any interval of length at least twice
its positive period. No divisibility of `J` by `q` is required. -/
lemma periodic_sum_lower {f : ℕ → ℝ} {q J : ℕ}
    (hq : 0 < q) (hJ : 2 * q ≤ J)
    (hperiod : Function.Periodic f q) (hnonneg : ∀ s, 0 ≤ f s)
    (hcycle : ∑ s ∈ Finset.range q, f s = 2 * (q : ℝ)) :
    (J : ℝ) ≤ ∑ s ∈ Finset.range J, f s := by
  have hqJ : q ≤ J := by omega
  have hdiv : 1 ≤ J / q := Nat.div_pos hqJ hq
  have hfull : q ≤ J / q * q := by
    simpa using Nat.mul_le_mul_right q hdiv
  have hrem : J % q < q := Nat.mod_lt J hq
  have hdecomp := Nat.mod_add_div J q
  rw [Nat.mul_comm q (J / q)] at hdecomp
  have hhalf : J ≤ 2 * (J / q * q) := by omega
  have hsub : J / q * q ≤ J := Nat.div_mul_le_self J q
  calc
    (J : ℝ) ≤ 2 * ((J / q : ℕ) : ℝ) * (q : ℝ) := by
      exact_mod_cast (show J ≤ 2 * (J / q) * q by simpa [Nat.mul_assoc] using hhalf)
    _ = ∑ s ∈ Finset.range (J / q * q), f s := by
      rw [sum_range_period_mul hperiod, hcycle]
      ring
    _ ≤ ∑ s ∈ Finset.range J, f s :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hsub)
        (fun s _ _ => hnonneg s)

end TreeEdit.BinaryLower.FinitePeriod

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FinitePeriod
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FinitePeriod.periodic_sum_lower := @_root_.OAI.TreeEdit.BinaryLower.FinitePeriod.periodic_sum_lower

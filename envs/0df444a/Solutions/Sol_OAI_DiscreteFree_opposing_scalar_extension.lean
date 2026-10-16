-- Prove2me | solution 1 for OAI.DiscreteFree.opposing_scalar_extension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:29:04.366714+00:00
-- url     : https://prove2.me/submissions/45e08ff0-78f0-4cb8-ab6d-4d690afdd508

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/SignedTests.lean:L121-L172
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.opposing_scalar_extension. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests

-- ---- from OAI.Analysis.LipschitzFree.SignedTests ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Signed variation, scalar extension, and incidence averaging
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

section Records

variable {D S : Type*}

end Records

section SignedTests

variable {S : Type*} [Fintype S]

end SignedTests
section

variable {N : Type*} [MetricSpace N]

theorem bounded_scalar_extension (P : Set N) (v : N → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hv : LipschitzOnWith 1 v P) (hvb : ∀ j ∈ P, |v j| ≤ L) :
    ∃ f : N → ℝ, LipschitzWith 1 f ∧ (∀ z, |f z| ≤ L) ∧ Set.EqOn f v P := by
  obtain ⟨F, hF, hFV⟩ := hv.extend_real
  refine ⟨fun z => max (-L) (min L (F z)), ?_, ?_, ?_⟩
  · exact (hF.const_min L).const_max (-L)
  · intro z
    apply abs_le.mpr
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  · intro z hz
    change max (-L) (min L (F z)) = v z
    rw [← hFV hz]
    obtain ⟨hl, hu⟩ := abs_le.mp (hvb z hz)
    rw [min_eq_right hu, max_eq_right hl]

theorem opposing_scalar_extension (P Q : Set N) (b c : N → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hbLip : LipschitzWith 1 b) (hcLip : LipschitzWith 1 c)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ L) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ L)
    (hcross : ∀ j ∈ P, ∀ k ∈ Q, dist j k < 2 * L → b j = 0 ∧ c k = 0) :
    ∃ f : N → ℝ, LipschitzWith 1 f ∧ (∀ z, |f z| ≤ L) ∧
      Set.EqOn f b P ∧ Set.EqOn f (fun z => -c z) Q := by
  classical
  have hzero : ∀ j ∈ P ∩ Q, b j = 0 ∧ c j = 0 := by
    intro j hj
    by_cases hpos : 0 < L
    · exact hcross j hj.1 j hj.2 (by simp; linarith)
    · have hz : L = 0 := le_antisymm (le_of_not_gt hpos) hL
      constructor <;> linarith [(hb j).1, (hb j).2, (hc j).1, (hc j).2]
  let v : N → ℝ := fun j => if j ∈ P then b j else -c j
  have hvP : Set.EqOn v b P := fun j hj => ite_eq_left hj
  have hvQ : Set.EqOn v (fun z => -c z) Q := by
    intro j hj
    by_cases hp : j ∈ P
    · have hz := hzero j ⟨hp, hj⟩
      simp [v, hp, hz.1, hz.2]
    · exact ite_eq_right hp
  have hcross' : ∀ j ∈ P, ∀ k ∈ Q, |b j - -c k| ≤ dist j k := by
    intro j hj k hk
    by_cases hd : dist j k < 2 * L
    · obtain ⟨hz, hz'⟩ := hcross j hj k hk hd
      simp [hz, hz', dist_nonneg]
    · rw [sub_neg_eq_add, abs_of_nonneg (add_nonneg (hb j).1 (hc k).1)]
      linarith [(hb j).2, (hc k).2, le_of_not_gt hd]
  have hvLip : LipschitzOnWith 1 v (P ∪ Q) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro j hj k hk
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rcases hj with hj | hj <;> rcases hk with hk | hk
    · rw [hvP hj, hvP hk]
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using hbLip.dist_le_mul j k
    · rw [hvP hj, hvQ hk]
      exact hcross' j hj k hk
    · rw [hvQ hj, hvP hk, abs_sub_comm, dist_comm]
      exact hcross' k hk j hj
    · rw [hvQ hj, hvQ hk]
      have := hcLip.dist_le_mul j k
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq, neg_sub_neg, abs_sub_comm] using this
  have hvBound : ∀ j ∈ P ∪ Q, |v j| ≤ L := by
    intro j hj
    rcases hj with hj | hj
    · rw [hvP hj, abs_of_nonneg (hb j).1]
      exact (hb j).2
    · rw [hvQ hj, abs_neg, abs_of_nonneg (hc j).1]
      exact (hc j).2
  obtain ⟨f, hf, hfB, hfv⟩ := bounded_scalar_extension (P ∪ Q) v L hL hvLip hvBound
  exact ⟨f, hf, hfB, fun j hj => (hfv (Or.inl hj)).trans (hvP hj),
    fun j hj => (hfv (Or.inr hj)).trans (hvQ hj)⟩

end

variable {X D S : Type*} [Fintype X] [Fintype D] [Fintype S]

end DiscreteFree

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal


theorem solution : type_of% @_root_.OAI.DiscreteFree.opposing_scalar_extension := @_root_.OAI.DiscreteFree.opposing_scalar_extension

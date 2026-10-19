-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.split_gain_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:35:21.711064+00:00
-- url     : https://prove2.me/submissions/a4f68074-4a2c-4d64-990b-3c46e2dc3593

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L144-L165
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.split_gain_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_split_energy_le

-- ---- from OAI.Analysis.DiamondDistortion.Ancestry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
/-- The explicit increase in the squared test after simultaneous splitting. -/
lemma split_gain_le (F : A.segments.Family) (H : Fin F.n → Set ι)
    (hH : ∀ i, A.Ancestral (H i)) (u : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ F.seg i, u v) ^ 2) +
      2 * (∑ i : Fin F.n, ((∑ v ∈ (F.seg i).filter (· ∉ H i), u v) ^ 2 -
        (∑ v ∈ F.seg i, u v) * (∑ v ∈ (F.seg i).filter (· ∉ H i), u v))) ≤
        (A.segments.primalSeminorm u) ^ 2 := by
  classical
  have he := A.split_energy_le F H hH u
  have hp (i : Fin F.n) :
      (∑ v ∈ (F.seg i).filter (· ∈ H i), u v) +
      (∑ v ∈ (F.seg i).filter (· ∉ H i), u v) = ∑ v ∈ F.seg i, u v := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : v ∈ H i <;> simp [h]
  convert he using 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hp i]
  ring

end Ancestry

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.split_gain_le := @_root_.OAI.DiamondDistortion.Ancestry.split_gain_le

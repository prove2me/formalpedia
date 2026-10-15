-- Prove2me | solution 1 for OAI.InfiniteMatroidCounterexample.RankModel.good_past_of_initial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:55:02.361862+00:00
-- url     : https://prove2.me/submissions/c8bedf56-a242-4e4b-9384-f0fbd1857536

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/TransfiniteConstruction.lean:L66-L81
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteMatroidCounterexample.RankModel.good_past_of_initial. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Zones
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Separation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Prototype
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_PrototypeExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_TransfiniteConstruction

-- ---- from OAI.Combinatorics.InfiniteMatroid.TransfiniteConstruction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma stage_subset_past {f : CIndex → Option (Set E0)} {a b : CIndex} (h : b < a) :
    stagePrototypes (f b) ⊆ pastPrototypes f a := by
  intro p hp
  exact mem_iUnion.mpr ⟨⟨b,h⟩,hp⟩
lemma stage_subset_initial {f : CIndex → Option (Set E0)} {a b : CIndex} (h : b ≤ a) :
    stagePrototypes (f b) ⊆ initialPrototypes f a := by
  rcases h.lt_or_eq with h|rfl
  · exact (stage_subset_past h).trans subset_union_left
  · exact subset_union_right
lemma initial_subset_past {f : CIndex → Option (Set E0)} {a b : CIndex} (h : b < a) :
    initialPrototypes f b ⊆ pastPrototypes f a := by
  rintro p (hp|hp)
  · obtain ⟨c,hc⟩ := mem_iUnion.mp hp
    exact stage_subset_past (c.2.trans h) hc
  · exact stage_subset_past h hp
namespace RankModel
variable (R : RankModel D)

lemma good_past_of_initial (f : CIndex → Option (Set E0)) (a : CIndex)
    (h : ∀ b < a, R.GoodPrototypes (initialPrototypes f b)) :
    R.GoodPrototypes (pastPrototypes f a) := by
  constructor
  · intro p hp
    obtain ⟨b,hb⟩ := mem_iUnion.mp hp
    exact (h b b.2).admissible p (Or.inr hb)
  · intro p hp
    obtain ⟨b,hb⟩ := mem_iUnion.mp hp
    exact initial_subset_past b.2 ((h b b.2).flip_closed p (Or.inr hb))
  · intro p hp q hq hne
    obtain ⟨b,hb⟩ := mem_iUnion.mp hp
    obtain ⟨c,hc⟩ := mem_iUnion.mp hq
    have hg := h (max b.1 c.1) (max_lt b.2 c.2)
    exact hg.separated p (stage_subset_initial (le_max_left _ _) hb)
      q (stage_subset_initial (le_max_right _ _) hc) hne

variable (hK : R.ideal = KIdeal)
include hK
end RankModel
end InfiniteMatroidCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteMatroidCounterexample OAI.InfiniteMatroidCounterexample.RankModel
open Set Filter
open scoped Topology symmDiff


theorem solution : type_of% @_root_.OAI.InfiniteMatroidCounterexample.RankModel.good_past_of_initial := @_root_.OAI.InfiniteMatroidCounterexample.RankModel.good_past_of_initial

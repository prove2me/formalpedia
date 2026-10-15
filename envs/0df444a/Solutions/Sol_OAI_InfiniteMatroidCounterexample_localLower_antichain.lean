-- Prove2me | solution 1 for OAI.InfiniteMatroidCounterexample.localLower_antichain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:51:13.170282+00:00
-- url     : https://prove2.me/submissions/0c063215-015e-427e-8418-c8f63895a788

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/LocalBases.lean:L100-L120
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteMatroidCounterexample.localLower_antichain. The node keeps its source
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

-- ---- from OAI.Combinatorics.InfiniteMatroid.Interpolation ----
namespace OAI

section

open Set Filter
open scoped Topology

namespace InfiniteMatroidCounterexample

lemma probeLiminf_mono {α : Type*} {f : ℕ → Set α → ℝ}
    {X Y : Set α} (h : ∀ n, f n X ≤ f n Y) :
    probeLiminf f X ≤ probeLiminf f Y := by
  exact liminf_le_liminf (Eventually.of_forall fun n ↦ EReal.coe_le_coe_iff.mpr (h n))

end InfiniteMatroidCounterexample
end

end OAI

-- ---- from OAI.Combinatorics.InfiniteMatroid.LocalBases ----
namespace OAI

section

open Set Filter
open scoped Topology symmDiff

namespace InfiniteMatroidCounterexample

lemma localLower_antichain (T : Set E0) :
    ∀ ⦃X Y⦄, X ∈ LocalLower T → Y ∈ LocalLower T → X ⊆ Y → X = Y := by
  intro X Y hX hY hXY
  by_contra hne
  obtain ⟨e, heY, heX⟩ := Set.not_subset.mp (fun hYX ↦ hne (Subset.antisymm hXY hYX))
  have hs : probeLiminf (fProbe T) (insert e X) = probeLiminf (fProbe T) X + 1 := by
    have heq : insert e X \ X = {e} := by ext x; simp [heX]
    have he := finite_change_eventually (T := T) (subset_insert e X)
      (show (insert e X \ X).Finite by rw [heq]; exact finite_singleton e)
    simp only [heq, ncard_singleton, Nat.cast_one] at he
    simpa using probeLiminf_finite_change he
  have hm := probeLiminf_mono (fun n ↦ fProbe_mono T (Set.insert_subset heY hXY) n)
  rw [hs] at hm
  have : (0 : EReal) < probeLiminf (fProbe T) X + 1 := by
    have hh := EReal.add_lt_add_right_coe hX.2.1 1
    have hz : (-1 : EReal) + 1 = 0 := by
      change ((-1 : ℝ) : EReal) + ((1 : ℝ) : EReal) = 0
      rw [← EReal.coe_add]
      norm_num
    simpa only [EReal.coe_one, hz] using hh
  exact (this.trans_le hm).not_ge hY.2.2

end InfiniteMatroidCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteMatroidCounterexample
open Set Filter
open scoped Topology symmDiff


theorem solution : type_of% @_root_.OAI.InfiniteMatroidCounterexample.localLower_antichain := @_root_.OAI.InfiniteMatroidCounterexample.localLower_antichain

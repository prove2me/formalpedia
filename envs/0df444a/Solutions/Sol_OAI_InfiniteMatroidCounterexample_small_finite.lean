-- Prove2me | solution 1 for OAI.InfiniteMatroidCounterexample.small_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:48:58.290179+00:00
-- url     : https://prove2.me/submissions/af9a2422-7442-42ba-ac18-93f75f04222b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/BlockDensity.lean:L196-L208
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteMatroidCounterexample.small_finite. The node keeps its source
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

-- ---- from OAI.Combinatorics.InfiniteMatroid.BlockDensity ----
namespace OAI

section

open Set Filter Finset
open scoped Topology symmDiff

namespace InfiniteMatroidCounterexample

lemma small_finite {X : Set E0} (hX : X.Finite) : Small X := by
  classical
  obtain ⟨N, hN⟩ := finite_subset_prefix hX
  have heq : density X =ᶠ[atTop] fun _ ↦ 0 := by
    filter_upwards [eventually_ge_atTop N] with m hm
    have hempty : traceFinset (wBlock m) X = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h1 := (mem_prefix x N).mp (hN ((mem_traceFinset (wBlock m) X x).mp hx).2)
      have h2 := (mem_wBlock x m).mp ((mem_traceFinset (wBlock m) X x).mp hx).1
      omega
    simp [density, finiteDensity, hempty]
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

end InfiniteMatroidCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteMatroidCounterexample
open Set Filter Finset
open scoped Topology symmDiff


theorem solution : type_of% @_root_.OAI.InfiniteMatroidCounterexample.small_finite := @_root_.OAI.InfiniteMatroidCounterexample.small_finite

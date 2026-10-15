-- Prove2me | solution 1 for OAI.InfiniteMatroidCounterexample.localRule_swap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:52:58.554813+00:00
-- url     : https://prove2.me/submissions/d1898c24-7177-46c3-8f13-7481a2469f3b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/BasisExtension.lean:L143-L157
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteMatroidCounterexample.localRule_swap. The node keeps its source
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
import Theorems.Thm_OAI_InfiniteMatroidCounterexample_small_finite

-- ---- from OAI.Combinatorics.InfiniteMatroid.BasisExtension ----
namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma localLower_swap {T B : Set E0} (hB : B ∈ LocalLower T)
    (e : E0) (he : e ∈ B) (f : E0) (hf : f ∉ B) : insert f (B \ {e}) ∈ LocalLower T := by
  have heq : B \ (B \ {e}) = {e} := by ext x; simp only [Set.mem_sdiff, Set.mem_singleton_iff]; aesop
  have hfq : insert f (B \ {e}) \ (B \ {e}) = {f} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    have : f ∉ B \ {e} := fun h ↦ hf h.1
    aesop
  have h1 := finite_change_eventually (T := T) (Set.sdiff_subset : B \ {e} ⊆ B)
    (show (B \ (B \ {e})).Finite by rw [heq]; exact finite_singleton e)
  have h2 := finite_change_eventually (T := T) (subset_insert f (B \ {e}))
    (show (insert f (B \ {e}) \ (B \ {e})).Finite by rw [hfq]; exact finite_singleton f)
  simp only [heq, hfq, ncard_singleton, Nat.cast_one] at h1 h2
  have hevent : ∀ᶠ n in atTop, fProbe T n (insert f (B \ {e})) = fProbe T n B + 0 := by
    filter_upwards [h1,h2] with n hn1 hn2
    rw [hn2, hn1, add_zero]
  have hlim := probeLiminf_finite_change hevent
  simp only [EReal.coe_zero, add_zero] at hlim
  refine ⟨?_,by simpa only [LowerBasis,hlim] using hB.2⟩
  have hclass := sameClass_add (sameClass_delete hB.1 (small_finite (finite_singleton e)))
    (small_finite (finite_singleton f))
  simpa only [Set.union_singleton] using hclass

lemma localRule_swap {s : Bool} {T B : Set E0} (hB : B ∈ LocalRule s T)
    (e : E0) (he : e ∈ B) (f : E0) (hf : f ∉ B) : insert f (B \ {e}) ∈ LocalRule s T := by
  cases s with
  | false => exact localLower_swap hB e he f hf
  | true =>
    have hc : (insert f (B \ {e}))ᶜ = insert e (Bᶜ \ {f}) := by
      ext x
      simp only [mem_compl_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      have hx1 : x = e → x ∈ B := fun h ↦ h ▸ he
      have hx2 : x = f → x ∉ B := fun h ↦ h ▸ hf
      tauto
    change (insert f (B \ {e}))ᶜ ∈ LocalLower Tᶜ
    rw [hc]
    change Bᶜ ∈ LocalLower Tᶜ at hB
    exact localLower_swap hB f hf e (by simpa using he)

end InfiniteMatroidCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteMatroidCounterexample
open Set Filter
open scoped Topology symmDiff


theorem solution : type_of% @_root_.OAI.InfiniteMatroidCounterexample.localRule_swap := @_root_.OAI.InfiniteMatroidCounterexample.localRule_swap

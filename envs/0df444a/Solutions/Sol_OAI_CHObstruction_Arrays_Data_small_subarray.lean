-- Prove2me | solution 1 for OAI.CHObstruction.Arrays.Data.small_subarray
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:43:13.489167+00:00
-- url     : https://prove2.me/submissions/ac50930e-a69b-4416-be89-763927547d4d

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/ArrayIsomorphisms.lean:L202-L245
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Arrays.Data.small_subarray. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors
import Definitions.Def_OAI_ModelTheory_Categoricity_EndpointDiagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_TailBound
import Definitions.Def_OAI_ModelTheory_Categoricity_Arrays
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayMaps
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayEmbeddings
import Definitions.Def_OAI_ModelTheory_Categoricity_Subarrays
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayIsomorphisms
import Theorems.Thm_OAI_CHObstruction_Arrays_Data_cardinal_le
import Theorems.Thm_OAI_CHObstruction_BaseOrders_small_hull
import Theorems.Thm_OAI_CHObstruction_Tuples_cardinal_bound

-- ---- from OAI.ModelTheory.Categoricity.ArrayEmbeddings ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Tests

open Tuples

theorem congr {I : Type v} (hCH : CH.{u}) {c d : Tuple I → Colors.Palette.{u}}
    (t : Tuple I) (h : ∀ m (e : Fin (m + 1) ↪o Fin (t.1 + 1)), c (sub t e) = d (sub t e)) :
    Test hCH c t ↔ Test hCH d t := by
  have he : (fun m (e : Fin (m + 1) ↪o Fin (t.1 + 1)) => c (sub t e)) =
      (fun m (e : Fin (m + 1) ↪o Fin (t.1 + 1)) => d (sub t e)) := funext (fun m => funext (h m))
  exact iff_of_eq (congrArg (Passes hCH) he)

end Tests

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_8
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_9
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_10
end Arrays

namespace Tuples

variable {I J : Type u}

end Tuples

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_11
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_12
end Arrays

namespace Tuples

end Tuples

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_13
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_14
variable (f : RawEmbedding M N)

end Arrays

end CHObstruction

end

end OAI

-- ---- from OAI.ModelTheory.Categoricity.Subarrays ----
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace BaseOrders

variable {B : Type u} [LinearOrder B] [DenselyOrdered B] [NoMinOrder B]
  [NoMaxOrder B] [Nonempty B]

end BaseOrders

namespace Arrays

open Tuples
open scoped symmDiff

variable (M : Data.{u})

variable {M}
variable (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
  [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S]

attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_15
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqElemB
theorem Data.restrict_object (hCH : CH.{u}) (hM : M.IsObject hCH) :
    (M.restrict J S).IsObject hCH := by
  intro t
  have hc := (hM (Tuples.map (Function.Embedding.subtype J) t)).preimage
    (Subtype.val_injective (p := fun b => b ∈ S))
  apply hc.mono
  intro b hb hh
  apply hb
  exact (Tests.map hCH (Function.Embedding.subtype J) (fun r => M.colors r b) t).mp hh

theorem Data.restrict_strong (hCH : CH.{u}) (hS : S.OrdConnected)
    (hbad : ∀ t : Tuple J, {b | ¬ Tests.Test hCH
      (fun r => M.colors r b) (Tuples.map (Function.Embedding.subtype J) t)} ⊆ S) :
    (M.restrictMap J S).Strong hCH := by
  have he : Set.range (M.restrictMap J S).base = S := by
    change Set.range (Subtype.val : S → M.B) = S
    exact Subtype.range_coe_subtype
  constructor
  · rw [he]; exact hS
  · intro t b hb
    rw [he] at hb
    have ht := not_not.1 (fun h => hb (hbad t h))
    have hm := (Tests.map hCH (Function.Embedding.subtype J) (fun r => M.colors r b) t).mp ht
    exact (Tests.congr hCH t (fun _ _ => Data.restrictMap_colors J S _ b)).mpr hm

end Arrays

end CHObstruction

end

end OAI

-- ---- from OAI.ModelTheory.Categoricity.ArrayIsomorphisms ----
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_16
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_17
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_18
variable (e : RawIso M N)

end Arrays

namespace CardinalTools

theorem union_le {X A : Type u} (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (hA : #A ≤ κ) (s : A → Set X) (hs : ∀ a, #(s a) ≤ κ) : #(⋃ a, s a) ≤ κ := by
  apply Cardinal.mk_iUnion_le_sum_mk.trans
  apply (Cardinal.sum_le_sum _ _ hs).trans
  simpa only [Cardinal.sum_const, Cardinal.lift_id, Cardinal.mul_eq_self hκ] using
    (mul_le_mul' hA (le_refl κ))

end CardinalTools

namespace Arrays

open Tuples
open scoped symmDiff

variable {M : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqI
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_19
theorem Data.restrictMap_range (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
    [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S] (x : M.Carrier)
    (hi : ↑x.indexSupport ⊆ J) (hb : ↑x.baseSupport ⊆ S) :
    x ∈ Set.range (M.restrictMap J S).onPoint := by
  classical
  have ht (t : Tuple M.I) (h : ↑((Finset.univ.map t.2)) ⊆ J) :
      ∃ r : Tuple J, Tuples.map (Function.Embedding.subtype J) r = t := by
    let r : Tuple J := ⟨t.1, ⟨fun i => ⟨t.2 i, h (Finset.mem_map.2 ⟨i, Finset.mem_univ i, rfl⟩)⟩,
      fun a b he => t.2.injective (congrArg Subtype.val he)⟩⟩
    exact ⟨r, rfl⟩
  have hs (s : Finset M.B) (h : ↑s ⊆ S) :
      (s.subtype (· ∈ S)).map (OrderEmbedding.subtype S).toEmbedding = s :=
    Finset.subtype_map_of_mem (p := fun x => x ∈ S) (fun _ ha => h ha)
  cases x with
  | index i => exact ⟨.index ⟨i, hi (Finset.mem_singleton_self i)⟩, rfl⟩
  | base b => exact ⟨.base ⟨b, hb (Finset.mem_singleton_self b)⟩, rfl⟩
  | group s => exact ⟨.group (s.subtype (· ∈ S)), congrArg Point.group (hs s hb)⟩
  | star v => exact ⟨.star v, rfl⟩
  | row t n s =>
    obtain ⟨r, hr⟩ := ht t hi
    refine ⟨.row r n (s.subtype (· ∈ S)), ?_⟩
    change Point.row (Tuples.map (Function.Embedding.subtype J) r) n
      (∅ ∆ (s.subtype (· ∈ S)).map (OrderEmbedding.subtype S).toEmbedding) = _
    rw [hr, hs s hb]
    simp
  | col t b v =>
    obtain ⟨r, hr⟩ := ht t hi
    refine ⟨.col r ⟨b, hb (Finset.mem_singleton_self b)⟩ v, ?_⟩
    change Point.col (Tuples.map (Function.Embedding.subtype J) r) b (∅ ∆ v) = _
    rw [hr]
    simp

theorem Data.small_subarray (M : Data.{u}) (hCH : CH.{u}) (hM : M.IsObject hCH)
    (A : Set M.Carrier) :
    ∃ N : Data.{u}, ∃ f : Map N M, N.IsObject hCH ∧ f.Strong hCH ∧
      A ⊆ Set.range f.onPoint ∧ #N.Carrier ≤ #A + ℵ₀ := by
  classical
  let κ : Cardinal.{u} := #A + ℵ₀
  have hκ : ℵ₀ ≤ κ := le_add_self
  have hA : #A ≤ κ := le_self_add
  let p : M.I := Classical.arbitrary M.I
  let J : Set M.I := (⋃ a : A, (a.val.indexSupport : Set M.I)) ∪ {p}
  have hJ : #J ≤ κ := by
    apply (Cardinal.mk_union_le _ _).trans
    apply Cardinal.add_le_of_le hκ
    · exact CardinalTools.union_le κ hκ hA _ (fun a =>
        (Cardinal.mk_le_aleph0_iff.2 (a.val.indexSupport.countable_toSet)).trans hκ)
    · simpa only [Cardinal.mk_singleton] using Cardinal.one_le_aleph0.trans hκ
  let : Nonempty J := ⟨⟨p, Or.inr rfl⟩⟩
  let T : Set M.B := (⋃ a : A, (a.val.baseSupport : Set M.B)) ∪
    (⋃ t : Tuple J, {b | ¬ Tests.Test hCH (fun r => M.colors r b)
      (Tuples.map (Function.Embedding.subtype J) t)})
  have hT : #T ≤ κ := by
    apply (Cardinal.mk_union_le _ _).trans
    apply Cardinal.add_le_of_le hκ
    · exact CardinalTools.union_le κ hκ hA _ (fun a =>
        (Cardinal.mk_le_aleph0_iff.2 (a.val.baseSupport.countable_toSet)).trans hκ)
    · exact CardinalTools.union_le κ hκ (Tuples.cardinal_bound κ hκ hJ) _
        (fun t => (Cardinal.mk_le_aleph0_iff.2 (hM _)).trans hκ)
  obtain ⟨S, hTS, hc, hn, hmin, hmax, hd, hS⟩ :=
    BaseOrders.small_hull M.locallyCountable T κ hκ hT
  let : Nonempty S := hn
  let : NoMinOrder S := hmin
  let : NoMaxOrder S := hmax
  let : DenselyOrdered S := hd
  refine ⟨M.restrict J S, M.restrictMap J S, M.restrict_object J S hCH hM,
    M.restrict_strong J S hCH hc ?_, ?_, ?_⟩
  · intro t b hb
    exact hTS (Or.inr (Set.mem_iUnion.2 ⟨t, hb⟩))
  · intro x hx
    apply Data.restrictMap_range J S x
    · intro i hi
      exact Or.inl (Set.mem_iUnion.2 ⟨⟨x, hx⟩, hi⟩)
    · intro b hb
      exact hTS (Or.inl (Set.mem_iUnion.2 ⟨⟨x, hx⟩, hb⟩))
  · exact Data.cardinal_le κ hκ hJ hS

end Arrays

end CHObstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.Arrays
open Cardinal Ordinal Order
open Tuples
open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqI
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_19


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Arrays.Data.small_subarray.{u} := @_root_.OAI.CHObstruction.Arrays.Data.small_subarray.{u}

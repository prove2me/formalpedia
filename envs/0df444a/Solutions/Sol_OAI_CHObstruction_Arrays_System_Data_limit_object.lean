-- Prove2me | solution 1 for OAI.CHObstruction.Arrays.System.Data.limit_object
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:48:21.748857+00:00
-- url     : https://prove2.me/submissions/6b80d3f5-321b-44fd-96c5-c46c98234e50

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/DirectedLimits.lean:L918-L940
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Arrays.System.Data.limit_object. The node keeps its source
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
import Definitions.Def_OAI_ModelTheory_Categoricity_DirectedLimits
import Theorems.Thm_OAI_CHObstruction_Arrays_System_Data_toLimit_strong

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
theorem Map.exceptions_countable (f : Map M N) (t : Tuple M.I) :
    (f.exceptions t).Countable := by
  classical
  apply Set.countable_iUnion
  intro m
  apply Set.countable_iUnion
  intro e
  exact Set.countable_iUnion (fun n => (f.rowShift (sub t e) n).countable_toSet)

theorem Map.test_away (f : Map M N) (hCH : CH.{u}) (t : Tuple M.I) (b : N.B)
    (hb : b ∉ f.exceptions t) :
    Tests.Test hCH (fun s => f.colors s b) t ↔
      Tests.Test hCH (fun s => N.colors s b) (Tuples.map f.index t) := by
  rw [Tests.map]
  apply Tests.congr
  intro m e
  have hn : ∀ n, b ∉ f.rowShift (sub t e) n := by
    intro n h
    apply hb
    exact Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨n, h⟩⟩⟩
  simp only [Map.colors, Data.colors, hn, decide_false, Bool.xor_false]

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

-- ---- from OAI.ModelTheory.Categoricity.DirectedLimits ----
namespace OAI

/-!
# Directed limits of finite-support arrays

The index, base and six-sorted carrier are constructed as directed limits.
Finite tuples and supports can be represented in a common stage. Compatible
row and column actions give the limit its relational interpretation, and
convexity supplies local countability and the strong-embedding properties.
-/

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace LimitTools

variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  {F : J → Type u} (f : ∀ i j, i ≤ j → F i ↪ F j) [DirectedSystem F (f · · ·)]
  (inj : ∀ i j h, Function.Injective (f i j h))

end LimitTools

namespace Arrays
namespace System

variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]

namespace Data

open Tuples

variable (S : Data (J := J))

open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.System.Data.instDecidableEqB
attribute [local instance] OAI.CHObstruction.Arrays.System.Data.instDecidableEqBObj
attribute [local instance] OAI.CHObstruction.Arrays.System.Data.instDecidableEqTupleIObj
variable (hconv : ∀ i j (h : i ≤ j), Set.OrdConnected (Set.range (S.map i j h).base))

variable {hCH : CH.{u}}

theorem limit_object (hobj : ∀ i, (S.obj i).IsObject hCH)
    (hstrong : ∀ i j h, (S.map i j h).Strong hCH) :
    (S.limitData hconv).IsObject hCH := by
  intro t
  obtain ⟨i, _, r, hr⟩ := S.tuple_exists t (Classical.arbitrary J)
  let f := S.toLimit hconv i
  have hf : f.Strong hCH := S.toLimit_strong hconv hstrong i
  have hbad := ((hobj i r).image f.base).union (f.exceptions_countable r)
  apply hbad.mono
  intro b hb
  by_cases hex : b ∈ f.exceptions r
  · exact Or.inr hex
  · left
    have ht : ¬ Tests.Test hCH (fun s => f.colors s b) r := by
      intro h
      apply hb
      have he := (f.test_away hCH r b hex).1 h
      change Tests.Test hCH (fun s => (S.limitData hconv).colors s b) (Tuples.map (S.index i) r) at he
      exact hr ▸ he
    by_cases hbase : b ∈ Set.range f.base
    · obtain ⟨c, rfl⟩ := hbase
      exact ⟨c, by simpa only [Set.mem_ofPred_eq, Map.colors_base] using ht, rfl⟩
    · exact (ht (hf.outside r b hbase)).elim

variable {N : Arrays.Data.{u}} (q : ∀ i, Map (S.obj i) N)
  (hq : ∀ i j h, (q j).comp (S.map i j h) = q i)

end Data
end System
end Arrays

end CHObstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.Arrays OAI.CHObstruction.Arrays.System OAI.CHObstruction.Arrays.System.Data
open Cardinal Ordinal Order
open Tuples
open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.System.Data.instDecidableEqB
attribute [local instance] OAI.CHObstruction.Arrays.System.Data.instDecidableEqBObj
attribute [local instance] OAI.CHObstruction.Arrays.System.Data.instDecidableEqTupleIObj


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Arrays.System.Data.limit_object.{u} := @_root_.OAI.CHObstruction.Arrays.System.Data.limit_object.{u}

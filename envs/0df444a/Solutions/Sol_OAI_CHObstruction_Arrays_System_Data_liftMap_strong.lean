-- Prove2me | solution 1 for OAI.CHObstruction.Arrays.System.Data.liftMap_strong
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:50:12.252741+00:00
-- url     : https://prove2.me/submissions/8a323a19-d377-4a13-9ac4-c18ea02c0163

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/DirectedLimits.lean:L1019-L1048
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Arrays.System.Data.liftMap_strong. The node keeps its source
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
theorem Map.comp_colors_outside (g : Map N P) (f : Map M N) (t : Tuple M.I) (b : P.B)
    (hb : b ∉ Set.range g.base) :
    (g.comp f).colors t b = g.colors (Tuples.map f.index t) b := by
  have hn : ∀ n, b ∉ (f.rowShift t n).map g.base.toEmbedding := by
    intro n h
    obtain ⟨a, _, ha⟩ := Finset.mem_map.1 h
    exact hb ⟨a, ha⟩
  apply ULift.ext
  apply congrArg Colors.color
  funext n
  change (P.bits (Tuples.map g.index (Tuples.map f.index t)) n b ^^ _) = _
  congr 1
  simp only [Map.comp, Finset.mem_symmDiff, hn, not_false_eq_true, and_true, false_and, or_false]

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

variable {N : Arrays.Data.{u}} (q : ∀ i, Map (S.obj i) N)
  (hq : ∀ i j h, (q j).comp (S.map i j h) = q i)

include hq in

theorem liftMap_strong (hs : ∀ i, (q i).Strong hCH) :
    (S.liftMap hconv q hq).Strong hCH := by
  let g := S.liftMap hconv q hq
  have hbase (i : J) (a : (S.obj i).B) : g.base (S.base i a) = (q i).base a :=
    congrArg (fun f : Map _ _ => f.base a) (S.liftMap_comp hconv q hq i)
  constructor
  · constructor
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩ b hb
    induction a, c using DirectLimit.induction₂ S.baseMap with
    | ih i a c =>
      change g.base (S.base i a) ≤ b ∧ b ≤ g.base (S.base i c) at hb
      rw [hbase, hbase] at hb
      obtain ⟨d, hd⟩ := (hs i).convex.out ⟨a, rfl⟩ ⟨c, rfl⟩ hb
      exact ⟨S.base i d, (hbase i d).trans hd⟩
  · intro t b hb
    obtain ⟨i, _, r, hr⟩ := S.tuple_exists t (Classical.arbitrary J)
    have hb' : b ∉ Set.range (q i).base := by
      rintro ⟨a, ha⟩
      exact hb ⟨S.base i a, (hbase i a).trans ha⟩
    have ht := (hs i).outside r b hb'
    have he (s : Tuple (S.obj i).I) :
        (q i).colors s b = g.colors (Tuples.map (S.index i) s) b := by
      rw [← S.liftMap_comp hconv q hq i]
      exact Map.comp_colors_outside g (S.toLimit hconv i) s b hb
    rw [← hr]
    change Tests.Test hCH (fun s : Tuple S.I => g.colors s b) (Tuples.map (S.index i) r)
    apply (Tests.map hCH (S.index i) (fun s : Tuple S.I => g.colors s b) r).2
    exact (Tests.congr hCH r (fun m e => he (Tuples.sub r e))).1 ht

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


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Arrays.System.Data.liftMap_strong.{u} := @_root_.OAI.CHObstruction.Arrays.System.Data.liftMap_strong.{u}

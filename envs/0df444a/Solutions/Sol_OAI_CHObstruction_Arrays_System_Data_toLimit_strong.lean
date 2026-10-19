-- Prove2me | solution 1 for OAI.CHObstruction.Arrays.System.Data.toLimit_strong
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:44:51.200628+00:00
-- url     : https://prove2.me/submissions/502b7c1f-c385-4f45-870a-2bfa0909d18b

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/DirectedLimits.lean:L893-L916
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Arrays.System.Data.toLimit_strong. The node keeps its source
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
import Theorems.Thm_OAI_CHObstruction_Arrays_Map_comp_colors_base

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

theorem toLimit_strong
    (hstrong : ∀ i j h, (S.map i j h).Strong hCH) (i : J) :
    (S.toLimit hconv i).Strong hCH := by
  constructor
  · exact S.base_convex hconv i
  · intro t b hb
    induction b using DirectLimit.induction S.baseMap with
    | ih j b =>
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      let c := (S.map j k hjk).base b
      have hc : c ∉ Set.range (S.map i k hik).base := by
        rintro ⟨a, ha⟩
        apply hb
        refine ⟨a, ?_⟩
        change S.base i a = S.base j b
        rw [← S.base_map i k hik a, ha, S.base_map]
      have ht := (hstrong i k hik).outside t c hc
      have he : ∀ r : Tuple (S.obj i).I,
          (S.toLimit hconv i).colors r (S.base j b) = (S.map i k hik).colors r c := by
        intro r
        rw [← S.toLimit_comp hconv i k hik, ← S.base_map j k hjk b]
        exact Map.comp_colors_base _ _ r c
      change Tests.Test hCH (fun r => (S.toLimit hconv i).colors r (S.base j b)) t
      simpa only [he] using ht

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


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Arrays.System.Data.toLimit_strong.{u} := @_root_.OAI.CHObstruction.Arrays.System.Data.toLimit_strong.{u}

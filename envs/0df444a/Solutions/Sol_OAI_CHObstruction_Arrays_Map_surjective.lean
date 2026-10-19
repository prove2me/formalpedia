-- Prove2me | solution 1 for OAI.CHObstruction.Arrays.Map.surjective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:31:47.080984+00:00
-- url     : https://prove2.me/submissions/86d3d978-9532-46f3-a882-5fadfe1f571f

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/ArrayEmbeddings.lean:L190-L217
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Arrays.Map.surjective. The node keeps its source
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

-- ---- from OAI.ModelTheory.Categoricity.ArrayEmbeddings ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Tests

open Tuples

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
theorem Map.surjective (f : Map M N) (hi : Function.Surjective f.index)
    (hb : Function.Surjective f.base) : Function.Surjective f.onPoint := by
  classical
  let ei : M.I ≃ N.I := Equiv.ofBijective f.index ⟨f.index.injective, hi⟩
  let eb : M.B ≃ N.B := Equiv.ofBijective f.base ⟨f.base.injective, hb⟩
  have hfin : ∀ s : Finset N.B, ∃ v : Finset M.B, v.map f.base.toEmbedding = s := by
    intro s
    refine ⟨s.map eb.symm.toEmbedding, ?_⟩
    rw [Finset.map_map]
    have he : eb.symm.toEmbedding.trans f.base.toEmbedding = Function.Embedding.refl N.B := by
      ext b
      exact eb.apply_symm_apply b
    rw [he, Finset.map_refl]
  have htup : Function.Surjective (Tuples.map f.index) := (Tuples.mapEquiv ei).surjective
  intro p
  cases p with
  | index i => obtain ⟨j, rfl⟩ := hi i; exact ⟨.index j, rfl⟩
  | base b => obtain ⟨a, rfl⟩ := hb b; exact ⟨.base a, rfl⟩
  | group s => obtain ⟨v, rfl⟩ := hfin s; exact ⟨.group v, rfl⟩
  | star v => exact ⟨.star v, rfl⟩
  | row t n s =>
    obtain ⟨r, rfl⟩ := htup t
    obtain ⟨v, hv⟩ := hfin (f.rowShift r n ∆ s)
    exact ⟨.row r n v, by simp [Map.onPoint, hv]⟩
  | col t b v =>
    obtain ⟨r, rfl⟩ := htup t
    obtain ⟨a, rfl⟩ := hb b
    exact ⟨.col r a (f.colShift r a ∆ v), by simp [Map.onPoint]⟩

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

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.Arrays
open Cardinal Ordinal Order
open Tuples
open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_11
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_12


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Arrays.Map.surjective.{u} := @_root_.OAI.CHObstruction.Arrays.Map.surjective.{u}

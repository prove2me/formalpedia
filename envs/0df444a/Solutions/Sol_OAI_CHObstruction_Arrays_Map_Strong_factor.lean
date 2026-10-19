-- Prove2me | solution 1 for OAI.CHObstruction.Arrays.Map.Strong.factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:39:17.393654+00:00
-- url     : https://prove2.me/submissions/3d6e64c8-1109-412e-aeba-c32465313f25

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/ArrayIsomorphisms.lean:L117-L136
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Arrays.Map.Strong.factor. The node keeps its source
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
import Theorems.Thm_OAI_CHObstruction_Arrays_Map_comp_colors_base

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

theorem Map.Strong.factor (hCH : CH.{u}) {f : Map M P} {g : Map N P} {k : Map M N}
    (hf : f.Strong hCH) (he : g.comp k = f) : k.Strong hCH := by
  have hb (a : M.B) : g.base (k.base a) = f.base a := by
    have h := congrArg (fun l : Map M P => l.base a) he
    exact h
  constructor
  · constructor
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ z ⟨haz, hzb⟩
    have hgz : g.base z ∈ Set.Icc (f.base a) (f.base b) := by
      rw [← hb, ← hb]
      exact ⟨g.base.monotone haz, g.base.monotone hzb⟩
    obtain ⟨c, hc⟩ := hf.convex.out ⟨a, rfl⟩ ⟨b, rfl⟩ hgz
    exact ⟨c, g.base.injective ((hb c).trans hc)⟩
  · intro t b hnb
    have hn : g.base b ∉ Set.range f.base := by
      rintro ⟨a, ha⟩
      exact hnb ⟨a, g.base.injective ((hb a).trans ha)⟩
    have ht := hf.outside t (g.base b) hn
    rw [← he] at ht
    simpa only [Map.comp_colors_base] using ht

end Arrays

namespace CardinalTools

end CardinalTools

namespace Arrays

open Tuples
open scoped symmDiff

variable {M : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqI
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_19
end Arrays

end CHObstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.Arrays
open Cardinal Ordinal Order
open Tuples
open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_16
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_17
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_18


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Arrays.Map.Strong.factor.{u} := @_root_.OAI.CHObstruction.Arrays.Map.Strong.factor.{u}

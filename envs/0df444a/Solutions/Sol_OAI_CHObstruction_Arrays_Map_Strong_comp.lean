-- Prove2me | solution 1 for OAI.CHObstruction.Arrays.Map.Strong.comp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:30:22.442321+00:00
-- url     : https://prove2.me/submissions/cc8d216c-2a00-4225-92bf-02816601fd88

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/ArrayEmbeddings.lean:L139-L161
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Arrays.Map.Strong.comp. The node keeps its source
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
import Theorems.Thm_OAI_CHObstruction_Arrays_Map_comp_colors_base

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

theorem Map.Strong.comp (hCH : CH.{u}) {g : Map N P} {f : Map M N}
    (hg : g.Strong hCH) (hf : f.Strong hCH) : (g.comp f).Strong hCH := by
  constructor
  · constructor
    intro x hx y hy z hz
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := hg.convex.out (by exact ⟨f.base a, rfl⟩)
      (by exact ⟨f.base b, rfl⟩) hz
    have hc : c ∈ Set.Icc (f.base a) (f.base b) := by
      exact ⟨g.base.le_iff_le.1 hz.1, g.base.le_iff_le.1 hz.2⟩
    obtain ⟨d, rfl⟩ := hf.convex.out ⟨a, rfl⟩ ⟨b, rfl⟩ hc
    exact ⟨d, rfl⟩
  · intro t b hb
    by_cases hbg : b ∈ Set.range g.base
    · obtain ⟨c, rfl⟩ := hbg
      have hc : c ∉ Set.range f.base := by
        rintro ⟨d, rfl⟩
        exact hb ⟨d, rfl⟩
      simpa only [Map.comp_colors_base] using hf.outside t c hc
    · have h := hg.outside (Tuples.map f.index t) b hbg
      rw [Tests.map] at h
      simpa only [Map.comp_colors_outside g f _ b hbg] using h

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

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.Arrays
open Cardinal Ordinal Order
open Tuples
open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_8
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_9
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_10


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Arrays.Map.Strong.comp.{u} := @_root_.OAI.CHObstruction.Arrays.Map.Strong.comp.{u}

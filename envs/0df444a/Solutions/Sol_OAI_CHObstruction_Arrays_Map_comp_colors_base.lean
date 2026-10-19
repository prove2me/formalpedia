-- Prove2me | solution 1 for OAI.CHObstruction.Arrays.Map.comp_colors_base
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:29:00.404378+00:00
-- url     : https://prove2.me/submissions/9b8d639a-66b0-40f9-a4c5-63635c91a2df

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/ArrayEmbeddings.lean:L106-L123
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Arrays.Map.comp_colors_base. The node keeps its source
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
theorem Map.comp_colors_base (g : Map N P) (f : Map M N) (t : Tuple M.I) (b : N.B) :
    (g.comp f).colors t (g.base b) = f.colors t b := by
  apply ULift.ext
  change Colors.color _ = Colors.color _
  have he : (fun n => P.bits (Tuples.map (g.comp f).index t) n (g.base b) ^^
      decide (g.base b ∈ (g.comp f).rowShift t n)) =
      (fun n => (N.bits (Tuples.map f.index t) n b ^^ decide (b ∈ f.rowShift t n)) ^^
        decide (n ∈ g.colShift (Tuples.map f.index t) b)) := by
    funext n
    have hv : g.colShift (Tuples.map f.index t) b ∆ ∅ =
        g.colShift (Tuples.map f.index t) b := by simp
    have h := g.bit_all (Tuples.map f.index t) n (f.rowShift t n) b ∅
    simp only [Matrix.bit, Finset.notMem_empty, decide_false, Bool.xor_false, hv] at h
    change (P.bits (Tuples.map g.index (Tuples.map f.index t)) n (g.base b) ^^
      decide (g.base b ∈ g.rowShift (Tuples.map f.index t) n ∆
        (f.rowShift t n).map g.base.toEmbedding)) = _
    rw [← h, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  rw [he, color_column]

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


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Arrays.Map.comp_colors_base.{u} := @_root_.OAI.CHObstruction.Arrays.Map.comp_colors_base.{u}

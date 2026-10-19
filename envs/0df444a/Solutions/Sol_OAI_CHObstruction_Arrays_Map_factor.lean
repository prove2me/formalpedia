-- Prove2me | solution 1 for OAI.CHObstruction.Arrays.Map.factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:36:54.176719+00:00
-- url     : https://prove2.me/submissions/e243d4ad-69f4-4d91-b323-2f39d4ac1540

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/ArrayIsomorphisms.lean:L74-L115
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Arrays.Map.factor. The node keeps its source
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

theorem Map.factor (f : Map M P) (g : Map N P)
    (h : ∀ x : M.Carrier, ∃ y, g.onPoint y = f.onPoint x) :
    ∃ k : Map M N, g.comp k = f := by
  let ef : M.Carrier → N.Carrier := fun x => (h x).choose
  have hef (x) : g.onPoint (ef x) = f.onPoint x := (h x).choose_spec
  have hinj : Function.Injective ef := by
    intro a b hab
    apply f.injective
    rw [← hef a, ← hef b, hab]
  let r : RawEmbedding M N := {
    toEmbedding := ⟨ef, hinj⟩
    relates := by
      intro s xs
      have he : (xs.map ef).map g.onPoint = xs.map f.onPoint := by
        rw [List.map_map]
        exact List.map_congr_left (fun x _ => hef x)
      change N.rawRel s (xs.map ef) ↔ M.rawRel s xs
      rw [← g.rawRel s (xs.map ef), he, f.rawRel]
    supports := by
      intro s b
      have hr := g.rawRel .incidence [.base b, ef (.group s)]
      simp only [List.map_cons, List.map_nil] at hr
      rw [hef] at hr
      change g.base b ∈ s.map f.base.toEmbedding ↔
        N.rawRel .incidence [.base b, ef (.group s)] at hr
      change N.rawRel .incidence [.base b, ef (.group s)] ↔
        ∃ a ∈ s, ef (.base a) = .base b
      rw [← hr]
      constructor
      · intro hb
        obtain ⟨a, has, ha⟩ := Finset.mem_map.1 hb
        refine ⟨a, has, g.injective ?_⟩
        rw [hef]
        exact congrArg Point.base ha
      · rintro ⟨a, has, ha⟩
        refine Finset.mem_map.2 ⟨a, has, ?_⟩
        have he := hef (.base a)
        rw [ha] at he
        exact Point.base.inj he.symm }
  refine ⟨r.toMap, Map.ext_onPoint (fun x => ?_)⟩
  rw [Map.comp_onPoint, r.toMap_onPoint]
  exact hef x

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


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Arrays.Map.factor.{u} := @_root_.OAI.CHObstruction.Arrays.Map.factor.{u}

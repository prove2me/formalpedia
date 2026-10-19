-- Prove2me | solution 1 for OAI.Release075.FullFilling.trace_mirror
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:38:02.379969+00:00
-- url     : https://prove2.me/submissions/fcc68ed4-6956-4a77-b234-7542ad569996

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/FullFilling.lean:L167-L188
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.FullFilling.trace_mirror. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling

-- ---- from OAI.GroupTheory.Hyperbolic.FullFilling ----
namespace OAI

namespace Release075
open Equiv PermCycles

attribute [instance] FullFilling.dartFintype

namespace TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end TriangleFilling

namespace FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : FullFilling flip color face w)

theorem trace_mirror (hflip : Function.Involutive flip)
    (hface : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (F : E → E → E → M)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0) :
    (D.mirror hflip hface).trace F = - D.trace F := by
  rw [trace,trace,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [mirror,Function.comp_apply]
  by_cases ha : a ∈ D.boundary
  · simp only [List.mem_reverse,ha,ite_true,neg_zero]
  simp only [List.mem_reverse,ha,ite_false]
  rcases D.cells a ha with ht | hb
  · have he := inv_cycle_three D.next ht.1
    rw [he.1,he.2.1]
    exact hmir _ _ _ ht.2.2
  · have he : ((D.next⁻¹)^2) a = a := by
      rw [inv_pow]
      apply (D.next^2).injective
      simpa only [perm_apply_inv,pow_two,Perm.mul_apply] using hb.2.symm
    rw [he,hb.2,hdeg,hdeg,neg_zero]

end FullFilling
end Release075

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.FullFilling.trace_mirror := @_root_.OAI.Release075.FullFilling.trace_mirror

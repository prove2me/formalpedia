-- Prove2me | solution 1 for OAI.Release075.FullFilling.trace_empty
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:40:31.733935+00:00
-- url     : https://prove2.me/submissions/3fd3922e-4d68-4b9d-bb33-9add8f16b352

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/FullFilling.lean:L199-L240
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.FullFilling.trace_empty. The node keeps its source
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
import Theorems.Thm_OAI_Release075_TriangleSphere_Dipole_delete

-- ---- from OAI.GroupTheory.Hyperbolic.Spheres ----
namespace OAI

namespace Release075
open Equiv PermCycles

attribute [instance] TriangleSphere.dartFintype

namespace TriangleSphere
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable (D : TriangleSphere flip color face)

end TriangleSphere
end Release075

namespace Release075.MarkedLineData
open Equiv PermCycles
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

namespace Release075.TriangleSphere
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Diagrammatic reducibility annihilates integral spherical face chains. -/
theorem cornerSum_eq_zero
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (D : TriangleSphere flip color face) : D.cornerSum F = 0 := by
  generalize hn : Fintype.card D.Dart = n
  induction n using Nat.strong_induction_on generalizing D with
  | h n ih =>
    by_cases hd : Nonempty D.Dipole
    · obtain ⟨P⟩ := hd
      obtain ⟨D',hlt,he⟩ := P.delete F hrot hmir
      rw [← he]
      exact ih (Fintype.card D'.Dart) (hn ▸ hlt) D' rfl
    · have : IsEmpty D.Dart := hempty D (not_nonempty_iff.mp hd)
      exact Finset.sum_eq_zero (fun b _ => isEmptyElim b)

end Release075.TriangleSphere

namespace Release075.TriangleSphere
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}

end Release075.TriangleSphere

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

end OAI

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

theorem bigon_reverse (a : D.Dart) : D.Bigon (D.reverse a) ↔ D.Bigon a := by
  have step (a : D.Dart) (h : D.Bigon a) : D.Bigon (D.reverse a) := by
    have hna : D.next (D.reverse a) = a := by
      rw [← h.1]
      exact h.2
    exact ⟨hna.trans (D.reverse_involutive a).symm,by
      simp only [pow_two,Perm.mul_apply,hna,h.1]⟩
  exact ⟨fun h => D.reverse_involutive a ▸ step _ h,step _⟩

theorem bigon_next (a : D.Dart) : D.Bigon (D.next a) ↔ D.Bigon a := by
  constructor
  · intro h
    have hna : D.next a = D.reverse a := by
      have h2 : D.next (D.next a) = a := D.next.injective h.2
      have hh : D.reverse (D.next a) = a := h.1.symm.trans h2
      exact (D.reverse_involutive (D.next a)).symm.trans (congrArg D.reverse hh)
    exact ⟨hna,D.next.injective h.2⟩
  · intro h
    rw [h.1]
    exact (D.bigon_reverse a).mpr h

end FullFilling
end Release075

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- A closed full filling is a disjoint union of triangular spheres and the
explicit isolated bigons. Consequently its integral cyclic evaluation vanishes. -/
theorem trace_empty
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0)
    (D : FullFilling flip color face []) : D.trace F = 0 := by
  have hb : D.boundary = [] := List.map_eq_nil_iff.mp D.boundary_word
  let hr : ∀ a, ¬D.Bigon (D.reverse a) ↔ ¬D.Bigon a := fun a => not_congr (D.bigon_reverse a)
  let hf : ∀ a, ¬D.Bigon (D.next a) ↔ ¬D.Bigon a := fun a => not_congr (D.bigon_next a)
  let S : TriangleSphere flip color face := {
    Dart := {a : D.Dart // ¬D.Bigon a}
    reverse := D.reverse.subtypePerm hr
    next := D.next.subtypePerm hf
    reverse_involutive := fun a => Subtype.ext (D.reverse_involutive a.val)
    reverse_ne := fun a h => D.reverse_ne a.val (congrArg Subtype.val h)
    label := D.label ∘ Subtype.val
    reverse_label := fun a => D.reverse_label a.val
    color_next := fun a => D.color_next a.val
    planar := by
      simpa only [PlanarMap,← Nat.card_eq_fintype_card] using
        D.planar.restrict (fun a => ¬D.Bigon a) hr hf
    triangular := by
      intro a
      have ht := (D.cells a.val (by simp [hb])).resolve_right a.property
      exact ⟨Subtype.ext ht.1,fun h => ht.2.1 (congrArg Subtype.val h),ht.2.2⟩ }
  have hz := TriangleSphere.cornerSum_eq_zero hempty F hrot hmir S
  let f : D.Dart → M := fun a => F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))
  have hpart := (Equiv.sumCompl D.Bigon).sum_comp f
  have hsum : (∑ a : {a : D.Dart // D.Bigon a}, f a.val) +
      (∑ a : {a : D.Dart // ¬D.Bigon a}, f a.val) = ∑ a, f a := by
    simpa only [Fintype.sum_sum_type,Equiv.sumCompl_apply_inl,Equiv.sumCompl_apply_inr] using hpart
  have hbig : (∑ a : {a : D.Dart // D.Bigon a}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    dsimp only [f]
    rw [a.property.2,hdeg]
  have htri : (∑ a : {a : D.Dart // ¬D.Bigon a}, f a.val) = 0 := hz
  rw [hbig,htri,zero_add] at hsum
  simpa only [trace,hb,List.not_mem_nil,ite_false] using hsum.symm

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


theorem solution : type_of% @_root_.OAI.Release075.FullFilling.trace_empty := @_root_.OAI.Release075.FullFilling.trace_empty

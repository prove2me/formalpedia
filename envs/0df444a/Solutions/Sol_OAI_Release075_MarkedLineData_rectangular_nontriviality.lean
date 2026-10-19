-- Prove2me | solution 1 for OAI.Release075.MarkedLineData.rectangular_nontriviality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:16:58.629108+00:00
-- url     : https://prove2.me/submissions/47e42072-1dc1-4459-94df-c576804d5953

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Rectangles.lean:L50-L88
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.MarkedLineData.rectangular_nontriviality. The node keeps its source
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
import Theorems.Thm_OAI_Release075_AngleDiskCounts_cannot_have_geodesic_boundary
import Theorems.Thm_OAI_Release075_BlockPresentation_rawRectangle_nullhomotopic_of_eq_one
import Theorems.Thm_OAI_Release075_Fillable_app
import Theorems.Thm_OAI_Release075_MarkedLineData_allLink_closed
import Theorems.Thm_OAI_Release075_MarkedLineData_x_turn_large
import Theorems.Thm_OAI_Release075_TriangleFilling_Dipole_cancel
import Theorems.Thm_OAI_Release075_TriangleFilling_dipole_of_link_backtrack
import Theorems.Thm_OAI_Release075_TriangleFilling_fold
import Theorems.Thm_OAI_Release075_TriangleRibbon_boundary_angle_lower
import Theorems.Thm_OAI_Release075_TriangleRibbon_interior_angle_lower

-- ---- from OAI.GroupTheory.Hyperbolic.TriangleFilling ----
namespace OAI

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq

attribute [instance] TriangleFilling.finiteDart

namespace TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end TriangleFilling
end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

end Release075

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

end Release075

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

namespace Fillable

theorem empty : Fillable flip color face [] := ⟨TriangleFilling.empty⟩

theorem rotateAppend {u v : List E} (h : Fillable flip color face (u++v)) :
    Fillable flip color face (v++u) := by
  obtain ⟨D⟩ := h
  have h' : Nonempty (TriangleFilling flip color face ((u++v).rotate u.length)) :=
    ⟨D.rotate u.length⟩
  simpa only [Fillable, List.rotate_append_length_eq] using h'

theorem mirror {w : List E} (h : Fillable flip color face w)
    (hi : Function.Involutive flip)
    (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b)) :
    Fillable flip color face (w.reverse.map flip) := by
  obtain ⟨D⟩ := h
  exact ⟨D.mirror hi hf⟩

theorem foldHead (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    {e : E} {w : List E} (h : Fillable flip color face (e::flip e::w)) :
    Fillable flip color face w := by
  obtain ⟨D⟩ := h
  obtain ⟨b,bs,hb,he,hbs⟩ := List.map_eq_cons_iff.mp D.boundary_word
  obtain ⟨a,l,ha,hae,hl⟩ := List.map_eq_cons_iff.mp hbs
  have hbound : D.boundary = b::a::l := by rw [hb,ha]
  have hab : D.label a = flip (D.label b) := by rw [he,hae]
  have hf := D.fold hi hn hbound hab
  rwa [hl] at hf

theorem erase (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (u v : List E) (e : E) (h : Fillable flip color face (u++e::flip e::v)) :
    Fillable flip color face (u++v) := by
  have h' : Fillable flip color face (e::flip e::(v++u)) := h.rotateAppend
  exact (h'.foldHead hi hn).rotateAppend

theorem backtrack (hi : Function.Involutive flip) (e : E) :
    Fillable flip color face [e,flip e] := ⟨TriangleFilling.backtrack hi e⟩

/-- Attach a stem, retaining its two directed traversals in the prescribed walk. -/
theorem stem (hi : Function.Involutive flip) {w : List E}
    (h : Fillable flip color face w) (e : E)
    (hc : ∀ a l, w = a::l → color (flip a) = color e) :
    Fillable flip color face (e::w++[flip e]) := by
  have hb : Fillable flip color face [flip e,e] := by
    have h' := backtrack (color := color) (face := face) hi (flip e)
    rwa [hi e] at h'
  have hh : Fillable flip color face ([flip e,e]++w) := hb.app h (by
    intro a l b m ha hm
    have hae : a = flip e := (List.cons.inj ha).1.symm
    rw [hae,hi]
    exact (hc b m hm).symm)
  exact rotateAppend (u := [flip e]) (v := e::w) hh

end Fillable
end Release075

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Words ----
namespace OAI

namespace Release075
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem reverseWord_reverse (hi : Function.Involutive flip) (w : List E) :
    reverseWord flip (reverseWord flip w) = w := by
  simp only [reverseWord,List.map_reverse,List.reverse_reverse,List.map_map]
  rw [show flip ∘ flip = id from funext hi]
  exact List.map_id w

namespace WordPath
variable {a b c : V} {u v : List E}

theorem source {e : E} {w : List E} (h : WordPath flip color a b (e::w)) :
    color (flip e) = a := by cases h; rfl

theorem append (h : WordPath flip color a b u) (h' : WordPath flip color b c v) :
    WordPath flip color a c (u++v) := by
  induction h with
  | nil => exact h'
  | cons e _ ih => exact .cons e (ih h')

theorem singleton (e : E) : WordPath flip color (color (flip e)) (color e) [e] :=
  .cons e (.nil _)

theorem reverse (hi : Function.Involutive flip) (h : WordPath flip color a b u) :
    WordPath flip color b a (reverseWord flip u) := by
  induction h with
  | nil => exact .nil _
  | cons e _ ih =>
    rw [reverseWord_cons]
    apply ih.append
    have hh := singleton (color := color) (flip := flip) (flip e)
    rwa [hi] at hh

end WordPath

namespace Fillable
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))

include hi hn in
/-- Erase a reversed path followed by the path, in any boundary context. -/
theorem erase_reverse (u v p : List E)
    (h : Fillable flip color face (u ++ reverseWord flip p ++ p ++ v)) :
    Fillable flip color face (u++v) := by
  induction p generalizing u with
  | nil => simpa only [reverseWord_nil,List.append_nil,List.nil_append] using h
  | cons e p ih =>
    simp only [reverseWord_cons,List.append_assoc,List.singleton_append] at h
    have h' : Fillable flip color face
        ((u++reverseWord flip p) ++ flip e :: flip (flip e) :: (p++v)) := by
      rw [hi e]
      simpa only [List.append_assoc,List.cons_append] using h
    exact ih u (by simpa only [List.append_assoc] using
      (h'.erase hi hn (u++reverseWord flip p) (p++v) (flip e)))

include hi in
/-- Attach a whole typed stem; each corner identification is type checked. -/
theorem stemPath {a b : V} {p w : List E} (hp : WordPath flip color a b p)
    (hw : WordPath flip color b b w) (h : Fillable flip color face w) :
    Fillable flip color face (p++w++reverseWord flip p) := by
  induction hp with
  | nil => simpa only [reverseWord_nil,List.nil_append,List.append_nil] using h
  | @cons e b p hp ih =>
    have hloop : WordPath flip color (color e) (color e)
        (p++w++reverseWord flip p) := (hp.append hw).append (hp.reverse hi)
    have hh := (ih hw).stem hi e (fun x xs hx => by
      rw [hx] at hloop
      exact hloop.source)
    simpa only [reverseWord_cons,List.cons_append,List.append_assoc] using hh

include hi in
theorem palindrome {a b : V} {p : List E} (hp : WordPath flip color a b p) :
    Fillable flip color face (p++reverseWord flip p) := by
  simpa only [List.append_nil] using (stemPath hi hp (.nil b)
    (empty (flip := flip) (color := color) (face := face)))

end Fillable

namespace FilledBetween
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))
variable (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
variable {a b c d : V} {p q r u v : List E}

include hi in
theorem refl (hp : WordPath flip color a b p) : FilledBetween flip color face p p :=
  Fillable.palindrome hi hp

include hi hf in
theorem symm (h : FilledBetween flip color face p q) : FilledBetween flip color face q p := by
  have hm := Fillable.mirror h hi hf
  change Fillable flip color face (reverseWord flip (p++reverseWord flip q)) at hm
  simpa only [FilledBetween,reverseWord_append,reverseWord_reverse hi] using hm

include hi hn in
theorem trans (hp : WordPath flip color a b p) (hq : WordPath flip color a b q)
    (hr : WordPath flip color a b r)
    (h : FilledBetween flip color face p q) (h' : FilledBetween flip color face q r) :
    FilledBetween flip color face p r := by
  have hloop := hp.append (hq.reverse hi)
  have hloop' := hq.append (hr.reverse hi)
  have hh := Fillable.app h h' (by
    intro e es f fs he hf
    rw [he] at hloop
    rw [hf] at hloop'
    exact hloop.source.trans hloop'.source.symm)
  apply Fillable.erase_reverse hi hn p (reverseWord flip r) q
  simpa only [List.append_assoc] using hh

include hi in
theorem whiskerLeft (hu : WordPath flip color c a u)
    (hp : WordPath flip color a b p) (hq : WordPath flip color a b q)
    (h : FilledBetween flip color face p q) :
    FilledBetween flip color face (u++p) (u++q) := by
  have hh := Fillable.stemPath hi hu (hp.append (hq.reverse hi)) h
  simpa only [FilledBetween,reverseWord_append,List.append_assoc] using hh

include hi in
theorem whiskerRight (hp : WordPath flip color a b p) (hq : WordPath flip color a b q)
    (hv : WordPath flip color b c v) (h : FilledBetween flip color face p q) :
    FilledBetween flip color face (p++v) (q++v) := by
  have h' : FilledBetween flip color face (reverseWord flip q) (reverseWord flip p) := by
    simpa only [FilledBetween,reverseWord_reverse hi] using
      (Fillable.rotateAppend (u := p) (v := reverseWord flip q) h)
  have hh := whiskerLeft hi (hv.reverse hi) (hq.reverse hi) (hp.reverse hi) h'
  have hh' := Fillable.rotateAppend hh
  simpa only [FilledBetween,reverseWord_append,reverseWord_reverse hi,List.append_assoc] using hh'

end FilledBetween
end Release075

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem edgeTarget_ne (e : d.OrientedEdge) : d.edgeTarget e ≠ d.edgeTarget (d.flipEdge e) := by
  rcases e with ⟨e,s⟩
  rcases e with x|l|rr <;> cases s <;> simp [edgeTarget,flipEdge]

theorem rawWord_typed {a c : Quiver.Symmetrify d.Vertex} (p : Quiver.Path a c) :
    WordPath d.flipEdge d.edgeTarget a c (d.rawWord p) := by
  change @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) a c at p
  induction p with
  | nil => exact .nil _
  | cons p f ih =>
    apply ih.append
    have hs := d.orientedLabel_source f
    have ht := d.orientedLabel_target f
    have hh := WordPath.singleton (flip := d.flipEdge) (color := d.edgeTarget) (d.orientedLabel f)
    simpa only [hs,ht] using hh

theorem TriangleFace.rotate {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.TriangleFace b c a := by
  cases h with
  | pos₀ b i u v => exact .pos₁ b i u v
  | pos₁ b i u v => exact .pos₂ b i u v
  | pos₂ b i u v => exact .pos₀ b i u v
  | neg₀ b i u v => exact .neg₁ b i u v
  | neg₁ b i u v => exact .neg₂ b i u v
  | neg₂ b i u v => exact .neg₀ b i u v

theorem TriangleFace.mirror {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.TriangleFace (d.flipEdge a) (d.flipEdge c) (d.flipEdge b) := by
  cases h with
  | pos₀ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₀ (d := d) b i u v
  | pos₁ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₂ (d := d) b i u v
  | pos₂ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.neg₁ (d := d) b i u v
  | neg₀ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₀ (d := d) b i u v
  | neg₁ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₂ (d := d) b i u v
  | neg₂ b i u v => simpa only [flipEdge_flipEdge] using TriangleFace.pos₁ (d := d) b i u v

theorem rawMove_filled {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawMove p q) :
    FilledBetween d.flipEdge d.edgeTarget d.TriangleFace (d.rawWord p) (d.rawWord q) := by
  cases h with
  | backtrack h =>
    cases h with
    | step a c f =>
      change Fillable d.flipEdge d.edgeTarget d.TriangleFace
        (reverseWord d.flipEdge [d.orientedLabel f,d.orientedLabel (Quiver.reverse f)])
      rw [d.orientedLabel_reverse]
      simp only [reverseWord_cons,reverseWord_nil,List.nil_append,
        flipEdge_flipEdge,List.singleton_append]
      exact ⟨TriangleFilling.backtrack (d.flipEdge_flipEdge) (d.orientedLabel f)⟩
  | triangle b i u v =>
    change Nonempty (TriangleFilling d.flipEdge d.edgeTarget d.TriangleFace
      [d.orientedL b i u v, d.orientedX i u v, d.flipEdge (d.orientedR b i u v)])
    exact ⟨TriangleFilling.triangle d.flipEdge_flipEdge (fun _ _ _ => TriangleFace.rotate d)
      _ _ _ rfl rfl rfl (by simpa only [flipEdge_flipEdge] using TriangleFace.neg₀ (d := d) b i u v)⟩

theorem rawHomotopic_filled {a c : d.RawPaths} {p q : a ⟶ c} (h : d.RawHomotopic p q) :
    FilledBetween d.flipEdge d.edgeTarget d.TriangleFace (d.rawWord p) (d.rawWord q) := by
  induction h with
  | rel p q h =>
    cases h with
    | intro a c u p q v h =>
      rw [d.rawWord_comp,d.rawWord_comp,d.rawWord_comp,d.rawWord_comp]
      exact FilledBetween.whiskerLeft d.flipEdge_flipEdge (d.rawWord_typed u)
        ((d.rawWord_typed p).append (d.rawWord_typed v))
        ((d.rawWord_typed q).append (d.rawWord_typed v))
        (FilledBetween.whiskerRight d.flipEdge_flipEdge (d.rawWord_typed p)
          (d.rawWord_typed q) (d.rawWord_typed v) (d.rawMove_filled h))
  | refl p => exact FilledBetween.refl d.flipEdge_flipEdge (d.rawWord_typed p)
  | symm p q _ ih =>
    exact FilledBetween.symm d.flipEdge_flipEdge
      (fun _ _ _ => TriangleFace.mirror d) ih
  | trans p q s _ _ ih ih' =>
    exact FilledBetween.trans d.flipEdge_flipEdge d.edgeTarget_ne
      (d.rawWord_typed p) (d.rawWord_typed q) (d.rawWord_typed s) ih ih'

theorem nullhomotopic_fillable {a : d.RawPaths} {p : a ⟶ a} (h : d.RawHomotopic p (𝟙 a)) :
    Fillable d.flipEdge d.edgeTarget d.TriangleFace (d.rawWord p) := by
  simpa only [FilledBetween,rawWord_nil,reverseWord_nil,List.append_nil] using
    d.rawHomotopic_filled h

/-- The actual presented rectangular word, if trivial, has a finite labelled
planar triangular filling. This lemma has no geometric hypothesis. -/
theorem rectangle_fillable_of_eq_one (i : I) (u u' v v' : Fin r)
    (h : d.x i u v * (d.x i u' v)⁻¹ * d.x i u' v' * (d.x i u v')⁻¹ = 1) :
    Fillable d.flipEdge d.edgeTarget d.TriangleFace
      [d.orientedX i u v, d.flipEdge (d.orientedX i u' v),
       d.orientedX i u' v', d.flipEdge (d.orientedX i u v')] := by
  exact d.nullhomotopic_fillable (d.rawRectangle_nullhomotopic_of_eq_one i u u' v v' h)

end Release075.BlockPresentation

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem TriangleFace.unique_aux {a b c a' b' c' : d.OrientedEdge}
    (h : d.TriangleFace a b c) (h' : d.TriangleFace a' b' c')
    (ha : a = a') (hb : b = b') : c = c' := by
  cases h <;> cases h' <;>
    simp only [orientedL,orientedX,orientedR,flipEdge,Prod.mk.injEq,
      Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
      Bool.not_true,and_true,false_and] at ha hb ⊢
  all_goals
    first
    | have hbb := congrArg Sigma.fst ha; cases hbb
    | have hbb := congrArg Sigma.fst hb; cases hbb
  all_goals simp only [Sigma.mk.inj_iff,heq_eq_eq,Prod.mk.injEq,Subtype.val_inj,true_and] at ha hb ⊢
  case pos₀.pos₀ b i u v u' v' i' =>
    rcases hb with ⟨rfl,rfl,rfl⟩
    simp
  case pos₁.pos₁ b i u v u' v' i' =>
    rcases ha with ⟨rfl,rfl,rfl⟩
    simp
  case pos₂.pos₂ b i u v u' v' i' =>
    rcases ha with ⟨rfl,hβ⟩
    rcases hb with ⟨rfl,hα⟩
    have hi := (d.block b).coordinates.injective
      (Prod.ext (add_right_cancel hα) (add_right_cancel hβ))
    subst i'
    exact ⟨rfl,rfl,rfl⟩
  case neg₀.neg₀ b i u v u' v' i' =>
    rcases ha with ⟨rfl,hα⟩
    rcases hb with ⟨rfl,hβ⟩
    have hi := (d.block b).coordinates.injective
      (Prod.ext (add_right_cancel hα) (add_right_cancel hβ))
    subst i'
    exact ⟨rfl,rfl,rfl⟩
  case neg₁.neg₁ b i u v u' v' i' =>
    rcases hb with ⟨rfl,rfl,rfl⟩
    simp
  case neg₂.neg₂ b i u v u' v' i' =>
    rcases ha with ⟨rfl,rfl,rfl⟩
    simp

theorem TriangleFace.unique {a b c c' : d.OrientedEdge}
    (h : d.TriangleFace a b c) (h' : d.TriangleFace a b c') : c = c' :=
  TriangleFace.unique_aux d h h' rfl rfl

end Release075.BlockPresentation

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Dipoles ----
namespace OAI

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Minimizing active size, not an assumed reduced-diagram axiom, produces a
filling with no cancellable adjacent labelled pair. -/
theorem exists_noDipole {w : List E} (h : Fillable flip color face w) :
    ∃ D : TriangleFilling flip color face w, IsEmpty D.Dipole := by
  have hex : ∃ n : ℕ, ∃ D : TriangleFilling flip color face w, D.activeCount = n := by
    obtain ⟨D⟩ := h
    exact ⟨D.activeCount,D,rfl⟩
  obtain ⟨D,hD⟩ := Nat.find_spec hex
  refine ⟨D,⟨fun P => ?_⟩⟩
  obtain ⟨D',hless⟩ := P.cancel
  have hmin := Nat.find_min' hex (show ∃ A : TriangleFilling flip color face w,
      A.activeCount = D'.activeCount from ⟨D',rfl⟩)
  omega

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : TriangleFilling flip color face w)

theorem noDipole_link_reduced
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (hD : IsEmpty D.Dipole)
    (x : D.Dart) (hx : D.Active x) (hnx : x ∉ D.boundary)
    (hnb : (D.reverse*D.next) x ∉ D.boundary) :
    D.label x ≠ D.label ((D.reverse*D.next) ((D.reverse*D.next) x)) := by
  intro h
  obtain ⟨P⟩ := D.dipole_of_link_backtrack hf hflip hmirror hunique x hx hnx hnb h
  exact hD.false P

end Release075.TriangleFilling

namespace Release075
namespace CyclicLink
variable {A V : Type*} {G : SimpleGraph V}

end CyclicLink
end Release075

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Ribbons ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075
open scoped BigOperators

attribute [instance] AngleDiskCounts.vertexFintype
namespace AngleDiskCounts
variable (D : AngleDiskCounts)

end AngleDiskCounts
end Release075

namespace Release075
open scoped BigOperators
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq

attribute [instance] TriangleRibbon.dartFintype

namespace TriangleRibbon
variable (R : TriangleRibbon)
end TriangleRibbon
end Release075

namespace Release075.SumWalk
variable {U V : Type*} {G : SimpleGraph U} {H : SimpleGraph V}

end Release075.SumWalk

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : TriangleFilling flip color face w)

end Release075.TriangleFilling

namespace Release075.SequenceWalk
variable {E : Type*} (L : SimpleGraph E)

end Release075.SequenceWalk

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.TriangleRibbon
open Equiv PermCycles
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable (R : TriangleRibbon)

variable {E : Type*} (L : SimpleGraph E) (label : R.Dart → E)
variable (hadj : ∀ a, ¬ R.IsOuter a → L.Adj (label a) (label (R.vertexPerm a)))
variable (hred : ∀ a, ¬ R.IsOuter a → ¬ R.IsOuter (R.vertexPerm a) →
  label a ≠ label (R.vertexPerm (R.vertexPerm a)))

include hadj hred

/-- Gauss--Bonnet on the actual permutation ribbon now rules out a filling whose
boundary turns are all separated by angle at least π in their target links. -/
theorem not_all_turns_geodesic
    (hclosed : ∀ a (p : L.Walk (label a) (label a)), 0 < p.length → ReducedWalk p →
      10 ≤ weight (R.color (cl R.vertexPerm a)) * p.length)
    (hboundary : ∀ a, R.IsOuter a →
      ∀ p : L.Walk (label (R.vertexPerm a)) (label a), ReducedWalk p →
        5 ≤ weight (R.color (cl R.vertexPerm a)) * p.length) : False :=
  R.counts.cannot_have_geodesic_boundary
    (R.interior_angle_lower L label hadj hred 10 hclosed)
    (R.boundary_angle_lower L label hadj hred hboundary)

end Release075.TriangleRibbon

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Links ----
namespace OAI

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

 theorem linkDirection_color (a : (d.presentation hr).OrientedEdge) :
    d.linkColor hr (d.linkDirection hr a) =
      (d.presentation hr).vertexColor ((d.presentation hr).edgeTarget a) := by
  rcases a with ⟨a,s⟩
  rcases a with ⟨i,u,v⟩|l|s' <;> cases s <;> rfl

 theorem linkDirection_injective : Function.Injective (d.linkDirection hr) := by
  rintro ⟨a,s⟩ ⟨b,t⟩ h
  rcases a with ⟨i,u,v⟩|l|s'
  all_goals rcases b with ⟨j,u',v'⟩|l'|t'
  all_goals cases s <;> cases t <;> simp_all [linkDirection]
  all_goals exact Sum.inr.inj h

 theorem face_corner_adj {a b c : (d.presentation hr).OrientedEdge}
    (h : (d.presentation hr).TriangleFace a b c) :
    (d.allLink hr).Adj (d.linkDirection hr a)
      (d.linkDirection hr ((d.presentation hr).flipEdge b)) := by
  cases h <;>
    simp only [BlockPresentation.orientedL,BlockPresentation.orientedX,
      BlockPresentation.orientedR,BlockPresentation.flipEdge, Bool.not_true,
      Bool.not_false, linkDirection,allLink,SimpleGraph.sum_adj_inl,SimpleGraph.sum_adj_inr]
  all_goals first | exact True.intro | exact ⟨Subtype.prop _,rfl,rfl⟩

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

theorem ribbon_outer_iff (a : D.ActiveDart) :
    (d.concreteRibbon hr D b hb).IsOuter a ↔ a.val ∈ D.boundary :=
  D.active_boundary_iff hb a

theorem ribbon_color (a : D.ActiveDart) :
    (d.concreteRibbon hr D b hb).color (cl (d.concreteRibbon hr D b hb).vertexPerm a) =
      d.linkColor hr (d.dartDirection hr D a) := by
  change (D.activeColor (d.presentation hr).vertexColor) (cl (D.activeReverse*D.activeNext) a) = _
  rw [TriangleFilling.activeColor,descend_cl]
  exact (d.linkDirection_color hr (D.label a)).symm

theorem ribbon_direction_step (a : D.ActiveDart) :
    d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm a) =
      d.linkDirection hr ((d.presentation hr).flipEdge (D.label (D.next a))) := by
  change d.linkDirection hr (D.label (D.reverse (D.next a))) = _
  rw [D.reverse_label]

theorem ribbon_adj (a : D.ActiveDart)
    (ha : ¬(d.concreteRibbon hr D b hb).IsOuter a) :
    (d.allLink hr).Adj (d.dartDirection hr D a)
      (d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm a)) := by
  rw [d.ribbon_direction_step hr D b hb a]
  exact d.face_corner_adj hr (D.triangular a a.property
    (fun h => ha ((d.ribbon_outer_iff hr D b hb a).mpr h))).2.2

theorem ribbon_reduced (hD : IsEmpty D.Dipole) (a : D.ActiveDart)
    (ha : ¬(d.concreteRibbon hr D b hb).IsOuter a)
    (ha' : ¬(d.concreteRibbon hr D b hb).IsOuter ((d.concreteRibbon hr D b hb).vertexPerm a)) :
    d.dartDirection hr D a ≠
      d.dartDirection hr D ((d.concreteRibbon hr D b hb).vertexPerm
        ((d.concreteRibbon hr D b hb).vertexPerm a)) := by
  intro he
  apply D.noDipole_link_reduced
    (fun _ _ _ => BlockPresentation.TriangleFace.colors _)
    (d.presentation hr).flipEdge_flipEdge
    (fun _ _ _ => BlockPresentation.TriangleFace.mirror _)
    (fun _ _ _ _ => BlockPresentation.TriangleFace.unique _) hD a a.property
    (fun h => ha ((d.ribbon_outer_iff hr D b hb a).mpr h))
    (fun h => ha' ((d.ribbon_outer_iff hr D b hb _).mpr h))
  exact d.linkDirection_injective hr he

theorem ribbon_closed (a : D.ActiveDart)
    (p : (d.allLink hr).Walk (d.dartDirection hr D a) (d.dartDirection hr D a))
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    10 ≤ TriangleRibbon.weight ((d.concreteRibbon hr D b hb).color
      (cl (d.concreteRibbon hr D b hb).vertexPerm a)) * p.length := by
  rw [d.ribbon_color hr D b hb a]
  exact le_trans (by norm_num) (d.allLink_closed hr _ p hn hp)

end Release075.MarkedLineData

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Rectangles ----
namespace OAI

namespace Release075.MarkedLineData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem rectangle_turn_large (i : d.Label) (u u' v v' : Fin r)
    (hu : u ≠ u') (hv : v ≠ v')
    (a b : (d.presentation hr).OrientedEdge)
    (ha : a ∈ [(d.presentation hr).orientedX i u v,
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u' v),
      (d.presentation hr).orientedX i u' v',
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u v')])
    (hb : b ∈ [(d.presentation hr).orientedX i u v,
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u' v),
      (d.presentation hr).orientedX i u' v',
      (d.presentation hr).flipEdge ((d.presentation hr).orientedX i u v')])
    (ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge b) =
      (d.presentation hr).edgeTarget a)
    (p : (d.allLink hr).Walk (d.linkDirection hr ((d.presentation hr).flipEdge b))
      (d.linkDirection hr a)) (hp : ReducedWalk p) :
    5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr a)) * p.length := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl|rfl|rfl|rfl
  all_goals rcases hb with rfl|rfl|rfl|rfl
  all_goals simp only [BlockPresentation.orientedX,BlockPresentation.flipEdge,
    BlockPresentation.edgeTarget,Bool.not_true,Bool.not_false] at ht
  all_goals cases ht
  all_goals
    first
    | exact d.x_turn_large hr i u v u' v true false rfl
        (by intro he; exact hu (congrArg Prod.fst he)) p hp
    | exact d.x_turn_large hr i u v u v' true false rfl
        (by intro he; exact hv (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u' v u v false true rfl
        (by intro he; exact hu.symm (congrArg Prod.fst he)) p hp
    | exact d.x_turn_large hr i u' v u' v' false true rfl
        (by intro he; exact hv (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u' v' u' v true false rfl
        (by intro he; exact hv.symm (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u' v' u v' true false rfl
        (by intro he; exact hu.symm (congrArg Prod.fst he)) p hp
    | exact d.x_turn_large hr i u v' u v false true rfl
        (by intro he; exact hv.symm (congrArg Prod.snd he)) p hp
    | exact d.x_turn_large hr i u v' u' v' false true rfl
        (by intro he; exact hu (congrArg Prod.fst he)) p hp

/-- Every actual rectangular word in the fixed presentation is nontrivial:
nullhomotopy gives a minimal labelled planar filling, whose reduced link sectors
contradict its Euler-characteristic-one angular identity. -/
theorem rectangular_nontriviality : d.RectangularNontriviality hr := by
  intro i u u' v v' hu hv he
  have hf := (d.presentation hr).rectangle_fillable_of_eq_one i u u' v v' he
  obtain ⟨D,hD⟩ := TriangleFilling.exists_noDipole hf
  have hn : D.boundary ≠ [] := by
    intro hz
    have hh := D.boundary_word
    rw [hz] at hh
    cases hh
  obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil D.boundary hn
  apply (d.concreteRibbon hr D b hb).not_all_turns_geodesic
    (d.allLink hr) (d.dartDirection hr D)
    (d.ribbon_adj hr D b hb) (d.ribbon_reduced hr D b hb hD)
    (d.ribbon_closed hr D b hb)
  intro a ha p hp
  have ha' : a.val ∈ D.boundary := (d.ribbon_outer_iff hr D b hb a).mp ha
  have hb' : D.next a.val ∈ D.boundary := (D.boundary_cycle.mem_iff a.val).mpr ha'
  have hal : D.label a.val ∈ _ := List.mem_map.mpr ⟨a.val,ha',rfl⟩
  have hbl : D.label (D.next a.val) ∈ _ := List.mem_map.mpr ⟨D.next a.val,hb',rfl⟩
  rw [D.boundary_word] at hal hbl
  rw [d.ribbon_color hr D b hb a]
  have ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge (D.label (D.next a.val))) =
      (d.presentation hr).edgeTarget (D.label a.val) := by
    rw [← D.reverse_label]
    exact D.color_next a.val
  have hs := d.ribbon_direction_step hr D b hb a
  let p' := p.copy hs rfl
  have hp' : ReducedWalk p' := by
    intro j hj
    simpa only [p',SimpleGraph.Walk.getVert_copy] using
      hp j (by simpa only [p',SimpleGraph.Walk.length_copy] using hj)
  have hh := d.rectangle_turn_large hr i u u' v v' hu hv _ _ hal hbl ht p' hp'
  have hlen : p'.length = p.length := SimpleGraph.Walk.length_copy p hs rfl
  change 5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr (D.label a.val))) * p'.length at hh
  rw [hlen] at hh
  exact hh

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

end Release075.MarkedLineData

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.MarkedLineData
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.MarkedLineData.rectangular_nontriviality := @_root_.OAI.Release075.MarkedLineData.rectangular_nontriviality

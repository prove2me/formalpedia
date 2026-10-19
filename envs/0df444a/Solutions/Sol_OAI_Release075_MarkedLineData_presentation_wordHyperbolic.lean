-- Prove2me | solution 1 for OAI.Release075.MarkedLineData.presentation_wordHyperbolic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:19:16.062677+00:00
-- url     : https://prove2.me/submissions/6d117da9-d21c-4b62-82da-475a004407bf

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Hyperbolicity.lean:L17-L49
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.MarkedLineData.presentation_wordHyperbolic. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
import Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric
import Definitions.Def_OAI_GroupTheory_Hyperbolic_ThinTriangles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CayleyMetric
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CayleyPaths
import Theorems.Thm_OAI_Release075_BlockPresentation_exists_path_word
import Theorems.Thm_OAI_Release075_BlockPresentation_rawMove_wordValue
import Theorems.Thm_OAI_Release075_Discrete_Metric_form_triangle_bound
import Theorems.Thm_OAI_Release075_Discrete_Path_triangleNear_of_cochainBound
import Theorems.Thm_OAI_Release075_Fillable_app
import Theorems.Thm_OAI_Release075_MarkedLineData_exists_lifted_linear_filling
import Theorems.Thm_OAI_Release075_TriangleFilling_edge_sum_bound
import Theorems.Thm_OAI_Release075_TriangleFilling_fold

-- ---- from OAI.GroupTheory.Hyperbolic.Presentation ----
namespace OAI

namespace Release075

namespace ShiftScheme
variable {I P B : Type*} {r : ℕ} {inc : P → Finset I} (d : ShiftScheme I P B r inc)

end ShiftScheme

end Release075

namespace Release075

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

end BlockPresentation

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

theorem generators_finite [Fintype I] [Fintype B] : (Set.range d.edge).Finite :=
  Set.finite_range d.edge

end BlockPresentation
end Release075

namespace Release075
noncomputable section
open scoped BigOperators
attribute [local instance] OAI.Release075.instDecidableEq_oAI
namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

end MarkedLineData

end
end Release075

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.WordPaths ----
namespace OAI

namespace Release075
/-! A combinatorial fundamental groupoid of the **un-collapsed** triangle complex.
The quotient imposes only its triangular faces. Tree edges are used for basing,
not mistaken for triangular two-cells in a van Kampen diagram. -/
namespace BlockPresentation
open CategoryTheory

variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

/-! A finite, purely combinatorial nullhomotopy follows from equality in the actual
fundamental groupoid. This is the starting point for the planar reduction,
not an assumed existence of a reduced diagram. -/
/-- Equality in the two-stage groupoid quotient is **exactly** a finite chain of
triangle moves and backtrack moves in arbitrary typed path contexts. -/
theorem raw_equality_iff {a c : d.RawPaths} (p q : a ⟶ c) :
    d.rawToFundamental.map p = d.rawToFundamental.map q ↔ d.RawHomotopic p q := by
  constructor
  · intro h
    have hh := congrArg (d.fundamentalToRawQuotient.map) h
    change (CategoryTheory.Quotient.functor d.RawMove).map p =
      (CategoryTheory.Quotient.functor d.RawMove).map q at hh
    exact Quot.eq.mp hh
  · intro h
    have hh : (CategoryTheory.Quotient.functor d.RawMove).map p =
        (CategoryTheory.Quotient.functor d.RawMove).map q := Quot.eq.mpr h
    exact congrArg (d.rawQuotientToFundamental.map) hh

end BlockPresentation
end Release075

end OAI

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

end Release075.BlockPresentation

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem TriangleFace.typed {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.edgeTarget (d.flipEdge b) = d.edgeTarget a ∧
    d.edgeTarget (d.flipEdge c) = d.edgeTarget b ∧
    d.edgeTarget (d.flipEdge a) = d.edgeTarget c := by
  cases h <;> simp [orientedL,orientedX,orientedR,flipEdge,edgeTarget]

end Release075.BlockPresentation

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.LiftedFilling ----
namespace OAI

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem liftedTarget_ne (e : d.LiftedEdge) :
    d.liftedTarget e ≠ d.liftedTarget (d.liftedFlip e) := by
  intro h
  exact d.edgeTarget_ne e.1 (congrArg Prod.fst h)

theorem LiftedFace.rotate {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) :
    d.LiftedFace b c a := ⟨TriangleFace.rotate d h.1,h.2.2.1,h.2.2.2,h.2.1⟩

theorem LiftedFace.mirror {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) :
    d.LiftedFace (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b) := by
  refine ⟨TriangleFace.mirror d h.1,?_,?_,?_⟩
  · simpa only [liftedFlip_flip] using h.2.2.2.symm
  · simpa only [liftedFlip_flip] using h.2.2.1.symm
  · simpa only [liftedFlip_flip] using h.2.1.symm

theorem liftWord_append (g : d.GroupType) (u v) :
    d.liftWord g (u++v) = d.liftWord g u ++ d.liftWord (g*d.wordValue u) v := by
  induction u generalizing g with
  | nil => simp only [List.nil_append,liftWord_nil,wordValue_nil,mul_one]
  | cons e u ih =>
    simp only [List.cons_append,liftWord_cons,ih,wordValue_cons,mul_assoc]

theorem liftWord_typed {a c : d.Vertex} {w : List d.OrientedEdge}
    (h : WordPath d.flipEdge d.edgeTarget a c w) (g : d.GroupType) :
    WordPath d.liftedFlip d.liftedTarget (a,g) (c,g*d.wordValue w) (d.liftWord g w) := by
  induction h generalizing g with
  | nil a => simpa only [wordValue_nil,mul_one,liftWord_nil] using
      (WordPath.nil (flip := d.liftedFlip) (color := d.liftedTarget) (a,g))
  | @cons e tgt w h ih =>
    simp only [liftWord_cons,wordValue_cons,← mul_assoc]
    have hh := WordPath.cons (e,g*d.edgeValue e) (ih _)
    simpa only [liftedTarget,liftedFlip,mul_inv_cancel_right] using hh

theorem TriangleFace.value {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.edgeValue a * d.edgeValue b * d.edgeValue c = 1 := by
  cases h <;>
    simp only [edgeValue,orientedL,orientedX,orientedR,flipEdge,Bool.not_true,
      Bool.false_eq_true,↓reduceIte]
  all_goals
    rw [show d.edge (.inl _) = _ from d.triangle_relation _ _ _ _]
  all_goals simp only [l,rr,edge] at *
  all_goals group

theorem TriangleFace.lift {a b c : d.OrientedEdge} (h : d.TriangleFace a b c)
    (g : d.GroupType) :
    d.LiftedFace (a,g*d.edgeValue a) (b,g*d.edgeValue a*d.edgeValue b) (c,g) := by
  obtain ⟨hab,hbc,hca⟩ := TriangleFace.typed d h
  have hv := TriangleFace.value d h
  refine ⟨h,Prod.ext hab ?_,Prod.ext hbc ?_,Prod.ext hca ?_⟩
  · change g*d.edgeValue a*d.edgeValue b*(d.edgeValue b)⁻¹ = g*d.edgeValue a
    group
  · change g*(d.edgeValue c)⁻¹ = g*d.edgeValue a*d.edgeValue b
    rw [mul_assoc]
    exact congrArg (g*·) (eq_inv_iff_mul_eq_one.mpr hv).symm
  · change g*d.edgeValue a*(d.edgeValue a)⁻¹ = g
    group

theorem rawHomotopic_wordValue {a c : d.RawPaths} {p q : a ⟶ c}
    (h : d.RawHomotopic p q) : d.wordValue (d.rawWord p) = d.wordValue (d.rawWord q) := by
  induction h with
  | rel p q h =>
    cases h with
    | intro a c u p q v h =>
      simp only [rawWord_comp,wordValue_append,d.rawMove_wordValue h]
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q s _ _ ih ih' => exact ih.trans ih'

theorem rawMove_lifted_filled {a c : d.RawPaths} {p q : a ⟶ c}
    (h : d.RawMove p q) (g : d.GroupType) :
    FilledBetween d.liftedFlip d.liftedTarget d.LiftedFace
      (d.liftWord g (d.rawWord p)) (d.liftWord g (d.rawWord q)) := by
  cases h with
  | backtrack h =>
    cases h with
    | step a c f =>
      change Fillable d.liftedFlip d.liftedTarget d.LiftedFace
        (reverseWord d.liftedFlip (d.liftWord g
          [d.orientedLabel f,d.orientedLabel (Quiver.reverse f)]))
      simp only [liftWord_cons,liftWord_nil,orientedLabel_reverse,edgeValue_flip,
        reverseWord_cons,reverseWord_nil,List.nil_append,List.singleton_append]
      have he : (d.flipEdge (d.orientedLabel f),g*d.edgeValue (d.orientedLabel f)*
          (d.edgeValue (d.orientedLabel f))⁻¹) =
          d.liftedFlip (d.orientedLabel f,g*d.edgeValue (d.orientedLabel f)) := rfl
      rw [he,d.liftedFlip_flip]
      exact Fillable.backtrack d.liftedFlip_flip _
  | triangle b i u v =>
    have hh := TriangleFace.lift d (TriangleFace.pos₀ (d := d) b i u v) g
    change Fillable d.liftedFlip d.liftedTarget d.LiftedFace
      (d.liftWord g [d.orientedL b i u v,d.orientedX i u v] ++
        reverseWord d.liftedFlip (d.liftWord g [d.orientedR b i u v]))
    simp only [liftWord_cons,liftWord_nil,reverseWord_cons,reverseWord_nil,List.nil_append,
      List.cons_append]
    have hr : d.liftedFlip (d.orientedR b i u v,g*d.edgeValue (d.orientedR b i u v)) =
        (d.flipEdge (d.orientedR b i u v),g) := by
      simp only [liftedFlip,mul_inv_cancel_right]
    rw [hr]
    exact ⟨TriangleFilling.triangle d.liftedFlip_flip
      (fun _ _ _ => LiftedFace.rotate d) _ _ _
      hh.2.1.symm hh.2.2.1.symm hh.2.2.2.symm (LiftedFace.mirror d hh)⟩

theorem rawHomotopic_lifted_filled {a c : d.RawPaths} {p q : a ⟶ c}
    (h : d.RawHomotopic p q) (g : d.GroupType) :
    FilledBetween d.liftedFlip d.liftedTarget d.LiftedFace
      (d.liftWord g (d.rawWord p)) (d.liftWord g (d.rawWord q)) := by
  induction h generalizing g with
  | rel p q h =>
    cases h with
    | intro a c u p q v h =>
      have he := d.rawMove_wordValue h
      have hu := d.liftWord_typed (d.rawWord_typed u) g
      have hp := d.liftWord_typed (d.rawWord_typed p) (g*d.wordValue (d.rawWord u))
      have hq := d.liftWord_typed (d.rawWord_typed q) (g*d.wordValue (d.rawWord u))
      rw [← he] at hq
      have hv := d.liftWord_typed (d.rawWord_typed v)
        (g*d.wordValue (d.rawWord u)*d.wordValue (d.rawWord p))
      have hf := FilledBetween.whiskerLeft d.liftedFlip_flip hu (hp.append hv) (hq.append hv)
        (FilledBetween.whiskerRight d.liftedFlip_flip hp hq hv
          (d.rawMove_lifted_filled h (g*d.wordValue (d.rawWord u))))
      simpa only [rawWord_comp,liftWord_append,wordValue_append,← he,mul_assoc,List.append_assoc]
        using hf
  | refl p => exact FilledBetween.refl d.liftedFlip_flip (d.liftWord_typed (d.rawWord_typed p) g)
  | symm p q _ ih =>
    exact FilledBetween.symm d.liftedFlip_flip (fun _ _ _ => LiftedFace.mirror d) (ih g)
  | trans p q s hpq hqs ih ih' =>
    have hq := d.liftWord_typed (d.rawWord_typed q) g
    have hs := d.liftWord_typed (d.rawWord_typed s) g
    rw [← d.rawHomotopic_wordValue hpq] at hq
    rw [← d.rawHomotopic_wordValue hqs,← d.rawHomotopic_wordValue hpq] at hs
    exact FilledBetween.trans d.liftedFlip_flip d.liftedTarget_ne
      (d.liftWord_typed (d.rawWord_typed p) g) hq hs (ih g) (ih' g)

theorem nullhomotopic_lifted_fillable {a : d.RawPaths} {p : a ⟶ a}
    (h : d.RawHomotopic p (𝟙 a)) (g : d.GroupType) :
    Fillable d.liftedFlip d.liftedTarget d.LiftedFace (d.liftWord g (d.rawWord p)) := by
  simpa only [FilledBetween,rawWord_nil,liftWord_nil,reverseWord_nil,List.append_nil] using
    d.rawHomotopic_lifted_filled h g

end Release075.BlockPresentation

namespace Release075.TriangleFilling
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w : List d.LiftedEdge}

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).LiftedEdge}

end Release075.MarkedLineData

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.BasedWords ----
namespace OAI

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

private theorem based_comp_formula {C : Type*} [Groupoid C] {o a b c : C}
    (A : o ⟶ a) (B : o ⟶ b) (C' : o ⟶ c) (f : a ⟶ b) (g : b ⟶ c) :
    (MulOpposite.op (End.of (A ≫ f ≫ Groupoid.inv B)) : (End o)ᵐᵒᵖ) *
      MulOpposite.op (End.of (B ≫ g ≫ Groupoid.inv C')) =
      MulOpposite.op (End.of (A ≫ (f ≫ g) ≫ Groupoid.inv C')) := by
  apply MulOpposite.unop_injective
  change (A ≫ f ≫ Groupoid.inv B) ≫ (B ≫ g ≫ Groupoid.inv C') = _
  simp [Category.assoc,Groupoid.inv_eq_inv]

private theorem based_id_formula {C : Type*} [Groupoid C] {o a : C} (A : o ⟶ a) :
    (1 : (End o)ᵐᵒᵖ) = MulOpposite.op (End.of (A ≫ (𝟙 a) ≫ Groupoid.inv A)) := by
  apply MulOpposite.unop_injective
  change 𝟙 _ = A ≫ (𝟙 a) ≫ Groupoid.inv A
  simp

private theorem based_eq_id {C : Type*} [Groupoid C] {o a : C} (A : o ⟶ a)
    (f : a ⟶ a) (h : A ≫ f ≫ Groupoid.inv A = 𝟙 o) : f = 𝟙 a := by
  have hh := congrArg (fun f => Groupoid.inv A ≫ f ≫ A) h
  simpa [Groupoid.inv_eq_inv,Category.assoc] using hh

theorem based_oriented_arrow {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.toFundamentalGroup (d.edgeValue (d.orientedLabel f)) =
      MulOpposite.op (End.of (d.basePath a ≫ d.rawToFundamental.map f.toPath ≫
        Groupoid.inv (d.basePath c))) := by
  change d.Arrow a c ⊕ d.Arrow c a at f
  rcases f with f | f
  · change d.Arrow a c at f
    cases f with
    | x e => exact d.toFundamentalGroup_edge (.inl e)
    | l e =>
      have h := d.toFundamentalGroup_edge (.inr (.inl e))
      change d.toFundamentalGroup (d.edge (.inr (.inl e))) =
        MulOpposite.op (End.of ((𝟙 _) ≫ d.pathL e ≫ Groupoid.inv d.treePathV))
      simpa only [Category.id_comp,basedEdge] using h
    | rr e =>
      have h := d.toFundamentalGroup_edge (.inr (.inr e))
      change d.toFundamentalGroup (d.edge (.inr (.inr e))) =
        MulOpposite.op (End.of ((𝟙 _) ≫ d.pathR e ≫ Groupoid.inv d.treePathW))
      simpa only [Category.id_comp,basedEdge] using h
  · change d.Arrow c a at f
    cases f with
    | x e =>
      change d.toFundamentalGroup ((d.edge (.inl e))⁻¹) = _
      rw [map_inv,d.toFundamentalGroup_edge]
      apply MulOpposite.unop_injective
      change Groupoid.inv (d.treePathV ≫ d.pathX e ≫ Groupoid.inv d.treePathW) =
        d.treePathW ≫ Groupoid.inv (d.pathX e) ≫ Groupoid.inv d.treePathV
      simp [Groupoid.inv_eq_inv,Category.assoc]
    | l e =>
      change d.toFundamentalGroup ((d.edge (.inr (.inl e)))⁻¹) = _
      rw [map_inv,d.toFundamentalGroup_edge]
      apply MulOpposite.unop_injective
      change Groupoid.inv (d.pathL e ≫ Groupoid.inv d.treePathV) =
        d.treePathV ≫ Groupoid.inv (d.pathL e) ≫ Groupoid.inv (𝟙 _)
      simp [Groupoid.inv_eq_inv]
    | rr e =>
      change d.toFundamentalGroup ((d.edge (.inr (.inr e)))⁻¹) = _
      rw [map_inv,d.toFundamentalGroup_edge]
      apply MulOpposite.unop_injective
      change Groupoid.inv (d.pathR e ≫ Groupoid.inv d.treePathW) =
        d.treePathW ≫ Groupoid.inv (d.pathR e) ≫ Groupoid.inv (𝟙 _)
      simp [Groupoid.inv_eq_inv]

theorem based_rawWord {a c : Quiver.Symmetrify d.Vertex} (p : Quiver.Path a c) :
    d.toFundamentalGroup (d.wordValue (d.rawWord p)) =
      MulOpposite.op (End.of (d.basePath a ≫ d.rawToFundamental.map p ≫
        Groupoid.inv (d.basePath c))) := by
  induction p with
  | nil =>
    change 1 = MulOpposite.op (End.of (d.basePath a ≫
      d.rawToFundamental.map (𝟙 (d.rawVertex a)) ≫ Groupoid.inv (d.basePath a)))
    exact (based_id_formula (d.basePath a)).trans
      (congrArg (fun f : d.vertex a ⟶ d.vertex a =>
          MulOpposite.op (End.of (d.basePath a ≫ f ≫ Groupoid.inv (d.basePath a))))
        (CategoryTheory.Functor.map_id d.rawToFundamental (d.rawVertex a)).symm)
  | @cons c e p f ih =>
    change d.toFundamentalGroup (d.wordValue (d.rawWord p ++ [d.orientedLabel f])) = _
    rw [wordValue_append,wordValue_cons,wordValue_nil,mul_one,map_mul,ih,d.based_oriented_arrow]
    exact (based_comp_formula (d.basePath a) (d.basePath c) (d.basePath e) _ _).trans
      (congrArg (fun z : d.vertex a ⟶ d.vertex e =>
          MulOpposite.op (End.of (d.basePath a ≫ z ≫ Groupoid.inv (d.basePath e))))
        (CategoryTheory.Functor.map_comp d.rawToFundamental
          (show d.rawVertex a ⟶ d.rawVertex c from p)
          (show d.rawVertex c ⟶ d.rawVertex e from f.toPath)).symm)

theorem rawWord_nullhomotopic {a : Quiver.Symmetrify d.Vertex}
    (p : Quiver.Path a a) (h : d.wordValue (d.rawWord p) = 1) :
    d.RawHomotopic p (𝟙 (d.rawVertex a)) := by
  have hh := congrArg d.toFundamentalGroup h
  rw [d.based_rawWord,map_one] at hh
  have hu := congrArg MulOpposite.unop hh
  change d.basePath a ≫ d.rawToFundamental.map p ≫ Groupoid.inv (d.basePath a) = 𝟙 _ at hu
  apply (d.raw_equality_iff _ _).mp
  exact (based_eq_id (d.basePath a) _ hu).trans
    (CategoryTheory.Functor.map_id d.rawToFundamental (d.rawVertex a)).symm

end Release075.BlockPresentation

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem WordPath.exists_raw {a c : d.Vertex} {w : List d.OrientedEdge}
    (h : Release075.WordPath d.flipEdge d.edgeTarget a c w) :
    ∃ p : (d.rawVertex a ⟶ d.rawVertex c), d.rawWord p = w := by
  induction h with
  | nil a => exact ⟨𝟙 _,rfl⟩
  | cons e h ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨(d.rawEdge e).toPath ≫ p,?_⟩
    exact (d.rawWord_path_comp (d.rawEdge e).toPath p).trans
      (congrArg₂ List.append
        ((d.rawWord_toPath (d.rawEdge e)).trans
          (congrArg (fun e => [e]) (d.orientedLabel_rawEdge e))) hp)

theorem typed_nullword_lifted_fillable {a : d.Vertex} {w : List d.OrientedEdge}
    (ht : Release075.WordPath d.flipEdge d.edgeTarget a a w)
    (hv : d.wordValue w = 1) (g : d.GroupType) :
    Fillable d.liftedFlip d.liftedTarget d.LiftedFace (d.liftWord g w) := by
  obtain ⟨p,rfl⟩ := WordPath.exists_raw d ht
  exact d.nullhomotopic_lifted_fillable (d.rawWord_nullhomotopic p hv) g

end Release075.BlockPresentation

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem WordPath.forget {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    WordPath d.flipEdge d.edgeTarget x.1 y.1 (w.map Prod.fst) := by
  induction hw with
  | nil x => exact .nil _
  | cons e hw ih => exact .cons e.1 ih

theorem WordPath.displacement {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    x.2 * d.wordValue (w.map Prod.fst) = y.2 := by
  induction hw with
  | nil x => simp
  | cons e hw ih =>
    change (e.2*(d.edgeValue e.1)⁻¹) *
      (d.edgeValue e.1 * d.wordValue (_:List d.OrientedEdge)) = _
    simpa only [mul_assoc,inv_mul_cancel_left,liftedTarget] using ih

theorem WordPath.liftWord_eq {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    d.liftWord x.2 (w.map Prod.fst) = w := by
  induction hw with
  | nil x => rfl
  | cons e hw ih =>
    change d.liftWord (e.2 * (d.edgeValue e.1)⁻¹) (e.1::_) = e::_
    simpa only [liftWord_cons,inv_mul_cancel_right,Prod.mk.eta,liftedTarget] using congrArg (e::·) ih

theorem lifted_closed_fillable {x : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x x w) :
    Fillable d.liftedFlip d.liftedTarget d.LiftedFace w := by
  have hv : d.wordValue (w.map Prod.fst) = 1 :=
    mul_left_cancel ((WordPath.displacement d hw).trans (mul_one x.2).symm)
  have hf := d.typed_nullword_lifted_fillable (WordPath.forget d hw) hv x.2
  rwa [WordPath.liftWord_eq d hw] at hf

end Release075.BlockPresentation

namespace Release075.FullFilling
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w w' : List d.LiftedEdge}
  (D : FullFilling d.liftedFlip d.liftedTarget d.LiftedFace w)

end Release075.FullFilling

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.DiscreteMetric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075.Discrete

variable {V : Type} (M : Metric V)

namespace Path
variable {M} {a b c : V}

end Path

namespace Metric
variable {M}

theorem form_flip (o a : V) (R : ℕ) (x y : V) : M.form o a R y x = -M.form o a R x y := by
  unfold form
  ring

end Metric
end Release075.Discrete

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c d e f : V}

end Path

end Release075.Discrete

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.CayleyMetric ----
namespace OAI

namespace Release075.Discrete
variable {V : Type} (X : SimpleGraph V) (hX : X.Connected)

theorem graphMetric_geodesicSpace : GeodesicSpace (graphMetric X hX) := by
  intro a b
  obtain ⟨p,hp⟩ := hX.exists_walk_length_eq_dist a b
  exact ⟨walkPath X hX p,hp⟩

end Release075.Discrete

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem cayley_dist_mul (g : d.GroupType) (e : d.OrientedEdge) :
    d.cayleyMetric.dist g (g*d.edgeValue e) ≤ 1 := by
  by_cases he : g = g*d.edgeValue e
  · rw [←he]
    exact (d.cayleyMetric.self g).le.trans (by omega)
  · suffices d.cayley.Adj g (g*d.edgeValue e) by
      exact (d.cayley.dist_eq_one_iff_adj.mpr this).le
    apply (SimpleGraph.mulCayley_adj' _ _ _).mpr
    refine ⟨he,d.edge e.1,⟨e.1,rfl⟩,?_⟩
    rcases e with ⟨e,s⟩
    cases s
    · right
      simp [edgeValue]
    · left
      simp [edgeValue]

theorem cayley_dist_liftedEdge (e : d.LiftedEdge) :
    d.cayleyMetric.dist (d.liftedFlip e).2 e.2 ≤ 1 := by
  have h := d.cayley_dist_mul (e.2*(d.edgeValue e.1)⁻¹) e.1
  simpa only [inv_mul_cancel_right,liftedFlip] using h

theorem liftedForm_flip (o a : d.GroupType) (T : ℕ) (e : d.LiftedEdge) :
    d.liftedForm o a T (d.liftedFlip e) = -d.liftedForm o a T e := by
  rw [liftedForm,d.liftedFlip_flip,Discrete.Metric.form_flip]
  rfl

theorem liftedForm_face_bound (o z : d.GroupType) (T : ℕ)
    {a b c : d.LiftedEdge} (hf : d.LiftedFace a b c) :
    |d.liftedForm o z T a+d.liftedForm o z T b+d.liftedForm o z T c| ≤ 2 := by
  have hab := congrArg Prod.snd hf.2.1
  have hbc := congrArg Prod.snd hf.2.2.1
  have hca := congrArg Prod.snd hf.2.2.2
  change (d.liftedFlip b).2 = a.2 at hab
  change (d.liftedFlip c).2 = b.2 at hbc
  change (d.liftedFlip a).2 = c.2 at hca
  have ha := d.cayley_dist_liftedEdge a
  have hb := d.cayley_dist_liftedEdge b
  have hc := d.cayley_dist_liftedEdge c
  rw [hca] at ha
  rw [hab] at hb
  rw [hbc] at hc
  simpa only [liftedForm,hab,hbc,hca] using
    d.cayleyMetric.form_triangle_bound o z c.2 a.2 b.2 T ha hb hc

end Release075.BlockPresentation

namespace Release075.TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem liftedForm_loop_bound {x : (d.presentation hr).LiftedVertex}
    {w : List (d.presentation hr).LiftedEdge}
    (hw : WordPath (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget x x w)
    (o a : (d.presentation hr).GroupType) (T : ℕ) :
    |(w.map ((d.presentation hr).liftedForm o a T)).sum| ≤ 38*w.length := by
  obtain ⟨D,hD⟩ := d.exists_lifted_linear_filling hr ((d.presentation hr).lifted_closed_fillable hw)
  have h := D.edge_sum_bound ((d.presentation hr).liftedForm o a T)
    ((d.presentation hr).liftedForm_flip o a T)
    (fun _ _ _ hf => (d.presentation hr).liftedForm_face_bound o a T hf)
  omega

end Release075.MarkedLineData

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Hyperbolicity ----
namespace OAI

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

/-- Honest linear filling estimate on *all* lazy Cayley loops, not just original edges. -/
theorem presentation_cochainBound : Discrete.CochainBound (d.presentation hr).cayleyMetric 114 := by
  intro o a x T p
  obtain ⟨w,hw,hlen,hF⟩ := (d.presentation hr).exists_path_word p
  have h := d.liftedForm_loop_bound hr hw o a T
  rw [hF] at h
  have hlen' : (w.length:ℤ) ≤ 3*p.length := by exact_mod_cast hlen
  omega

/-- The constructed finite presentation is word hyperbolic in the literal thin-triangle sense. -/
theorem presentation_wordHyperbolic : WordHyperbolic (d.presentation hr).GroupType := by
  let P := d.presentation hr
  refine ⟨Set.range P.edge,P.generators_finite,P.cayley_connected,10000*(114+1),?_⟩
  intro x y z p q s hp hq hs
  let p' := Discrete.walkPath P.cayley P.cayley_connected p
  let q' := Discrete.walkPath P.cayley P.cayley_connected q
  let s' := Discrete.walkPath P.cayley P.cayley_connected s.reverse
  have hp' : p'.Geodesic := hp
  have hq' : q'.Geodesic := hq
  have hs' : s'.Geodesic := by
    change s.reverse.length = P.cayley.dist x z
    rw [SimpleGraph.Walk.length_reverse,P.cayley.dist_comm]
    exact hs
  have hthin := Discrete.Path.triangleNear_of_cochainBound
    (Discrete.graphMetric_geodesicSpace P.cayley P.cayley_connected)
    (d.presentation_cochainBound hr) hp' hq' hs'
  have hpMem (v : P.GroupType) : p'.Mem v ↔ v ∈ p.support :=
    Discrete.walkPath_mem P.cayley P.cayley_connected p
  have hqMem (v : P.GroupType) : q'.Mem v ↔ v ∈ q.support :=
    Discrete.walkPath_mem P.cayley P.cayley_connected q
  have hsMem (v : P.GroupType) : s'.Mem v ↔ v ∈ s.support := by
    rw [Discrete.walkPath_mem,SimpleGraph.Walk.support_reverse,List.mem_reverse]
  refine ⟨?_,?_,?_⟩
  · intro v hv
    obtain ⟨w,hw,hd⟩ := hthin.1 v ((hpMem v).mpr hv)
    exact ⟨w,hw.imp ((hqMem w).mp) ((hsMem w).mp),hd⟩
  · intro v hv
    obtain ⟨w,hw,hd⟩ := hthin.2.1 v ((hqMem v).mpr hv)
    exact ⟨w,hw.imp ((hsMem w).mp) ((hpMem w).mp),hd⟩
  · intro v hv
    obtain ⟨w,hw,hd⟩ := hthin.2.2 v ((hsMem v).mpr hv)
    exact ⟨w,hw.imp ((hpMem w).mp) ((hqMem w).mp),hd⟩

end Release075.MarkedLineData

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.MarkedLineData


theorem solution : type_of% @_root_.OAI.Release075.MarkedLineData.presentation_wordHyperbolic := @_root_.OAI.Release075.MarkedLineData.presentation_wordHyperbolic

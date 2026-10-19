-- Prove2me | solution 2 for OAI.Release075.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:21:41.270983+00:00
-- url     : https://prove2.me/submissions/4b76a0d1-9bf7-4e43-b7e4-564b700f245f

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Main.lean:L7-L16
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Release075.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Release075_main) verbatim and is proved by it.
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
import Theorems.Thm_OAI_Release075_BlockPresentation_rawMove_wordValue
import Theorems.Thm_OAI_Release075_Fillable_app
import Theorems.Thm_OAI_Release075_FreeChain_cyclic_chain_obstruction
import Theorems.Thm_OAI_Release075_FullFilling_trace_cyclic
import Theorems.Thm_OAI_Release075_FullFilling_trace_edge
import Theorems.Thm_OAI_Release075_FullFilling_trace_unique
import Theorems.Thm_OAI_Release075_MarkedLineData_presentation_not_residuallyFinite
import Theorems.Thm_OAI_Release075_MarkedLineData_presentation_wordHyperbolic
import Theorems.Thm_OAI_Release075_MarkedLineData_rectangular_nontriviality
import Theorems.Thm_OAI_Release075_MarkedLineData_sphere_empty_of_noDipole
import Theorems.Thm_OAI_Release075_TriangleFilling_fold
import Theorems.Thm_OAI_Release075_large_prime_grid_outcome
import Theorems.Thm_OAI_Release075_retained_girth

-- ---- from OAI.GroupTheory.Hyperbolic.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

end CycleCandidate

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

end Degrees

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end EncodingIncidence

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype K] [Fintype V]

end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

omit [Fintype V] in
theorem mem_chosenLinePoints (a z : V) (d : Projectivization K V) :
    z ∈ chosenLinePoints a d ↔ OnChosenLine a z d := by
  simp only [chosenLinePoints, Finset.mem_image, Finset.mem_univ, true_and, OnChosenLine]

theorem incidence_not_deleted (S : Finset V) (ω : S → Projectivization K V) (z : V)
    (hz : z ∉ deletedPoints S ω) (a : S) (ha : PuncturedIncidence a.val z (ω a)) :
    a ∉ deletedMarks S ω := by
  intro hdel
  apply hz
  exact Finset.mem_biUnion.mpr ⟨a,hdel,(mem_chosenLinePoints a.val z (ω a)).mpr ha.2⟩

/-- Outside the discarded geometric lines, no incidence is changed by alteration. -/
theorem retainedIncidence_card (S : Finset V) (ω : S → Projectivization K V) (z : V)
    (hz : z ∉ deletedPoints S ω) : (retainedIncidence S ω z).card = pointDegree S ω z := by
  let e : {a : Retained S ω // PuncturedIncidence a.val.val z (ω a.val)} ≃
      {a : S // PuncturedIncidence a.val z (ω a)} :=
    {toFun := fun a => ⟨a.val.val,a.property⟩
     invFun := fun a => ⟨⟨a.val,incidence_not_deleted S ω z hz a.val a.property⟩,a.property⟩
     left_inv := fun a => rfl
     right_inv := fun a => rfl}
  have h := Fintype.card_congr e
  simpa only [Fintype.card_subtype,pointDegree,retainedIncidence] using h

/-- The exact degree threshold needed for the two-block partition. -/
theorem retainedIncidence_card_ge (S : Finset V) (ω : S → Projectivization K V) (T : ℕ)
    (z : V) (hz : z ∉ exceptionalPoints S ω T) : T ≤ (retainedIncidence S ω z).card := by
  have hz' := not_or.mp ((Finset.mem_union).not.mp hz)
  rw [retainedIncidence_card S ω z hz'.2]
  have hh := hz'.1
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hh

end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

end AlterationMean

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

end DimensionTwenty

attribute [instance] MarkedLineData.labelFintype

theorem exists_markedLineData :
    ∃ (q r : ℕ) (hq : q.Prime), let _ : Fact q.Prime := ⟨hq⟩
      0 < r ∧ r < q ∧ 100*100^20 ≤ r ∧ Nonempty (MarkedLineData q r) := by
  classical
  let r : ℕ := 200*200^20
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (1000*200^20*r^2+400)
  let : Fact q.Prime := ⟨hprime⟩
  let : Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q)) := Fintype.ofFinite _
  have hq200 : 200 ≤ q := by omega
  have hqbig : 1000*200^20*r^2 ≤ q := by omega
  have hr : 0 < r := by norm_num [r]
  have hrq : r < q := by
    have hh : r < 1000*200^20*r^2+400 := by norm_num [r]
    exact hh.trans_le hq
  have hrc : 100*100^20 ≤ r := by norm_num [r]
  obtain ⟨S,_,hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (ZMod q))) (n := q/100) (by
      simpa only [Finset.card_univ,ZMod.card] using Nat.div_le_self q 100)
  obtain ⟨ω,hω⟩ := large_prime_grid_outcome q r rfl hq200 hqbig S hS
  refine ⟨q,r,hprime,hr,hrq,hrc,⟨?_⟩⟩
  exact
    { scalarGrid := S
      grid_card := hS
      Label := Retained (gridMarks q S) ω
      mark := fun i => i.val.val
      direction := fun i => ω i.val
      marks_mem := fun i => Fintype.mem_piFinset.mp i.val.property
      marks_injective := fun _ _ h => Subtype.ext (Subtype.ext h)
      exceptional := exceptionalPoints (gridMarks q S) ω (4*r^2)
      degree := retainedIncidence_card_ge (gridMarks q S) ω (4*r^2)
      budget := by simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card] using hω
      girth := retained_girth (gridMarks q S) ω }

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

-- ---- from OAI.GroupTheory.Hyperbolic.Rectangles ----
namespace OAI

namespace Release075.MarkedLineData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

namespace Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).OrientedEdge}
variable (D : TriangleFilling (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
  (d.presentation hr).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

/-- The fixed presentation's non-residual-finiteness is now unconditional in
its finite incidence data; no rectangular nontriviality premise remains. -/
theorem actual_presentation_not_residuallyFinite (hq : r < q) (hq200 : 200 ≤ q) :
    ¬ Group.ResiduallyFinite (d.presentation hr).GroupType :=
  d.presentation_not_residuallyFinite hr hq hq200 (d.rectangular_nontriviality hr)

end Release075.MarkedLineData

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

end Release075.TriangleSphere

namespace Release075.TriangleSphere
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}

theorem noDipole_forgetLift {D : TriangleSphere d.liftedFlip d.liftedTarget d.LiftedFace}
    (h : IsEmpty D.Dipole) : IsEmpty D.forgetLift.Dipole := ⟨fun P => h.false P.lift⟩

end Release075.TriangleSphere

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem lifted_sphere_empty_of_noDipole
    (D : TriangleSphere (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace) (hD : IsEmpty D.Dipole) : IsEmpty D.Dart :=
  d.sphere_empty_of_noDipole hr D.forgetLift (TriangleSphere.noDipole_forgetLift hD)

end Release075.MarkedLineData

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.FullGluing ----
namespace OAI

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.FullFilling
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem trace_add {w : List E} (D : FullFilling flip color face w)
    (F H : E → E → E → M) : D.trace (fun a b c => F a b c + H a b c) = D.trace F + D.trace H := by
  unfold trace
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [add_zero]

theorem trace_cyclic_sum {w : List E} (D : FullFilling flip color face w)
    (ht : ∀ a, a ∉ D.boundary → (D.next^3) a = a)
    (F : E → E → E → M) :
    D.trace (fun a b c => F a b c + F b c a + F c a b) = 3 • D.trace F := by
  rw [trace_add,trace_add,trace_cyclic D ht F]
  have hh : D.trace (fun a b c => F c a b) = D.trace F :=
    (D.trace_cyclic ht (fun a b c => F b c a)).trans (D.trace_cyclic ht F)
  rw [hh]
  simp only [succ_nsmul,zero_nsmul,zero_add]

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M N : Type} [AddCommGroup M] [AddCommGroup N]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem trace_congr {w : List E} (D : FullFilling flip color face w)
    {F H : E → E → E → M}
    (h : ∀ a, a ∉ D.boundary →
      F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a)) =
      H (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))) : D.trace F = D.trace H := by
  unfold trace
  apply Finset.sum_congr rfl
  intro a _
  split_ifs with ha
  · rfl
  · exact h a ha

end Release075.FullFilling

namespace Release075.TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem full_triangular {w : List E} (D : TriangleFilling flip color face w)
    (a : D.full.Dart) (ha : a ∉ D.full.boundary) :
    (D.full.next^3) a = a ∧ D.full.next a ≠ a ∧
      face (D.full.label a) (D.full.label (D.full.next a)) (D.full.label ((D.full.next^2) a)) := by
  have hn : a.val ∉ D.boundary := by
    intro h
    apply ha
    exact List.mem_pmap.mpr ⟨a.val,h,rfl⟩
  have ht := D.triangular a.val a.property hn
  exact ⟨Subtype.ext ht.1,fun he => ht.2.1 (congrArg Subtype.val he),ht.2.2⟩

end Release075.TriangleFilling

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Chains ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

namespace Release075

namespace BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem boundary₁_edgeChain (e : d.LiftedEdge) :
    d.boundary₁ (d.edgeChain e) = Finsupp.single (d.liftedTarget e) 1 -
      Finsupp.single (d.liftedTarget (d.liftedFlip e)) 1 := by
  rcases e with ⟨⟨e,s⟩,g⟩
  cases s <;> simp [edgeChain,boundary₁,liftedFlip,liftedTarget,flipEdge,edgeValue]

theorem boundary₁_boundary₂ (c : d.C₂) : d.boundary₁ (d.boundary₂ c) = 0 := by
  have he : d.boundary₁.comp d.boundary₂ = 0 := by
    apply Finsupp.lhom_ext
    intro t n
    obtain ⟨t,g⟩ := t
    have h := TriangleFace.lift d t.property.1 g
    simp only [LinearMap.comp_apply,boundary₂,Finsupp.linearCombination_single,map_smul,
      map_add,boundary₁_edgeChain,LinearMap.zero_apply]
    rw [h.2.1,h.2.2.1,h.2.2.2]
    have hz :
        (Finsupp.single (d.liftedTarget (t.val.1,g*d.edgeValue t.val.1)) 1 -
          Finsupp.single (d.liftedTarget (t.val.2.2,g)) 1) +
        (Finsupp.single (d.liftedTarget (t.val.2.1,g*d.edgeValue t.val.1*d.edgeValue t.val.2.1)) 1 -
          Finsupp.single (d.liftedTarget (t.val.1,g*d.edgeValue t.val.1)) 1) +
        (Finsupp.single (d.liftedTarget (t.val.2.2,g)) 1 -
          Finsupp.single (d.liftedTarget (t.val.2.1,g*d.edgeValue t.val.1*d.edgeValue t.val.2.1)) 1) = (0 : d.C₀) := by abel
    rw [hz,smul_zero]
  exact LinearMap.congr_fun he c

theorem faceEval_rotate (a b c : d.LiftedEdge) : d.faceEval b c a = d.faceEval a b c := by
  unfold faceEval
  abel

theorem orderedEval_mirror (a b c : d.LiftedEdge) :
    d.orderedEval (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b) = - d.orderedEval b c a := by
  simp only [orderedEval,liftedFlip_flip]
  abel

theorem faceEval_mirror (a b c : d.LiftedEdge) :
    d.faceEval (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b) = -d.faceEval a b c := by
  simp only [faceEval,orderedEval_mirror]
  abel

theorem positiveAtom_eq_zero {a b c : d.LiftedEdge}
    (h : ¬d.TriangleFace a.1 b.1 c.1) : d.positiveAtom a b c = 0 := by
  simp only [positiveAtom]
  split_ifs with hh
  · exact False.elim (h hh.1)
  · rfl

theorem positiveAtom_degenerate (a b : d.LiftedEdge) :
    d.positiveAtom a b a = 0 ∧ d.positiveAtom a a b = 0 ∧ d.positiveAtom b a a = 0 := by
  refine ⟨d.positiveAtom_eq_zero ?_,d.positiveAtom_eq_zero ?_,d.positiveAtom_eq_zero ?_⟩
  · intro h; exact (TriangleFace.colors d h).2.2 rfl
  · intro h; exact (TriangleFace.colors d h).1 rfl
  · intro h; exact (TriangleFace.colors d h).2.1 rfl

theorem faceEval_degenerate (a b : d.LiftedEdge) : d.faceEval a b a = 0 := by
  obtain ⟨ha,hb,hc⟩ := d.positiveAtom_degenerate a b
  obtain ⟨ha',hb',hc'⟩ := d.positiveAtom_degenerate (d.liftedFlip a) (d.liftedFlip b)
  simp only [faceEval,orderedEval,ha,hb,hc,ha',hb',hc',sub_self,add_zero]

end BlockPresentation
end Release075

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem positiveAtom_zero_first {a b c : d.LiftedEdge} (h : d.edgeTarget a.1 ≠ .v) :
    d.positiveAtom a b c = 0 := by
  unfold positiveAtom
  split_ifs with hh
  · exact False.elim (h hh.2.1)
  · rfl

theorem positiveAtom_zero_second {a b c : d.LiftedEdge} (h : d.edgeTarget b.1 ≠ .w) :
    d.positiveAtom a b c = 0 := by
  unfold positiveAtom
  split_ifs with hh
  · exact False.elim (h hh.2.2.1)
  · rfl

theorem faceEval_positive {a b c : d.LiftedEdge} (h : d.LiftedFace a b c)
    (hp : d.PositiveFace (a.1,b.1,c.1)) : d.faceEval a b c = d.positiveAtom a b c := by
  have hva : d.edgeTarget (d.liftedFlip a).1 = .o :=
    (congrArg Prod.fst h.2.2.2).trans hp.2.2.2
  have hvc : d.edgeTarget (d.liftedFlip c).1 = .w :=
    (congrArg Prod.fst h.2.2.1).trans hp.2.2.1
  have hb := d.positiveAtom_zero_first (a := b) (b := c) (c := a) (by rw [hp.2.2.1]; intro he; cases he)
  have hc := d.positiveAtom_zero_first (a := c) (b := a) (c := b) (by rw [hp.2.2.2]; intro he; cases he)
  have h₁ := d.positiveAtom_zero_first (a := d.liftedFlip c) (b := d.liftedFlip b)
    (c := d.liftedFlip a) (by rw [hvc]; intro he; cases he)
  have h₂ := d.positiveAtom_zero_first (a := d.liftedFlip a) (b := d.liftedFlip c)
    (c := d.liftedFlip b) (by rw [hva]; intro he; cases he)
  have h₃ := d.positiveAtom_zero_second (a := d.liftedFlip b) (b := d.liftedFlip a)
    (c := d.liftedFlip c) (by rw [hva]; intro he; cases he)
  simp only [faceEval,orderedEval,hb,hc,h₁,h₂,h₃,sub_zero,add_zero]

theorem boundary₂_positiveAtom {a b c : d.LiftedEdge} (h : d.LiftedFace a b c)
    (hp : d.PositiveFace (a.1,b.1,c.1)) :
    d.boundary₂ (d.positiveAtom a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
  have ha : a.2 = c.2*d.edgeValue a.1 :=
    mul_inv_eq_iff_eq_mul.mp (congrArg Prod.snd h.2.2.2)
  have hb : b.2 = a.2*d.edgeValue b.1 :=
    mul_inv_eq_iff_eq_mul.mp (congrArg Prod.snd h.2.1)
  simp only [positiveAtom,dite_eq_left hp,boundary₂,Finsupp.linearCombination_single,one_smul]
  rw [← ha,← hb]

theorem TriangleFace.positive_orient {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.PositiveFace (a,b,c) ∨ d.PositiveFace (b,c,a) ∨ d.PositiveFace (c,a,b) ∨
    d.PositiveFace (d.flipEdge a,d.flipEdge c,d.flipEdge b) ∨
    d.PositiveFace (d.flipEdge b,d.flipEdge a,d.flipEdge c) ∨
    d.PositiveFace (d.flipEdge c,d.flipEdge b,d.flipEdge a) := by
  have hp (b : B) (i : (d.block b).labels) (u v : Fin r) :
      d.PositiveFace (d.orientedL b i u v,d.orientedX i u v,d.flipEdge (d.orientedR b i u v)) := by
    refine ⟨TriangleFace.pos₀ _ _ _ _,?_,?_,?_⟩ <;> rfl
  cases h with
  | pos₀ b i u v => exact Or.inl (hp _ _ _ _)
  | pos₁ b i u v => exact Or.inr (Or.inr (Or.inl (hp _ _ _ _)))
  | pos₂ b i u v => exact Or.inr (Or.inl (hp _ _ _ _))
  | neg₀ b i u v =>
    exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [flipEdge_flipEdge] using hp b i u v))))
  | neg₁ b i u v =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [flipEdge_flipEdge] using hp b i u v)))))
  | neg₂ b i u v =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [flipEdge_flipEdge] using hp b i u v)))))

theorem boundary₂_faceEval {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) :
    d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
  have pos {a b c : d.LiftedEdge} (h : d.LiftedFace a b c)
      (hp : d.PositiveFace (a.1,b.1,c.1)) :
      d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
    rw [d.faceEval_positive h hp]
    exact d.boundary₂_positiveAtom h hp
  have circ {a b c : d.LiftedEdge}
      (hp : d.boundary₂ (d.faceEval b c a) = d.edgeChain b + d.edgeChain c + d.edgeChain a) :
      d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
    rw [faceEval_rotate] at hp
    rw [hp]
    abel
  have mir {a b c : d.LiftedEdge}
      (hp : d.boundary₂ (d.faceEval (d.liftedFlip a) (d.liftedFlip c) (d.liftedFlip b)) =
        d.edgeChain (d.liftedFlip a) + d.edgeChain (d.liftedFlip c) + d.edgeChain (d.liftedFlip b)) :
      d.boundary₂ (d.faceEval a b c) = d.edgeChain a + d.edgeChain b + d.edgeChain c := by
    rw [faceEval_mirror,map_neg,edgeChain_flip,edgeChain_flip,edgeChain_flip] at hp
    apply neg_injective
    rw [hp]
    abel
  rcases TriangleFace.positive_orient d h.1 with hp | hp | hp | hp | hp | hp
  · exact pos h hp
  · exact circ (pos (h.rotate d) hp)
  · exact circ (circ (pos ((h.rotate d).rotate d) hp))
  · exact mir (pos (h.mirror d) hp)
  · exact circ (mir (pos ((h.rotate d).mirror d) hp))
  · exact circ (circ (mir (pos (((h.rotate d).rotate d).mirror d) hp)))

end Release075.BlockPresentation

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

end Release075.BlockPresentation

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.FullChains ----
namespace OAI

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

end Release075.BlockPresentation

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w : List d.LiftedEdge} (D : FullFilling d.liftedFlip d.liftedTarget d.LiftedFace w)

theorem triple_faceChain (hD : D.AllTriangles) : 3 • D.faceChain = -D.trace d.faceEval := by
  rw [faceChain,smul_neg]
  refine congrArg Neg.neg ?_
  exact (D.trace_cyclic_sum (fun a ha => (hD a ha).1) d.orderedEval).symm

theorem boundary₂_faceChain (hD : D.AllTriangles) : d.boundary₂ D.faceChain = d.wordChain w := by
  apply nsmul_right_injective (by decide : 3 ≠ 0)
  change (3:ℕ) • d.boundary₂ D.faceChain = 3 • d.wordChain w
  rw [← map_nsmul,D.triple_faceChain hD,map_neg]
  change -d.boundary₂.toAddMonoidHom (D.trace d.faceEval) = _
  rw [D.trace_map d.faceEval d.boundary₂.toAddMonoidHom]
  have he : D.trace (fun a b c => d.boundary₂ (d.faceEval a b c)) =
      D.trace (fun a b c => d.edgeChain a + d.edgeChain b + d.edgeChain c) := by
    apply D.trace_congr
    intro a ha
    exact d.boundary₂_faceEval (hD a ha).2.2
  change -D.trace (fun a b c => d.boundary₂ (d.faceEval a b c)) = _
  rw [he,D.trace_cyclic_sum (fun a ha => (hD a ha).1) (fun a _ _ => d.edgeChain a),
    trace_edge _ d.edgeChain d.edgeChain_flip]
  simp only [smul_neg,neg_neg,BlockPresentation.wordChain]

theorem allTriangles_shift (hD : D.AllTriangles) (g : d.GroupType) : (D.shift g).AllTriangles :=
  fun a ha => ⟨(hD a ha).1,(hD a ha).2.1,(hD a ha).2.2.shift d g⟩

theorem allTriangles_rotate (hD : D.AllTriangles) (n : ℕ) : (D.rotate n).AllTriangles := by
  intro a ha
  exact hD a (by simpa only [List.mem_rotate] using ha)

end Release075.FullFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem fullChain_unique {w : List (d.presentation hr).LiftedEdge}
    {x : (d.presentation hr).LiftedVertex}
    (hw : WordPath (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget x x w)
    (D D' : FullFilling (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget
      (d.presentation hr).LiftedFace w) (ht : D.AllTriangles) (ht' : D'.AllTriangles) :
    D.faceChain = D'.faceChain := by
  let P := d.presentation hr
  apply nsmul_right_injective (by decide : 3 ≠ 0)
  change (3 : ℕ) • D.faceChain = 3 • D'.faceChain
  rw [D.triple_faceChain ht,D'.triple_faceChain ht']
  apply congrArg Neg.neg
  exact FullFilling.trace_unique (d.lifted_sphere_empty_of_noDipole hr)
    P.liftedFlip_flip P.liftedTarget_ne (fun _ _ _ h => h.mirror P) P.faceEval
    (fun a b c _ => P.faceEval_rotate a b c) (fun a b c _ => P.faceEval_mirror a b c)
    P.faceEval_degenerate hw D D'

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

theorem wordValue_reverse (w : List d.OrientedEdge) :
    d.wordValue (reverseWord d.flipEdge w) = (d.wordValue w)⁻¹ := by
  induction w with
  | nil => simp
  | cons e w ih => simp [reverseWord_cons,ih,mul_inv_rev]

theorem exists_based_word (g : d.GroupType) :
    ∃ w, WordPath d.flipEdge d.edgeTarget .o .o w ∧ d.wordValue w = g := by
  let K : Subgroup d.GroupType := {
    carrier := {g | ∃ w, WordPath d.flipEdge d.edgeTarget .o .o w ∧ d.wordValue w = g}
    one_mem' := ⟨[],.nil _,rfl⟩
    mul_mem' := by
      rintro g h ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩
      exact ⟨u++v,hu.append hv,d.wordValue_append u v⟩
    inv_mem' := by
      rintro g ⟨w,hw,rfl⟩
      exact ⟨reverseWord d.flipEdge w,hw.reverse d.flipEdge_flipEdge,d.wordValue_reverse w⟩ }
  apply PresentedGroup.generated_by d.relators K _ g
  intro e
  change ∃ w, WordPath d.flipEdge d.edgeTarget .o .o w ∧ d.wordValue w = d.edge e
  rcases e with e | e | e
  · refine ⟨[(d.treeL,true),(.inl e,true),(d.treeR,false)],?_,?_⟩
    · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,true)
        (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (Sum.inl e,true)
          (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o)))
    · simp [wordValue,edgeValue,d.treeL_eq_one,d.treeR_eq_one]
  · refine ⟨[(.inr (.inl e),true),(d.treeL,false)],?_,?_⟩
    · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
        (.inr (.inl e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,false) (WordPath.nil Vertex.o))
    · simp [wordValue,edgeValue,d.treeL_eq_one]
  · refine ⟨[(.inr (.inr e),true),(d.treeR,false)],?_,?_⟩
    · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
        (.inr (.inr e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o))
    · simp [wordValue,edgeValue,d.treeR_eq_one]

theorem WordPath.shift {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) (g : d.GroupType) :
    WordPath d.liftedFlip d.liftedTarget (d.shiftVertex g x) (d.shiftVertex g y)
      (w.map (d.shiftEdge g)) := by
  induction hw with
  | nil x => exact .nil _
  | cons e hw ih =>
    have hh := WordPath.cons (flip:=d.liftedFlip) (color:=d.liftedTarget) (d.shiftEdge g e) ih
    simpa only [List.map_cons,←d.shiftEdge_flip,d.shiftEdge_target] using hh

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

theorem exists_lifted_path (g : d.GroupType) :
    ∃ w, WordPath d.liftedFlip d.liftedTarget (.o,1) (.o,g) w := by
  obtain ⟨w,hw,hv⟩ := d.exists_based_word g
  exact ⟨d.liftWord 1 w,by simpa only [hv,one_mul] using d.liftWord_typed hw 1⟩

theorem boundary₁_wordChain {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    d.boundary₁ (d.wordChain w) = Finsupp.single y 1 - Finsupp.single x 1 := by
  induction hw with
  | nil x => simp [wordChain]
  | cons e hw ih =>
    change d.boundary₁ (d.edgeChain e + d.wordChain _) = _
    rw [map_add,d.boundary₁_edgeChain,ih]
    abel

theorem powerWord_succ (g : d.GroupType) (w : List d.LiftedEdge) (n : ℕ) :
    d.powerWord g w (n+1) = d.powerWord g w n ++ w.map (d.shiftEdge (g^n)) := rfl

theorem powerWord_succ_left (g : d.GroupType) (w : List d.LiftedEdge) (n : ℕ) :
    d.powerWord g w (n+1) = w ++ (d.powerWord g w n).map (d.shiftEdge g) := by
  induction n with
  | zero => simpa only [powerWord,pow_zero,List.nil_append,List.map_nil,List.append_nil] using
      (List.map_id'' (d.shiftEdge_one) w)
  | succ n ih =>
    rw [powerWord_succ]
    conv_lhs => rw [ih]
    conv_rhs => rw [powerWord_succ]
    rw [List.map_append,List.map_map,List.append_assoc]
    congr 2
    apply List.map_congr_left
    intro e _
    simp only [Function.comp_def,←shiftEdge_mul,←pow_succ']

theorem powerWord_typed (g : d.GroupType) {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget (.o,1) (.o,g) w) (n : ℕ) :
    WordPath d.liftedFlip d.liftedTarget (.o,1) (.o,g^n) (d.powerWord g w n) := by
  induction n with
  | zero => simpa only [powerWord_zero,pow_zero] using
      (WordPath.nil (flip:=d.liftedFlip) (color:=d.liftedTarget) (.o,1))
  | succ n ih =>
    rw [powerWord_succ]
    apply ih.append
    simpa only [shiftVertex,mul_one,pow_succ] using WordPath.shift d hw (g^n)

theorem powerWord_chain (g : d.GroupType) (w : List d.LiftedEdge) (n : ℕ) :
    d.wordChain (d.powerWord g w n) = ∑ i ∈ Finset.range n, chainShift (g^i) (d.wordChain w) := by
  induction n with
  | zero => simp [wordChain]
  | succ n ih => rw [powerWord_succ,wordChain_append,wordChain_shift,ih,Finset.sum_range_succ]

theorem powerWord_shift_rotate (g : d.GroupType) (w : List d.LiftedEdge) {n : ℕ}
    (hn : 0 < n) (hg : g^n = 1) :
    (d.powerWord g w n).map (d.shiftEdge g) = (d.powerWord g w n).rotate w.length := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  conv_rhs => rw [powerWord_succ_left,List.rotate_append_length_eq]
  rw [powerWord_succ,List.map_append,List.map_map]
  congr 1
  have he : (d.shiftEdge g) ∘ (d.shiftEdge (g^k)) = id := by
    funext e
    simp only [Function.comp_def,← shiftEdge_mul,← pow_succ',hg,shiftEdge_one,id_eq]
  rw [he,List.map_id]

theorem powerWord_chain_norm (g : d.GroupType) (hg : IsOfFinOrder g)
    [Fintype (Subgroup.zpowers g)] (w : List d.LiftedEdge) :
    d.wordChain (d.powerWord g w (orderOf g)) =
      FreeChain.subgroupNorm (Subgroup.zpowers g) (d.wordChain w) := by
  rw [powerWord_chain]
  simp only [FreeChain.subgroupNorm,LinearMap.sum_apply,LinearEquiv.coe_coe]
  rw [← Equiv.sum_comp (finEquivZPowers hg)]
  exact (Fin.sum_univ_eq_sum_range (fun i => chainShift (g^i) (d.wordChain w)) (orderOf g)).symm

end Release075.BlockPresentation

namespace Release075.FullFilling
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w w' : List d.LiftedEdge}
  (D : FullFilling d.liftedFlip d.liftedTarget d.LiftedFace w)

theorem allTriangles_reword (hD : D.AllTriangles) (h : w = w') :
    (D.reword h).AllTriangles := by subst w'; exact hD

end Release075.FullFilling

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Torsion ----
namespace OAI

namespace Release075.MarkedLineData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem presentation_finiteOrder_eq_one (g : (d.presentation hr).GroupType)
    (hg : IsOfFinOrder g) : g = 1 := by
  let P := d.presentation hr
  let H := Subgroup.zpowers g
  let : Finite H := hg.finite_zpowers
  let : Fintype H := Fintype.ofFinite H
  let t : H := ⟨g,Subgroup.mem_zpowers g⟩
  have ht : ∀ x : H, x ∈ Subgroup.zpowers t := by
    intro x
    obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
    exact Subgroup.mem_zpowers_iff.mpr ⟨n,Subtype.ext hn⟩
  obtain ⟨w,hw⟩ := P.exists_lifted_path g
  let W := P.powerWord g w (orderOf g)
  have hW : WordPath P.liftedFlip P.liftedTarget (.o,1) (.o,1) W := by
    simpa only [pow_orderOf_eq_one] using P.powerWord_typed g hw (orderOf g)
  obtain ⟨D⟩ := P.lifted_closed_fillable hW
  have hD : D.full.AllTriangles := D.full_triangular
  have hrot : W.map (P.shiftEdge g) = W.rotate w.length :=
    P.powerWord_shift_rotate g w hg.orderOf_pos (pow_orderOf_eq_one g)
  have hinv : chainShift g D.full.faceChain = D.full.faceChain := by
    have hu := d.fullChain_unique hr (BlockPresentation.WordPath.shift P hW g)
      (D.full.shift g) ((D.full.rotate w.length).reword hrot.symm)
      (D.full.allTriangles_shift hD g)
      ((D.full.rotate w.length).allTriangles_reword
        (D.full.allTriangles_rotate hD w.length) hrot.symm)
    simpa only [FullFilling.faceChain_shift,FullFilling.faceChain_reword,
      FullFilling.faceChain_rotate] using hu
  apply FreeChain.cyclic_chain_obstruction H t ht P.boundary₁ P.boundary₂
    (fun h c => P.boundary₁_shift h c) (fun h c => P.boundary₂_shift h c)
    P.boundary₁_boundary₂ P.augmentation_boundary₁
    (Finsupp.single (.o,1) 1) (by simp) (P.wordChain w) _ D.full.faceChain _ hinv
  · simpa only [chainShift_single,one_mul,mul_one] using P.boundary₁_wordChain hw
  · exact (D.full.boundary₂_faceChain hD).trans (P.powerWord_chain_norm g hg w)

theorem presentation_torsionFree : TorsionFree (d.presentation hr).GroupType := by
  intro g n hn hg
  exact d.presentation_finiteOrder_eq_one hr g (isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,hg⟩)

end Release075.MarkedLineData

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Main ----
namespace OAI

namespace Release075

theorem main : ∃ (G : Type) (_ : Group G),
    TorsionFree G ∧ WordHyperbolic G ∧ ¬ Group.ResiduallyFinite G := by
  obtain ⟨q,r,hq,hr,hrq,hrb,⟨d⟩⟩ := exists_markedLineData
  let : Fact q.Prime := ⟨hq⟩
  have hq200 : 200 ≤ q := by
    have hb : 200 ≤ 100*100^20 := by norm_num
    omega
  exact ⟨(d.presentation hr).GroupType, inferInstance,
    d.presentation_torsionFree hr, d.presentation_wordHyperbolic hr,
    d.actual_presentation_not_residuallyFinite hr hrq hq200⟩

end Release075

end OAI

-- ---- mission target ----
open OAI OAI.Release075
universe u v

namespace OAI
namespace Release075
theorem _root_.solution : ∃ (G : Type) (_ : Group G),
    TorsionFree G ∧ WordHyperbolic G ∧ ¬ Group.ResiduallyFinite G := by
  first
    | exact OAI.Release075.main
    | (apply OAI.Release075.main <;> assumption)
    | (intros; apply OAI.Release075.main <;> assumption)
end Release075
end OAI

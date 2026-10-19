-- Prove2me | solution 1 for OAI.Release075.MarkedLineData.sphere_empty_of_noDipole
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:29:14.743988+00:00
-- url     : https://prove2.me/submissions/aab38c64-730f-4fba-9952-b524cad39716

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Spheres.lean:L235-L257
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.MarkedLineData.sphere_empty_of_noDipole. The node keeps its source
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
import Theorems.Thm_OAI_Release075_MarkedLineData_allLink_closed
import Theorems.Thm_OAI_Release075_TriangleSphere_dipole_of_link_backtrack
import Theorems.Thm_OAI_Release075_TriangleSphere_empty_of_angles

-- ---- from OAI.GroupTheory.Hyperbolic.Presentation ----
namespace OAI

namespace Release075

theorem ReducedWalk.map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : LocallyInjective f) {a b : V} {p : G.Walk a b}
    (hp : ReducedWalk p) : ReducedWalk (p.map f) := by
  intro n hn heq
  simp only [SimpleGraph.Walk.length_map] at hn
  simp only [SimpleGraph.Walk.getVert_map] at heq
  apply hp n hn
  apply hf (p.getVert (n+1)) _ _
    (p.adj_getVert_succ (by omega)).symm (p.adj_getVert_succ (by omega)) heq

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

-- ---- from OAI.GroupTheory.Hyperbolic.Words ----
namespace OAI

namespace Release075
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

namespace WordPath
variable {a b c : V} {u v : List E}

end WordPath

namespace Fillable
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))

end Fillable

namespace FilledBetween
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))
variable (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
variable {a b c d : V} {p q r u v : List E}

end FilledBetween
end Release075

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

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

theorem getVert_walk (a : ℕ → E) (n : ℕ) (h) (i : ℕ) (hi : i ≤ n) :
    (walk L a n h).getVert i = a i := by
  induction n generalizing a i with
  | zero => have : i = 0 := by omega
            subst i
            rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (fun j => a (j+1)) _ i (by omega)

theorem reduced_walk (a : ℕ → E) (n : ℕ) (h)
    (hr : ∀ i, i+2 ≤ n → a i ≠ a (i+2)) : ReducedWalk (walk L a n h) := by
  intro i hi
  simp only [length_walk] at hi
  rw [getVert_walk L a n h i (by omega),getVert_walk L a n h (i+2) hi]
  exact hr i hi

end Release075.SequenceWalk

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem pow_card_orbit (f : Perm A) (a : A) : (f^(orbit f a).card) a = a := by
  rw [orbit_card_eq_minimalPeriod]
  exact Function.iterate_minimalPeriod

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

theorem noDipole_link_reduced
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (hD : IsEmpty D.Dipole)
    (x : D.Dart) :
    D.label x ≠ D.label ((D.reverse*D.next) ((D.reverse*D.next) x)) := by
  intro h
  obtain ⟨P⟩ := D.dipole_of_link_backtrack hf hflip hmirror hunique x h
  exact hD.false P

theorem local_angle_lower (q : V → Fin 3) (L : SimpleGraph E)
    (hadj : ∀ a b c, face a b c → L.Adj a (flip b))
    (hred : ∀ a, D.label a ≠ D.label (D.vertexPerm (D.vertexPerm a)))
    (hclosed : ∀ a (p : L.Walk a a), 0 < p.length → ReducedWalk p →
      10 ≤ TriangleRibbon.weight (q (color a)) * p.length)
    (v : Cycles D.vertexPerm) : 10 ≤ D.vertexAngle q v := by
  obtain ⟨a,rfl⟩ := cl_surjective D.vertexPerm v
  let n := (orbit D.vertexPerm a).card
  let seq := fun i : ℕ => D.label ((D.vertexPerm^i) a)
  have hn : 0 < n := by
    change 0 < (orbit D.vertexPerm a).card
    rw [orbit_card_eq_minimalPeriod]
    exact minimalPeriod_pos _ _
  have hstep (b : D.Dart) : L.Adj (D.label b) (D.label (D.vertexPerm b)) := by
    change L.Adj (D.label b) (D.label (D.reverse (D.next b)))
    rw [D.reverse_label]
    exact hadj _ _ _ (D.triangular b).2.2
  have hs (i : ℕ) (_hi : i < n) : L.Adj (seq i) (seq (i+1)) := by
    simpa only [seq,pow_succ',Perm.mul_apply] using hstep ((D.vertexPerm^i) a)
  have hres (i : ℕ) (_hi : i+2 ≤ n) : seq i ≠ seq (i+2) := by
    simpa only [seq,show i+2 = (i+1)+1 by omega,pow_succ',Perm.mul_apply] using
      hred ((D.vertexPerm^i) a)
  have hend : seq n = D.label a := congrArg D.label (pow_card_orbit D.vertexPerm a)
  let p := (SequenceWalk.walk L seq n hs).copy (show seq 0 = D.label a from rfl) hend
  have hlen : p.length = n := (SimpleGraph.Walk.length_copy _ _ _).trans
    (SequenceWalk.length_walk L seq n hs)
  have hp : ReducedWalk p := by
    intro i hi
    simpa only [p,SimpleGraph.Walk.getVert_copy] using
      SequenceWalk.reduced_walk L seq n hs hres i
        (by simpa only [p,SimpleGraph.Walk.length_copy] using hi)
  have h := hclosed (D.label a) p (by rw [hlen]; exact hn) hp
  simpa only [vertexAngle,paint_cl,card_fiber,hlen,n] using h

end TriangleSphere
end Release075

namespace Release075.MarkedLineData
open Equiv PermCycles
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

/-- Every nonempty spherical map over the actual presentation has a dipole. -/
theorem sphere_empty_of_noDipole
    (D : TriangleSphere (d.presentation hr).flipEdge (d.presentation hr).edgeTarget
      (d.presentation hr).TriangleFace) (hD : IsEmpty D.Dipole) : IsEmpty D.Dart := by
  let L := (d.allLink hr).comap (d.linkDirection hr)
  apply D.empty_of_angles (d.presentation hr).vertexColor
    (fun _ _ _ => BlockPresentation.TriangleFace.colors _)
  apply D.local_angle_lower (d.presentation hr).vertexColor L
    (fun _ _ _ h => d.face_corner_adj hr h)
    (D.noDipole_link_reduced
      (fun _ _ _ => BlockPresentation.TriangleFace.colors _)
      (d.presentation hr).flipEdge_flipEdge
      (fun _ _ _ => BlockPresentation.TriangleFace.mirror _)
      (fun _ _ _ _ => BlockPresentation.TriangleFace.unique _) hD)
  intro a p hn hp
  let f : L →g d.allLink hr := SimpleGraph.Hom.comap (d.linkDirection hr) (d.allLink hr)
  have h := d.allLink_closed hr _ (p.map f)
    (by simpa only [SimpleGraph.Walk.length_map] using hn)
    (hp.map f (fun _ _ _ _ _ h => d.linkDirection_injective hr h))
  simp only [SimpleGraph.Walk.length_map] at h
  change 12 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr a)) * p.length at h
  rw [d.linkDirection_color hr] at h
  linarith

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

end Release075.TriangleSphere

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.MarkedLineData
open Equiv PermCycles


theorem solution : type_of% @_root_.OAI.Release075.MarkedLineData.sphere_empty_of_noDipole := @_root_.OAI.Release075.MarkedLineData.sphere_empty_of_noDipole

-- Prove2me | solution 1 for OAI.Release075.TriangleRibbon.boundary_angle_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:11:44.659329+00:00
-- url     : https://prove2.me/submissions/3262f924-409b-4316-8041-9676acda5dff

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Ribbons.lean:L658-L707
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.TriangleRibbon.boundary_angle_lower. The node keeps its source
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

theorem class_filter (f : Perm A) (a : A) :
    Finset.univ.filter (fun d => cl f d = cl f a) = orbit f a := by
  ext d
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,cl_eq_iff,mem_orbit,Perm.sameCycle_comm]

theorem pow_card_orbit (f : Perm A) (a : A) : (f^(orbit f a).card) a = a := by
  rw [orbit_card_eq_minimalPeriod]
  exact Function.iterate_minimalPeriod

theorem pow_ne_of_lt_card_orbit (f : Perm A) (a : A) (n : ℕ)
    (hn : 0 < n) (hlt : n < (orbit f a).card) : (f^n) a ≠ a := by
  intro h
  rw [orbit_card_eq_minimalPeriod] at hlt
  have hz : 0 < Function.minimalPeriod (f : A → A) a := minimalPeriod_pos f a
  have hh : n = 0 := Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
    (x := a) hlt hz h
  omega

end Release075.PermCycles

namespace Release075.TriangleRibbon
open Equiv PermCycles
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable (R : TriangleRibbon)

theorem visits_cl (a : R.Dart) : R.visits (cl R.vertexPerm a) = (R.outerCorners a).card := by
  unfold visits outerCorners IsOuter
  rw [← class_filter,Finset.filter_filter,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> rfl

theorem angles_cl (a : R.Dart) :
    R.angles (cl R.vertexPerm a) = weight (R.color (cl R.vertexPerm a)) * (R.innerCorners a).card := by
  have hs : R.angles (cl R.vertexPerm a) =
      ∑ d ∈ R.innerCorners a, weight (R.color (cl R.vertexPerm a)) := by
    rw [angles,innerCorners,← class_filter,Finset.filter_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    simp only [cornerAngle,IsOuter]
    by_cases h : cl R.vertexPerm d = cl R.vertexPerm a <;>
      by_cases ho : cl R.face d = R.outer <;> simp [h,ho]
  rw [hs]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]

theorem corner_count (a : R.Dart) :
    (R.innerCorners a).card + (R.outerCorners a).card = (orbit R.vertexPerm a).card := by
  have h := Finset.card_filter_add_card_filter_not (s := orbit R.vertexPerm a) R.IsOuter
  change (R.outerCorners a).card + (R.innerCorners a).card = _ at h
  omega

theorem unique_outer_of_visits_one (a : R.Dart) (ha : R.IsOuter a)
    (h : R.visits (cl R.vertexPerm a) = 1) {b : R.Dart}
    (hb : R.vertexPerm.SameCycle a b) (ho : R.IsOuter b) : b = a := by
  rw [R.visits_cl,Finset.card_eq_one] at h
  obtain ⟨c,hc⟩ := h
  have hma : a ∈ R.outerCorners a := Finset.mem_filter.mpr ⟨(mem_orbit _ _ _).mpr (.refl _ _),ha⟩
  have hmb : b ∈ R.outerCorners a := Finset.mem_filter.mpr ⟨(mem_orbit _ _ _).mpr hb,ho⟩
  rw [hc,Finset.mem_singleton] at hma hmb
  exact hmb.trans hma.symm

variable {E : Type*} (L : SimpleGraph E) (label : R.Dart → E)
variable (hadj : ∀ a, ¬ R.IsOuter a → L.Adj (label a) (label (R.vertexPerm a)))
variable (hred : ∀ a, ¬ R.IsOuter a → ¬ R.IsOuter (R.vertexPerm a) →
  label a ≠ label (R.vertexPerm (R.vertexPerm a)))

include hadj hred

/-- A vertex with exactly one exterior corner has a reduced interior-sector
path from the outgoing boundary direction back to the incoming one. -/
theorem boundary_angle_lower
    (hboundary : ∀ a, R.IsOuter a →
      ∀ p : L.Walk (label (R.vertexPerm a)) (label a), ReducedWalk p →
        5 ≤ weight (R.color (cl R.vertexPerm a)) * p.length)
    (v : R.Vertex) (hv : R.visits v = 1) : 5 ≤ R.angles v := by
  obtain ⟨a,ha⟩ : ∃ a, cl R.vertexPerm a = v ∧ R.IsOuter a := by
    obtain ⟨b,rfl⟩ := cl_surjective R.vertexPerm v
    rw [R.visits_cl,Finset.card_eq_one] at hv
    obtain ⟨a,ha⟩ := hv
    have hm : a ∈ R.outerCorners b := by rw [ha]; simp
    obtain ⟨hc,ho⟩ := Finset.mem_filter.mp hm
    exact ⟨a,(cl_eq_iff _ _ _).mpr ((mem_orbit _ _ _).mp hc).symm,ho⟩
  obtain ⟨rfl,ha⟩ := ha
  let n := (orbit R.vertexPerm a).card
  let seq := fun i : ℕ => label ((R.vertexPerm^(i+1)) a)
  have hn : 0 < n := by
    change 0 < (orbit R.vertexPerm a).card
    rw [orbit_card_eq_minimalPeriod]
    exact minimalPeriod_pos _ _
  have hout (i : ℕ) (hi : 0 < i) (hin : i < n) : ¬ R.IsOuter ((R.vertexPerm^i) a) := by
    intro ho
    have hh := R.unique_outer_of_visits_one a ha hv
      ((Perm.SameCycle.refl _ _).pow_right) ho
    exact pow_ne_of_lt_card_orbit R.vertexPerm a i hi hin hh
  have hadj' (i : ℕ) (hi : i < n-1) : L.Adj (seq i) (seq (i+1)) := by
    simpa only [seq,pow_succ',Perm.mul_apply] using
      hadj ((R.vertexPerm^(i+1)) a) (hout (i+1) (by omega) (by omega))
  have hred' (i : ℕ) (hi : i+2 ≤ n-1) : seq i ≠ seq (i+2) := by
    have hh := hred ((R.vertexPerm^(i+1)) a) (hout (i+1) (by omega) (by omega))
      (by simpa only [pow_succ',Perm.mul_apply] using hout (i+2) (by omega) (by omega))
    simpa only [seq,show i+2+1 = (i+1)+1+1 by omega,pow_succ',Perm.mul_apply] using hh
  have hstart : seq 0 = label (R.vertexPerm a) := rfl
  have hend : seq (n-1) = label a := by
    dsimp [seq]
    rw [Nat.sub_add_cancel hn,pow_card_orbit]
  let p := (SequenceWalk.walk L seq (n-1) hadj').copy hstart hend
  have hr : ReducedWalk p := by
    intro i hi
    simpa only [p,SimpleGraph.Walk.getVert_copy] using
      SequenceWalk.reduced_walk L seq (n-1) hadj' hred' i
        (by simpa only [p,SimpleGraph.Walk.length_copy] using hi)
  have hh := hboundary a ha p hr
  have hc : (R.innerCorners a).card = n-1 := by
    have hc := R.corner_count a
    rw [← R.visits_cl,hv] at hc
    omega
  rw [R.angles_cl,hc]
  simpa only [p,SimpleGraph.Walk.length_copy,SequenceWalk.length_walk] using hh

end Release075.TriangleRibbon

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.TriangleRibbon
open Equiv PermCycles
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.TriangleRibbon.boundary_angle_lower := @_root_.OAI.Release075.TriangleRibbon.boundary_angle_lower

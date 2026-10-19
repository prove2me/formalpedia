-- Prove2me | solution 1 for OAI.Release075.TriangleRibbon.interior_angle_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:10:04.283387+00:00
-- url     : https://prove2.me/submissions/0de972ff-21b6-4356-a078-2c8f245c3b13

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Ribbons.lean:L619-L656
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.TriangleRibbon.interior_angle_lower. The node keeps its source
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

theorem no_outer_of_visits_zero (a : R.Dart) (h : R.visits (cl R.vertexPerm a) = 0)
    {b : R.Dart} (hb : R.vertexPerm.SameCycle a b) : ¬ R.IsOuter b := by
  intro ho
  rw [R.visits_cl,Finset.card_eq_zero] at h
  have hm : b ∈ R.outerCorners a := Finset.mem_filter.mpr ⟨(mem_orbit _ _ _).mpr hb,ho⟩
  rw [h] at hm
  exact Finset.notMem_empty _ hm

variable {E : Type*} (L : SimpleGraph E) (label : R.Dart → E)
variable (hadj : ∀ a, ¬ R.IsOuter a → L.Adj (label a) (label (R.vertexPerm a)))
variable (hred : ∀ a, ¬ R.IsOuter a → ¬ R.IsOuter (R.vertexPerm a) →
  label a ≠ label (R.vertexPerm (R.vertexPerm a)))

include hadj hred

/-- The full corner orbit at a vertex disjoint from the exterior is a genuinely
reduced nonempty closed link walk. -/
theorem interior_angle_lower (M : ℝ)
    (hclosed : ∀ a (p : L.Walk (label a) (label a)), 0 < p.length → ReducedWalk p →
      M ≤ weight (R.color (cl R.vertexPerm a)) * p.length)
    (v : R.Vertex) (hv : R.visits v = 0) : M ≤ R.angles v := by
  obtain ⟨a,rfl⟩ := cl_surjective R.vertexPerm v
  let n := (orbit R.vertexPerm a).card
  let seq := fun i : ℕ => label ((R.vertexPerm^i) a)
  have hn : 0 < n := by
    change 0 < (orbit R.vertexPerm a).card
    rw [orbit_card_eq_minimalPeriod]
    exact minimalPeriod_pos _ _
  have hout (i : ℕ) : ¬ R.IsOuter ((R.vertexPerm^i) a) :=
    R.no_outer_of_visits_zero a hv ((Perm.SameCycle.refl _ _).pow_right)
  have hadj' (i : ℕ) (_hi : i < n) : L.Adj (seq i) (seq (i+1)) := by
    simpa only [seq,pow_succ',Perm.mul_apply] using hadj _ (hout i)
  have hred' (i : ℕ) (_hi : i+2 ≤ n) : seq i ≠ seq (i+2) := by
    have hh := hred ((R.vertexPerm^i) a) (hout i)
      (by simpa only [pow_succ',Perm.mul_apply] using hout (i+1))
    simpa only [seq,show i+2 = (i+1)+1 by omega,pow_succ',Perm.mul_apply] using hh
  have hend : seq n = label a := congrArg label (pow_card_orbit R.vertexPerm a)
  have hstart : seq 0 = label a := rfl
  let p := (SequenceWalk.walk L seq n hadj').copy hstart hend
  have hlen : p.length = n := (SimpleGraph.Walk.length_copy _ _ _).trans
    (SequenceWalk.length_walk L seq n hadj')
  have hr : ReducedWalk p := by
    intro i hi
    simpa only [p,SimpleGraph.Walk.getVert_copy] using
      SequenceWalk.reduced_walk L seq n hadj' hred' i
        (by simpa only [p,SimpleGraph.Walk.length_copy] using hi)
  have hh := hclosed a p (by rw [hlen]; exact hn) hr
  have hc : (R.innerCorners a).card = n := by
    have hc := R.corner_count a
    rw [← R.visits_cl,hv] at hc
    omega
  rw [R.angles_cl,hc]
  simpa only [hlen] using hh

end Release075.TriangleRibbon

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.TriangleRibbon
open Equiv PermCycles
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.TriangleRibbon.interior_angle_lower := @_root_.OAI.Release075.TriangleRibbon.interior_angle_lower

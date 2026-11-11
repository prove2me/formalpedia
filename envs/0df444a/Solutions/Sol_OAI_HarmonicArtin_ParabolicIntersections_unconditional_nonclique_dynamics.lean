-- Prove2me | solution 1 for OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T20:09:55.382688+00:00
-- url     : https://prove2.me/submissions/f78c31a6-f871-42a0-a45e-7fd536b3d2e6

import Mathlib
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.PushoutI
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap011
import Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_exists_minimal_parabolic_s236
import Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_unconditional_parabolic_intersections

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_Cartan
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric

open scoped Classical

variable {S W : Type*} [DecidableEq S] [Group W]

variable [Fintype S]

lemma simple_injective {M : CoxeterMatrix S} (cs : CoxeterSystem M W) :
    Function.Injective cs.simple := by
  intro i j h
  by_contra hij
  have hh := congrArg (fun w => representation cs w (Pi.single i 1) i) h
  simp only [representation_simple,simpleReflection_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,Pi.single_eq_same] at hh
  have hji : (Pi.single j (1:ℝ) : S → ℝ) i = 0 := Pi.single_eq_of_ne hij 1
  have hrow : (Matrix.mulVec (cartan M) (Pi.single i (1:ℝ))) i=2 := by simp [Matrix.mulVec_single]
  rw [hji,hrow] at hh
  norm_num at hh

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_CoordinateExtension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [DecidableEq S]

lemma parabolic_exterior (M:CoxeterMatrix S) (J:Set S) (w:coxeterParabolic M J)
    (v:S → ℝ) (i:S) (hi:i∉J) : representation M.toCoxeterSystem w v i=v i := by
  have hh : ∀ (g:M.Group),g∈coxeterParabolic M J →
      ∀ (v:S → ℝ) (i:S),i∉J → representation M.toCoxeterSystem g v i=v i := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨j,hj,rfl⟩:=hg
      intro v i hi
      have hij:i≠j:=fun h=>hi (h.symm ▸ hj)
      have hr : representation M.toCoxeterSystem (M.simple j)=simpleReflection M j :=
        representation_simple M.toCoxeterSystem j
      rw [hr]
      simp [simpleReflection_apply,hij]
    | one =>
      intro v i hi
      simp only [map_one]
      rfl
    | mul a b ha hb ia ib =>
      intro v i hi
      simp only [map_mul,LinearEquiv.mul_apply]
      rw [ia _ _ hi,ib _ _ hi]
    | inv a ha ia =>
      intro v i hi
      have h:=ia (representation M.toCoxeterSystem a⁻¹ v) i hi
      have hmul : representation M.toCoxeterSystem a
          (representation M.toCoxeterSystem a⁻¹ v)=v := by
        rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one]
        rfl
      rw [hmul] at h
      exact h.symm
  exact hh w w.property v i hi

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_ArtinCoxeter
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} (M : CoxeterMatrix S)

lemma artinCoxeter_word (w : List S) : artinCoxeter M (wordArtin M w) = wordCoxeter M w := by
  induction w with
  | nil => exact map_one _
  | cons s w ih =>
    change artinCoxeter M (generator M s * wordArtin M w) = M.toCoxeterSystem.simple s * wordCoxeter M w
    rw [map_mul,artinCoxeter_generator,ih]

@[simp] lemma artinCoxeter_positiveLift (w : M.Group) :
    artinCoxeter M (positiveLift M w) = w := by
  rw [positiveLift,artinCoxeter_word,wordCoxeter_reducedExpression]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_Basic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parabolic subgroups for result 082-03

We use the Artin presentation and standard parabolics already used by
`Topology.ArtinGroups`. In Mathlib's Coxeter matrix convention, a zero
off-diagonal entry means an infinite label.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {G : Type*} [Group G]

theorem conjugate_inf (g : G) (P Q : Subgroup G) :
    conjugate g (P ⊓ Q) = conjugate g P ⊓ conjugate g Q := rfl

theorem conjugate_sup (g : G) (P Q : Subgroup G) :
    conjugate g (P ⊔ Q) = conjugate g P ⊔ conjugate g Q :=
  (conjugateOrderIso g).map_sup P Q

variable {S : Type*} (M : CoxeterMatrix S)

theorem standard_univ : artinParabolic M Set.univ = ⊤ := by
  rw [artinParabolic, Set.image_univ]
  exact PresentedGroup.closure_range_of (braidRelators M)

theorem standard_union (X Y : Set S) :
    artinParabolic M (X ∪ Y) = artinParabolic M X ⊔ artinParabolic M Y := by
  simp only [artinParabolic, Set.image_union, Subgroup.closure_union]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_AmalgamGraph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coset graph of a two-factor amalgam, with its genuine group action. -/
namespace HarmonicArtin.ParabolicIntersections.AmalgamTree
open Monoid
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G : Bool → Type} [∀ b, Group (G b)] {H : Type} [Group H]
variable (φ : ∀ b, H →* G b)

lemma vertex_adj (g : Amalgam φ) : (graph φ).Adj (vertex φ false g) (vertex φ true g) :=
  ⟨Bool.false_ne_true,g,rfl,rfl⟩

lemma vertex_factor_fixed (b : Bool) (a : G b) :
    vertex φ b (PushoutI.of b a)=vertex φ b 1 := by
  apply Sigma.mk.inj_iff.mpr
  refine ⟨rfl,heq_of_eq ?_⟩
  apply QuotientGroup.eq.mpr
  change (PushoutI.of b a)⁻¹*1∈(PushoutI.of (φ := φ) b).range
  exact ⟨a⁻¹,by simp⟩

lemma root_to_base (b : Bool) :
    (graph φ).Reachable (vertex φ false 1) (vertex φ b 1) := by
  cases b
  · rfl
  · exact (vertex_adj φ 1).reachable

lemma base_to_base (b c : Bool) :
    (graph φ).Reachable (vertex φ b 1) (vertex φ c 1) :=
  (root_to_base φ b).symm.trans (root_to_base φ c)

lemma root_to_vertex (g : Amalgam φ) (b : Bool) :
    (graph φ).Reachable (vertex φ false 1) (vertex φ b g) := by
  suffices h : ∀ b, (graph φ).Reachable (vertex φ false 1) (vertex φ b g) from h b
  induction g using PushoutI.induction_on with
  | of i a =>
    intro b
    have h := (base_to_base φ i b).map (translate φ (PushoutI.of i a))
    change (graph φ).Reachable (vertex φ i (PushoutI.of i a*1))
      (vertex φ b (PushoutI.of i a*1)) at h
    simp only [mul_one,vertex_factor_fixed] at h
    exact (root_to_base φ i).trans h
  | base a =>
    intro b
    rw [←PushoutI.of_apply_eq_base φ false a]
    have h := (base_to_base φ false b).map (translate φ (PushoutI.of false (φ false a)))
    change (graph φ).Reachable (vertex φ false (PushoutI.of false (φ false a)*1))
      (vertex φ b (PushoutI.of false (φ false a)*1)) at h
    simpa only [mul_one,vertex_factor_fixed] using h
  | mul g h ihg ihh =>
    intro b
    have hh := (ihh b).map (translate φ g)
    change (graph φ).Reachable (vertex φ false (g*1)) (vertex φ b (g*h)) at hh
    rw [mul_one] at hh
    exact (ihg false).trans hh

theorem connected : (graph φ).Connected := by
  let : Nonempty (Vertex φ) := ⟨vertex φ false 1⟩
  refine ⟨?_⟩
  rintro ⟨b,u⟩ ⟨c,v⟩
  obtain ⟨g,rfl⟩ := Quotient.exists_rep u
  obtain ⟨h,rfl⟩ := Quotient.exists_rep v
  exact (root_to_vertex φ g b).symm.trans (root_to_vertex φ h c)

lemma vertex_stabilizer (b : Bool) (g : Amalgam φ) :
    MulAction.stabilizer (Amalgam φ) (vertex φ b g)=conjugate g (Factor φ b) := by
  ext a
  change (a • vertex φ b g=vertex φ b g) ↔ _
  rw [smul_vertex]
  simp only [vertex,Sigma.mk.inj_iff,heq_eq_eq,true_and,QuotientGroup.eq,mem_conjugate]
  constructor
  · intro h
    simpa only [mul_inv_rev,inv_inv,mul_assoc] using (Factor φ b).inv_mem h
  · intro h
    simpa only [mul_inv_rev,inv_inv,mul_assoc] using (Factor φ b).inv_mem h

end HarmonicArtin.ParabolicIntersections.AmalgamTree

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_AmalgamReduced
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reduced edge chains in the amalgamated product cannot close. -/
namespace HarmonicArtin.ParabolicIntersections.AmalgamTree
open Monoid
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G : Bool → Type} [∀ b, Group (G b)] {H : Type} [Group H]
variable (φ : ∀ b, H →* G b)

/-- The normal-form theorem, expressed using a list of actual factor elements. -/
lemma reduced_word_not_base (hφ : ∀ b, Function.Injective (φ b))
    (w : List (Σ b, G b)) (hw : w≠[])
    (hchain : w.IsChain (fun a b => a.1≠b.1))
    (hred : ∀ a∈w, a.2∉(φ a.1).range) :
    (w.map (fun a => PushoutI.of (φ := φ) a.1 a.2)).prod∉(PushoutI.base φ).range := by
  intro h
  let W : CoprodI.Word G := ⟨w,by
    intro a ha he
    apply hred a ha
    exact ⟨1,(map_one _).trans he.symm⟩,hchain⟩
  have hr : PushoutI.Reduced φ W := hred
  have he : W=CoprodI.Word.empty := hr.eq_empty_of_mem_range hφ (by
    simpa only [CoprodI.Word.prod,map_list_prod,List.map_map,Function.comp_def,
      PushoutI.ofCoprodI_of] using h)
  exact hw (congrArg CoprodI.Word.toList he)

lemma transition_product (e : ℕ → Amalgam φ) (n : ℕ) :
    (List.ofFn (fun i : Fin n => (e i)⁻¹*e (i+1))).prod=(e 0)⁻¹*e n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ',List.prod_concat]
    change (List.ofFn (fun i : Fin n => (e i)⁻¹*e (i+1))).prod*((e n)⁻¹*e (n+1))=_
    rw [ih]
    group

/-- Consecutive edges with distinct edge cosets give a nontrivial reduced
word, provided their common vertex types alternate. -/
theorem transition_not_base (hφ : ∀ b, Function.Injective (φ b))
    (e : ℕ → Amalgam φ) (b : ℕ → Bool) (n : ℕ) (hn : 0<n)
    (hfactor : ∀ i<n, (e i)⁻¹*e (i+1)∈Factor φ (b i))
    (hdistinct : ∀ i<n, (e i)⁻¹*e (i+1)∉(PushoutI.base φ).range)
    (halt : ∀ i, i+1<n → b i≠b (i+1)) :
    (e 0)⁻¹*e n∉(PushoutI.base φ).range := by
  let a (i : Fin n) : G (b i) := Classical.choose (hfactor i i.isLt)
  have ha (i : Fin n) : PushoutI.of (φ := φ) (b i) (a i)=(e i)⁻¹*e (i+1) :=
    Classical.choose_spec (hfactor i i.isLt)
  let w : List (Σ b,G b) := List.ofFn (fun i : Fin n => ⟨b i,a i⟩)
  have hw : w≠[] := by
    intro h
    have := congrArg List.length h
    simp only [w,List.length_ofFn,List.length_nil] at this
    omega
  have hchain : w.IsChain (fun a b => a.1≠b.1) := by
    apply List.isChain_ofFn.mpr
    intro i hi
    exact halt i hi
  have hred : ∀ x∈w, x.2∉(φ x.1).range := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    rintro ⟨h,he⟩
    change φ (b i) h=a i at he
    apply hdistinct i i.isLt
    refine ⟨h,?_⟩
    rw [←ha i,←he]
    exact (PushoutI.of_apply_eq_base φ (b i) h).symm
  have hprod : (w.map (fun x => PushoutI.of (φ := φ) x.1 x.2)).prod=(e 0)⁻¹*e n := by
    dsimp only [w]
    rw [List.map_ofFn]
    change (List.ofFn (fun i : Fin n => PushoutI.of (φ := φ) (b i) (a i))).prod=_
    simp only [ha]
    exact transition_product φ e n
  rw [←hprod]
  exact reduced_word_not_base φ hφ w hw hchain hred

end HarmonicArtin.ParabolicIntersections.AmalgamTree

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_AmalgamAcyclic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Bass--Serre coset graph is a tree: a cycle would be a nonempty
reduced word in the amalgam equal to an element of the edge group. -/
namespace HarmonicArtin.ParabolicIntersections.AmalgamTree
open Monoid
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G : Bool → Type} [∀ b, Group (G b)] {H : Type} [Group H]
variable (φ : ∀ b, H →* G b)

lemma adj_representatives {u v : Vertex φ} (h : (graph φ).Adj u v) :
    ∃ g : Amalgam φ, u=vertex φ u.1 g ∧ v=vertex φ v.1 g := by
  obtain ⟨hn,g,hu,hv⟩ := h
  exact ⟨g,Sigma.ext rfl (heq_of_eq hu),Sigma.ext rfl (heq_of_eq hv)⟩

lemma vertex_eq_iff (b : Bool) (g h : Amalgam φ) :
    vertex φ b g=vertex φ b h ↔ g⁻¹*h∈Factor φ b := by
  simp only [vertex,Sigma.mk.inj_iff,heq_eq_eq,true_and,QuotientGroup.eq]

lemma base_le_factor (b : Bool) : (PushoutI.base φ).range≤Factor φ b := by
  rintro _ ⟨h,rfl⟩
  exact ⟨φ b h,PushoutI.of_apply_eq_base φ b h⟩

lemma vertex_eq_of_base (b : Bool) {g h : Amalgam φ}
    (he : g⁻¹*h∈(PushoutI.base φ).range) : vertex φ b g=vertex φ b h :=
  (vertex_eq_iff φ b g h).mpr (base_le_factor φ b he)

lemma other_endpoint_eq {u v w : Vertex φ} {g h : Amalgam φ}
    (hu : u=vertex φ u.1 g) (hw : w=vertex φ w.1 h)
    (huv : u.1≠v.1) (hvw : v.1≠w.1)
    (he : g⁻¹*h∈(PushoutI.base φ).range) : u=w := by
  have ht : u.1=w.1 := by
    cases hu' : u.1 <;> cases hv' : v.1 <;> cases hw' : w.1 <;> simp_all
  calc
    u = vertex φ u.1 g := hu
    _ = vertex φ u.1 h := vertex_eq_of_base φ u.1 he
    _ = vertex φ w.1 h := congrArg (fun b => vertex φ b h) ht
    _ = w := hw.symm

/-- No cycle is possible in the coset graph of an injective amalgam. -/
theorem acyclic (hφ : ∀ b, Function.Injective (φ b)) : (graph φ).IsAcyclic := by
  intro v p hp
  have hn : 0<p.length := lt_of_lt_of_le (by decide : 0<3) hp.three_le_length
  choose r hr using (fun i : Fin p.length => adj_representatives φ (p.adj_getVert_succ i.isLt))
  let e (i : ℕ) : Amalgam φ := if hi : i<p.length then r ⟨i,hi⟩ else r ⟨0,hn⟩
  have he (i : ℕ) (hi : i<p.length) :
      p.getVert i=vertex φ (p.getVert i).1 (e i) ∧
      p.getVert (i+1)=vertex φ (p.getVert (i+1)).1 (e i) := by
    dsimp only [e]
    rw [dite_eq_left hi]
    exact hr ⟨i,hi⟩
  have hend : e p.length=e 0 := by
    simp only [e,dite_eq_right (lt_irrefl _),dite_eq_left hn]
  have hlast : p.getVert p.length=p.getVert 0 := by simp
  let b (i : ℕ) := (p.getVert (i+1)).1
  have hf : ∀ i<p.length, (e i)⁻¹*e (i+1)∈Factor φ (b i) := by
    intro i hi
    apply (vertex_eq_iff φ (b i) _ _).mp
    have h₁ := (he i hi).2
    by_cases hi' : i+1<p.length
    · exact h₁.symm.trans (he (i+1) hi').1
    · have hi' : i+1=p.length := by omega
      rw [hi',hend]
      rw [hi'] at h₁
      simpa only [b,hi',hlast] using h₁.symm.trans (hlast.trans (he 0 hn).1)
  have hd : ∀ i<p.length, (e i)⁻¹*e (i+1)∉(PushoutI.base φ).range := by
    intro i hi hmem
    by_cases hi' : i+1<p.length
    · have heq : p.getVert i=p.getVert (i+2) := other_endpoint_eq φ
        (he i hi).1 (by simpa only [Nat.add_assoc] using (he (i+1) hi').2)
        (p.adj_getVert_succ hi).1 (by simpa only [Nat.add_assoc] using (p.adj_getVert_succ hi').1) hmem
      have hne := hp.getVert_sub_one_ne_getVert_add_one (i := i+1) (by omega)
      apply hne
      simpa only [Nat.add_sub_cancel,Nat.add_assoc] using heq
    · have hi' : i+1=p.length := by omega
      have hmem' : (e i)⁻¹*e 0∈(PushoutI.base φ).range := by simpa only [hi',hend] using hmem
      have heq : p.getVert i=p.getVert 1 := other_endpoint_eq φ
        (he i hi).1 (he 0 hn).2 (p.adj_getVert_succ hi).1
        (by simpa only [hi',hlast] using (p.adj_getVert_succ hn).1) hmem'
      have hi1 := hp.getVert_injOn' (by change i≤p.length-1; omega)
        (by change 1≤p.length-1; have := hp.three_le_length; omega) heq
      have := hp.three_le_length
      omega
  have ha : ∀ i, i+1<p.length → b i≠b (i+1) := by
    intro i hi
    exact (p.adj_getVert_succ hi).1
  have hnon := transition_not_base φ hφ e b p.length hn hf hd ha
  apply hnon
  rw [hend,inv_mul_cancel]
  exact (PushoutI.base φ).range.one_mem

/-- The Bass--Serre tree of an injective two-factor amalgam. -/
theorem isTree (hφ : ∀ b, Function.Injective (φ b)) : (graph φ).IsTree :=
  ⟨connected φ,acyclic φ hφ⟩

end HarmonicArtin.ParabolicIntersections.AmalgamTree

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_DynamicsDefinitions
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Acylindrical actions and visual splittings

The definitions below spell out the metric content of acylindrical
hyperbolicity. Non-elementarity means that an orbit has three distinct
Gromov-boundary limit points, represented by Gromov sequences whose
pairwise mixed products are bounded. No dynamical assertion is built
into a definition of an Artin group.
-/
namespace HarmonicArtin.ParabolicIntersections

variable {S : Type} (M : CoxeterMatrix S)

lemma infinite_pair_visual_split (s t : S) (hst : s ≠ t) (hlabel : M s t=0) :
    IsVisualSplit M {s}ᶜ {t}ᶜ := by
  refine ⟨?_,?_,?_,?_⟩
  · ext a
    simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_singleton_iff,Set.mem_univ,iff_true]
    by_cases ha : a=s
    · exact Or.inr (by simpa [ha] using hst)
    · exact Or.inl ha
  · apply Set.ssubset_univ_iff.mpr
    intro h
    have hs : s ∈ ({s}ᶜ : Set S) := h.symm ▸ Set.mem_univ s
    simp at hs
  · apply Set.ssubset_univ_iff.mpr
    intro h
    have ht : t ∈ ({t}ᶜ : Set S) := h.symm ▸ Set.mem_univ t
    simp at ht
  · intro a ha b hb
    have hat : a=t := by simpa using ha.2
    have hbs : b=s := by simpa using hb.2
    subst a
    subst b
    rw [M.symmetric]
    exact hlabel

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphRealizationSpace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric realization of a connected graph by unit intervals. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (H : SimpleGraph V)

lemma distance_vertices (x y : V) : distance H (.vertex x) (.vertex y)=(H.dist x y : ℝ) := by
  simp [distance,via,route,anchor,weight]

lemma distance_edge (e : H.Dart) (t s : Set.Icc (0 : ℝ) 1) :
    distance H (.edge e t) (.edge e s)=|(t : ℝ)-s| := by
  apply le_antisymm (distance_le_direct H e t s)
  rcases distance_cases H (.edge e t) (.edge e s) with ⟨f,a,b,he,he',hd⟩|⟨i,j,hd⟩
  · cases he
    cases he'
    exact hd.ge
  · rw [hd]
    have hdist : H.dist e.fst e.snd=1 := H.dist_eq_one_iff_adj.mpr e.adj
    have hdist' : H.dist e.snd e.fst=1 := H.dist_eq_one_iff_adj.mpr e.adj.symm
    cases i <;> cases j <;>
      simp only [route,anchor,weight,hdist,hdist',SimpleGraph.dist_self,Nat.cast_zero,Nat.cast_one]
    all_goals apply abs_le.mpr; constructor <;> linarith [t.property.1,t.property.2,s.property.1,s.property.2]

lemma weight_le_one (p : Point H) (i : Bool) : weight H p i ≤ 1 := by
  cases p with
  | vertex v => norm_num [weight]
  | edge e t => cases i <;> simp only [weight] <;> linarith [t.property.1,t.property.2]

lemma distance_anchor_le (p : Point H) (i : Bool) :
    distance H p (.vertex (anchor H p i)) ≤ weight H p i := by
  simpa [route,anchor,weight] using distance_le_route H p (.vertex (anchor H p i)) i false

lemma dist_embed (hH : H.Connected) (p q : Point H) :
    dist (embed H hH p) (embed H hH q)=distance H p q := rfl

lemma dist_vertex (hH : H.Connected) (x y : V) :
    dist (vertex H hH x) (vertex H hH y)=(H.dist x y : ℝ) := distance_vertices H x y

lemma exists_near_vertex (hH : H.Connected) (x : Space H hH) :
    ∃ v,dist x (vertex H hH v) ≤ 1 := by
  obtain ⟨p,rfl⟩ := embed_surjective H hH x
  exact ⟨anchor H p false,(distance_anchor_le H p false).trans (weight_le_one H p false)⟩

lemma dist_arc (hH : H.Connected) (e : H.Dart) (t s : Set.Icc (0 : ℝ) 1) :
    dist (arc H hH e t) (arc H hH e s)=|(t : ℝ)-s| := distance_edge H e t s

lemma arc_zero (hH : H.Connected) (e : H.Dart) :
    arc H hH e ⟨0,by norm_num⟩=vertex H hH e.fst := by
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  exact distance_anchor_le H (.edge e ⟨0,by norm_num⟩) false

lemma arc_one (hH : H.Connected) (e : H.Dart) :
    arc H hH e ⟨1,by norm_num⟩=vertex H hH e.snd := by
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  change distance H (.edge e ⟨1,by norm_num⟩) (.vertex e.snd) ≤ 0
  simpa only [anchor,weight,sub_self] using distance_anchor_le H (.edge e ⟨1,by norm_num⟩) true

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphRealizationAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An action on a graph extends isometrically to its unit-interval realization. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (H : SimpleGraph V) (hA : PreservesAdj (G := G) H)

lemma action_isometric (hH : H.Connected) (g : G) :
    let _ := action H hA hH
    Isometry (fun x : Space H hH => g • x) := by
  let _ := action H hA hH
  apply isometry_iff_dist_eq.mpr
  intro x y
  obtain ⟨p,rfl⟩ := embed_surjective H hH x
  obtain ⟨q,rfl⟩ := embed_surjective H hH y
  change dist (act H hA hH g (embed H hH p)) (act H hA hH g (embed H hH q))= _
  rw [act_embed,act_embed,dist_embed,dist_embed,distance_act H hA hH g]

lemma act_vertex (hH : H.Connected) (g : G) (v : V) :
    act H hA hH g (vertex H hH v)=vertex H hH (g • v) := act_embed H hA hH g (.vertex v)

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreePathMetric
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distance and path-support facts used by the tree acylindrification. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {V : Type} (T : SimpleGraph V)

lemma path_length_eq_dist (hT : T.IsAcyclic) {x y : V}
    (p : T.Walk x y) (hp : p.IsPath) : p.length=T.dist x y := by
  obtain ⟨q,hq,hl⟩ := p.reachable.exists_path_of_dist
  have he : p=q := congrArg Subtype.val
    (hT.subsingleton_path x y |>.elim ⟨p,hp⟩ ⟨q,hq⟩)
  rw [he]
  exact hl

lemma path_metric_additive (hT : T.IsAcyclic) {x y w : V}
    (p : T.Walk x y) (hp : p.IsPath) (hw : w∈p.support) :
    T.dist x y=T.dist x w+T.dist w y := by
  obtain ⟨q,r,hq,hr,he⟩ := hp.mem_support_iff_exists_append.mp hw
  rw [←path_length_eq_dist T hT p hp,he,SimpleGraph.Walk.length_append,
    path_length_eq_dist T hT q hq,path_length_eq_dist T hT r hr]

lemma path_support_subset_walk (hT : T.IsAcyclic) {x y : V}
    (p : T.Walk x y) (hp : p.IsPath) (q : T.Walk x y) : p.support⊆q.support := by
  classical
  have he : p=(q.toPath : T.Walk x y) := congrArg Subtype.val
    (hT.subsingleton_path x y |>.elim ⟨p,hp⟩ q.toPath)
  rw [he]
  exact q.support_toPath_subset_support

lemma path_support_subset_append (hT : T.IsAcyclic) {x y z : V}
    (p : T.Walk x z) (hp : p.IsPath) (q : T.Walk x y) (r : T.Walk y z)
    {w : V} (hw : w∈p.support) : w∈q.support ∨ w∈r.support := by
  have h := path_support_subset_walk T hT p hp (q.append r) hw
  exact (SimpleGraph.Walk.mem_support_append_iff q r).mp h

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeShortcutMetric
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tree paths are approximate geodesics in a graph with convex shortcuts. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {V : Type} (T H : SimpleGraph V)

lemma shortcut_adj_split (hS : PathSaturated T H) {x y w : V}
    (hxy : H.Adj x y) (p : T.Walk x y) (hp : p.IsPath) (hw : w∈p.support) :
    ∃ (q : H.Walk x w) (r : H.Walk w y),q.length≤1 ∧ r.length≤1 := by
  have hx : ∃ q : H.Walk x w,q.length≤1 := by
    by_cases he : x=w
    · subst w
      exact ⟨.nil,by simp⟩
    · exact ⟨(hS hxy p hp x p.start_mem_support w hw he).toWalk,by simp⟩
  have hy : ∃ r : H.Walk w y,r.length≤1 := by
    by_cases he : w=y
    · subst w
      exact ⟨.nil,by simp⟩
    · exact ⟨(hS hxy p hp w hw y p.end_mem_support he).toWalk,by simp⟩
  obtain ⟨q,hq⟩ := hx
  obtain ⟨r,hr⟩ := hy
  exact ⟨q,r,hq,hr⟩

lemma shortcut_path_split (hT : T.IsTree) (hS : PathSaturated T H)
    {x y : V} (q : H.Walk x y) (p : T.Walk x y) (hp : p.IsPath)
    {w : V} (hw : w∈p.support) :
    ∃ (a : H.Walk x w) (b : H.Walk w y),a.length+b.length≤q.length+1 := by
  induction q with
  | nil =>
    have he : p=.nil := congrArg Subtype.val
      (hT.isAcyclic.subsingleton_path _ _ |>.elim ⟨p,hp⟩ ⟨.nil,by simp⟩)
    rw [he] at hw
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hw
    subst w
    exact ⟨.nil,.nil,by simp⟩
  | @cons x z y hxz q ih =>
    obtain ⟨r,hr⟩ := hT.connected.exists_isPath x z
    obtain ⟨s,hs⟩ := hT.connected.exists_isPath z y
    rcases path_support_subset_append T hT.isAcyclic p hp r s hw with hw|hw
    · obtain ⟨a,b,ha,hb⟩ := shortcut_adj_split T H hS hxz r hr hw
      refine ⟨a,b.append q,?_⟩
      simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons]
      omega
    · obtain ⟨a,b,hab⟩ := ih s hs hw
      refine ⟨a.cons hxz,b,?_⟩
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- A tree-path point splits distance in the shortcut graph up to one edge. -/
theorem shortcut_dist_split (hT : T.IsTree) (hH : H.Connected)
    (hS : PathSaturated T H) {x y w : V}
    (p : T.Walk x y) (hp : p.IsPath) (hw : w∈p.support) :
    H.dist x w+H.dist w y≤H.dist x y+1 := by
  obtain ⟨q,hq⟩ := hH.exists_walk_length_eq_dist x y
  obtain ⟨a,b,hab⟩ := shortcut_path_split T H hT hS q p hp hw
  calc
    H.dist x w+H.dist w y ≤ a.length+b.length :=
      Nat.add_le_add (H.dist_le a) (H.dist_le b)
    _ ≤ q.length+1 := hab
    _ = H.dist x y+1 := by rw [hq]

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreePaths
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary path geometry in a simplicial tree. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (T : SimpleGraph V)

/-- Paths starting in different directions meet only at their initial vertex. -/
theorem common_support_eq_start (hT : T.IsAcyclic) {u v w x : V}
    (p : T.Walk u v) (q : T.Walk u w) (hp : p.IsPath) (hq : q.IsPath)
    (hs : p.snd≠q.snd) (hxp : x∈p.support) (hxq : x∈q.support) : x=u := by
  by_contra hxu
  have he : p.takeUntil x hxp=q.takeUntil x hxq :=
    congrArg Subtype.val (hT.subsingleton_path u x |>.elim
      ⟨_,hp.takeUntil hxp⟩ ⟨_,hq.takeUntil hxq⟩)
  have hh := congrArg (fun r : T.Walk u x => r.snd) he
  rw [SimpleGraph.Walk.snd_takeUntil hxu,SimpleGraph.Walk.snd_takeUntil hxu] at hh
  exact hs hh

/-- Two paths in different directions form a single longer path. -/
theorem reverse_append_isPath (hT : T.IsAcyclic) {u v w : V}
    (p : T.Walk u v) (q : T.Walk u w) (hp : p.IsPath) (hq : q.IsPath)
    (hs : p.snd≠q.snd) : (p.reverse.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append]
  apply List.Nodup.append (hp.reverse.support_nodup.sublist (List.dropLast_sublist _)) hq.support_nodup
  intro x hxp hxq
  have hxp' : x∈p.support := by
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using List.dropLast_subset _ hxp
  have he := common_support_eq_start T hT p q hp hq hs hxp' hxq
  have hn := hp.reverse.support_nodup.rel_dropLast_getLast hxp
  exact hn (by simpa only [SimpleGraph.Walk.getLast_support] using he)

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeTripod
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common prefixes and tripods for paths in a tree. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (T : SimpleGraph V)

lemma walk_common_prefix {x y z : V} (p : T.Walk x y) (q : T.Walk x z) :
    ∃ b, ∃ (r : T.Walk x b) (s : T.Walk b y) (t : T.Walk b z),
      p=r.append s ∧ q=r.append t ∧ (s.Nil ∨ t.Nil ∨ s.snd≠t.snd) := by
  classical
  induction p generalizing z with
  | nil => exact ⟨_,.nil,.nil,q,by simp,by simp,Or.inl .nil⟩
  | @cons x v y h p ih =>
    cases q with
    | nil => exact ⟨x,.nil,p.cons h,.nil,by simp,by simp,Or.inr (Or.inl .nil)⟩
    | @cons _ w z h' q =>
      by_cases he : v=w
      · subst w
        obtain ⟨b,r,s,t,hp,hq,hd⟩ := ih q
        refine ⟨b,r.cons h,s,t,?_,?_,hd⟩
        · rw [hp]
          rfl
        · rw [hq]
          rfl
      · refine ⟨x,.nil,p.cons h,q.cons h',by simp,by simp,Or.inr (Or.inr ?_)⟩
        simpa only [SimpleGraph.Walk.snd_cons] using he

lemma prefixes_comparable {x y a b : V} (p : T.Walk x y)
    (ha : a∈p.support) (hb : b∈p.support) :
    a∈(p.takeUntil b hb).support ∨ b∈(p.takeUntil a ha).support := by
  classical
  rcases le_total (p.takeUntil a ha).length (p.takeUntil b hb).length with h|h
  · left
    have he : (p.takeUntil b hb).getVert (p.takeUntil a ha).length=a := by
      rw [p.getVert_takeUntil hb h,p.getVert_length_takeUntil ha]
    exact he ▸ (p.takeUntil b hb).getVert_mem_support _
  · right
    have he : (p.takeUntil a ha).getVert (p.takeUntil b hb).length=b := by
      rw [p.getVert_takeUntil ha h,p.getVert_length_takeUntil hb]
    exact he ▸ (p.takeUntil a ha).getVert_mem_support _

lemma common_support_in_prefix (hT : T.IsAcyclic) {x b y z w : V}
    (a : T.Walk x b) (s : T.Walk b y) (t : T.Walk b z)
    (hs : s.IsPath) (ht : t.IsPath) (hd : s.Nil ∨ t.Nil ∨ s.snd≠t.snd)
    (hw : w∈(a.append s).support) (hw' : w∈(a.append t).support) :
    w∈a.support := by
  rcases hd with hn|hn|hne
  · cases hn
    simpa only [SimpleGraph.Walk.append_nil] using hw
  · cases hn
    simpa only [SimpleGraph.Walk.append_nil] using hw'
  · by_contra hwa
    have hws := ((SimpleGraph.Walk.mem_support_append_iff a s).mp hw).resolve_left hwa
    have hwt := ((SimpleGraph.Walk.mem_support_append_iff a t).mp hw').resolve_left hwa
    have he := common_support_eq_start T hT s t hs ht hne hws hwt
    exact hwa (he.symm ▸ a.end_mem_support)

/-- The common prefix contains every common vertex of the two paths. -/
lemma tree_branchpoint (hT : T.IsAcyclic) {x y z : V}
    (p : T.Walk x y) (q : T.Walk x z) (r : T.Walk y z)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath) :
    ∃ b, ∃ hbp : b∈p.support,
      b∈q.support ∧ b∈r.support ∧
        ∀ w∈p.support,w∈q.support → w∈(p.takeUntil b hbp).support := by
  classical
  obtain ⟨b,a,s,t,hp',hq',hd⟩ := walk_common_prefix T p q
  have ha : a.IsPath := (hp' ▸ hp).of_append_left
  have hs : s.IsPath := (hp' ▸ hp).of_append_right
  have ht : t.IsPath := (hq' ▸ hq).of_append_right
  have hbp : b∈p.support := by
    rw [hp']
    exact SimpleGraph.Walk.support_subset_support_append_left a s a.end_mem_support
  have hbq : b∈q.support := by
    rw [hq']
    exact SimpleGraph.Walk.support_subset_support_append_left a t a.end_mem_support
  have hst : (s.reverse.append t).IsPath := by
    rcases hd with hn|hn|hne
    · cases hn
      simpa using ht
    · cases hn
      simpa using hs.reverse
    · exact reverse_append_isPath T hT s t hs ht hne
  have he : r=s.reverse.append t := congrArg Subtype.val
    (hT.subsingleton_path y z |>.elim ⟨r,hr⟩ ⟨_,hst⟩)
  have hbr : b∈r.support := by
    rw [he]
    exact SimpleGraph.Walk.support_subset_support_append_right s.reverse t t.start_mem_support
  refine ⟨b,hbp,hbq,hbr,?_⟩
  have htake : p.takeUntil b hbp=a := congrArg Subtype.val
    (hT.subsingleton_path x b |>.elim ⟨_,hp.takeUntil hbp⟩ ⟨a,ha⟩)
  intro w hwp hwq
  rw [htake]
  apply common_support_in_prefix T hT a s t hs ht hd
  · rwa [←hp']
  · rwa [←hq']

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeShortcutHyperbolic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gromov hyperbolicity of a tree with convex shortcuts. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (T H : SimpleGraph V)

lemma graphProduct_branch_bounds (hT : T.IsTree) (hH : H.Connected)
    (hS : PathSaturated T H) {o x y b : V}
    (p : T.Walk o x) (q : T.Walk o y) (r : T.Walk x y)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hbp : b∈p.support) (hbq : b∈q.support) (hbr : b∈r.support) :
    (H.dist o b : ℝ)-1≤graphProduct H o x y ∧
      graphProduct H o x y≤H.dist o b+1 := by
  have h1 : (H.dist o b : ℝ)+H.dist b x≤H.dist o x+1 := by
    exact_mod_cast shortcut_dist_split T H hT hH hS p hp hbp
  have h2 : (H.dist o b : ℝ)+H.dist b y≤H.dist o y+1 := by
    exact_mod_cast shortcut_dist_split T H hT hH hS q hq hbq
  have h3 : (H.dist b x : ℝ)+H.dist b y≤H.dist x y+1 := by
    have h := shortcut_dist_split T H hT hH hS r hr hbr
    rw [H.dist_comm (u := x) (v := b)] at h
    exact_mod_cast h
  have t1 : (H.dist o x : ℝ)≤H.dist o b+H.dist b x := by
    exact_mod_cast hH.dist_triangle (u := o) (v := b) (w := x)
  have t2 : (H.dist o y : ℝ)≤H.dist o b+H.dist b y := by
    exact_mod_cast hH.dist_triangle (u := o) (v := b) (w := y)
  have t3 : (H.dist x y : ℝ)≤H.dist b x+H.dist b y := by
    have h := hH.dist_triangle (u := x) (v := b) (w := y)
    rw [H.dist_comm (u := x) (v := b)] at h
    exact_mod_cast h
  unfold graphProduct
  constructor <;> linarith

/-- Convex shortcuts preserve hyperbolicity, with a uniform constant. -/
theorem shortcut_graph_hyperbolic (hT : T.IsTree) (hH : H.Connected)
    (hS : PathSaturated T H) (o x y z : V) :
    min (graphProduct H o x y) (graphProduct H o y z)≤graphProduct H o x z+3 := by
  obtain ⟨p,hp⟩ := hT.connected.exists_isPath o x
  obtain ⟨q,hq⟩ := hT.connected.exists_isPath o y
  obtain ⟨r,hr⟩ := hT.connected.exists_isPath o z
  obtain ⟨pxy,hxy⟩ := hT.connected.exists_isPath x y
  obtain ⟨pyz,hyz⟩ := hT.connected.exists_isPath y z
  obtain ⟨pxz,hxz⟩ := hT.connected.exists_isPath x z
  obtain ⟨a,hap,haq,haxy,_⟩ := tree_branchpoint T hT.isAcyclic p q pxy hp hq hxy
  obtain ⟨b,hbq,hbr,hbyz,_⟩ := tree_branchpoint T hT.isAcyclic q r pyz hq hr hyz
  obtain ⟨c,hcp,hcr,hcxz,hcmax⟩ := tree_branchpoint T hT.isAcyclic p r pxz hp hr hxz
  have hga := graphProduct_branch_bounds T H hT hH hS p q pxy hp hq hxy hap haq haxy
  have hgb := graphProduct_branch_bounds T H hT hH hS q r pyz hq hr hyz hbq hbr hbyz
  have hgc := graphProduct_branch_bounds T H hT hH hS p r pxz hp hr hxz hcp hcr hcxz
  rcases prefixes_comparable T q haq hbq with hab|hba
  · have he : q.takeUntil b hbq=r.takeUntil b hbr := congrArg Subtype.val
      (hT.isAcyclic.subsingleton_path o b |>.elim
        ⟨_,hq.takeUntil hbq⟩ ⟨_,hr.takeUntil hbr⟩)
    have har : a∈r.support := r.support_takeUntil_subset_support hbr (he ▸ hab)
    have hac := hcmax a hap har
    have hd := shortcut_dist_split T H hT hH hS (p.takeUntil c hcp) (hp.takeUntil hcp) hac
    have hd' : (H.dist o a : ℝ)≤H.dist o c+1 := by
      have hn : H.dist o a≤H.dist o c+1 := by omega
      exact_mod_cast hn
    calc
      min (graphProduct H o x y) (graphProduct H o y z)≤graphProduct H o x y := min_le_left _ _
      _ ≤ graphProduct H o x z+3 := by linarith [hga.2,hgc.1]
  · have he : q.takeUntil a haq=p.takeUntil a hap := congrArg Subtype.val
      (hT.isAcyclic.subsingleton_path o a |>.elim
        ⟨_,hq.takeUntil haq⟩ ⟨_,hp.takeUntil hap⟩)
    have hbp : b∈p.support := p.support_takeUntil_subset_support hap (he ▸ hba)
    have hbc := hcmax b hbp hbr
    have hd := shortcut_dist_split T H hT hH hS (p.takeUntil c hcp) (hp.takeUntil hcp) hbc
    have hd' : (H.dist o b : ℝ)≤H.dist o c+1 := by
      have hn : H.dist o b≤H.dist o c+1 := by omega
      exact_mod_cast hn
    calc
      min (graphProduct H o x y) (graphProduct H o y z)≤graphProduct H o y z := min_le_right _ _
      _ ≤ graphProduct H o x z+3 := by linarith [hgb.2,hgc.1]

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphRealizationHyperbolic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hyperbolicity passes from graph vertices to the unit-interval realization. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
variable {V : Type} (H : SimpleGraph V) (hH : H.Connected)

lemma dist_change {X : Type} [MetricSpace X] {x y x' y' : X}
    (hx : dist x x' ≤ 1) (hy : dist y y' ≤ 1) :
    dist x y ≤ dist x' y'+2 ∧ dist x' y' ≤ dist x y+2 := by
  have h₁ := dist_triangle x x' y
  have h₂ := dist_triangle x' y' y
  have h₃ := dist_triangle x' x y'
  have h₄ := dist_triangle x y y'
  rw [dist_comm y' y] at h₂
  rw [dist_comm x' x] at h₃
  constructor <;> linarith

lemma product_close {o x y : Space H hH} {a b c : V}
    (ho : dist o (vertex H hH a) ≤ 1) (hx : dist x (vertex H hH b) ≤ 1)
    (hy : dist y (vertex H hH c) ≤ 1) :
    product H hH o x y ≤ graphProduct H a b c+3 ∧
      graphProduct H a b c ≤ product H hH o x y+3 := by
  have h₁ := dist_change ho hx
  have h₂ := dist_change ho hy
  have h₃ := dist_change hx hy
  rw [dist_vertex] at h₁ h₂ h₃
  unfold product graphProduct
  constructor <;> linarith

theorem realization_hyperbolic (δ : ℝ)
    (hδ : ∀ o x y z,min (graphProduct H o x y) (graphProduct H o y z) ≤ graphProduct H o x z+δ)
    (o x y z : Space H hH) :
    min (product H hH o x y) (product H hH o y z) ≤ product H hH o x z+(δ+6) := by
  obtain ⟨a,ha⟩ := exists_near_vertex H hH o
  obtain ⟨b,hb⟩ := exists_near_vertex H hH x
  obtain ⟨c,hc⟩ := exists_near_vertex H hH y
  obtain ⟨d,hd⟩ := exists_near_vertex H hH z
  have h₁ := product_close H hH ha hb hc
  have h₂ := product_close H hH ha hc hd
  have h₃ := product_close H hH ha hb hd
  have hm := min_le_min h₁.1 h₂.1
  rw [min_add_add_right] at hm
  have hh := hδ a b c d
  linarith

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphRealizationAcylindrical
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Acylindricity passes from graph vertices to their unit-interval realization. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (H : SimpleGraph V) (hA : PreservesAdj (G := G) H) (hH : H.Connected)

lemma vertex_displacement_le (g : G) (x : Space H hH) (v : V)
    (hv : dist x (vertex H hH v) ≤ 1) (r : ℕ) :
    let _ := action H hA hH
    dist x (g • x) ≤ r →
    (H.dist v (g • v) : ℝ) ≤ r+2 := by
  let _ := action H hA hH
  change dist x (g • x) ≤ (r : ℝ) → _
  intro hg
  have h₁ := dist_triangle (vertex H hH v) x (g • vertex H hH v)
  have h₂ := dist_triangle x (g • x) (g • vertex H hH v)
  rw [dist_comm (vertex H hH v) x] at h₁
  rw [(action_isometric H hA hH g).dist_eq] at h₂
  have he : dist (vertex H hH v) (g • vertex H hH v)=(H.dist v (g • v) : ℝ) := by
    change dist (vertex H hH v) (act H hA hH g (vertex H hH v))= _
    rw [act_vertex,dist_vertex]
  rw [he] at h₁
  linarith

theorem acylindricity_transfer (r R N : ℕ)
    (hcount : ∀ v w : V,R ≤ H.dist v w →
      {g : G | H.dist v (g • v) ≤ r+2 ∧ H.dist w (g • w) ≤ r+2}.Finite ∧
      {g : G | H.dist v (g • v) ≤ r+2 ∧ H.dist w (g • w) ≤ r+2}.ncard ≤ N)
    (x y : Space H hH) (hxy : (R : ℝ)+2 ≤ dist x y) :
    let _ := action H hA hH
    {g : G | dist x (g • x) ≤ r ∧ dist y (g • y) ≤ r}.Finite ∧
      {g : G | dist x (g • x) ≤ r ∧ dist y (g • y) ≤ r}.ncard ≤ N := by
  let _ := action H hA hH
  obtain ⟨v,hv⟩ := exists_near_vertex H hH x
  obtain ⟨w,hw⟩ := exists_near_vertex H hH y
  have hdist : R ≤ H.dist v w := by
    have h := (dist_change hv hw).1
    rw [dist_vertex] at h
    have h' : (R : ℝ) ≤ H.dist v w := by linarith
    exact_mod_cast h'
  obtain ⟨hfin,hcard⟩ := hcount v w hdist
  have hsub : {g : G | dist x (g • x) ≤ r ∧ dist y (g • y) ≤ r} ⊆
      {g : G | H.dist v (g • v) ≤ r+2 ∧ H.dist w (g • w) ≤ r+2} := by
    intro g hg
    constructor
    · have h := vertex_displacement_le H hA hH g x v hv r hg.1
      exact_mod_cast h
    · have h := vertex_displacement_le H hA hH g y w hw r hg.2
      exact_mod_cast h
  exact ⟨hfin.subset hsub,(Set.ncard_le_ncard hsub hfin).trans hcard⟩

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MetricUnitCurves
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concatenation of unit-speed curves and realization of distance. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
variable {X : Type} [MetricSpace X]

lemma curve_const (x : X) : HasCurve x x 0 :=
  ⟨fun _ => x,fun _ _ => by simp,rfl,rfl⟩

lemma curve_subsegment (f : ℝ → X) (hf : ∀ s t,dist (f s) (f t) ≤ |s-t|)
    (a b : ℝ) : HasCurve (f a) (f b) |a-b| := by
  by_cases hab : a ≤ b
  · refine ⟨fun t => f (a+t),?_,by simp,?_⟩
    · intro s t
      simpa only [add_sub_add_left_eq_sub] using hf (a+s) (a+t)
    · apply congrArg f
      rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
  · refine ⟨fun t => f (a-t),?_,by simp,?_⟩
    · intro s t
      have he : (a-s)-(a-t)=t-s := by ring
      simpa only [he,abs_sub_comm t s] using hf (a-s) (a-t)
    · apply congrArg f
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hab))]
      ring

lemma curve_reverse {x y : X} {L : ℝ} (hc : HasCurve x y L) : HasCurve y x L := by
  obtain ⟨f,hf,hx,hy⟩ := hc
  refine ⟨fun t => f (L-t),?_,by simpa using hy,by simpa using hx⟩
  intro s t
  have he : (L-s)-(L-t)=t-s := by ring
  simpa only [he,abs_sub_comm t s] using hf (L-s) (L-t)

lemma curve_concat {x y z : X} {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hc : HasCurve x y L) (hd : HasCurve y z K) : HasCurve x z (L+K) := by
  obtain ⟨f,hf,hx,hy⟩ := hc
  obtain ⟨g,hg,hy',hz⟩ := hd
  let F (t : ℝ) := if t ≤ L then f t else g (t-L)
  have hbound (s t : ℝ) (hst : s ≤ t) : dist (F s) (F t) ≤ |s-t| := by
    by_cases hs : s ≤ L <;> by_cases ht : t ≤ L
    · simpa only [F,ite_eq_left hs,ite_eq_left ht] using hf s t
    · have hm : dist (f s) (g (t-L)) ≤ dist (f s) (f L)+dist (g 0) (g (t-L)) := by
        rw [hy,hy']
        exact dist_triangle (f s) y (g (t-L))
      have h₁ := hf s L
      have h₂ := hg 0 (t-L)
      rw [abs_of_nonpos (sub_nonpos.mpr hs)] at h₁
      rw [abs_of_nonpos (by linarith : 0-(t-L) ≤ 0)] at h₂
      simp only [F,ite_eq_left hs,ite_eq_right ht]
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      linarith
    · exact False.elim (hs (hst.trans ht))
    · have he : (s-L)-(t-L)=s-t := by ring
      simpa only [F,ite_eq_right hs,ite_eq_right ht,he] using hg (s-L) (t-L)
  refine ⟨F,?_,?_,?_⟩
  · intro s t
    rcases le_total s t with h|h
    · exact hbound s t h
    · simpa only [dist_comm,abs_sub_comm] using hbound t s h
  · simpa only [F,ite_eq_left hL] using hx
  · by_cases hK' : K=0
    · subst K
      have he : y=z := hy'.symm.trans hz
      simpa only [add_zero,F,ite_eq_left le_rfl,he] using hy
    · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK')
      have hLK : ¬L+K ≤ L := by linarith
      simpa only [F,ite_eq_right hLK,add_sub_cancel_left] using hz

/-- A unit-speed curve whose length is the endpoint distance is a geodesic. -/
lemma curve_realizes_distance {x y : X} (hc : HasCurve x y (dist x y)) :
    ∃ γ : Set.Icc (0 : ℝ) (dist x y) → X, Isometry γ ∧
      γ ⟨0,le_rfl,dist_nonneg⟩=x ∧ γ ⟨dist x y,dist_nonneg,le_rfl⟩=y := by
  obtain ⟨f,hf,hx,hy⟩ := hc
  refine ⟨fun t => f t,?_,hx,hy⟩
  apply isometry_iff_dist_eq.mpr
  intro a b
  change dist (f a) (f b)=|(a : ℝ)-b|
  apply le_antisymm (hf a b)
  have lower (a b : Set.Icc (0 : ℝ) (dist x y)) (hab : (a : ℝ) ≤ b) :
      |(a : ℝ)-b| ≤ dist (f a) (f b) := by
    have h₁ := hf 0 a
    have h₂ := hf b (dist x y)
    rw [hx,abs_of_nonpos (by linarith [a.property.1] : 0-(a : ℝ) ≤ 0)] at h₁
    rw [hy,abs_of_nonpos (sub_nonpos.mpr b.property.2)] at h₂
    have h₃ := dist_triangle x (f a) y
    have h₄ := dist_triangle (f a) (f b) y
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith
  rcases le_total (a : ℝ) b with h|h
  · exact lower a b h
  · simpa only [dist_comm,abs_sub_comm] using lower b a h

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphRealizationGeodesic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shortest paths in the unit-interval realization of a connected graph. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
variable {V : Type} (H : SimpleGraph V) (hH : H.Connected)

lemma arc_curve (e : H.Dart) (t s : Set.Icc (0 : ℝ) 1) :
    HasCurve (arc H hH e t) (arc H hH e s) |(t : ℝ)-s| := by
  let f : ℝ → Space H hH := fun r => arc H hH e (Set.projIcc 0 1 (by norm_num) r)
  have hf (a b : ℝ) : dist (f a) (f b) ≤ |a-b| := by
    rw [dist_arc]
    simpa only [Subtype.dist_eq,Real.dist_eq,NNReal.coe_one,one_mul] using
      (LipschitzWith.projIcc (by norm_num : (0 : ℝ) ≤ 1)).dist_le_mul a b
  have ht : f t=arc H hH e t := by
    simp only [f,Set.projIcc_val]
  have hs : f s=arc H hH e s := by
    simp only [f,Set.projIcc_val]
  simpa only [ht,hs] using curve_subsegment f hf (t : ℝ) (s : ℝ)

lemma curve_to_anchor (p : Point H) (i : Bool) :
    HasCurve (embed H hH p) (vertex H hH (anchor H p i)) (weight H p i) := by
  cases p with
  | vertex v => exact curve_const _
  | edge e t =>
    cases i
    · have h := arc_curve H hH e t ⟨0,by norm_num⟩
      change HasCurve (arc H hH e t) (vertex H hH e.fst) (t : ℝ)
      simpa only [arc_zero,sub_zero,abs_of_nonneg t.property.1] using h
    · have h := arc_curve H hH e t ⟨1,by norm_num⟩
      change HasCurve (arc H hH e t) (vertex H hH e.snd) (1-(t : ℝ))
      simpa only [arc_one,abs_of_nonpos (sub_nonpos.mpr t.property.2),neg_sub] using h

lemma curve_of_adj {x y : V} (hxy : H.Adj x y) :
    HasCurve (vertex H hH x) (vertex H hH y) 1 := by
  let e : H.Dart := ⟨(x,y),hxy⟩
  have h := arc_curve H hH e ⟨0,by norm_num⟩ ⟨1,by norm_num⟩
  simpa only [arc_zero,arc_one,zero_sub,abs_neg,abs_one] using h

lemma curve_of_walk {x y : V} (p : H.Walk x y) :
    HasCurve (vertex H hH x) (vertex H hH y) (p.length : ℝ) := by
  induction p with
  | @nil x => simpa only [SimpleGraph.Walk.length_nil,Nat.cast_zero] using curve_const (vertex H hH x)
  | @cons x z y hxz p ih =>
    have h := curve_concat (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg p.length)
      (curve_of_adj H hH hxz) ih
    simpa only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one,add_comm] using h

lemma curve_between_vertices (x y : V) :
    HasCurve (vertex H hH x) (vertex H hH y) (H.dist x y : ℝ) := by
  obtain ⟨p,hp⟩ := hH.exists_walk_length_eq_dist x y
  simpa only [hp] using curve_of_walk H hH p

lemma curve_via (p q : Point H) (i j : Bool) :
    HasCurve (embed H hH p) (embed H hH q) (route H p q i j) := by
  have hc := curve_concat (weight_nonneg H p i)
    (Nat.cast_nonneg (H.dist (anchor H p i) (anchor H q j)))
    (curve_to_anchor H hH p i) (curve_between_vertices H hH (anchor H p i) (anchor H q j))
  exact curve_concat (add_nonneg (weight_nonneg H p i) (Nat.cast_nonneg _))
    (weight_nonneg H q j) hc (curve_reverse (curve_to_anchor H hH q j))

theorem curve_between (x y : Space H hH) : HasCurve x y (dist x y) := by
  obtain ⟨p,rfl⟩ := embed_surjective H hH x
  obtain ⟨q,rfl⟩ := embed_surjective H hH y
  rw [dist_embed]
  rcases distance_cases H p q with ⟨e,t,s,rfl,rfl,hd⟩|⟨i,j,hd⟩
  · rw [hd]
    exact arc_curve H hH e t s
  · rw [hd]
    exact curve_via H hH p q i j

theorem realization_geodesic (x y : Space H hH) :
    ∃ γ : Set.Icc (0 : ℝ) (dist x y) → Space H hH, Isometry γ ∧
      γ ⟨0,le_rfl,dist_nonneg⟩=x ∧ γ ⟨dist x y,dist_nonneg,le_rfl⟩=y :=
  curve_realizes_distance (curve_between H hH x y)

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeInteriorImage
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small endpoint displacement preserves the interior of a tree path. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T H : SimpleGraph V)

lemma image_mem_of_deep (hT : T.IsTree) (hH : H.Connected)
    (hS : PathSaturated T H) (hA : PreservesAdj (G := G) T)
    (hB : PreservesAdj (G := G) H) {x y w : V} (p : T.Walk x y) (hp : p.IsPath)
    (hw : w∈p.support) (r : ℕ) (hx : r+1 < H.dist x w) (hy : r+1 < H.dist y w)
    (g : G) (hgx : H.dist x (g • x) ≤ r) (hgy : H.dist y (g • y) ≤ r) :
    g • w∈p.support := by
  obtain ⟨a,ha⟩ := hT.connected.exists_isPath (g • x) x
  obtain ⟨b,hb⟩ := hT.connected.exists_isPath y (g • y)
  let q := p.map (translate T hA g)
  have hq : q.IsPath := hp.map (MulAction.toPerm g).injective
  have hgw : g • w∈q.support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  have hm := path_support_subset_walk T hT.isAcyclic q hq ((a.append p).append b) hgw
  rcases (SimpleGraph.Walk.mem_support_append_iff (a.append p) b).mp hm with hm|hm
  · rcases (SimpleGraph.Walk.mem_support_append_iff a p).mp hm with hm|hm
    · have h := shortcut_dist_split T H hT hH hS a ha hm
      rw [graph_action_dist H hH hB g x w,
        H.dist_comm (u := g • x) (v := x)] at h
      omega
    · exact hm
  · have h := shortcut_dist_split T H hT hH hS b hb hm
    rw [H.dist_comm (u := g • w) (v := g • y),
      graph_action_dist H hH hB g y w] at h
    omega

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeConvexSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity of connected subgraphs, including the support of any walk. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {V : Type} (T : SimpleGraph V)

lemma connected_subgraph_pathClosed (hT : T.IsAcyclic) (H : T.Subgraph)
    (hH : H.Connected) : PathClosed T H.verts := by
  intro x y hx hy p hp w hw
  obtain ⟨q,hq⟩ := (hH ⟨x,hx⟩ ⟨y,hy⟩).exists_isPath
  have hqm : (q.map H.hom).IsPath := hq.map H.hom_injective
  have he : q.map H.hom=p :=
    congrArg Subtype.val (hT.subsingleton_path x y |>.elim ⟨_,hqm⟩ ⟨p,hp⟩)
  have hw' : w∈(q.map H.hom).support := he.symm ▸ hw
  rw [SimpleGraph.Walk.support_map] at hw'
  obtain ⟨z,_,hz⟩ := List.mem_map.mp hw'
  exact hz ▸ z.property

lemma walk_support_pathClosed (hT : T.IsAcyclic) {x y : V} (p : T.Walk x y) :
    PathClosed T {w | w∈p.support} := by
  rw [←p.verts_toSubgraph]
  exact connected_subgraph_pathClosed T hT p.toSubgraph p.toSubgraph_connected

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeSegmentOccurrences
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite translates of a segment inside a finite path

This is the finite-pattern input for constructing an acylindrical graph
from a tree action. The segment is in the actual tree and its pointwise
stabilizer is trivial; its occurrences are group elements, not formal labels.
-/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]

lemma pair_orbit_injective {u v : V} (h : pairStabilizer (G := G) u v=⊥) :
    Function.Injective (fun g : G => (g • u,g • v)) := by
  intro a b hab
  have hu : a • u=b • u := congrArg Prod.fst hab
  have hv : a • v=b • v := congrArg Prod.snd hab
  have hm : b⁻¹*a∈pairStabilizer (G := G) u v := by
    constructor
    · change (b⁻¹*a) • u=u
      rw [mul_smul,hu,inv_smul_smul]
    · change (b⁻¹*a) • v=v
      rw [mul_smul,hv,inv_smul_smul]
  rw [h,Subgroup.mem_bot] at hm
  exact (inv_mul_eq_one.mp hm).symm

lemma segmentOccurrences_finite {u v : V} (h : pairStabilizer (G := G) u v=⊥)
    (T : SimpleGraph V) {x y : V} (p : T.Walk x y) :
    (segmentOccurrences (G := G) u v T p).Finite := by
  let A : Set V := {w | w∈p.support}
  have hA : A.Finite := p.support.finite_toSet
  have hprod : (A×ˢA).Finite := hA.prod hA
  exact hprod.preimage (pair_orbit_injective h).injOn

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeAvoidingGraph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coning off paths that avoid a fixed orbit of segments

The vertices remain those of the original tree. A new edge joins the
endpoints of a path containing no translate of the chosen segment.
-/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

lemma avoidingGraph_subpath (hT : T.IsAcyclic) {x y a b : V}
    (p : T.Walk x y) (hn : ¬ContainsSegment (G := G) u v T p)
    (ha : a∈p.support) (hb : b∈p.support) (hab : a≠b) :
    (avoidingGraph (G := G) T u v).Adj a b := by
  refine ⟨hab,?_⟩
  intro q hq hbad
  obtain ⟨g,hgu,hgv⟩ := hbad
  have hc := walk_support_pathClosed T hT p ha hb q hq
  exact hn ⟨g,hc _ hgu,hc _ hgv⟩

lemma avoidingGraph_pathSaturated (hT : T.IsAcyclic) :
    PathSaturated T (avoidingGraph (G := G) T u v) := by
  intro x y hxy p hp a ha b hb hab
  exact avoidingGraph_subpath T u v hT p (hxy.2 p hp) ha hb hab

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeBallCount
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformly bounded intersections of a tree path with a metric ball. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (T : SimpleGraph V)

lemma path_prefix_dist (hT : T.IsAcyclic) {x y : V}
    (p : T.Walk x y) (hp : p.IsPath) (i : ℕ) (hi : i≤p.length) :
    T.dist x (p.getVert i)=i := by
  have he := path_length_eq_dist T hT (p.take i) (hp.take i)
  rw [SimpleGraph.Walk.take_length,Nat.min_eq_left hi] at he
  exact he.symm

lemma path_index_dist (hT : T.IsAcyclic) {x y w : V}
    (p : T.Walk x y) (hp : p.IsPath) (hw : w∈p.support) :
    T.dist x w=p.support.idxOf w := by
  have hi : p.support.idxOf w≤p.length := by
    have h := List.idxOf_lt_length_of_mem hw
    rw [SimpleGraph.Walk.length_support] at h
    omega
  have he := path_prefix_dist T hT p hp _ hi
  rwa [SimpleGraph.Walk.getVert_support_idxOf p hw] at he

/-- Even in a tree of infinite valence, a radius-`L` ball meets a simple
path in at most `2L+1` vertices. -/
theorem path_ball_ncard (hT : T.IsTree) {x y b : V}
    (p : T.Walk x y) (hp : p.IsPath) (hb : b∈p.support) (L : ℕ) :
    {w | w∈p.support ∧ T.dist b w≤L}.ncard≤2*L+1 := by
  let i := p.support.idxOf b
  let C := Finset.Icc (i-L) (i+L)
  have hsubset : {w | w∈p.support ∧ T.dist b w≤L} ⊆
      (↑(C.image p.getVert) : Set V) := by
    intro w hw
    let j := p.support.idxOf w
    have hdw : T.dist x w=j := path_index_dist T hT.isAcyclic p hp hw.1
    have hdb : T.dist x b=i := path_index_dist T hT.isAcyclic p hp hb
    have hbw : T.dist b w≤L := hw.2
    have hj : j ≤ i+L := by
      have h := hT.connected.dist_triangle (u := x) (v := b) (w := w)
      rw [hdw,hdb] at h
      omega
    have hi : i ≤ j+L := by
      have h := hT.connected.dist_triangle (u := x) (v := w) (w := b)
      rw [hdw,hdb,T.dist_comm (u := w) (v := b)] at h
      omega
    apply Finset.mem_image.mpr
    refine ⟨j,?_,SimpleGraph.Walk.getVert_support_idxOf p hw.1⟩
    exact Finset.mem_Icc.mpr ⟨by omega,hj⟩
  calc
    {w | w∈p.support ∧ T.dist b w≤L}.ncard ≤ (C.image p.getVert).card := by
      exact_mod_cast Set.ncard_le_ncard hsubset (Finset.finite_toSet _)
    _ ≤ C.card := Finset.card_image_le
    _ ≤ 2*L+1 := by
      dsimp only [C]
      rw [Nat.card_Icc]
      omega

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeSegmentBallCount
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform counts for translates of a free segment near a path vertex. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

/-- The bound is independent of the path length and of vertex valences. -/
theorem localSegmentOccurrences_bound (hT : T.IsTree)
    (hfree : pairStabilizer (G := G) u v=⊥)
    {x y b : V} (p : T.Walk x y) (hp : p.IsPath) (hb : b∈p.support) (L : ℕ) :
    (localSegmentOccurrences (G := G) T u v p b L).Finite ∧
      (localSegmentOccurrences (G := G) T u v p b L).ncard≤(2*L+1)^2 := by
  let B : Set V := {w | w∈p.support ∧ T.dist b w≤L}
  have hB : B.Finite := p.support.finite_toSet.subset (fun _ hw => hw.1)
  have hcard : B.ncard≤2*L+1 := path_ball_ncard T hT p hp hb L
  have hpair := pair_orbit_injective hfree
  have hfin : (localSegmentOccurrences (G := G) T u v p b L).Finite :=
    (hB.prod hB).preimage hpair.injOn
  refine ⟨hfin,?_⟩
  calc
    (localSegmentOccurrences (G := G) T u v p b L).ncard ≤ (B×ˢB).ncard :=
      Set.ncard_le_ncard_of_injOn (fun g : G => (g • u,g • v))
        (fun _ hg => hg) hpair.injOn (hB.prod hB)
    _ = B.ncard*B.ncard := Set.ncard_prod
    _ ≤ (2*L+1)*(2*L+1) := Nat.mul_le_mul hcard hcard
    _ = (2*L+1)^2 := (pow_two _).symm

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeSeparatedPaths
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distances between different branches of a tree. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (T : SimpleGraph V)

lemma reverse_append_of_common {b x y : V} (s : T.Walk b x) (t : T.Walk b y)
    (hs : s.IsPath) (ht : t.IsPath)
    (hc : ∀ w∈s.support,w∈t.support → w=b) : (s.reverse.append t).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append]
  apply List.Nodup.append (hs.reverse.support_nodup.sublist (List.dropLast_sublist _)) ht.support_nodup
  intro w hw ht'
  have hs' : w∈s.support := by
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using List.dropLast_subset _ hw
  have he := hc w hs' ht'
  have hn := hs.reverse.support_nodup.rel_dropLast_getLast hw
  exact hn (by simpa only [SimpleGraph.Walk.getLast_support] using he)

lemma dist_sum_of_branches (hT : T.IsAcyclic) {b x y a c : V}
    (s : T.Walk b x) (t : T.Walk b y) (hs : s.IsPath) (ht : t.IsPath)
    (hc : ∀ w∈s.support,w∈t.support → w=b)
    (ha : a∈s.support) (hc' : c∈t.support) :
    T.dist b a+T.dist b c=T.dist a c := by
  let p := s.takeUntil a ha
  let q := t.takeUntil c hc'
  have hp : p.IsPath := hs.takeUntil ha
  have hq : q.IsPath := ht.takeUntil hc'
  have hpq : (p.reverse.append q).IsPath :=
    reverse_append_of_common T p q hp hq (fun w hw hw' =>
      hc w (s.support_takeUntil_subset_support ha hw) (t.support_takeUntil_subset_support hc' hw'))
  have hb : b∈(p.reverse.append q).support :=
    SimpleGraph.Walk.support_subset_support_append_right _ _ q.start_mem_support
  have he := path_metric_additive T hT _ hpq hb
  rw [T.dist_comm (u := a) (v := b)] at he
  exact he.symm

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeSegmentCount
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform counts of free segment translates along shortcut paths. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

lemma segmentOccurrences_branches (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    {b x y : V} (s : T.Walk b x) (t : T.Walk b y)
    (hs : s.IsPath) (ht : t.IsPath)
    (hc : ∀ w∈s.support,w∈t.support → w=b) :
    segmentOccurrences (G := G) u v T (s.reverse.append t) ⊆
      segmentOccurrences u v T s ∪ segmentOccurrences u v T t ∪
        localSegmentOccurrences T u v (s.reverse.append t) b (T.dist u v) := by
  intro g hg
  have hgu := (SimpleGraph.Walk.mem_support_append_iff s.reverse t).mp hg.1
  have hgv := (SimpleGraph.Walk.mem_support_append_iff s.reverse t).mp hg.2
  simp only [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hgu hgv
  have hd := graph_action_dist T hT.connected hA g u v
  rcases hgu with hgu|hgu <;> rcases hgv with hgv|hgv
  · exact Or.inl (Or.inl ⟨hgu,hgv⟩)
  · right
    have he := dist_sum_of_branches T hT.isAcyclic s t hs ht hc hgu hgv
    exact ⟨⟨hg.1,by omega⟩,⟨hg.2,by omega⟩⟩
  · right
    have he := dist_sum_of_branches T hT.isAcyclic s t hs ht hc hgv hgu
    rw [T.dist_comm (u := g • v) (v := g • u)] at he
    exact ⟨⟨hg.1,by omega⟩,⟨hg.2,by omega⟩⟩
  · exact Or.inl (Or.inr ⟨hgu,hgv⟩)

lemma branch_support_common (hT : T.IsAcyclic) {b x y : V}
    (s : T.Walk b x) (t : T.Walk b y) (hs : s.IsPath) (ht : t.IsPath)
    (hd : s.Nil ∨ t.Nil ∨ s.snd≠t.snd) :
    ∀ w∈s.support,w∈t.support → w=b := by
  intro w hw hw'
  rcases hd with hn|hn|hne
  · cases hn
    simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hw
  · cases hn
    simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hw'
  · exact common_support_eq_start T hT s t hs ht hne hw hw'

/-- A shortcut walk of length `n` crosses at most `n (2L+1)^2`
translates of a free length-`L` segment, independently of vertex valences. -/
theorem segmentOccurrences_bound (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v)
    {x y : V} (q : (avoidingGraph (G := G) T u v).Walk x y)
    (p : T.Walk x y) (hp : p.IsPath) :
    (segmentOccurrences (G := G) u v T p).ncard ≤ q.length*(2*T.dist u v+1)^2 := by
  induction q with
  | @nil x =>
    have he : p=.nil := congrArg Subtype.val
      (hT.isAcyclic.subsingleton_path _ _ |>.elim ⟨p,hp⟩ ⟨.nil,by simp⟩)
    rw [he]
    have hempty : segmentOccurrences (G := G) u v T (.nil : T.Walk x x)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hgu : g • u=x := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hg.1
      have hgv : g • v=x := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hg.2
      exact hne ((MulAction.toPerm g).injective (hgu.trans hgv.symm))
    rw [hempty]
    simp
  | @cons x z y hxz q ih =>
    obtain ⟨r,hr⟩ := hT.connected.exists_isPath x z
    obtain ⟨w,hw⟩ := hT.connected.exists_isPath z y
    obtain ⟨b,a,s,t,hrs,hwt,hd⟩ := walk_common_prefix T r.reverse w
    have hs : s.IsPath := (hrs ▸ hr.reverse).of_append_right
    have ht : t.IsPath := (hwt ▸ hw).of_append_right
    have hc := branch_support_common T hT.isAcyclic s t hs ht hd
    have hst := reverse_append_of_common T s t hs ht hc
    have he : p=s.reverse.append t := congrArg Subtype.val
      (hT.isAcyclic.subsingleton_path _ _ |>.elim ⟨p,hp⟩ ⟨_,hst⟩)
    have hno : ¬ContainsSegment (G := G) u v T r := hxz.2 r hr
    have hsub : segmentOccurrences (G := G) u v T p ⊆
        segmentOccurrences u v T w ∪ localSegmentOccurrences T u v p b (T.dist u v) := by
      intro g hg
      rw [he] at hg
      rcases segmentOccurrences_branches T u v hT hA s t hs ht hc hg with (hgs|hgt)|hgl
      · exfalso
        apply hno
        have hsr : s.support⊆r.reverse.support := by
          rw [hrs]
          exact SimpleGraph.Walk.support_subset_support_append_right a s
        refine ⟨g,?_,?_⟩
        · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hsr hgs.1
        · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hsr hgs.2
      · left
        have htw : t.support⊆w.support := by
          rw [hwt]
          exact SimpleGraph.Walk.support_subset_support_append_right a t
        exact ⟨htw hgt.1,htw hgt.2⟩
      · exact Or.inr (he ▸ hgl)
    have hb : b∈p.support := by
      rw [he]
      exact SimpleGraph.Walk.support_subset_support_append_right s.reverse t t.start_mem_support
    have hlocal := localSegmentOccurrences_bound T u v hT hfree p hp hb (T.dist u v)
    have hn := ih w hw
    calc
      (segmentOccurrences (G := G) u v T p).ncard ≤
          (segmentOccurrences u v T w ∪ localSegmentOccurrences T u v p b (T.dist u v)).ncard :=
        Set.ncard_le_ncard hsub ((segmentOccurrences_finite hfree T w).union hlocal.1)
      _ ≤ (segmentOccurrences (G := G) u v T w).ncard+
          (localSegmentOccurrences T u v p b (T.dist u v)).ncard := Set.ncard_union_le _ _
      _ ≤ q.length*(2*T.dist u v+1)^2+(2*T.dist u v+1)^2 := Nat.add_le_add hn hlocal.2
      _ = (q.cons hxz).length*(2*T.dist u v+1)^2 := by
        simp only [SimpleGraph.Walk.length_cons,Nat.add_mul,one_mul]

theorem segmentOccurrences_bound_dist (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v)
    {x y : V} (p : T.Walk x y) (hp : p.IsPath) :
    (segmentOccurrences (G := G) u v T p).ncard ≤
      (avoidingGraph (G := G) T u v).dist x y*(2*T.dist u v+1)^2 := by
  obtain ⟨q,hq⟩ := (avoidingGraph_connected T u v hT hA hne hnadj).exists_walk_length_eq_dist x y
  simpa only [hq] using segmentOccurrences_bound T u v hT hA hfree hne q p hp

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphWalkLevels
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer distance levels along a graph walk. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {V : Type} (H : SimpleGraph V)

lemma walk_exists_dist_level (hH : H.Connected) (o : V) {x y : V}
    (p : H.Walk x y) (k : ℕ) (hx : H.dist o x ≤ k) (hy : k ≤ H.dist o y) :
    ∃ w∈p.support,H.dist o w=k := by
  induction p with
  | nil => exact ⟨_,by simp,Nat.le_antisymm hx hy⟩
  | @cons x z y hxz p ih =>
    by_cases he : H.dist o x=k
    · exact ⟨x,by simp,he⟩
    · have hz : H.dist o z ≤ k := by
        have ht := hH.dist_triangle (u := o) (v := x) (w := z)
        have hd := H.dist_eq_one_iff_adj.mpr hxz
        omega
      obtain ⟨w,hw,hd⟩ := ih hz hy
      exact ⟨w,by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hw,hd⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeShortcutPosition
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior segments and prefixes in the shortcut metric. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

lemma tree_walk_level (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hne : u≠v) (hnadj : ¬T.Adj u v) {x y : V}
    (p : T.Walk x y) (k : ℕ) (hk : k ≤ (avoidingGraph (G := G) T u v).dist x y) :
    ∃ w∈p.support,(avoidingGraph (G := G) T u v).dist x w=k := by
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hle := le_avoidingGraph T u v hT.isAcyclic hA hne hnadj
  obtain ⟨w,hw,hd⟩ := walk_exists_dist_level H hH x (p.mapLe hle) k (by simp) hk
  exact ⟨w,by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hw,hd⟩

/-- A long shortcut path contains a translate of the fixed segment
well inside both ends, and at bounded distance from its first end. -/
theorem exists_interior_segment (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hne : u≠v) (hnadj : ¬T.Adj u v) {x y : V}
    (p : T.Walk x y) (hp : p.IsPath) (r : ℕ)
    (hxy : 2*r+10 ≤ (avoidingGraph (G := G) T u v).dist x y) :
    ∃ g : G, ∀ w∈({u,v} : Set V), g • w∈p.support ∧
      r+1 < (avoidingGraph (G := G) T u v).dist x (g • w) ∧
      r+1 < (avoidingGraph (G := G) T u v).dist y (g • w) ∧
      (avoidingGraph (G := G) T u v).dist x (g • w) ≤ r+8 := by
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hS := avoidingGraph_pathSaturated (G := G) T u v hT.isAcyclic
  obtain ⟨a,ha,hda⟩ := tree_walk_level T u v hT hA hne hnadj p (r+5) (by omega)
  have hay : 2 ≤ H.dist a y := by
    have hh := hH.dist_triangle (u := x) (v := a) (w := y)
    change H.dist x a=r+5 at hda
    change 2*r+10 ≤ H.dist x y at hxy
    dsimp only [H] at *
    omega
  let s := p.dropUntil a ha
  have hs : s.IsPath := hp.dropUntil ha
  obtain ⟨b,hb,hdb⟩ := tree_walk_level T u v hT hA hne hnadj s 2 hay
  let t := s.takeUntil b hb
  have ht : t.IsPath := hs.takeUntil hb
  have hseg : ContainsSegment (G := G) u v T t := by
    by_contra hn
    have hab : a≠b := by
      intro he
      subst b
      simp at hdb
    have hadj := avoidingGraph_subpath T u v hT.isAcyclic t hn
      t.start_mem_support t.end_mem_support hab
    have hd := H.dist_eq_one_iff_adj.mpr hadj
    change H.dist a b=2 at hdb
    omega
  obtain ⟨g,hgu,hgv⟩ := hseg
  refine ⟨g,?_⟩
  intro w hw
  have hgw : g • w∈t.support := by
    rcases Set.mem_insert_iff.mp hw with he|he
    · exact he ▸ hgu
    · exact Set.mem_singleton_iff.mp he ▸ hgv
  have hdist := shortcut_dist_split T H hT hH hS t ht hgw
  change H.dist a b=2 at hdb
  have hnear : H.dist a (g • w) ≤ 3 := by omega
  have hmem : g • w∈p.support :=
    p.support_dropUntil_subset_support ha (s.support_takeUntil_subset_support hb hgw)
  have hx := hH.dist_triangle (u := x) (v := g • w) (w := a)
  have hy := hH.dist_triangle (u := x) (v := a) (w := g • w)
  have hz := hH.dist_triangle (u := x) (v := g • w) (w := y)
  rw [H.dist_comm (u := g • w) (v := a)] at hx
  rw [H.dist_comm (u := g • w) (v := y)] at hz
  refine ⟨hmem,?_,?_,?_⟩ <;> dsimp only [H] at * <;> omega

lemma bounded_vertices_in_prefix (H : SimpleGraph V) (hT : T.IsTree)
    (hH : H.Connected) (hS : PathSaturated T H) {x y b w : V}
    (p : T.Walk x y) (hp : p.IsPath) (hb : b∈p.support) (hw : w∈p.support)
    (K : ℕ) (hdb : H.dist x b=K+2) (hdw : H.dist x w ≤ K) :
    w∈(p.takeUntil b hb).support := by
  rcases prefixes_comparable T p hw hb with h|h
  · exact h
  · have hh := shortcut_dist_split T H hT hH hS (p.takeUntil w hw) (hp.takeUntil hw) h
    omega

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeShortcutAcylindrical
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform acylindricity of the graph obtained by coning off segment-free paths. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

/-- The constants depend only on displacement and on the chosen free
segment, even when the original tree has infinite-valence vertices. -/
theorem avoidingGraph_acylindrical_count (hT : T.IsTree)
    (hA : PreservesAdj (G := G) T) (hfree : pairStabilizer (G := G) u v=⊥)
    (hne : u≠v) (hnadj : ¬T.Adj u v) (r : ℕ) (x y : V)
    (hxy : 2*r+10 ≤ (avoidingGraph (G := G) T u v).dist x y) :
    {g : G | (avoidingGraph (G := G) T u v).dist x (g • x) ≤ r ∧
      (avoidingGraph (G := G) T u v).dist y (g • y) ≤ r}.Finite ∧
    {g : G | (avoidingGraph (G := G) T u v).dist x (g • x) ≤ r ∧
      (avoidingGraph (G := G) T u v).dist y (g • y) ≤ r}.ncard ≤
        (2*r+10)*(2*T.dist u v+1)^2 := by
  let H := avoidingGraph (G := G) T u v
  have hH : H.Connected := avoidingGraph_connected T u v hT hA hne hnadj
  have hS : PathSaturated T H := avoidingGraph_pathSaturated T u v hT.isAcyclic
  have hB : PreservesAdj (G := G) H := avoidingGraph_preservesAdj T u v hA
  obtain ⟨p,hp⟩ := hT.connected.exists_isPath x y
  obtain ⟨a,ha⟩ := exists_interior_segment T u v hT hA hne hnadj p hp r hxy
  obtain ⟨b,hb,hdb⟩ := tree_walk_level T u v hT hA hne hnadj p (2*r+10) hxy
  let q := p.takeUntil b hb
  have hq : q.IsPath := hp.takeUntil hb
  let A : Set G := {g | H.dist x (g • x) ≤ r ∧ H.dist y (g • y) ≤ r}
  let B := segmentOccurrences (G := G) u v T q
  have hmap : ∀ g∈A,g*a∈B := by
    intro g hg
    have hm (w : V) (hw : w∈({u,v} : Set V)) : (g*a) • w∈q.support := by
      obtain ⟨hmem,hleft,hright,hupper⟩ := ha w hw
      have himage : g • (a • w)∈p.support :=
        image_mem_of_deep T H hT hH hS hA hB p hp hmem r hleft hright g hg.1 hg.2
      have hdist : H.dist x (g • (a • w)) ≤ 2*r+8 := by
        have htri := hH.dist_triangle (u := x) (v := g • x) (w := g • (a • w))
        rw [graph_action_dist H hH hB g x (a • w)] at htri
        have hgx : H.dist x (g • x) ≤ r := hg.1
        change H.dist x (a • w) ≤ r+8 at hupper
        omega
      rw [mul_smul]
      exact bounded_vertices_in_prefix T H hT hH hS p hp hb himage (2*r+8)
        (by simpa only [Nat.add_assoc] using hdb) hdist
    exact ⟨hm u (by simp),hm v (by simp)⟩
  have hinj : Function.Injective (fun g : G => g*a) := fun _ _ h => mul_right_cancel h
  have hfinB : B.Finite := segmentOccurrences_finite hfree T q
  have hfinA : A.Finite := (hfinB.preimage hinj.injOn).subset hmap
  refine ⟨hfinA,?_⟩
  calc
    A.ncard ≤ B.ncard := Set.ncard_le_ncard_of_injOn (fun g : G => g*a) hmap hinj.injOn hfinB
    _ ≤ H.dist x b*(2*T.dist u v+1)^2 :=
      segmentOccurrences_bound_dist T u v hT hA hfree hne hnadj q hq
    _ = (2*r+10)*(2*T.dist u v+1)^2 := by rw [hdb]

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_AvoidingRealization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine geodesic acylindrical hyperbolic space of a free tree segment. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

theorem avoiding_realization_geometry (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v) :
    let H := avoidingGraph (G := G) T u v
    let hH := avoidingGraph_connected T u v hT hA hne hnadj
    let hB := avoidingGraph_preservesAdj T u v hA
    let X := GraphRealization.Space H hH
    let _ := GraphRealization.action H hB hH
    IsGeodesicMetric X ∧ IsGromovHyperbolic X ∧
      (∀ g : G,Isometry (fun x : X => g • x)) ∧ IsAcylindrical G X := by
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hB := avoidingGraph_preservesAdj T u v hA
  let _ := GraphRealization.action H hB hH
  refine ⟨GraphRealization.realization_geodesic H hH,?_,GraphRealization.action_isometric H hB hH,?_⟩
  · refine ⟨9,by norm_num,?_⟩
    intro o x y z
    simpa only [gromovProduct,GraphRealization.product,show (3 : ℝ)+6=9 by norm_num] using GraphRealization.realization_hyperbolic H hH 3
      (shortcut_graph_hyperbolic T H hT hH (avoidingGraph_pathSaturated T u v hT.isAcyclic)) o x y z
  · intro ε hε
    let r := Nat.ceil ε
    let R := 2*(r+2)+10
    let N := R*(2*T.dist u v+1)^2
    refine ⟨(R : ℝ)+2,N,?_⟩
    intro x y hxy
    have hcount (a b : V) (hab : R ≤ H.dist a b) :
        {g : G | H.dist a (g • a) ≤ r+2 ∧ H.dist b (g • b) ≤ r+2}.Finite ∧
        {g : G | H.dist a (g • a) ≤ r+2 ∧ H.dist b (g • b) ≤ r+2}.ncard ≤ N :=
      avoidingGraph_acylindrical_count T u v hT hA hfree hne hnadj (r+2) a b hab
    obtain ⟨hfin,hcard⟩ := GraphRealization.acylindricity_transfer H hB hH r R N hcount x y hxy
    have hεr : ε ≤ (r : ℝ) := Nat.le_ceil ε
    have hsub : {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε} ⊆
        {g : G | dist x (g • x) ≤ r ∧ dist y (g • y) ≤ r} :=
      fun _ hg => ⟨hg.1.trans hεr,hg.2.trans hεr⟩
    exact ⟨hfin.subset hsub,(Set.ncard_le_ncard hsub hfin).trans hcard⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreePeriodicPaths
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterating a tree segment without backtracking produces an actual translation axis. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)

lemma periodicPath_length (g : G) {x : V} (p : T.Walk x (g • x)) (n : ℕ) :
    (periodicPath T hA g p n).length=n*p.length := by
  induction n with
  | zero => simp [periodicPath]
  | succ n ih =>
    simp only [periodicPath,SimpleGraph.Walk.length_copy]
    calc
      _ = (periodicPath T hA g p n).length+(p.map (shiftHom T hA (g^n))).length :=
        SimpleGraph.Walk.length_append _ _
      _ = (n+1)*p.length := by rw [ih,SimpleGraph.Walk.length_map,Nat.add_mul,one_mul]

private lemma first_append_nonempty {x y z : V} (p : T.Walk x y) (q : T.Walk y z)
    (hp : ¬p.Nil) : (p.append q).snd=p.snd := by
  cases p with
  | nil => exact (hp .nil).elim
  | cons h p => simp only [SimpleGraph.Walk.cons_append,SimpleGraph.Walk.snd_cons]

lemma periodicPath_reverse_snd (g : G) {x : V} (p : T.Walk x (g • x))
    (hp : ¬p.Nil) (n : ℕ) :
    (periodicPath T hA g p (n+1)).reverse.snd=g^n • p.reverse.snd := by
  unfold periodicPath
  rw [SimpleGraph.Walk.reverse_copy]
  simp only [SimpleGraph.Walk.getVert_copy]
  rw [SimpleGraph.Walk.reverse_append (periodicPath T hA g p n) (p.map (shiftHom T hA (g^n)))]
  change ((p.map (shiftHom T hA (g^n))).reverse.append
    (periodicPath T hA g p n).reverse).snd= _
  rw [first_append_nonempty T _ _ (by
    intro hn
    have hl := hn.length_eq_zero
    simp only [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.length_map] at hl
    exact hp (SimpleGraph.Walk.length_eq_zero_iff.mp hl))]
  rw [SimpleGraph.Walk.reverse_map]
  exact SimpleGraph.Walk.getVert_map _ _ 1

private lemma nil_copy_append {x y z : V} (h : x=y) (q : T.Walk y z) :
    ((.nil : T.Walk x x).copy rfl h).append q=q.copy h.symm rfl := by
  subst y
  rfl

theorem periodicPath_isPath (hT : T.IsAcyclic) (g : G) {x : V}
    (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (n : ℕ) :
    (periodicPath T hA g p n).IsPath := by
  induction n with
  | zero => simp [periodicPath]
  | succ n ih =>
    apply (SimpleGraph.Walk.isPath_copy _ _ _).mpr
    have hmap : (p.map (shiftHom T hA (g^n))).IsPath := hp.map (MulAction.toPerm (g^n)).injective
    by_cases hn : n=0
    · subst n
      simp only [periodicPath,nil_copy_append]
      exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr hmap
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hne : (periodicPath T hA g p (k+1)).reverse.snd≠
          (p.map (shiftHom T hA (g^(k+1)))).snd := by
        rw [periodicPath_reverse_snd T hA g p hpn k]
        change g^k • p.reverse.snd ≠ (p.map (shiftHom T hA (g^(k+1)))).getVert 1
        rw [SimpleGraph.Walk.getVert_map]
        change g^k • p.reverse.snd ≠ g^(k+1) • p.snd
        rw [pow_succ,mul_smul]
        exact fun he => hturn ((MulAction.toPerm (g^k)).injective he)
      have h := reverse_append_isPath T hT
        (periodicPath T hA g p (k+1)).reverse (p.map (shiftHom T hA (g^(k+1))))
        ih.reverse hmap hne
      simpa only [SimpleGraph.Walk.reverse_reverse] using h

include hA in
theorem periodic_orbit_distance (hT : T.IsAcyclic) (g : G) {x : V}
    (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (n : ℕ) :
    T.dist x (g^n • x)=n*p.length := by
  rw [←path_length_eq_dist T hT _ (periodicPath_isPath T hA hT g p hp hpn hturn n),
    periodicPath_length]

lemma periodicPath_support_step (g : G) {x : V} (p : T.Walk x (g • x)) (n : ℕ) :
    (periodicPath T hA g p n).support ⊆ (periodicPath T hA g p (n+1)).support := by
  simp only [periodicPath,SimpleGraph.Walk.support_copy]
  exact SimpleGraph.Walk.support_subset_support_append_left _ _

lemma periodicPath_translate_mem (g : G) {x w : V} (p : T.Walk x (g • x))
    (hw : w∈p.support) (n : ℕ) :
    g^n • w∈(periodicPath T hA g p (n+1)).support := by
  simp only [periodicPath,SimpleGraph.Walk.support_copy]
  apply SimpleGraph.Walk.support_subset_support_append_right
  rw [SimpleGraph.Walk.support_map]
  exact List.mem_map.mpr ⟨w,hw,rfl⟩

lemma periodicPath_translate_mem_of_lt (g : G) {x w : V} (p : T.Walk x (g • x))
    (hw : w∈p.support) (k n : ℕ) (hkn : k < n) :
    g^k • w∈(periodicPath T hA g p n).support := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hk : k < n
    · exact periodicPath_support_step T hA g p n (ih hk)
    · have he : k=n := by omega
      subst k
      exact periodicPath_translate_mem T hA g p hw n

lemma periodicPath_vertex_mem (g : G) {x : V} (p : T.Walk x (g • x))
    (k n : ℕ) (hkn : k ≤ n) : g^k • x∈(periodicPath T hA g p n).support := by
  rcases lt_or_eq_of_le hkn with h|h
  · exact periodicPath_translate_mem_of_lt T hA g p p.start_mem_support k n h
  · subst k
    exact (periodicPath T hA g p n).end_mem_support

lemma periodicPath_snd (g : G) {x : V} (p : T.Walk x (g • x))
    (hpn : ¬p.Nil) (n : ℕ) : (periodicPath T hA g p (n+1)).snd=p.snd := by
  induction n with
  | zero =>
    change (periodicPath T hA g p (0+1)).getVert 1=p.getVert 1
    simp only [periodicPath,nil_copy_append,SimpleGraph.Walk.getVert_copy,
      SimpleGraph.Walk.getVert_map,pow_zero]
    exact one_smul G (p.getVert 1)
  | succ n ih =>
    change (periodicPath T hA g p (n+1+1)).getVert 1=p.snd
    rw [periodicPath,SimpleGraph.Walk.getVert_copy]
    have hn : ¬(periodicPath T hA g p (n+1)).Nil := by
      intro hn
      have hl := hn.length_eq_zero
      rw [periodicPath_length] at hl
      have hpos : 0 < p.length := Nat.pos_of_ne_zero (fun he => hpn (SimpleGraph.Walk.length_eq_zero_iff.mp he))
      exact (Nat.mul_pos (Nat.succ_pos n) hpos).ne' hl
    exact (first_append_nonempty T _ _ hn).trans ih

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeTranslationSegment
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflecting a segment at both ends constructs a tree translation. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)

lemma actPath_copy_length (g : G) {x y x' y' : V} (p : T.Walk x y)
    (hx : g • x=x') (hy : g • y=y') :
    ((actPath T hA g p).copy hx hy).length=p.length :=
  (SimpleGraph.Walk.length_copy _ _ _).trans (SimpleGraph.Walk.length_map _ _)

lemma actPath_copy_snd (g : G) {x y x' y' : V} (p : T.Walk x y)
    (hx : g • x=x') (hy : g • y=y') :
    ((actPath T hA g p).copy hx hy).snd=g • p.snd := by
  change ((actPath T hA g p).copy hx hy).getVert 1=g • p.getVert 1
  rw [SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_map]
  rfl

lemma actPath_copy_reverse_snd (g : G) {x y x' y' : V} (p : T.Walk x y)
    (hx : g • x=x') (hy : g • y=y') :
    ((actPath T hA g p).copy hx hy).reverse.snd=g • p.reverse.snd := by
  change ((actPath T hA g p).copy hx hy).reverse.getVert 1=g • p.reverse.getVert 1
  rw [SimpleGraph.Walk.reverse_copy,SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.reverse_map,
    SimpleGraph.Walk.getVert_map]
  rfl

lemma append_first {x y z : V} (p : T.Walk x y) (q : T.Walk y z)
    (hp : ¬p.Nil) : (p.append q).snd=p.snd := by
  cases p with
  | nil => exact (hp .nil).elim
  | cons h p => simp only [SimpleGraph.Walk.cons_append,SimpleGraph.Walk.snd_cons]

include hA in
theorem translation_segment (hT : T.IsAcyclic) {u v : V}
    (p : T.Walk u v) (hp : p.IsPath) (hpn : ¬p.Nil)
    (a b : G) (ha : a • u=u) (hb : b • v=v)
    (ha' : a • p.snd≠p.snd) (hb' : b • p.reverse.snd≠p.reverse.snd) :
    ∃ q : T.Walk u ((a*b) • u), q.IsPath ∧ ¬q.Nil ∧
      q.reverse.snd≠(a*b) • q.snd ∧ a • u∈q.support ∧ a • v∈q.support := by
  let l := (actPath T hA a p).copy ha rfl
  let r := (actPath T hA (a*b) p.reverse).copy (by rw [mul_smul,hb]) rfl
  have hl : l.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).mpr (hp.map (MulAction.toPerm a).injective)
  have hr : r.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).mpr (hp.reverse.map (MulAction.toPerm (a*b)).injective)
  have hlenl : l.length=p.length := by simp only [l,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map]
  have hlenr : r.length=p.length := by simp only [r,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map,SimpleGraph.Walk.length_reverse]
  have hn : 0 < p.length := Nat.pos_of_ne_zero (fun he => hpn (SimpleGraph.Walk.length_eq_zero_iff.mp he))
  have hln : ¬l.Nil := fun h => (by have he := h.length_eq_zero; omega)
  have hrn : ¬r.reverse.Nil := by
    intro h
    have he := h.length_eq_zero
    rw [SimpleGraph.Walk.length_reverse,hlenr] at he
    omega
  have hls : l.snd=a • p.snd := actPath_copy_snd T hA a p ha rfl
  have hlrs : l.reverse.snd=a • p.reverse.snd := actPath_copy_reverse_snd T hA a p ha rfl
  have hrs : r.snd=(a*b) • p.reverse.snd :=
    actPath_copy_snd T hA (a*b) p.reverse _ rfl
  have hrrs : r.reverse.snd=(a*b) • p.snd := by
    simpa only [SimpleGraph.Walk.reverse_reverse] using
      actPath_copy_reverse_snd T hA (a*b) p.reverse (by rw [mul_smul,hb]) rfl
  have hsep : l.reverse.snd≠r.snd := by
    rw [hlrs,hrs,mul_smul]
    exact fun he => hb' ((MulAction.toPerm a).injective he).symm
  have hq : (l.append r).IsPath := by
    have h := reverse_append_isPath T hT l.reverse r hl.reverse hr hsep
    simpa only [SimpleGraph.Walk.reverse_reverse] using h
  refine ⟨l.append r,hq,?_,?_,?_,?_⟩
  · intro h
    have he := h.length_eq_zero
    rw [SimpleGraph.Walk.length_append,hlenl,hlenr] at he
    omega
  · rw [SimpleGraph.Walk.reverse_append,append_first T r.reverse l.reverse hrn,
      append_first T l r hln,hls,hrrs]
    exact fun he => ha' ((MulAction.toPerm (a*b)).injective he).symm
  · rw [ha]
    exact (l.append r).start_mem_support
  · exact SimpleGraph.Walk.support_subset_support_append_left l r l.end_mem_support

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeBoundaryRays
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct directions of tree rays determine distinct shortcut-boundary points. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T H : SimpleGraph V)

lemma separated_graphProduct (hT : T.IsTree) (hH : H.Connected) (hS : PathSaturated T H)
    {x a b : V} (p : T.Walk x a) (q : T.Walk x b) (hp : p.IsPath) (hq : q.IsPath)
    (hsep : p.Nil ∨ q.Nil ∨ p.snd≠q.snd) : graphProduct H x a b ≤ 1/2 := by
  rcases hsep with hn|hn|hne
  · cases hn
    unfold graphProduct
    rw [SimpleGraph.dist_self]
    simp
  · cases hn
    unfold graphProduct
    rw [SimpleGraph.dist_self,H.dist_comm (u := a) (v := x)]
    simp
  · have hpq := reverse_append_isPath T hT.isAcyclic p q hp hq hne
    have hx : x∈(p.reverse.append q).support :=
      SimpleGraph.Walk.support_subset_support_append_right _ _ q.start_mem_support
    have h := shortcut_dist_split T H hT hH hS (p.reverse.append q) hpq hx
    rw [H.dist_comm (u := a) (v := x)] at h
    have h' : (H.dist x a : ℝ)+H.dist x b ≤ H.dist a b+1 := by exact_mod_cast h
    unfold graphProduct
    linarith

variable (hA : PreservesAdj (G := G) T)

lemma inverseSegment_isPath (g : G) {x : V} (p : T.Walk x (g • x)) (hp : p.IsPath) :
    (inverseSegment T hA g p).IsPath :=
  (SimpleGraph.Walk.isPath_copy _ _ _).mpr (hp.reverse.map (MulAction.toPerm g⁻¹).injective)

lemma inverseSegment_snd (g : G) {x : V} (p : T.Walk x (g • x)) :
    (inverseSegment T hA g p).snd=g⁻¹ • p.reverse.snd :=
  actPath_copy_snd T hA g⁻¹ p.reverse _ rfl

lemma inverseSegment_reverse_snd (g : G) {x : V} (p : T.Walk x (g • x)) :
    (inverseSegment T hA g p).reverse.snd=g⁻¹ • p.snd := by
  simpa only [inverseSegment,SimpleGraph.Walk.reverse_reverse] using
    actPath_copy_reverse_snd T hA g⁻¹ p.reverse (by simp) rfl

lemma inverseSegment_nonempty (g : G) {x : V} (p : T.Walk x (g • x)) (hpn : ¬p.Nil) :
    ¬(inverseSegment T hA g p).Nil := by
  intro hn
  have hl := hn.length_eq_zero
  simp only [inverseSegment,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map,
    SimpleGraph.Walk.length_reverse] at hl
  exact hpn (SimpleGraph.Walk.length_eq_zero_iff.mp hl)

lemma inverseSegment_turn (g : G) {x : V} (p : T.Walk x (g • x))
    (hturn : p.reverse.snd≠g • p.snd) :
    (inverseSegment T hA g p).reverse.snd≠g⁻¹ • (inverseSegment T hA g p).snd := by
  rw [inverseSegment_reverse_snd,inverseSegment_snd]
  intro he
  have h₁ := congrArg (fun w : V => g • w) he
  simp only [smul_inv_smul] at h₁
  have h₂ := congrArg (fun w : V => g • w) h₁
  simp only [smul_inv_smul] at h₂
  exact hturn h₂.symm

lemma inverseSegment_mem (g a : G) {x w : V} (p : T.Walk x (g • x))
    (hw : a • w∈p.support) : (g⁻¹*a) • w∈(inverseSegment T hA g p).support := by
  simp only [inverseSegment,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map]
  apply List.mem_map.mpr
  refine ⟨a • w,?_,?_⟩
  · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw
  · exact (mul_smul g⁻¹ a w).symm

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreePeriodicGrowth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic translates of a free segment give boundary points of the shortcut graph. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)
include hA

lemma periodic_powers_injective (hT : T.IsAcyclic) (g : G) {x : V}
    (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) : Function.Injective (fun n : ℕ => g^n) := by
  intro m n he
  have hd := congrArg (fun a : G => T.dist x (a • x)) he
  rw [periodic_orbit_distance T hA hT g p hp hpn hturn m,
    periodic_orbit_distance T hA hT g p hp hpn hturn n] at hd
  have hpos : 0 < p.length := Nat.pos_of_ne_zero (fun hz => hpn (SimpleGraph.Walk.length_eq_zero_iff.mp hz))
  exact Nat.mul_right_cancel hpos hd

theorem periodic_occurrences (hT : T.IsAcyclic) (g : G) {x u v : V}
    (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd)
    (hfree : pairStabilizer (G := G) u v=⊥) (a : G)
    (hau : a • u∈p.support) (hav : a • v∈p.support) (n : ℕ) :
    n ≤ (segmentOccurrences (G := G) u v T (periodicPath T hA g p n)).ncard := by
  let f (k : Fin n) : G := g^k.val*a
  have hmem (k : Fin n) : f k∈segmentOccurrences (G := G) u v T (periodicPath T hA g p n) := by
    constructor
    · change (g^k.val*a) • u∈_
      rw [mul_smul]
      exact periodicPath_translate_mem_of_lt T hA g p hau k.val n k.isLt
    · change (g^k.val*a) • v∈_
      rw [mul_smul]
      exact periodicPath_translate_mem_of_lt T hA g p hav k.val n k.isLt
  have hinj : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact periodic_powers_injective T hA hT g p hp hpn hturn (mul_right_cancel he)
  have hc := Set.ncard_le_ncard_of_injOn (s := Set.univ) f (fun k _ => hmem k) hinj.injOn
    (segmentOccurrences_finite hfree T (periodicPath T hA g p n))
  simpa only [Set.ncard_univ,Nat.card_fin] using hc

theorem periodic_shortcut_growth (hT : T.IsTree) (u v : V)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v)
    (g : G) {x : V} (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (a : G)
    (hau : a • u∈p.support) (hav : a • v∈p.support) (n : ℕ) :
    n ≤ (avoidingGraph (G := G) T u v).dist x (g^n • x)*(2*T.dist u v+1)^2 := by
  exact (periodic_occurrences T hA hT.isAcyclic g p hp hpn hturn hfree a hau hav n).trans
    (segmentOccurrences_bound_dist T u v hT hA hfree hne hnadj (periodicPath T hA g p n)
      (periodicPath_isPath T hA hT.isAcyclic g p hp hpn hturn n))

theorem periodic_shortcut_escape (hT : T.IsTree) (u v : V)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v)
    (g : G) {x : V} (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (a : G)
    (hau : a • u∈p.support) (hav : a • v∈p.support) (R : ℝ) :
    ∃ N : ℕ,∀ n,N ≤ n → R ≤ ((avoidingGraph (G := G) T u v).dist x (g^n • x) : ℝ) := by
  let C := (2*T.dist u v+1)^2
  refine ⟨Nat.ceil (R*C),?_⟩
  intro n hn
  have hc : (0 : ℝ) < C := by dsimp only [C] <;> positivity
  have h₁ : R*C ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h₂ : (n : ℝ) ≤ ((avoidingGraph (G := G) T u v).dist x (g^n • x) : ℝ)*C := by
    exact_mod_cast periodic_shortcut_growth T hA hT u v hfree hne hnadj g p hp hpn hturn a hau hav n
  exact (mul_le_mul_iff_left₀ hc).mp (by simpa only [mul_comm] using h₁.trans h₂)

theorem periodic_shortcut_gromov (hT : T.IsTree) (u v : V)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v)
    (g : G) {x : V} (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (a : G)
    (hau : a • u∈p.support) (hav : a • v∈p.support) (R : ℝ) :
    ∃ N : ℕ,∀ m,N ≤ m → ∀ n,N ≤ n →
      R ≤ graphProduct (avoidingGraph (G := G) T u v) x (g^m • x) (g^n • x) := by
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hS := avoidingGraph_pathSaturated (G := G) T u v hT.isAcyclic
  obtain ⟨N,hN⟩ := periodic_shortcut_escape T hA hT u v hfree hne hnadj g p hp hpn hturn a hau hav (R+1)
  refine ⟨N,?_⟩
  have hordered (m n : ℕ) (hm : N ≤ m) (hmn : m ≤ n) :
      R ≤ graphProduct H x (g^m • x) (g^n • x) := by
    have h := shortcut_dist_split T H hT hH hS (periodicPath T hA g p n)
      (periodicPath_isPath T hA hT.isAcyclic g p hp hpn hturn n)
      (periodicPath_vertex_mem T hA g p m n hmn)
    have h' : (H.dist x (g^m • x) : ℝ)+H.dist (g^m • x) (g^n • x) ≤ H.dist x (g^n • x)+1 := by
      exact_mod_cast h
    have hd := hN m hm
    change R+1 ≤ (H.dist x (g^m • x) : ℝ) at hd
    unfold graphProduct
    linarith
  intro m hm n hn
  rcases le_total m n with h|h
  · exact hordered m n hm h
  · have he : graphProduct H x (g^m • x) (g^n • x)=graphProduct H x (g^n • x) (g^m • x) := by
      unfold graphProduct
      rw [H.dist_comm (u := g^m • x) (v := g^n • x)]
      ring
    rw [he]
    exact hordered n m hn h

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_AvoidingBoundaryRays
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tree rays give three distinct orbit limit points in the genuine metric realization. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
open GraphRealization
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

lemma realization_orbit_product (H : SimpleGraph V) (hH : H.Connected)
    (hB : PreservesAdj (G := G) H) (x : V) (g h : G) :
    gromovProduct (vertex H hH x) (act H hB hH g (vertex H hH x))
      (act H hB hH h (vertex H hH x))=graphProduct H x (g • x) (h • x) := by
  rw [act_vertex,act_vertex]
  simp only [gromovProduct,graphProduct,dist_vertex]

theorem realization_three_rays (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hne : u≠v) (hnadj : ¬T.Adj u v)
    (x : V) (seq : Fin 3 → ℕ → G) (P : ∀ i n,T.Walk x (seq i n • x))
    (hP : ∀ i n,(P i n).IsPath) (hzero : ∀ i,(P i 0).Nil)
    (d : Fin 3 → V) (hd : Function.Injective d)
    (hfirst : ∀ i n,0 < n → (P i n).snd=d i)
    (hseq : ∀ (i : Fin 3) (R : ℝ), ∃ N : ℕ,∀ m,N ≤ m → ∀ n,N ≤ n →
      R ≤ graphProduct (avoidingGraph (G := G) T u v) x (seq i m • x) (seq i n • x)) :
    let H := avoidingGraph (G := G) T u v
    let hH := avoidingGraph_connected T u v hT hA hne hnadj
    let hB := avoidingGraph_preservesAdj T u v hA
    let _ := action H hB hH
    HasThreeOrbitLimitPoints G (Space H hH) := by
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hB := avoidingGraph_preservesAdj T u v hA
  let _ := action H hB hH
  refine ⟨vertex H hH x,seq,?_,?_⟩
  · intro i R
    obtain ⟨N,hN⟩ := hseq i R
    refine ⟨N,?_⟩
    intro m hm n hn
    change R ≤ gromovProduct (vertex H hH x) (act H hB hH (seq i m) (vertex H hH x))
      (act H hB hH (seq i n) (vertex H hH x))
    rw [realization_orbit_product]
    exact hN m hm n hn
  · intro i j hij
    refine ⟨1/2,?_⟩
    intro m n
    change gromovProduct (vertex H hH x) (act H hB hH (seq i m) (vertex H hH x))
      (act H hB hH (seq j n) (vertex H hH x)) ≤ 1/2
    rw [realization_orbit_product]
    apply separated_graphProduct T H hT hH (avoidingGraph_pathSaturated T u v hT.isAcyclic)
      (P i m) (P j n) (hP i m) (hP j n)
    by_cases hm : m=0
    · exact Or.inl (hm ▸ hzero i)
    by_cases hn : n=0
    · exact Or.inr (Or.inl (hn ▸ hzero j))
    refine Or.inr (Or.inr ?_)
    rw [hfirst i m (Nat.pos_of_ne_zero hm),hfirst j n (Nat.pos_of_ne_zero hn)]
    exact fun he => hij (hd he)

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_NormalParabolic
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal parabolics in irreducible Artin groups

This proves the sufficient case of Charney--Martin--Morris-Wright (2026),
Lemma 3.3, used in the visual-splitting argument. The obstruction is detected
in the actual Coxeter geometric representation, without any assumption on
positive-monoid embeddings.
-/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)

omit [Fintype S] in
lemma artinCoxeter_mem_parabolic {X : Set S} {a : Artin M}
    (ha : a ∈ artinParabolic M X) :
    artinCoxeter M a ∈ coxeterParabolic M X := by
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨s,hs,rfl⟩ := hx
    rw [artinCoxeter_generator]
    exact Subgroup.subset_closure ⟨s,hs,rfl⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy => rw [map_mul]; exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih => rw [map_inv]; exact Subgroup.inv_mem _ ih

/-- The standard generators in a standard parabolic are exactly its type. -/
lemma generator_mem_standard_iff (X : Set S) (t : S) :
    generator M t ∈ artinParabolic M X ↔ t∈X := by
  constructor
  · intro h
    by_contra ht
    have he := parabolic_exterior M X ⟨_,artinCoxeter_mem_parabolic M h⟩
      (Pi.single t 1) t ht
    change representation M.toCoxeterSystem (artinCoxeter M (generator M t))
      (Pi.single t 1) t=(Pi.single t 1 : S → ℝ) t at he
    rw [artinCoxeter_generator,representation_simple,simpleReflection_apply] at he
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same,
      Matrix.mulVec_single,Matrix.col,Matrix.transpose_apply,MulOpposite.op_one,
      one_smul,cartan_diag] at he
    norm_num at he
  · intro ht
    exact Subgroup.subset_closure ⟨t,ht,rfl⟩

lemma standard_ne_top_of_ne_univ {X : Set S} (hX : X≠Set.univ) :
    artinParabolic M X≠⊤ := by
  intro he
  apply hX
  apply Set.eq_univ_of_forall
  intro t
  apply (generator_mem_standard_iff M X t).mp
  rw [he]
  trivial

omit [Fintype S] in
lemma cartan_ne_zero_of_not_commuting (s t : S) (hst : s ≠ t) (hlabel : M s t ≠ 2) :
    cartan M s t ≠ 0 := by
  by_cases hz : M s t=0
  · simp [cartan,hst,hz]
  · have hm : 3 ≤ M s t := by have := M.off_diagonal s t hst; omega
    have hmr : (2 : ℝ)<M s t := by exact_mod_cast (by omega : 2<M s t)
    have hp : 0 < Real.pi/(M s t : ℝ) := div_pos Real.pi_pos (by linarith)
    have hlt : Real.pi/(M s t : ℝ)<Real.pi/2 := by
      apply (div_lt_div_iff₀ (by linarith : (0 : ℝ)<M s t) (by norm_num)).mpr
      nlinarith [Real.pi_pos]
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hlt⟩
    simp only [cartan,ite_eq_right hst,ite_eq_right hz]
    exact mul_ne_zero (by norm_num) (ne_of_gt hc)

/-- A noncommuting generator outside a standard parabolic does not normalize it. -/
theorem generator_conjugate_not_mem {X : Set S} {s t : S}
    (hs : s∈X) (ht : t∉X) (hlabel : M s t≠2) :
    generator M t * generator M s * (generator M t)⁻¹ ∉ artinParabolic M X := by
  intro h
  have hst : s≠t := fun he => ht (he ▸ hs)
  have hc := cartan_ne_zero_of_not_commuting M s t hst hlabel
  have he := parabolic_exterior M X ⟨_,artinCoxeter_mem_parabolic M h⟩
    (Pi.single t 1) t ht
  have hinv : (simpleReflection M t)⁻¹=simpleReflection M t := by
    exact inv_eq_of_mul_eq_one_left (simpleReflection_squared M t)
  simp only [map_mul,map_inv,artinCoxeter_generator,representation_simple,hinv,
    LinearEquiv.mul_apply] at he
  rw [simpleReflection_apply,simpleReflection_apply,simpleReflection_apply] at he
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same,
    Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.mulVec_single,
    Matrix.col,Matrix.transpose_apply,MulOpposite.op_one,one_smul,cartan_diag,
    Pi.single_eq_of_ne hst.symm] at he
  rw [cartan_symm M t s] at he
  nlinarith [sq_pos_of_ne_zero hc]

/-- CMMW Lemma 3.3: in irreducible type a normal standard parabolic is
trivial or the whole Artin group. -/
theorem normal_standard_parabolic (hIrred : IsIrreducible M) (X : Set S)
    (hn : (artinParabolic M X).Normal) : X=∅ ∨ X=Set.univ := by
  by_cases hx : X=∅
  · exact Or.inl hx
  right
  by_contra hu
  have hx' : X.Nonempty := Set.nonempty_iff_ne_empty.mpr hx
  have hu' : Xᶜ.Nonempty := Set.nonempty_compl.mpr hu
  obtain ⟨s,hs,t,ht,hst⟩ := hIrred X hx' hu'
  have hgen : generator M s ∈ artinParabolic M X := Subgroup.subset_closure ⟨s,hs,rfl⟩
  exact generator_conjugate_not_mem M hs ht hst (hn.conj_mem _ hgen _)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_CoxeterChainRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive roots carried along a simple path in the noncommutation graph. -/
namespace HarmonicArtin.ParabolicIntersections
open Geometric CoxeterExchange
open scoped _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)

lemma reflection_nonneg_of_zero (a : S) (x : S → ℝ) (hx : ∀ i, 0≤x i) (ha : x a=0) :
    ∀ i, 0 ≤ simpleReflection M a x i := by
  have hr : (cartan M *ᵥ x) a≤0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : a=j
    · subst j
      rw [ha,mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (cartan_off_nonpos M a j hj) (hx j)
  intro i
  rw [simpleReflection_apply]
  by_cases hi : i=a
  · subst i
    simpa only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same,mul_one,ha,zero_sub]
      using neg_nonneg.mpr hr
  · simpa only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_of_ne hi,mul_zero,sub_zero]
      using hx i

lemma reflection_pos_of_neighbor (a b : S) (hab : a≠b) (hm : M a b≠2)
    (x : S → ℝ) (hx : ∀ i, 0≤x i) (ha : x a=0) (hb : 0<x b) :
    0 < simpleReflection M a x a := by
  have hc : cartan M a b<0 :=
    lt_of_le_of_ne (cartan_off_nonpos M a b hab) (cartan_ne_zero_of_not_commuting M a b hab hm)
  have hrow : (cartan M *ᵥ x) a<0 := by
    change (∑ j, cartan M a j*x j)<0
    have hsum := Finset.sum_lt_sum (s := (Finset.univ : Finset S))
      (f := fun j => cartan M a j*x j) (g := fun _ => (0 : ℝ))
      (by
        intro j _
        by_cases hj : a=j
        · subst j
          rw [ha,mul_zero]
        · exact mul_nonpos_of_nonpos_of_nonneg (cartan_off_nonpos M a j hj) (hx j))
      ⟨b,Finset.mem_univ _,mul_neg_of_neg_of_pos hc hb⟩
    simpa only [Finset.sum_const_zero] using hsum
  rw [simpleReflection_apply]
  simpa only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same,mul_one,ha,zero_sub]
    using neg_pos.mpr hrow

/-- A word of distinct vertices along a noncommutation path carries the
last simple root to a nonnegative root positive at every vertex of the path. -/
theorem root_along_chain (u : List S) (s : S) (hN : (u++[s]).Nodup)
    (hC : (u++[s]).IsChain (fun a b => a≠b ∧ M a b≠2)) :
    let x := representation M.toCoxeterSystem (M.toCoxeterSystem.wordProd u) (Pi.single s 1)
    (∀ i, 0 ≤ x i) ∧ (∀ i∈u++[s], 0 < x i) ∧ (∀ i, i∉u++[s] → x i=0) := by
  induction u with
  | nil =>
    simp only [List.nil_append,CoxeterSystem.wordProd_nil,map_one]
    change (∀ i, 0 ≤ (Pi.single s (1 : ℝ) : S → ℝ) i) ∧
      (∀ i∈[s], 0 < (Pi.single s (1 : ℝ) : S → ℝ) i) ∧
      (∀ i, i∉[s] → (Pi.single s (1 : ℝ) : S → ℝ) i=0)
    refine ⟨?_,?_,?_⟩
    · intro i
      by_cases hi : i=s <;> simp [hi]
    · intro i hi
      have hi' : i=s := List.mem_singleton.mp hi
      subst i
      simpa only [Pi.single_eq_same] using (zero_lt_one : (0 : ℝ)<1)
    · intro i hi
      exact Pi.single_eq_of_ne (by simpa only [List.mem_singleton] using hi) 1
  | cons a u ih =>
    obtain ⟨hna,hn⟩ := List.nodup_cons.mp hN
    have hc : (u++[s]).IsChain (fun a b => a≠b ∧ M a b≠2) := hC.tail
    obtain ⟨hx,hpos,hzero⟩ := ih hn hc
    let x := representation M.toCoxeterSystem (M.toCoxeterSystem.wordProd u) (Pi.single s 1)
    have hxa : x a=0 := hzero a hna
    obtain ⟨b,hb,hab,hm⟩ : ∃ b∈u++[s], a≠b ∧ M a b≠2 := by
      cases u with
      | nil => exact ⟨s,by simp,(List.isChain_cons_cons.mp hC).1⟩
      | cons b u => exact ⟨b,by simp,(List.isChain_cons_cons.mp hC).1⟩
    have hpa := reflection_pos_of_neighbor M a b hab hm x hx hxa (hpos b hb)
    simp only [List.cons_append,CoxeterSystem.wordProd_cons,map_mul,LinearEquiv.mul_apply,
      representation_simple]
    change (∀ i,0 ≤ simpleReflection M a x i) ∧
      (∀ i∈a::(u++[s]),0 < simpleReflection M a x i) ∧
      (∀ i,i∉a::(u++[s]) → simpleReflection M a x i=0)
    refine ⟨reflection_nonneg_of_zero M a x hx hxa,?_,?_⟩
    · intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · exact hpa
      · have hia : i≠a := fun he => hna (he ▸ hi)
        simpa only [simpleReflection_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
          Pi.single_eq_of_ne hia,mul_zero,sub_zero] using hpos i hi
    · intro i hi
      have hia : i≠a := fun he => hi (List.mem_cons.mpr (Or.inl he))
      have hiu : i∉u++[s] := fun hm => hi (List.mem_cons_of_mem a hm)
      simpa only [simpleReflection_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
        Pi.single_eq_of_ne hia,mul_zero,sub_zero] using hzero i hiu

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_CoxeterChainMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A noncommutation path starting outside a parabolic gives a minimal
Coxeter coset representative. -/
namespace HarmonicArtin.ParabolicIntersections
open Geometric CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)
local notation "cs" => M.toCoxeterSystem

lemma conjugate_simple_not_parabolic (X : Set S) (w : M.Group) (s t : S) (ht : t∉X)
    (hr : representation cs w (Pi.single s 1) t≠0) :
    w*(cs).simple s*w⁻¹∉parabolic cs X := by
  intro hm
  let x := representation cs w (Pi.single s 1)
  have hn : simpleReflection M s (Pi.single s 1)=-(Pi.single s 1) := by
    simp only [simpleReflection_apply,Matrix.mulVec_single,Matrix.col,Matrix.transpose_apply,
      MulOpposite.op_one,one_smul,cartan_diag]
    module
  have he : representation cs (w*(cs).simple s*w⁻¹) x=-x := by
    calc
      representation cs (w*(cs).simple s*w⁻¹) x =
          representation cs ((w*(cs).simple s*w⁻¹)*w) (Pi.single s 1) := by
        exact (DFunLike.congr_fun (map_mul (representation cs)
          (w*(cs).simple s*w⁻¹) w) (Pi.single s 1)).symm
      _ = representation cs (w*(cs).simple s) (Pi.single s 1) := by
        congr 2
        group
      _ = representation cs w (simpleReflection M s (Pi.single s 1)) := by
        rw [map_mul,LinearEquiv.mul_apply,representation_simple]
      _ = -x := by rw [hn,map_neg]
  have hx := parabolic_exterior M X ⟨_,hm⟩ x t ht
  change representation cs (w*(cs).simple s*w⁻¹) x t=x t at hx
  rw [he] at hx
  change -x t=x t at hx
  exact hr (by change x t=0; linarith)

lemma minimum_append_chain (X : Set S) (u : List S) (s t : S)
    (hmin : IsParabolicMinimum cs X ((cs).wordProd u))
    (hN : (u++[s]).Nodup)
    (hC : (u++[s]).IsChain (fun a b => a≠b ∧ M a b≠2))
    (ht : t∈u++[s]) (htX : t∉X) :
    IsParabolicMinimum cs X ((cs).wordProd (u++[s])) := by
  rw [(cs).wordProd_append,(cs).wordProd_singleton]
  rcases parabolic_minimum_step cs X _ hmin s with h|⟨j,hj,he⟩
  · exact h
  · have hr := (root_along_chain M u s hN hC).2.1 t ht
    apply False.elim
    apply conjugate_simple_not_parabolic M X ((cs).wordProd u) s t htX (ne_of_gt hr)
    have hh : (cs).wordProd u*(cs).simple s*((cs).wordProd u)⁻¹=(cs).simple j := by
      rw [he,mul_inv_cancel_right]
    rw [hh]
    exact simple_mem_parabolic cs X hj

/-- Every prefix of a simple noncommutation path starting outside `X` is
minimal in its left `X`-coset. -/
theorem chain_word_minimum (X : Set S) (a : S) (ha : a∉X) (u : List S)
    (hN : (a::u).Nodup) (hC : (a::u).IsChain (fun a b => a≠b ∧ M a b≠2)) :
    IsParabolicMinimum cs X ((cs).wordProd (a::u)) := by
  induction u using List.reverseRecOn with
  | nil =>
    apply minimum_append_chain M X [] a a
    · intro g _
      simp only [(cs).wordProd_nil,(cs).length_one]
      exact Nat.zero_le _
    · exact hN
    · exact hC
    · simp only [List.nil_append,List.mem_singleton]
    · exact ha
  | append_singleton u s ih =>
    have hn : ((a::u)++[s]).Nodup := hN
    have hc : ((a::u)++[s]).IsChain (fun a b => a≠b ∧ M a b≠2) := hC
    apply minimum_append_chain M X (a::u) s a
    · exact ih (List.nodup_append.mp hn).1 hc.left_of_append
    · exact hn
    · exact hc
    · exact List.mem_append_left _ List.mem_cons_self
    · exact ha

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicCosetProjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical minimal coset representatives and their parabolic components. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    (J : Set S)

lemma parabolicRep_of_minimum (v : W) (hv : IsParabolicMinimum cs J v) :
    parabolicRep cs J v=v :=
  parabolicRep_eq_of_decomposition cs J v 1 v (parabolic cs J).one_mem hv (one_mul v).symm

lemma parabolicRep_left_mul (a w : W) (ha : a ∈ parabolic cs J) :
    parabolicRep cs J (a*w)=parabolicRep cs J w := by
  apply parabolicRep_eq_of_decomposition cs J (a*w) (a*parabolicComponent cs J w)
    (parabolicRep cs J w) ((parabolic cs J).mul_mem ha (parabolicComponent_mem cs J w))
    (parabolicRep_min cs J w)
  rw [mul_assoc,parabolicComponent_mul_rep]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_CoxeterProjectionSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parabolic projection preserves any standard subgroup containing its input. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

private lemma component_one (X : Set S) : parabolicComponent cs X 1=1 := by
  have hr : parabolicRep cs X 1=1 := parabolicRep_of_minimum cs X 1 (by
    intro a _
    rw [cs.length_one]
    exact Nat.zero_le _)
  simp only [parabolicComponent,hr,inv_one,mul_one]

lemma rep_mem_of_component_mem (X C : Set S) (w : W)
    (hw : w∈parabolic cs C) (hc : parabolicComponent cs X w∈parabolic cs C) :
    parabolicRep cs X w∈parabolic cs C := by
  have he : parabolicRep cs X w=(parabolicComponent cs X w)⁻¹*w := by
    exact (eq_inv_mul_iff_mul_eq).mpr (parabolicComponent_mul_rep cs X w)
  rw [he]
  exact (parabolic cs C).mul_mem ((parabolic cs C).inv_mem hc) hw

lemma component_step_mem (X C : Set S) (w : W) (s : S)
    (hw : w∈parabolic cs C) (hc : parabolicComponent cs X w∈parabolic cs C) (hs : s∈C) :
    parabolicComponent cs X (w*cs.simple s)∈parabolic cs C := by
  have hr := rep_mem_of_component_mem cs X C w hw hc
  have hh : parabolicStepRatio cs X w s∈parabolic cs C := by
    by_cases he : parabolicStepRatio cs X w s=1
    · rw [he]
      exact Subgroup.one_mem _
    · rw [parabolicStepRatio_reflection cs X w s he]
      exact (parabolic cs C).mul_mem
        ((parabolic cs C).mul_mem hr (simple_mem_parabolic cs C hs))
        ((parabolic cs C).inv_mem hr)
  have he : parabolicComponent cs X (w*cs.simple s)=
      parabolicComponent cs X w*parabolicStepRatio cs X w s := by
    unfold parabolicStepRatio
    rw [mul_inv_cancel_left]
  rw [he]
  exact (parabolic cs C).mul_mem hc hh

/-- The parabolic component of an element of `W_C` is again in `W_C`. -/
theorem component_mem_of_mem (X C : Set S) (w : W) (hw : w∈parabolic cs C) :
    parabolicComponent cs X w∈parabolic cs C := by
  obtain ⟨u,hu,rfl⟩ := (mem_parabolic_iff_word cs C w).mp hw
  induction u using List.reverseRecOn with
  | nil =>
    rw [cs.wordProd_nil,component_one]
    exact Subgroup.one_mem _
  | append_singleton u s ih =>
    have hu' : ∀ i∈u, i∈C := fun i hi => hu i (List.mem_append_left _ hi)
    have hs : s∈C := hu s (List.mem_append_right _ (by simp))
    rw [cs.wordProd_append,cs.wordProd_singleton]
    exact component_step_mem cs X C _ s (wordProd_mem_parabolic cs C u hu')
      (ih hu' (wordProd_mem_parabolic cs C u hu')) hs

/-- The canonical minimal representative also stays in `W_C`. -/
theorem rep_mem_of_mem (X C : Set S) (w : W) (hw : w∈parabolic cs C) :
    parabolicRep cs X w∈parabolic cs C :=
  rep_mem_of_component_mem cs X C w hw (component_mem_of_mem cs X C w hw)

/-- A minimal left representative outside `W_C` cannot lie in `W_X W_C`. -/
theorem minimum_not_product (X C : Set S) (w : W) (hmin : IsParabolicMinimum cs X w)
    (hw : w∉parabolic cs C) (a b : W) (ha : a∈parabolic cs X) (hb : b∈parabolic cs C) :
    w≠a*b := by
  intro he
  apply hw
  have hr := rep_mem_of_mem cs X C b hb
  rw [←parabolicRep_left_mul cs X a b ha,←he,parabolicRep_of_minimum cs X w hmin] at hr
  exact hr

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeFixedPaths
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed paths and branching for group actions on simplicial trees. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V)

lemma stabilizer_smul (g : G) (v : V) :
    MulAction.stabilizer G (g • v)=conjugate g (MulAction.stabilizer G v) := by
  ext a
  rw [mem_conjugate,MulAction.mem_stabilizer_iff,MulAction.mem_stabilizer_iff,
    ←smul_left_cancel_iff g⁻¹]
  simp only [smul_smul,inv_mul_cancel,one_smul,mul_assoc]

lemma pairStabilizer_smul (g : G) (u v : V) :
    pairStabilizer (G := G) (g • u) (g • v)=conjugate g (pairStabilizer (G := G) u v) := by
  rw [pairStabilizer,stabilizer_smul,stabilizer_smul,←conjugate_inf]
  rfl

/-- An element fixing the endpoints of a tree path fixes each vertex of it. -/
theorem fixes_path (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
    {u v : V} (p : T.Walk u v) (hp : p.IsPath) (g : G)
    (hu : g • u=u) (hv : g • v=v) (n : ℕ) : g • p.getVert n=p.getVert n := by
  let q := (p.map (translate T hA g)).copy hu hv
  have hq : q.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy _ _ _).mpr
    exact hp.map (MulAction.toPerm g).injective
  have he : q=p := congrArg Subtype.val (hT.subsingleton_path u v |>.elim ⟨q,hq⟩ ⟨p,hp⟩)
  have hh := congrArg (fun r : T.Walk u v => r.getVert n) he
  calc
    g • p.getVert n = (p.map (translate T hA g)).getVert n :=
      (SimpleGraph.Walk.getVert_map (translate T hA g) p n).symm
    _ = q.getVert n := (SimpleGraph.Walk.getVert_copy _ n hu hv).symm
    _ = p.getVert n := hh

theorem fixes_path_support (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
    {u v : V} (p : T.Walk u v) (hp : p.IsPath) (g : G)
    (hu : g • u=u) (hv : g • v=v) {w : V} (hw : w∈p.support) : g • w=w := by
  have h := fixes_path T hT hA p hp g hu hv (p.support.idxOf w)
  simpa only [SimpleGraph.Walk.getVert_support_idxOf _ hw] using h

/-- Endpoint stabilizers also fix all intermediate vertices. -/
lemma pairStabilizer_le_at_path (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
    {u v : V} (p : T.Walk u v) (hp : p.IsPath) {w : V} (hw : w∈p.support) :
    pairStabilizer (G := G) u v≤MulAction.stabilizer G w := by
  intro g hg
  exact fixes_path_support T hT hA p hp g hg.1 hg.2 hw

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_OrbitEdgeGraph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The connected subtree generated by an orbit of one edge. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (P : Subgroup G) (u v : V) (hne : u≠v)

lemma orbit_base_adj : (orbitEdgeGraph P u v hne).Adj u v := by
  refine ⟨1,P.one_mem,Or.inl ?_⟩
  simp only [one_smul,and_self]

variable {P u v hne}

lemma orbit_reachable_generator {A : Set G} (hP : P=Subgroup.closure A)
    (hA : ∀ a∈A, a • u=u ∨ a • v=v) {g : G} (hg : g∈P) :
    (orbitEdgeGraph P u v hne).Reachable u (g • u) := by
  have hg' : g∈Subgroup.closure A := hP ▸ hg
  clear hg
  induction hg' using Subgroup.closure_induction with
  | mem g hg =>
    rcases hA g hg with hu|hv
    · rw [hu]
    · have h := (orbit_base_adj P u v hne).reachable.map
        (orbit_translate P u v hne g (hP.symm ▸ Subgroup.subset_closure hg))
      change (orbitEdgeGraph P u v hne).Reachable (g • u) (g • v) at h
      rw [hv] at h
      exact (orbit_base_adj P u v hne).reachable.trans h.symm
  | one =>
    rw [one_smul]
  | mul a b ha hb iha ihb =>
    have h := ihb.map (orbit_translate P u v hne a (hP.symm ▸ ha))
    change (orbitEdgeGraph P u v hne).Reachable (a • u) (a • (b • u)) at h
    rw [←mul_smul] at h
    exact iha.trans h
  | inv a ha ih =>
    have h := ih.map (orbit_translate P u v hne a⁻¹ (P.inv_mem (hP.symm ▸ ha)))
    change (orbitEdgeGraph P u v hne).Reachable (a⁻¹ • u) (a⁻¹ • (a • u)) at h
    rw [inv_smul_smul] at h
    exact h.symm

lemma orbit_reachable {A : Set G} (hP : P=Subgroup.closure A)
    (hA : ∀ a∈A, a • u=u ∨ a • v=v) {w : V} (hw : w∈orbitVertices P u v) :
    (orbitEdgeGraph P u v hne).Reachable u w := by
  obtain ⟨p,hp,rfl|rfl⟩ := hw
  · exact orbit_reachable_generator hP hA hp
  · have h := (orbit_base_adj P u v hne).reachable.map (orbit_translate P u v hne p hp)
    exact (orbit_reachable_generator hP hA hp).trans h

lemma orbit_adj_mem {x y : V} (h : (orbitEdgeGraph P u v hne).Adj x y) :
    x∈orbitVertices P u v ∧ y∈orbitVertices P u v := by
  obtain ⟨p,hp,h⟩ := h
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨⟨p,hp,Or.inl rfl⟩,⟨p,hp,Or.inr rfl⟩⟩
  · exact ⟨⟨p,hp,Or.inr rfl⟩,⟨p,hp,Or.inl rfl⟩⟩

lemma orbit_walk_support {x y : V} (p : (orbitEdgeGraph P u v hne).Walk x y)
    (hx : x∈orbitVertices P u v) : ∀ w∈p.support,w∈orbitVertices P u v := by
  induction p with
  | nil =>
    intro w hw
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hw
    subst w
    exact hx
  | @cons x y z h p ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact hx
    · exact ih (orbit_adj_mem h).2 w hw

lemma orbit_graph_le (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)
    (huv : T.Adj u v) : orbitEdgeGraph P u v hne≤T := by
  rintro x y ⟨p,_,h⟩
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact hA p huv
  · exact (hA p huv).symm

lemma orbit_smul_mem {p : G} (hp : p∈P) {x : V}
    (hx : x∈orbitVertices P u v) : p • x∈orbitVertices P u v := by
  obtain ⟨q,hq,rfl|rfl⟩ := hx
  · exact ⟨p*q,P.mul_mem hp hq,Or.inl (mul_smul p q u).symm⟩
  · exact ⟨p*q,P.mul_mem hp hq,Or.inr (mul_smul p q v).symm⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeConvex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex vertex sets and boundary edges in a simplicial tree. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]

lemma orbit_pathClosed (T : SimpleGraph V) (hT : T.IsAcyclic)
    (hA : PreservesAdj (G := G) T) (P : Subgroup G) (u v : V) (huv : T.Adj u v)
    {A : Set G} (hP : P=Subgroup.closure A)
    (hgen : ∀ a∈A,a • u=u ∨ a • v=v) : PathClosed T (orbitVertices P u v) := by
  intro x y hx hy p hp w hw
  have hr := (orbit_reachable (hne := huv.ne) hP hgen hx).symm.trans
    (orbit_reachable (hne := huv.ne) hP hgen hy)
  obtain ⟨q,hq⟩ := hr.exists_isPath
  have hle := orbit_graph_le (P := P) (hne := huv.ne) T hA huv
  have hqm : (q.mapLe hle).IsPath := hq.map Function.injective_id
  have he : q.mapLe hle=p :=
    congrArg Subtype.val (hT.subsingleton_path x y |>.elim ⟨_,hqm⟩ ⟨p,hp⟩)
  have hwq : w∈q.support := by
    rw [←SimpleGraph.Walk.support_mapLe_eq_support hle q,he]
    exact hw
  exact orbit_walk_support q hx w hwq

lemma pathClosed_smul (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)
    {U : Set V} (hU : PathClosed T U) (g : G) : PathClosed T ((g • ·) '' U) := by
  intro x y hx hy p hp w hw
  have hx' : g⁻¹ • x∈U := by
    obtain ⟨a,ha,rfl⟩ := hx
    simpa only [inv_smul_smul] using ha
  have hy' : g⁻¹ • y∈U := by
    obtain ⟨a,ha,rfl⟩ := hy
    simpa only [inv_smul_smul] using ha
  have hm : g⁻¹ • w∈(p.map (translate T hA g⁻¹)).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  have hmem := hU hx' hy' _ (hp.map (MulAction.toPerm g⁻¹).injective) _ hm
  exact ⟨g⁻¹ • w,hmem,smul_inv_smul g w⟩

lemma exists_boundary_edge (T : SimpleGraph V) {U : Set V} {u v : V}
    (hu : u∈U) (hv : v∉U) (p : T.Walk u v) :
    ∃ x y,T.Adj x y ∧ x∈U ∧ y∉U := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v h p ih =>
    by_cases hw : w∈U
    · exact ih hw hv
    · exact ⟨u,w,h,hu,hw⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeBridge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A group preserving both sides of a bridge fixes its endpoints. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V)

lemma snd_append_of_not_nil {u v w : V} (p : T.Walk u v) (q : T.Walk v w)
    (hp : ¬p.Nil) : (p.append q).snd=p.snd := by
  cases p with
  | nil => exact (hp .nil).elim
  | cons h p => simp only [SimpleGraph.Walk.cons_append,SimpleGraph.Walk.snd_cons]

/-- The endpoint-exit condition identifies a bridge between two convex sets.
Comparing its length with a translated path forces both endpoints to be fixed. -/
theorem fixes_bridge (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    {U W : Set V} (hU : PathClosed T U) (hW : PathClosed T W)
    {u v : V} (hu : u∈U) (hv : v∈W) (p : T.Walk u v) (hp : p.IsPath)
    (hpu : p.snd∉U) (hpv : p.reverse.snd∉W)
    (g : G) (hgU : ∀ x∈U,g • x∈U) (hgW : ∀ x∈W,g • x∈W) :
    g • u=u ∧ g • v=v := by
  obtain ⟨q,hq⟩ := hT.connected.exists_isPath u (g • u)
  obtain ⟨r,hr⟩ := hT.connected.exists_isPath v (g • v)
  have hqs : q.snd∈U := hU hu (hgU u hu) q hq _ (q.getVert_mem_support 1)
  have hrs : r.snd∈W := hW hv (hgW v hv) r hr _ (r.getVert_mem_support 1)
  have hqp : (q.reverse.append p).IsPath :=
    reverse_append_isPath T hT.isAcyclic q p hq hp (fun he => hpu (he ▸ hqs))
  have hn : ¬p.reverse.Nil := by
    intro hn
    have hnil : p.Nil := by
      apply SimpleGraph.Walk.length_eq_zero_iff.mp
      simpa only [SimpleGraph.Walk.length_reverse] using hn.length_eq_zero
    have hs : p.snd=u := by
      cases hnil
      exact SimpleGraph.Walk.getVert_nil u
    exact hpu (hs.symm ▸ hu)
  have hs : (q.reverse.append p).reverse.snd=p.reverse.snd := by
    rw [SimpleGraph.Walk.reverse_append,SimpleGraph.Walk.reverse_reverse]
    exact snd_append_of_not_nil T p.reverse q hn
  have hfull : ((q.reverse.append p).append r).IsPath := by
    have h := reverse_append_isPath T hT.isAcyclic (q.reverse.append p).reverse r
      hqp.reverse hr (fun he => hpv (hs ▸ he.symm ▸ hrs))
    simpa only [SimpleGraph.Walk.reverse_reverse] using h
  have he : (q.reverse.append p).append r=p.map (translate T hA g) :=
    congrArg Subtype.val (hT.isAcyclic.subsingleton_path (g • u) (g • v) |>.elim
      ⟨_,hfull⟩ ⟨_,hp.map (MulAction.toPerm g).injective⟩)
  have hl := congrArg SimpleGraph.Walk.length he
  simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse] at hl
  have hm := SimpleGraph.Walk.length_map (translate T hA g) p
  have hl' : q.length+p.length+r.length=p.length := hl.trans hm
  have hq0 : q.length=0 := by omega
  have hr0 : r.length=0 := by omega
  exact ⟨(SimpleGraph.Walk.eq_of_length_eq_zero hq0).symm,
    (SimpleGraph.Walk.eq_of_length_eq_zero hr0).symm⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeInvariantTranslate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equivariance of invariant vertex sets under subgroup conjugation. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]

lemma conjugate_preserves_image (P : Subgroup G) (U : Set V)
    (hU : ∀ p∈P,∀ x∈U,p • x∈U) (a : G)
    {g : G} (hg : g∈conjugate a P) {y : V} (hy : y∈(a • ·) '' U) :
    g • y∈(a • ·) '' U := by
  obtain ⟨x,hx,rfl⟩ := hy
  refine ⟨(a⁻¹*g*a) • x,hU _ ((mem_conjugate a P g).mp hg) _ hx,?_⟩
  simp only [smul_smul,mul_assoc,mul_inv_cancel_left]

lemma not_mem_image_of_smul_eq {U : Set V} {a : G} {x y : V}
    (hx : x∉U) (he : a • x=y) : y∉(a • ·) '' U := by
  rintro ⟨z,hz,h⟩
  have heq : z=x := (MulAction.toPerm a).injective (h.trans he.symm)
  exact hx (heq ▸ hz)

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualAmalgam
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual amalgamated-product presentation of a visual splitting.
The factors and edge group are the standard subgroups of the given Artin
group, and the inverse homomorphism is constructed from its braid relators. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S) (Y Z : Set S)

lemma visualToArtin_from (hsplit : IsVisualSplit M Y Z) (a : Artin M) :
    visualToArtin M Y Z (visualFromArtin M Y Z hsplit a)=a := by
  have h : (visualToArtin M Y Z).comp (visualFromArtin M Y Z hsplit)=MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro s
    simp only [MonoidHom.comp_apply,MonoidHom.id_apply]
    exact (congrArg (visualToArtin M Y Z) (visualFromArtin_generator M Y Z hsplit s)).trans
      (visualToArtin_generator M Y Z hsplit s)
  exact DFunLike.congr_fun h a

lemma visualFromArtin_factor (hsplit : IsVisualSplit M Y Z) (b : Bool)
    (a : artinParabolic M (visualSide Y Z b)) :
    visualFromArtin M Y Z hsplit a=Monoid.PushoutI.of b a := by
  obtain ⟨a,ha⟩ := a
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨s,hs,rfl⟩ := hx
    rw [visualFromArtin_generator]
    exact visualGenerator_eq M Y Z hsplit b s hs
  | one =>
    change visualFromArtin M Y Z hsplit 1=Monoid.PushoutI.of b (1 : artinParabolic M (visualSide Y Z b))
    rw [map_one,map_one]
  | mul x y hx hy ihx ihy =>
    change visualFromArtin M Y Z hsplit (x*y)=_
    rw [map_mul,ihx,ihy,←map_mul]
    rfl
  | inv x hx ih =>
    change visualFromArtin M Y Z hsplit x⁻¹=_
    rw [map_inv,ih,←map_inv]
    rfl

lemma visualFromArtin_to (hsplit : IsVisualSplit M Y Z) (a : VisualAmalgam M Y Z) :
    visualFromArtin M Y Z hsplit (visualToArtin M Y Z a)=a := by
  have h : (visualFromArtin M Y Z hsplit).comp (visualToArtin M Y Z)=MonoidHom.id _ := by
    apply Monoid.PushoutI.hom_ext_nonempty
    intro b
    ext a
    simp only [MonoidHom.comp_apply,MonoidHom.id_apply,visualToArtin]
    exact visualFromArtin_factor M Y Z hsplit b a
  exact DFunLike.congr_fun h a

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualTree
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Bass--Serre tree and stabilizers of an actual visual Artin splitting. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S) (Y Z : Set S)
local notation "φ" => visualEdgeInclusion M Y Z

variable [hSplit : Fact (IsVisualSplit M Y Z)]

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instMulActionArtinVisualVertex
lemma visual_factor_comap (b : Bool) :
    (AmalgamTree.Factor φ b).comap (visualFromArtin M Y Z hSplit.out)=
      artinParabolic M (visualSide Y Z b) := by
  ext a
  constructor
  · rintro ⟨x,hx⟩
    have h := congrArg (visualToArtin M Y Z) hx
    rw [visualToArtin_from] at h
    have hx' : visualToArtin M Y Z (Monoid.PushoutI.of b x)=x.val :=
      Monoid.PushoutI.lift_of _ _ _ _
    rw [hx'] at h
    exact h ▸ x.property
  · intro ha
    exact ⟨⟨a,ha⟩,(visualFromArtin_factor M Y Z hSplit.out b ⟨a,ha⟩).symm⟩

lemma conjugate_comap_hom {A B : Type*} [Group A] [Group B]
    (f : A →* B) (g : A) (P : Subgroup B) :
    (conjugate (f g) P).comap f=conjugate g (P.comap f) := by
  ext a
  simp only [Subgroup.mem_comap,mem_conjugate,map_mul,map_inv]

lemma visual_vertex_stabilizer (b : Bool) (g : Artin M) :
    MulAction.stabilizer (Artin M) (visualVertex M Y Z hSplit.out b g)=
      conjugate g (artinParabolic M (visualSide Y Z b)) := by
  change (MulAction.stabilizer (VisualAmalgam M Y Z)
    (AmalgamTree.vertex φ b (visualFromArtin M Y Z hSplit.out g))).comap
      (visualFromArtin M Y Z hSplit.out)=_
  rw [AmalgamTree.vertex_stabilizer,conjugate_comap_hom,visual_factor_comap]

omit hSplit in
lemma visualGraph_isTree : (visualGraph M Y Z).IsTree := by
  apply AmalgamTree.isTree
  intro b
  exact Subgroup.inclusion_injective _

lemma visual_vertex_exists (v : VisualVertex M Y Z) :
    ∃ b g, v=visualVertex M Y Z hSplit.out b g := by
  obtain ⟨b,v⟩ := v
  obtain ⟨g,rfl⟩ := Quotient.exists_rep v
  refine ⟨b,visualToArtin M Y Z g,?_⟩
  unfold visualVertex
  rw [visualFromArtin_to]
  rfl

lemma visual_vertex_isParabolic (v : VisualVertex M Y Z) :
    IsParabolic M (MulAction.stabilizer (Artin M) v) := by
  obtain ⟨b,g,rfl⟩ := visual_vertex_exists M Y Z v
  rw [visual_vertex_stabilizer]
  exact ⟨_,g,rfl⟩

lemma visual_vertex_adj (g : Artin M) :
    (visualGraph M Y Z).Adj (visualVertex M Y Z hSplit.out false g)
      (visualVertex M Y Z hSplit.out true g) := AmalgamTree.vertex_adj φ _

lemma visual_adj_representatives {u v : VisualVertex M Y Z}
    (h : (visualGraph M Y Z).Adj u v) :
    ∃ g : Artin M, u=visualVertex M Y Z hSplit.out u.1 g ∧
      v=visualVertex M Y Z hSplit.out v.1 g := by
  obtain ⟨g,hu,hv⟩ := AmalgamTree.adj_representatives φ h
  refine ⟨visualToArtin M Y Z g,?_,?_⟩ <;>
    unfold visualVertex <;> rw [visualFromArtin_to] <;> assumption

/-- The stabilizers of the endpoints of every edge generate the whole group. -/
lemma visual_adj_stabilizers_generate {u v : VisualVertex M Y Z}
    (h : (visualGraph M Y Z).Adj u v) :
    MulAction.stabilizer (Artin M) u ⊔ MulAction.stabilizer (Artin M) v=⊤ := by
  obtain ⟨g,hu,hv⟩ := visual_adj_representatives M Y Z h
  rw [hu,hv,visual_vertex_stabilizer,visual_vertex_stabilizer,←conjugate_sup]
  have hne : u.1≠v.1 := h.1
  have hsides : visualSide Y Z u.1 ∪ visualSide Y Z v.1=Set.univ := by
    by_cases hu' : u.1=false
    · have hv' : v.1=true := Bool.eq_true_of_not_eq_false (fun hf => hne (hu'.trans hf.symm))
      rw [hu',hv']
      exact hSplit.out.1
    · have hu'' : u.1=true := Bool.eq_true_of_not_eq_false hu'
      have hv' : v.1=false := Bool.eq_false_of_not_eq_true (fun hf => hne (hu''.trans hf.symm))
      rw [hu'',hv',Set.union_comm]
      exact hSplit.out.1
  have he : artinParabolic M (visualSide Y Z u.1) ⊔
      artinParabolic M (visualSide Y Z v.1)=⊤ := by
    rw [←standard_union,hsides,standard_univ]
  rw [he,conjugate_top]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualEdgeTransitive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transitivity on oriented edges of the visual Bass--Serre tree. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.visualEdgeTransitiveAction
lemma visual_oriented_edge_transitive {x y u v : VisualVertex M Y Z}
    (hxy : (visualGraph M Y Z).Adj x y) (huv : (visualGraph M Y Z).Adj u v)
    (hx : x.1=u.1) : ∃ a : Artin M,a • x=u ∧ a • y=v := by
  obtain ⟨k,hxk,hyk⟩ := visual_adj_representatives M Y Z hxy
  obtain ⟨g,hug,hvg⟩ := visual_adj_representatives M Y Z huv
  have hy : y.1=v.1 := by
    have h : ∀ a b c d : Bool,a≠b → c≠d → a=c → b=d := by decide
    exact h _ _ _ _ hxy.1 huv.1 hx
  refine ⟨g*k⁻¹,?_,?_⟩
  · rw [hxk,visual_smul_vertex,mul_assoc,inv_mul_cancel,mul_one,hx]
    exact hug.symm
  · rw [hyk,visual_smul_vertex,mul_assoc,inv_mul_cancel,mul_one,hy]
    exact hvg.symm

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicRetractionAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The parabolic gallery retraction as an action of the Artin presentation. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (J : Set S)

lemma parabolicRetractionAction_generator (s : S) :
    parabolicRetractionAction M J (generator M s)=MulOpposite.op (parabolicStepPerm M J s) :=
  PresentedGroup.toGroup.of _

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_StandardEmbedding
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injectivity of every finite-rank standard Artin parabolic. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (J : Set S)
local notation "cs" => M.toCoxeterSystem
local notation "R" => restrictedMatrix M J

omit [Fintype S] in
private lemma component_of_parabolic (w : M.Group) (hw : w ∈ parabolic cs J) :
    parabolicComponent cs J w=w := by
  have hmin : IsParabolicMinimum cs J (1 : M.Group) := by
    intro a _
    simp only [(cs).length_one,mul_one]
    exact Nat.zero_le _
  have hr : parabolicRep cs J w=1 :=
    parabolicRep_eq_of_decomposition cs J w w 1 hw hmin (mul_one w).symm
  simp only [parabolicComponent,hr,inv_one,mul_one]

lemma parabolicStepLetter_standard (w : M.Group) (hw : w ∈ parabolic cs J) (s : J) :
    parabolicStepLetter cs J w s=some s := by
  have hws : w*(cs).simple s ∈ parabolic cs J :=
    (parabolic cs J).mul_mem hw (simple_mem_parabolic cs J s.property)
  have hv := parabolicStepLetter_value cs J w s
  unfold parabolicStepRatio at hv
  rw [component_of_parabolic M J w hw,component_of_parabolic M J _ hws,inv_mul_cancel_left] at hv
  cases hl : parabolicStepLetter cs J w s with
  | none =>
    rw [hl] at hv
    change 1=(cs).simple s at hv
    have hh := congrArg (cs).length hv
    rw [(cs).length_one,(cs).length_simple] at hh
    omega
  | some t =>
    rw [hl] at hv
    have he : t=s := Subtype.ext (simple_injective cs hv)
    exact congrArg some he

/-- On the standard parabolic, the gallery action is its right regular action. -/
theorem parabolicRetractionAction_standard (g a : Artin R) :
    MulOpposite.unop (parabolicRetractionAction M J (restrictedArtinHom M J g))
      (parabolicState M J a)=parabolicState M J (a*g) := by
  let f := (parabolicRetractionAction M J).comp (restrictedArtinHom M J)
  have hg : g ∈ Subgroup.closure (Set.range (generator R)) := by
    rw [show Subgroup.closure (Set.range (generator R))=⊤ from
      PresentedGroup.closure_range_of (braidRelators R)]
    trivial
  change MulOpposite.unop (f g) (parabolicState M J a)=_
  induction hg using Subgroup.closure_induction generalizing a with
  | mem x hx =>
    obtain ⟨s,rfl⟩ := hx
    have hw : restrictionHom M J (artinCoxeter R a) ∈ parabolic cs J :=
      restrictionHom_mem_parabolic M J _
    simp only [f,MonoidHom.comp_apply,restrictedArtinHom_generator,
      parabolicRetractionAction_generator]
    change (restrictionHom M J (artinCoxeter R a)*(cs).simple s,
      a*parabolicStepArtin M J (restrictionHom M J (artinCoxeter R a)) s)=_
    rw [parabolicStepArtin,parabolicStepLetter_standard M J _ hw]
    simp only [Option.toList_some,wordArtin,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
      parabolicState,map_mul,artinCoxeter_generator,restrictionHom_simple]
  | one => simp only [map_one,MulOpposite.unop_one,Equiv.Perm.one_apply,mul_one]
  | mul x y hx hy ihx ihy =>
    rw [map_mul,MulOpposite.unop_mul]
    change MulOpposite.unop (f y) (MulOpposite.unop (f x) (parabolicState M J a))=_
    rw [ihx,ihy,mul_assoc]
  | inv x hx ih =>
    rw [map_inv,MulOpposite.unop_inv]
    change (MulOpposite.unop (f x)).symm (parabolicState M J a)=_
    apply (MulOpposite.unop (f x)).injective
    simp only [Equiv.apply_symm_apply,ih,inv_mul_cancel_right]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicCore
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal core of every proper parabolic in irreducible type is trivial.
The arbitrary-intersection theorem also supplies a finite list of conjugates
realizing this core. These are the algebraic inputs to the tree argument. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable

variable {G : Type*} [Group G]

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

omit [LinearOrder S] in
/-- The conjugate form of CMMW Lemma 3.3. -/
theorem normal_parabolic (hIrred : IsIrreducible M)
    (P : Subgroup (Artin M)) (hP : IsParabolic M P) (hn : P.Normal) :
    P=⊥ ∨ P=⊤ := by
  obtain ⟨X,g,rfl⟩ := hP
  have hn' : (conjugate g⁻¹ (conjugate g (artinParabolic M X))).Normal := by
    exact hn.comap (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  rw [conjugate_inv_cancel] at hn'
  rcases normal_standard_parabolic M hIrred X hn' with hx|hx
  · left
    simp [hx,artinParabolic]
  · right
    rw [hx,standard_univ,conjugate_top]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_NormalizerAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalizing a subgroup can be tested outside any proper subgroup. -/
namespace HarmonicArtin.ParabolicIntersections
variable {G : Type*} [Group G]

lemma conjugate_eq_map (g : G) (P : Subgroup G) :
    conjugate g P=P.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_conjugate,Subgroup.mem_map_equiv]
  rfl

lemma mem_normalizer_iff_conjugate (g : G) (P : Subgroup G) :
    g∈Subgroup.normalizer (P : Set G) ↔ conjugate g P=P := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (P.map (MulAut.conj g).toMonoidHom=P) ↔ _
  rw [←conjugate_eq_map]

lemma le_normalizer_of_outside (P K C : Subgroup G)
    (ha : ∃ a : G, a∈K ∧ a∉C)
    (hn : ∀ g : G, g∈K → g∉C → conjugate g P=P) :
    K≤Subgroup.normalizer (P : Set G) := by
  obtain ⟨a,ha,haC⟩ := ha
  have haN := (mem_normalizer_iff_conjugate a P).mpr (hn a ha haC)
  intro g hg
  by_cases hgC : g∈C
  · have hgaC : g*a∉C := by
      intro h
      exact haC (by simpa only [inv_mul_cancel_left] using C.mul_mem (C.inv_mem hgC) h)
    have hgaN := (mem_normalizer_iff_conjugate (g*a) P).mpr (hn (g*a) (K.mul_mem hg ha) hgaC)
    have h := (Subgroup.normalizer (P : Set G)).mul_mem hgaN
      ((Subgroup.normalizer (P : Set G)).inv_mem haN)
    simpa only [mul_inv_cancel_right] using h
  · exact (mem_normalizer_iff_conjugate g P).mpr (hn g hg hgC)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeBranch
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflecting a segment at an endpoint and extending it along a new edge. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
include hT hA

lemma moved_first_vertex_ne_endpoint {u v : V} (p : T.Walk v u) (hp : p.IsPath)
    (g : G) (hg : g • v=v) (hw : g • p.snd≠p.snd) : g • u≠u := by
  intro hu
  exact hw (fixes_path T hT hA p hp g hg hu 1)

/-- Reflecting a path across its initial vertex intersects its endpoint
stabilizer with a conjugate, and still gives an endpoint stabilizer. -/
theorem reflected_pair (u v : V) (p : T.Walk v u) (hp : p.IsPath)
    (g : G) (hg : g • v=v) (hw : g • p.snd≠p.snd) :
    pairStabilizer (G := G) u (g • u)=pairStabilizer (G := G) u v ⊓
      conjugate g (pairStabilizer (G := G) u v) := by
  let q := (p.map (translate T hA g)).copy hg rfl
  have hq : q.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy _ _ _).mpr
    exact hp.map (MulAction.toPerm g).injective
  have hs : p.snd≠q.snd := by
    change p.getVert 1≠q.getVert 1
    have hqv : q.getVert 1=g • p.getVert 1 := by
      calc
        q.getVert 1 = (p.map (translate T hA g)).getVert 1 :=
          SimpleGraph.Walk.getVert_copy _ 1 hg rfl
        _ = g • p.getVert 1 := SimpleGraph.Walk.getVert_map _ _ 1
    rw [hqv]
    exact hw.symm
  have hr := reverse_append_isPath T hT p q hp hq hs
  have hv : v∈(p.reverse.append q).support := by
    rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append]
    exact List.mem_append_right _ q.start_mem_support
  have hfix := pairStabilizer_le_at_path T hT hA (p.reverse.append q) hr hv
  rw [←pairStabilizer_smul,hg]
  apply le_antisymm
  · intro a ha
    exact ⟨⟨ha.1,hfix ha⟩,ha.2,hfix ha⟩
  · intro a ha
    exact ⟨ha.1.1,ha.2.1⟩

omit hA in
/-- An edge leaving the initial direction of a path extends the path. -/
lemma reverse_concat_isPath {u v w : V} (p : T.Walk v u) (hp : p.IsPath)
    (hadj : T.Adj v w) (hw : w≠p.snd) : (p.reverse.concat hadj).IsPath := by
  apply hp.reverse.concat
  · intro hm
    have hm' : w∈p.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hm
    exact hw (hT.eq_snd_of_adj_start hp hadj hm')

/-- If the old stabilizer fixes the added vertex, extension preserves it. -/
theorem extended_pair (u v w : V) (p : T.Walk v u) (hp : p.IsPath)
    (hadj : T.Adj v w) (hw : w≠p.snd)
    (hfix : pairStabilizer (G := G) u v≤MulAction.stabilizer G w) :
    pairStabilizer (G := G) u w=pairStabilizer (G := G) u v := by
  have hr := reverse_concat_isPath T hT p hp hadj hw
  have hv : v∈(p.reverse.concat hadj).support := by
    rw [SimpleGraph.Walk.support_concat]
    exact List.mem_append_left _ p.reverse.end_mem_support
  have hfix' := pairStabilizer_le_at_path T hT hA _ hr hv
  apply le_antisymm
  · intro a ha
    exact ⟨ha.1,hfix' ha⟩
  · intro a ha
    exact ⟨ha.1,hfix ha⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeMinimalPair
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A minimal segment stabilizer is normalized by its endpoint stabilizers. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
include hT hA

theorem minimal_pair_endpoint (u v : V) (hne : u≠v)
    (hmin : ∀ a b : V, a≠b → pairStabilizer (G := G) a b≤pairStabilizer (G := G) u v →
      pairStabilizer (G := G) a b=pairStabilizer (G := G) u v)
    (p : T.Walk v u) (hp : p.IsPath)
    (hbranch : ∀ w : V, T.Adj v w → ∃ a : G, a • v=v ∧ a • w≠w) :
    MulAction.stabilizer G v≤Subgroup.normalizer (pairStabilizer (G := G) u v : Set G) := by
  let P := pairStabilizer (G := G) u v
  let C := MulAction.stabilizer G v ⊓ MulAction.stabilizer G p.snd
  have hpnot : ¬p.Nil := fun h => hne (hp.nil_iff_eq.mp h).symm
  obtain ⟨a,ha,haw⟩ := hbranch p.snd (p.adj_snd hpnot)
  have haC : a∉C := fun h => haw h.2
  apply le_normalizer_of_outside P (MulAction.stabilizer G v) C ⟨a,ha,haC⟩
  have hle (g : G) (hg : g • v=v) (hw : g • p.snd≠p.snd) : P ≤ conjugate g P := by
    have hne' : u≠g • u := (moved_first_vertex_ne_endpoint T hT hA p hp g hg hw).symm
    have he := reflected_pair T hT hA u v p hp g hg hw
    have hm := hmin u (g • u) hne' (by rw [he]; exact inf_le_left)
    rw [he] at hm
    have hi : P ⊓ conjugate g P ≤ conjugate g P := inf_le_right
    rwa [hm] at hi
  intro g hg hgC
  have hw : g • p.snd≠p.snd := fun h => hgC ⟨hg,h⟩
  have hgi : g⁻¹ • v=v := by
    have hh := congrArg (fun x : V => g⁻¹ • x) hg
    simpa only [inv_smul_smul] using hh.symm
  have hwi : g⁻¹ • p.snd≠p.snd := by
    intro h
    have hh := congrArg (fun x : V => g • x) h
    exact hw (by simpa only [smul_inv_smul] using hh.symm)
  apply le_antisymm
  · have h := conjugate_mono g (hle g⁻¹ hgi hwi)
    simpa only [←conjugate_mul,mul_inv_cancel,conjugate_one] using h
  · exact hle g hg hw

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeMinimalNormal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A minimal segment stabilizer in a branching tree action is normal when
adjacent vertex stabilizers generate the acting group. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
include hT hA

theorem minimal_pair_normal (u v : V) (hne : u≠v)
    (hmin : ∀ a b : V, a≠b → pairStabilizer (G := G) a b≤pairStabilizer (G := G) u v →
      pairStabilizer (G := G) a b=pairStabilizer (G := G) u v)
    (p : T.Walk v u) (hp : p.IsPath)
    (hbranch : ∀ v w : V, T.Adj v w → ∃ a : G, a • v=v ∧ a • w≠w)
    (hgen : ∀ v w : V, T.Adj v w →
      MulAction.stabilizer G v ⊔ MulAction.stabilizer G w=⊤) :
    (pairStabilizer (G := G) u v).Normal := by
  let P := pairStabilizer (G := G) u v
  have hnV := minimal_pair_endpoint T hT hA u v hne hmin p hp (hbranch v)
  have hpnot : ¬p.Nil := fun h => hne (hp.nil_iff_eq.mp h).symm
  obtain ⟨a,ha,haw⟩ := hbranch v p.snd (p.adj_snd hpnot)
  have haN : conjugate a P=P := (mem_normalizer_iff_conjugate a P).mp (hnV ha)
  have hadj : T.Adj v (a • p.snd) := by
    have h := hA a (p.adj_snd hpnot)
    rwa [ha] at h
  have hfix : P≤MulAction.stabilizer G (a • p.snd) := by
    rw [stabilizer_smul,←haN]
    apply conjugate_mono
    exact pairStabilizer_le_at_path T hT hA p.reverse hp.reverse
      (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse]
        using p.getVert_mem_support 1)
  have he : pairStabilizer (G := G) u (a • p.snd)=P :=
    extended_pair T hT hA u v (a • p.snd) p hp hadj haw hfix
  have hne' : u≠a • p.snd := by
    intro hu
    have hmem : a • p.snd∈p.support := hu ▸ p.end_mem_support
    exact haw (hT.eq_snd_of_adj_start hp hadj hmem)
  have hmin' : ∀ x y : V, x≠y →
      pairStabilizer (G := G) x y≤pairStabilizer (G := G) u (a • p.snd) →
      pairStabilizer (G := G) x y=pairStabilizer (G := G) u (a • p.snd) := by
    intro x y hxy hle
    rw [he] at hle ⊢
    exact hmin x y hxy hle
  have hpath := reverse_concat_isPath T hT p hp hadj haw
  have hnW := minimal_pair_endpoint T hT hA u (a • p.snd) hne' hmin'
    (p.reverse.concat hadj).reverse hpath.reverse (hbranch (a • p.snd))
  rw [he] at hnW
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  rw [←hgen v (a • p.snd) hadj]
  exact sup_le hnV hnW

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualTreeProperties
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Proper stabilizers and branching in the visual Bass--Serre tree. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instMulActionArtinVisualVertex_1
omit [Fintype S] in
lemma visual_preservesAdj : TreeAction.PreservesAdj (G := Artin M) (visualGraph M Y Z) := by
  intro g u v h
  exact (AmalgamTree.translate (visualEdgeInclusion M Y Z)
    (visualFromArtin M Y Z hSplit.out g)).map_adj h

lemma visual_vertex_proper (v : VisualVertex M Y Z) :
    MulAction.stabilizer (Artin M) v≠⊤ := by
  obtain ⟨b,g,rfl⟩ := visual_vertex_exists M Y Z v
  rw [visual_vertex_stabilizer]
  intro he
  have he' := congrArg (conjugate g⁻¹) he
  rw [conjugate_inv_cancel,conjugate_top] at he'
  apply standard_ne_top_of_ne_univ M _ he'
  cases b
  · exact (Set.ssubset_iff_subset_ne.mp hSplit.out.2.1).2
  · exact (Set.ssubset_iff_subset_ne.mp hSplit.out.2.2.1).2

/-- Every direction at every vertex can be moved by its stabilizer. -/
lemma visual_branching (v w : VisualVertex M Y Z) (h : (visualGraph M Y Z).Adj v w) :
    ∃ a : Artin M, a • v=v ∧ a • w≠w := by
  have hn : ¬MulAction.stabilizer (Artin M) v≤MulAction.stabilizer (Artin M) w := by
    intro hle
    apply visual_vertex_proper M Y Z w
    have he := visual_adj_stabilizers_generate M Y Z h
    rwa [sup_eq_right.mpr hle] at he
  obtain ⟨a,ha,hna⟩ := SetLike.not_le_iff_exists.mp hn
  exact ⟨a,ha,hna⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualTrivialSegment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The visual tree has a segment with trivial pointwise stabilizer.
This proves the segment step in CMMW (2026), Theorem 3.2, using the
unconditional parabolic intersection theorem and rank descent. -/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instMulActionArtinVisualVertex_2
lemma visual_pair_isParabolic (u v : VisualVertex M Y Z) :
    IsParabolic M (pairStabilizer (G := Artin M) u v) := by
  obtain ⟨X,g,hg⟩ := visual_vertex_isParabolic M Y Z u
  obtain ⟨X',g',hg'⟩ := visual_vertex_isParabolic M Y Z v
  change IsParabolic M (MulAction.stabilizer (Artin M) u ⊓ MulAction.stabilizer (Artin M) v)
  rw [hg,hg']
  exact unconditional_parabolic_intersections M X X' g g'

/-- A finite segment of the genuine Bass--Serre tree has trivial stabilizer. -/
theorem visual_exists_trivial_pair (hIrred : IsIrreducible M) :
    ∃ u v : VisualVertex M Y Z, u≠v ∧ pairStabilizer (G := Artin M) u v=⊥ := by
  let F : Set (Subgroup (Artin M)) :=
    {P | ∃ u v : VisualVertex M Y Z, u≠v ∧ P=pairStabilizer (G := Artin M) u v}
  have hF : F.Nonempty := by
    let u := visualVertex M Y Z hSplit.out false 1
    let v := visualVertex M Y Z hSplit.out true 1
    exact ⟨pairStabilizer (G := Artin M) u v,u,v,
      (visual_vertex_adj M Y Z 1).ne,rfl⟩
  obtain ⟨P,hP,hmin⟩ := exists_minimal_parabolic_s236 M F hF (by
    rintro P ⟨u,v,_,rfl⟩
    exact visual_pair_isParabolic M Y Z u v)
  obtain ⟨u,v,hne,rfl⟩ := hP
  have hmin' : ∀ a b : VisualVertex M Y Z, a≠b →
      pairStabilizer (G := Artin M) a b≤pairStabilizer (G := Artin M) u v →
      pairStabilizer (G := Artin M) a b=pairStabilizer (G := Artin M) u v := by
    intro a b hab hle
    exact hmin _ ⟨a,b,hab,rfl⟩ hle
  obtain ⟨p,hp⟩ := (visualGraph_isTree M Y Z).connected.exists_isPath v u
  have hn := minimal_pair_normal (visualGraph M Y Z) (visualGraph_isTree M Y Z).isAcyclic
    (visual_preservesAdj M Y Z) u v hne hmin' p hp
    (visual_branching M Y Z) (fun _ _ h => visual_adj_stabilizers_generate M Y Z h)
  have hproper : pairStabilizer (G := Artin M) u v≠⊤ := by
    intro he
    apply visual_vertex_proper M Y Z u
    exact top_le_iff.mp (he ▸ (inf_le_left : pairStabilizer (G := Artin M) u v≤_))
  exact ⟨u,v,hne,(normal_parabolic M hIrred _ (visual_pair_isParabolic M Y Z u v) hn).resolve_right hproper⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_WeakMalnormalAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation and subgroup facts about weak malnormality. -/
namespace HarmonicArtin.ParabolicIntersections
variable {G : Type} [Group G]

lemma weaklyMalnormal_of_conjugates_inf_bot (P : Subgroup G) (g h : G)
    (he : conjugate g P ⊓ conjugate h P=⊥) : WeaklyMalnormal P := by
  have he' := congrArg (conjugate g⁻¹) he
  rw [conjugate_inf,conjugate_inv_cancel,←conjugate_mul,conjugate_bot] at he'
  refine ⟨g⁻¹*h,?_⟩
  rw [he']
  exact Set.finite_singleton 1

lemma WeaklyMalnormal.conjugate_subgroup {P : Subgroup G} (hP : WeaklyMalnormal P) (g : G) :
    WeaklyMalnormal (conjugate g P) := by
  obtain ⟨h,hh⟩ := hP
  refine ⟨g*h*g⁻¹,?_⟩
  have he : conjugate g P ⊓ conjugate (g*h*g⁻¹) (conjugate g P)=
      conjugate g (P ⊓ conjugate h P) := by
    rw [conjugate_inf,←conjugate_mul,←conjugate_mul]
    group
  rw [he]
  have him := hh.image (fun x : G => g*x*g⁻¹)
  apply him.subset
  intro x hx
  refine ⟨g⁻¹*x*g,(mem_conjugate _ _ _).mp hx,?_⟩
  group

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualFactorMalnormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak malnormality for the vertex factors, and hence their parabolics. -/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instMulActionArtinVisualVertex_4
omit [LinearOrder S] in
private lemma trivial_pair_endpoint_type (u v : VisualVertex M Y Z) (hne : u≠v)
    (he : pairStabilizer (G := Artin M) u v=⊥) (b : Bool) :
    ∃ w : VisualVertex M Y Z, u≠w ∧ w.1=b ∧ pairStabilizer (G := Artin M) u w=⊥ := by
  by_cases hv : v.1=b
  · exact ⟨v,hne,hv,he⟩
  obtain ⟨p,hp⟩ := (visualGraph_isTree M Y Z).connected.exists_isPath v u
  have hpnot : ¬p.Nil := fun h => hne (hp.nil_iff_eq.mp h).symm
  obtain ⟨a,ha,haw⟩ := visual_branching M Y Z v p.snd (p.adj_snd hpnot)
  have hadj : (visualGraph M Y Z).Adj v (a • p.snd) := by
    have h := visual_preservesAdj M Y Z a (p.adj_snd hpnot)
    rwa [ha] at h
  have hn : u≠a • p.snd := by
    intro hu
    have hmem : a • p.snd∈p.support := hu ▸ p.end_mem_support
    exact haw ((visualGraph_isTree M Y Z).isAcyclic.eq_snd_of_adj_start hp hadj hmem)
  refine ⟨a • p.snd,hn,?_,?_⟩
  · have hne' := hadj.1
    cases hb : b <;> cases hv' : v.1 <;> cases hw : (a • p.snd).1 <;>
      simp_all only [Bool.false_eq_true,Bool.true_eq_false,not_false_eq_true,not_true_eq_false]
  · rw [extended_pair (visualGraph M Y Z) (visualGraph_isTree M Y Z).isAcyclic
      (visual_preservesAdj M Y Z) u v (a • p.snd) p hp hadj haw]
    · exact he
    · rw [he]
      exact bot_le

/-- A nondegenerate segment with trivial stabilizer in either vertex orbit. -/
lemma visual_trivial_pair_distinct_type (hIrred : IsIrreducible M) (b : Bool) :
    ∃ u v : VisualVertex M Y Z, u≠v ∧ u.1=b ∧ v.1=b ∧
      pairStabilizer (G := Artin M) u v=⊥ := by
  obtain ⟨u,v,hne,he⟩ := visual_exists_trivial_pair M Y Z hIrred
  obtain ⟨w,hnw,hw,hew⟩ := trivial_pair_endpoint_type M Y Z u v hne he b
  have he' : pairStabilizer (G := Artin M) w u=⊥ := by
    simpa only [pairStabilizer,inf_comm] using hew
  obtain ⟨x,hnx,hx,hex⟩ := trivial_pair_endpoint_type M Y Z w u hnw.symm he' b
  exact ⟨w,x,hnx,hw,hx,hex⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_NoncommutingGraph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Irreducibility is connectedness of the noncommutation graph. -/
namespace HarmonicArtin.ParabolicIntersections
variable {S : Type} (M : CoxeterMatrix S)

lemma noncommuting_reachable (hIrred : IsIrreducible M) (s t : S) :
    (noncommutingGraph M).Reachable s t := by
  by_contra ht
  let X : Set S := {v | (noncommutingGraph M).Reachable s v}
  obtain ⟨a,ha,b,hb,hm⟩ := hIrred X ⟨s,SimpleGraph.Reachable.rfl⟩ ⟨t,ht⟩
  have hab : a≠b := fun he => hb (he ▸ ha)
  exact hb (ha.trans (show (noncommutingGraph M).Adj a b from ⟨hab,hm⟩).reachable)

/-- A list with a term outside a set has an initial segment whose last
term is the first outside term. -/
lemma list_first_outside (C : Set S) (l : List S) (h : ∃ s∈l,s∉C) :
    ∃ u s v, l=u++s::v ∧ (∀ t∈u,t∈C) ∧ s∉C := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : a∈C
    · have hl : ∃ s∈l,s∉C := by
        obtain ⟨s,hs,hsc⟩ := h
        rcases List.mem_cons.mp hs with rfl|hs
        · exact (hsc ha).elim
        · exact ⟨s,hs,hsc⟩
      obtain ⟨u,s,v,he,hu,hs⟩ := ih hl
      refine ⟨a::u,s,v,?_,?_,hs⟩
      · rw [he]
        rfl
      · intro t ht
        rcases List.mem_cons.mp ht with rfl|ht
        · exact ha
        · exact hu t ht
    · exact ⟨[],a,l,rfl,by simp,ha⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicProductProper
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! In irreducible type, two proper standard parabolics never multiply to
the whole Coxeter or Artin group. This detects proper parabolic subtrees. -/
namespace HarmonicArtin.ParabolicIntersections
open Geometric CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)
local notation "cs" => M.toCoxeterSystem

lemma coxeter_simple_not_parabolic (C : Set S) (s : S) (hs : s∉C) :
    (cs).simple s∉parabolic cs C := by
  intro hm
  have he := parabolic_exterior M C ⟨_,hm⟩ (Pi.single s 1) s hs
  change representation cs ((cs).simple s) (Pi.single s 1) s=(Pi.single s 1 : S → ℝ) s at he
  simp only [representation_simple,simpleReflection_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,Pi.single_eq_same,Matrix.mulVec_single,Matrix.col,Matrix.transpose_apply,
    MulOpposite.op_one,one_smul,cartan_diag] at he
  norm_num at he

/-- A noncommutation path supplies an explicit missing double coset. -/
theorem coxeter_parabolic_product_proper (hIrred : IsIrreducible M)
    (X C : Set S) (hX : X≠Set.univ) (hC : C≠Set.univ) :
    ∃ w : M.Group, ∀ a∈parabolic cs X, ∀ b∈parabolic cs C, w≠a*b := by
  obtain ⟨s,hs⟩ := Set.nonempty_compl.mpr hX
  obtain ⟨t,ht⟩ := Set.nonempty_compl.mpr hC
  obtain ⟨p,hp⟩ := (noncommuting_reachable M hIrred s t).exists_isPath
  obtain ⟨u,d,v,he,hu,hd⟩ := list_first_outside C p.support ⟨t,p.end_mem_support,ht⟩
  have he' : p.support=(u++[d])++v := by
    rw [he,List.append_assoc]
    rfl
  have hn : (u++[d]).Nodup := (List.nodup_append.mp (he' ▸ hp.support_nodup)).1
  have hc : (u++[d]).IsChain (fun a b => a≠b ∧ M a b≠2) :=
    (show ((u++[d])++v).IsChain (noncommutingGraph M).Adj from
      he' ▸ p.isChain_adj_support).left_of_append
  have hfirst : p.support.headD s=s := by cases p <;> rfl
  have hh := congrArg (fun l : List S => l.headD s) he
  rw [hfirst] at hh
  have hhead : ∃ r, u++[d]=s::r := by
    cases u with
    | nil =>
      change s=d at hh
      subst d
      exact ⟨[],rfl⟩
    | cons a u =>
      change s=a at hh
      subst a
      exact ⟨u++[d],rfl⟩
  obtain ⟨r,hr⟩ := hhead
  have hmin : IsParabolicMinimum cs X ((cs).wordProd (u++[d])) := by
    rw [hr] at hn hc ⊢
    exact chain_word_minimum M X s hs r hn hc
  have hw : (cs).wordProd (u++[d])∉parabolic cs C := by
    intro hm
    rw [(cs).wordProd_append,(cs).wordProd_singleton] at hm
    have huC := wordProd_mem_parabolic cs C u hu
    have hdC := (parabolic cs C).mul_mem ((parabolic cs C).inv_mem huC) hm
    rw [inv_mul_cancel_left] at hdC
    exact coxeter_simple_not_parabolic M C d hd hdC
  exact ⟨_,fun a ha b hb => minimum_not_product cs X C _ hmin hw a b ha hb⟩

/-- The same proper-product statement for the actual Artin presentation. -/
theorem artin_parabolic_product_proper (hIrred : IsIrreducible M)
    (X C : Set S) (hX : X≠Set.univ) (hC : C≠Set.univ) :
    ∃ g : Artin M, ∀ a∈artinParabolic M X, ∀ b∈artinParabolic M C, g≠a*b := by
  obtain ⟨w,hw⟩ := coxeter_parabolic_product_proper M hIrred X C hX hC
  refine ⟨positiveLift M w,?_⟩
  intro a ha b hb he
  have hh := congrArg (artinCoxeter M) he
  rw [artinCoxeter_positiveLift,map_mul] at hh
  exact hw _ (artinCoxeter_mem_parabolic M ha) _ (artinCoxeter_mem_parabolic M hb) hh

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualParabolicSubtree
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every proper standard parabolic preserves a proper convex subtree. -/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.visualParabolicSubtreeAction
omit [Fintype S] in
lemma parabolicSubtree_generators (X : Set S) :
    ∀ a∈generator M '' X,
      a • visualVertex M Y Z hSplit.out false 1=visualVertex M Y Z hSplit.out false 1 ∨
      a • visualVertex M Y Z hSplit.out true 1=visualVertex M Y Z hSplit.out true 1 := by
  rintro a ⟨s,_,rfl⟩
  have hs : s∈Y ∪ Z := hSplit.out.1.symm ▸ Set.mem_univ s
  rcases hs with hs|hs
  · left
    apply (MulAction.mem_stabilizer_iff).mp
    rw [visual_vertex_stabilizer,conjugate_one]
    exact Subgroup.subset_closure ⟨s,hs,rfl⟩
  · right
    apply (MulAction.mem_stabilizer_iff).mp
    rw [visual_vertex_stabilizer,conjugate_one]
    exact Subgroup.subset_closure ⟨s,hs,rfl⟩

omit [Fintype S] in
lemma parabolicSubtree_pathClosed (X : Set S) :
    PathClosed (visualGraph M Y Z) (parabolicSubtree M Y Z X) :=
  orbit_pathClosed (visualGraph M Y Z) (visualGraph_isTree M Y Z).isAcyclic
    (visual_preservesAdj M Y Z) _ _ _ (visual_vertex_adj M Y Z 1) rfl
    (parabolicSubtree_generators M Y Z X)

omit [Fintype S] in
lemma parabolicSubtree_invariant (X : Set S) {p : Artin M} (hp : p∈artinParabolic M X)
    {w : VisualVertex M Y Z} (hw : w∈parabolicSubtree M Y Z X) :
    p • w∈parabolicSubtree M Y Z X := orbit_smul_mem hp hw

lemma parabolicSubtree_proper (hIrred : IsIrreducible M) (X : Set S)
    (hX : X≠Set.univ) : ∃ w : VisualVertex M Y Z,w∉parabolicSubtree M Y Z X := by
  obtain ⟨g,hg⟩ := artin_parabolic_product_proper M hIrred X Y hX
    (Set.ssubset_iff_subset_ne.mp hSplit.out.2.1).2
  refine ⟨visualVertex M Y Z hSplit.out false g,?_⟩
  rintro ⟨p,hp,he|he⟩
  · have heq : g • visualVertex M Y Z hSplit.out false 1=
        p • visualVertex M Y Z hSplit.out false 1 := by
      simpa only [visual_smul_vertex,mul_one] using he
    have ha : p⁻¹*g∈MulAction.stabilizer (Artin M) (visualVertex M Y Z hSplit.out false 1) := by
      change (p⁻¹*g) • visualVertex M Y Z hSplit.out false 1=_
      rw [mul_smul,heq,inv_smul_smul]
    rw [visual_vertex_stabilizer,conjugate_one] at ha
    exact hg p hp (p⁻¹*g) ha (by group)
  · have h := congrArg (fun w : VisualVertex M Y Z => w.1) he
    exact Bool.false_ne_true h

lemma parabolicSubtree_boundary (hIrred : IsIrreducible M) (X : Set S)
    (hX : X≠Set.univ) : ∃ u v : VisualVertex M Y Z,
    (visualGraph M Y Z).Adj u v ∧ u∈parabolicSubtree M Y Z X ∧
      v∉parabolicSubtree M Y Z X := by
  obtain ⟨w,hw⟩ := parabolicSubtree_proper M Y Z hIrred X hX
  let u := visualVertex M Y Z hSplit.out false 1
  have hu : u∈parabolicSubtree M Y Z X :=
    ⟨1,Subgroup.one_mem _,Or.inl (one_smul _ _).symm⟩
  obtain ⟨p,_⟩ := (visualGraph_isTree M Y Z).connected.exists_isPath u w
  exact exists_boundary_edge (visualGraph M Y Z) hu hw p

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ProperParabolicMalnormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weak malnormality of all proper parabolics

This proves the implication needed from Charney--Martin--Morris-Wright,
*Acylindrical hyperbolicity for Artin groups with a visual splitting*,
Algebraic & Geometric Topology 26 (2026), Proposition 4.2, for the present
Artin groups. A proper parabolic preserves a proper convex subtree. Two
translates can be placed at the ends of a segment with trivial stabilizer.
Their common stabilizer fixes that segment, hence is trivial.
-/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
include hSplit

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.properParabolicAction
/-- The two conjugates have trivial intersection; this is stronger than
finiteness in the published weak-malnormality criterion. -/
theorem standard_parabolic_trivial_conjugates (hIrred : IsIrreducible M)
    (X : Set S) (hX : X≠Set.univ) :
    ∃ a b : Artin M,
      conjugate a (artinParabolic M X) ⊓ conjugate b (artinParabolic M X)=⊥ := by
  let U := parabolicSubtree M Y Z X
  have hU : PathClosed (visualGraph M Y Z) U := parabolicSubtree_pathClosed M Y Z X
  obtain ⟨x,y,hxy,hx,hy⟩ := parabolicSubtree_boundary M Y Z hIrred X hX
  obtain ⟨u,v,huv,hu,hv,hpair⟩ := visual_trivial_pair_distinct_type M Y Z hIrred x.1
  obtain ⟨p,hp⟩ := (visualGraph_isTree M Y Z).connected.exists_isPath u v
  have hpn : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne huv
  have hprn : ¬p.reverse.Nil := SimpleGraph.Walk.not_nil_of_ne huv.symm
  obtain ⟨a,hax,hay⟩ := visual_oriented_edge_transitive M Y Z hxy
    (p.adj_snd hpn) hu.symm
  obtain ⟨b,hbx,hby⟩ := visual_oriented_edge_transitive M Y Z hxy
    (p.reverse.adj_snd hprn) hv.symm
  refine ⟨a,b,?_⟩
  apply le_antisymm _ bot_le
  intro g hg
  have haU : u∈(a • ·) '' U := ⟨x,hx,hax⟩
  have hbU : v∈(b • ·) '' U := ⟨x,hx,hbx⟩
  have hpa : p.snd∉(a • ·) '' U := not_mem_image_of_smul_eq hy hay
  have hpb : p.reverse.snd∉(b • ·) '' U := not_mem_image_of_smul_eq hy hby
  have hfix := fixes_bridge (visualGraph M Y Z) (visualGraph_isTree M Y Z)
    (visual_preservesAdj M Y Z)
    (pathClosed_smul _ (visual_preservesAdj M Y Z) hU a)
    (pathClosed_smul _ (visual_preservesAdj M Y Z) hU b)
    haU hbU p hp hpa hpb g
    (fun w hw => conjugate_preserves_image (artinParabolic M X) U
      (fun q hq z hz => parabolicSubtree_invariant M Y Z X hq hz) a hg.1 hw)
    (fun w hw => conjugate_preserves_image (artinParabolic M X) U
      (fun q hq z hz => parabolicSubtree_invariant M Y Z X hq hz) b hg.2 hw)
  have hgpair : g∈pairStabilizer (G := Artin M) u v := hfix
  rwa [hpair] at hgpair

/-- Every proper parabolic of an irreducible visually split Artin group
is weakly malnormal, with no published hypotheses. -/
theorem proper_parabolic_weaklyMalnormal (hIrred : IsIrreducible M)
    (P : Subgroup (Artin M)) (hP : IsParabolic M P) (hne : P≠⊤) : WeaklyMalnormal P := by
  obtain ⟨X,g,rfl⟩ := hP
  have hX : X≠Set.univ := by
    intro he
    apply hne
    rw [he,standard_univ,conjugate_top]
  obtain ⟨a,b,hab⟩ := standard_parabolic_trivial_conjugates M Y Z hIrred X hX
  exact (weaklyMalnormal_of_conjugates_inf_bot _ a b hab).conjugate_subgroup g

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GeneratorPowers
attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_eq_smul _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamily_one _root_.OAI.HarmonicArtin.ParabolicIntersections.visualFromArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visualToArtin_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.visual_smul_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Infinite cyclic generator subgroups and their intersections with standard
parabolics. The retraction argument supplies infinite branching in visual trees. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S)

lemma generator_zpow_eq_one_iff (s : S) (n : ℤ) :
    generator M s ^ n=1 ↔ n=0 := by
  constructor
  · intro h
    have he := congrArg (artinExponent M) h
    simp only [map_zpow,map_one] at he
    rw [artinExponent_generator] at he
    simpa using congrArg Multiplicative.toAdd he
  · rintro rfl
    exact zpow_zero _

variable [Fintype S] (J : Set S)
local notation "cs" => M.toCoxeterSystem
local notation "R" => restrictedMatrix M J

lemma parabolicStepLetter_one_outside (t : S) (ht : t∉J) :
    parabolicStepLetter cs J 1 t=none := by
  have hrep : parabolicRep cs J 1=1 :=
    parabolicRep_of_minimum cs J 1 (by intro a _; simp only [(cs).length_one]; omega)
  have hcomp : parabolicComponent cs J 1=1 := by simp only [parabolicComponent,hrep,inv_one,mul_one]
  cases hh : parabolicStepLetter cs J 1 t with
  | none => rfl
  | some s =>
    have he := parabolicStepLetter_conjugate cs J 1 t s hh
    simp only [hcomp,MulAut.conj_apply,one_mul,inv_one,mul_one] at he
    exact False.elim (ht ((simple_injective cs he) ▸ s.property))

lemma parabolicStepArtin_one_outside (t : S) (ht : t∉J) :
    parabolicStepArtin M J 1 t=1 := by
  simp only [parabolicStepArtin,parabolicStepLetter_one_outside M J t ht,
    Option.toList_none,wordArtin,List.map_nil,List.prod_nil]

/-- Every integral power of an outside generator has trivial parabolic read. -/
lemma generator_power_retraction (t : S) (ht : t∉J) (n : ℤ) :
    (MulOpposite.unop (parabolicRetractionAction M J (generator M t ^ n))
      (1,1)).2=1 := by
  let f := parabolicStepPerm M J t
  let B : Set (M.Group × Artin R) := {x | (x.1=1 ∨ x.1=(cs).simple t) ∧ x.2=1}
  have hs := parabolicStepArtin_one_outside M J t ht
  have hs' : parabolicStepArtin M J ((cs).simple t) t=1 := by
    simpa only [one_mul] using (parabolicStepArtin_reverse M J 1 t).trans hs
  have hf : ∀ x∈B, f x∈B := by
    rintro ⟨w,a⟩ ⟨hw,ha⟩
    rcases hw with rfl|rfl
    · refine ⟨Or.inr (one_mul _),?_⟩
      change a*parabolicStepArtin M J 1 t=1
      rwa [hs,mul_one]
    · refine ⟨Or.inl ((cs).simple_mul_simple_self t),?_⟩
      change a*parabolicStepArtin M J ((cs).simple t) t=1
      rwa [hs',mul_one]
  have hfi : ∀ x∈B, f.symm x∈B := by
    rintro ⟨w,a⟩ ⟨hw,ha⟩
    rcases hw with rfl|rfl
    · refine ⟨Or.inr (one_mul _),?_⟩
      change a*(parabolicStepArtin M J 1 t)⁻¹=1
      rwa [hs,inv_one,mul_one]
    · refine ⟨Or.inl ((cs).simple_mul_simple_self t),?_⟩
      change a*(parabolicStepArtin M J ((cs).simple t) t)⁻¹=1
      rwa [hs',inv_one,mul_one]
  have hall : ∀ n : ℤ, MulOpposite.unop (parabolicRetractionAction M J (generator M t ^ n)) (1,1)∈B := by
    intro n
    induction n using Int.induction_on with
    | zero =>
      simp only [zpow_zero,map_one,MulOpposite.unop_one,Equiv.Perm.one_apply]
      exact ⟨Or.inl rfl,rfl⟩
    | succ n ih =>
      rw [zpow_add_one,map_mul,MulOpposite.unop_mul,Equiv.Perm.mul_apply,
        parabolicRetractionAction_generator,MulOpposite.unop_op]
      exact hf _ ih
    | pred n ih =>
      rw [zpow_sub_one,map_mul,map_inv,MulOpposite.unop_mul,Equiv.Perm.mul_apply,
        parabolicRetractionAction_generator,MulOpposite.unop_inv,MulOpposite.unop_op]
      exact hfi _ ih
  exact (hall n).2

/-- A nonzero power of an omitted generator never lies in a standard parabolic. -/
theorem generator_zpow_not_mem (t : S) (ht : t∉J) (n : ℤ) (hn : n≠0) :
    generator M t ^ n∉artinParabolic M J := by
  intro hm
  obtain ⟨a,ha⟩ := (restrictedArtinHom_range M J ▸ hm)
  have h := parabolicRetractionAction_standard M J a 1
  have he := generator_power_retraction M J t ht n
  rw [←ha] at he
  change (MulOpposite.unop (parabolicRetractionAction M J (restrictedArtinHom M J a))
    (parabolicState M J 1)).2=1 at he
  rw [h] at he
  change 1*a=1 at he
  rw [one_mul] at he
  have hh : generator M t ^ n=1 := by rw [←ha,he,map_one]
  exact hn ((generator_zpow_eq_one_iff M t n).mp hh)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualInfiniteBranching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Infinite branching for the genuine visual tree. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable

private lemma injective_zpow_orbit {G V : Type} [Group G] [MulAction G V]
    (a : G) (v : V) (ha : ∀ n : ℤ, n≠0 → a^n∉MulAction.stabilizer G v) :
    Function.Injective (fun n : ℤ => a^n • v) := by
  intro m n he
  change a^m • v=a^n • v at he
  by_contra hmn
  have hn : -m+n≠0 := by omega
  apply ha (-m+n) hn
  change a^(-m+n) • v=v
  rw [zpow_add,mul_smul,←he,zpow_neg,inv_smul_smul]

variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]

attribute [local instance] OAI.HarmonicArtin.ParabolicIntersections.instMulActionArtinVisualVertex_5
/-- Every oriented edge belongs to an infinite orbit under the stabilizer
of its initial vertex. In particular, the visual tree is not a line. -/
theorem visual_infinite_branching {u v : VisualVertex M Y Z}
    (h : (visualGraph M Y Z).Adj u v) :
    ∃ a : Artin M, a∈MulAction.stabilizer (Artin M) u ∧
      Function.Injective (fun n : ℤ => a^n • v) := by
  obtain ⟨g,hu,hv⟩ := visual_adj_representatives M Y Z h
  have hside : visualSide Y Z v.1≠Set.univ := by
    cases v.1
    · exact (Set.ssubset_iff_subset_ne.mp hSplit.out.2.1).2
    · exact (Set.ssubset_iff_subset_ne.mp hSplit.out.2.2.1).2
  obtain ⟨t,ht⟩ := Set.nonempty_compl.mpr hside
  have hgen : generator M t∈artinParabolic M (visualSide Y Z u.1) := by
    apply (generator_mem_standard_iff M _ _).mpr
    have hcover : visualSide Y Z u.1 ∪ visualSide Y Z v.1=Set.univ := by
      have hne := h.1
      cases hu' : u.1 <;> cases hv' : v.1
      · exact False.elim (hne (hu'.trans hv'.symm))
      · exact hSplit.out.1
      · exact Set.union_comm Y Z ▸ hSplit.out.1
      · exact False.elim (hne (hu'.trans hv'.symm))
    exact (hcover.symm ▸ Set.mem_univ t : t∈visualSide Y Z u.1 ∪ visualSide Y Z v.1).resolve_right ht
  let a := g*generator M t*g⁻¹
  have hapow (n : ℤ) : a^n=g*(generator M t)^n*g⁻¹ := by
    exact (map_zpow (MulAut.conj g).toMonoidHom (generator M t) n).symm
  refine ⟨a,?_,injective_zpow_orbit a v ?_⟩
  · rw [hu,visual_vertex_stabilizer,mem_conjugate]
    have he : g⁻¹*a*g=generator M t := by dsimp only [a]; group
    rw [he]
    exact hgen
  · intro n hn hm
    rw [hv,visual_vertex_stabilizer,mem_conjugate,hapow] at hm
    have he : g⁻¹*(g*generator M t^n*g⁻¹)*g=generator M t^n := by group
    rw [he] at hm
    exact generator_zpow_not_mem M (visualSide Y Z v.1) t ht n hn hm

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_DynamicsMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Corollary 1.3 with only the general amalgam criterion remaining

The Artin-specific statements of Charney--Martin--Morris-Wright,
Theorem 3.2 and Proposition 4.2, are proved in this development.
The only remaining published input is Minasyan--Osin (2015), Corollary 2.2,
for arbitrary amalgamated products. In particular the weak-malnormality
half of the corollary has no published hypotheses.
-/
namespace HarmonicArtin.ParabolicIntersections
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- The weak-malnormality assertion of paper 082-03, Corollary 1.3,
without any published input. -/
theorem unconditional_nonclique_weaklyMalnormal
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S,s≠t ∧ M s t=0)
    (P : Subgroup (Artin M)) (hP : IsParabolic M P) (hne : P≠⊤) : WeaklyMalnormal P := by
  obtain ⟨s,t,hst,hm⟩ := hInf
  let : Fact (IsVisualSplit M {s}ᶜ {t}ᶜ) := ⟨infinite_pair_visual_split M s t hst hm⟩
  exact proper_parabolic_weaklyMalnormal M {s}ᶜ {t}ᶜ hIrred P hP hne

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PeriodicBoundary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A periodic free segment and a third direction give a non-elementary action. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
open GraphRealization
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

lemma graphProduct_smul (H : SimpleGraph V) (hH : H.Connected)
    (hB : PreservesAdj (G := G) H) (g : G) (x y z : V) :
    graphProduct H (g • x) (g • y) (g • z)=graphProduct H x y z := by
  simp only [graphProduct,graph_action_dist H hH hB]

theorem periodic_three_limit_points (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v)
    (g : G) {x : V} (p : T.Walk x (g • x)) (hp : p.IsPath) (hpn : ¬p.Nil)
    (hturn : p.reverse.snd≠g • p.snd) (a : G)
    (hau : a • u∈p.support) (hav : a • v∈p.support)
    (c : G) (hc : c • x=x) (hc₁ : c • p.snd≠p.snd)
    (hc₂ : c • p.snd≠g⁻¹ • p.reverse.snd) :
    let H := avoidingGraph (G := G) T u v
    let hH := avoidingGraph_connected T u v hT hA hne hnadj
    let hB := avoidingGraph_preservesAdj T u v hA
    let _ := action H hB hH
    HasThreeOrbitLimitPoints G (Space H hH) := by
  let q := inverseSegment T hA g p
  have hq : q.IsPath := inverseSegment_isPath T hA g p hp
  have hqn : ¬q.Nil := inverseSegment_nonempty T hA g p hpn
  have hqt : q.reverse.snd≠g⁻¹ • q.snd := inverseSegment_turn T hA g p hturn
  have hqu : (g⁻¹*a) • u∈q.support := inverseSegment_mem T hA g a p hau
  have hqv : (g⁻¹*a) • v∈q.support := inverseSegment_mem T hA g a p hav
  have hback : q.snd≠p.snd := by
    rw [inverseSegment_snd]
    intro he
    have hh := congrArg (fun w : V => g • w) he
    rw [smul_inv_smul] at hh
    exact hturn hh
  let seq : Fin 3 → ℕ → G := ![fun n => g^n,fun n => (g⁻¹)^n,fun n => c*g^n]
  let P : ∀ i n,T.Walk x (seq i n • x) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro n
      exact periodicPath T hA g p n
    · intro j
      refine Fin.cases ?_ ?_ j
      · intro n
        exact periodicPath T hA g⁻¹ q n
      · intro k
        refine Fin.cases ?_ (fun z => Fin.elim0 z) k
        intro n
        exact (actPath T hA c (periodicPath T hA g p n)).copy hc (mul_smul c (g^n) x).symm
  let d : Fin 3 → V := ![p.snd,q.snd,c • p.snd]
  refine realization_three_rays T u v hT hA hne hnadj x seq P ?_ ?_ d ?_ ?_ ?_
  · intro i n
    fin_cases i
    · exact periodicPath_isPath T hA hT.isAcyclic g p hp hpn hturn n
    · exact periodicPath_isPath T hA hT.isAcyclic g⁻¹ q hq hqn hqt n
    · apply (SimpleGraph.Walk.isPath_copy _ _ _).mpr
      exact (periodicPath_isPath T hA hT.isAcyclic g p hp hpn hturn n).map
        (MulAction.toPerm c).injective
  · intro i
    fin_cases i
    · change (periodicPath T hA g p 0).Nil
      simp [periodicPath]
    · change (periodicPath T hA g⁻¹ q 0).Nil
      simp [periodicPath]
    · change ((actPath T hA c (periodicPath T hA g p 0)).copy hc _).Nil
      apply SimpleGraph.Walk.length_eq_zero_iff.mp
      exact (actPath_copy_length T hA c (periodicPath T hA g p 0) hc _).trans
        ((periodicPath_length T hA g p 0).trans (zero_mul _))
  · intro i j he
    have hc₂' : c • p.snd≠q.snd := by simpa only [q,inverseSegment_snd] using hc₂
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hback (show p.snd=q.snd from he).symm)
    · exact False.elim (hc₁ (show p.snd=c • p.snd from he).symm)
    · exact False.elim (hback (show q.snd=p.snd from he))
    · rfl
    · exact False.elim (hc₂' (show q.snd=c • p.snd from he).symm)
    · exact False.elim (hc₁ (show c • p.snd=p.snd from he))
    · exact False.elim (hc₂' (show c • p.snd=q.snd from he))
    · rfl
  · intro i n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    fin_cases i
    · exact periodicPath_snd T hA g p hpn k
    · exact periodicPath_snd T hA g⁻¹ q hqn k
    · change ((actPath T hA c (periodicPath T hA g p (k+1))).copy hc _).snd=c • p.snd
      exact (actPath_copy_snd T hA c (periodicPath T hA g p (k+1)) hc _).trans
        (congrArg (fun w : V => c • w) (periodicPath_snd T hA g p hpn k))
  · intro i R
    fin_cases i
    · exact periodic_shortcut_gromov T hA hT u v hfree hne hnadj g p hp hpn hturn a hau hav R
    · exact periodic_shortcut_gromov T hA hT u v hfree hne hnadj g⁻¹ q hq hqn hqt (g⁻¹*a) hqu hqv R
    · obtain ⟨N,hN⟩ := periodic_shortcut_gromov T hA hT u v hfree hne hnadj g p hp hpn hturn a hau hav R
      refine ⟨N,?_⟩
      intro m hm n hn
      change R ≤ graphProduct (avoidingGraph (G := G) T u v) x ((c*g^m) • x) ((c*g^n) • x)
      rw [mul_smul,mul_smul]
      have he := graphProduct_smul _ (avoidingGraph_connected T u v hT hA hne hnadj)
        (avoidingGraph_preservesAdj T u v hA) c x (g^m • x) (g^n • x)
      rw [hc] at he
      rw [he]
      exact hN m hm n hn

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeBranchingHyperbolic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sufficient tree-action case of the published amalgam criterion, proved directly. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
open GraphRealization
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V)

lemma zpow_orbit_moves {a : G} {x : V}
    (ha : Function.Injective (fun n : ℤ => a^n • x)) : a • x≠x := by
  intro he
  have h : (1 : ℤ)=0 := ha (by simpa only [zpow_one,zpow_zero,one_smul] using he)
  norm_num at h

lemma zpow_third_direction {a : G} {x y z : V} (hx : a • x=x)
    (ha : Function.Injective (fun n : ℤ => a^n • y)) :
    ∃ c : G,c • x=x ∧ c • y≠y ∧ c • y≠z := by
  have ha₁ : a • y≠y := zpow_orbit_moves ha
  by_cases haz : a • y=z
  · have ha₂ : a^2 • y≠y := by
      intro he
      have h : (2 : ℤ)=0 := ha (by simpa using he)
      norm_num at h
    have ha₂₁ : a^2 • y≠a • y := by
      intro he
      have h : (2 : ℤ)=1 := ha (by simpa using he)
      norm_num at h
    refine ⟨a^2,?_,ha₂,?_⟩
    · rw [pow_two,mul_smul,hx,hx]
    · exact fun he => ha₂₁ (he.trans haz.symm)
  · exact ⟨a,hx,ha₁,haz⟩

/-- A free segment and infinite branching provide an explicit
non-elementary acylindrical action on a geodesic hyperbolic space. -/
theorem acylindricallyHyperbolic_of_free_segment
    (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hbranch : ∀ x y : V,T.Adj x y →
      ∃ a : G,a • x=x ∧ Function.Injective (fun n : ℤ => a^n • y))
    (u v : V) (hne : u≠v) (hnadj : ¬T.Adj u v)
    (hfree : pairStabilizer (G := G) u v=⊥) : AcylindricallyHyperbolic G := by
  obtain ⟨p,hp⟩ := hT.connected.exists_isPath u v
  have hpn : ¬p.Nil := fun h => hne (hp.nil_iff_eq.mp h)
  have hprn : ¬p.reverse.Nil := by
    intro h
    have hl := h.length_eq_zero
    rw [SimpleGraph.Walk.length_reverse] at hl
    exact hpn (SimpleGraph.Walk.length_eq_zero_iff.mp hl)
  obtain ⟨a,ha,ha'⟩ := hbranch u p.snd (p.adj_snd hpn)
  obtain ⟨b,hb,hb'⟩ := hbranch v p.reverse.snd (p.reverse.adj_snd hprn)
  obtain ⟨q,hq,hqn,hqt,hqu,hqv⟩ := translation_segment T hA hT.isAcyclic p hp hpn
    a b ha hb (zpow_orbit_moves ha') (zpow_orbit_moves hb')
  obtain ⟨c,hc,hc'⟩ := hbranch u q.snd (q.adj_snd hqn)
  obtain ⟨d,hd,hd₁,hd₂⟩ := zpow_third_direction (z := (a*b)⁻¹ • q.reverse.snd) hc hc'
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hB := avoidingGraph_preservesAdj T u v hA
  let X := Space H hH
  let _ := action H hB hH
  obtain ⟨hgeo,hhyp,hiso,hacyl⟩ := avoiding_realization_geometry T u v hT hA hfree hne hnadj
  have hlim : HasThreeOrbitLimitPoints G X :=
    periodic_three_limit_points T u v hT hA hfree hne hnadj (a*b) q hq hqn hqt a hqu hqv d hd hd₁ hd₂
  exact ⟨X,inferInstance,action H hB hH,hgeo,hhyp,hiso,hacyl,hlim⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualAcylindrical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An unconditional acylindrical action for the Artin visual splitting

The sufficient Artin case of Minasyan--Osin (2015), Corollary 2.2,
is proved here by constructing a geodesic hyperbolic realization of the
shortcut graph, a uniform acylindricity bound, and three distinct orbit
limit points. No instance of the published amalgam criterion is assumed.
-/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]

noncomputable local instance visualAcylindricalAction_r5eca9b_1 : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out
include hSplit in
theorem visual_acylindricallyHyperbolic (hIrred : IsIrreducible M) :
    AcylindricallyHyperbolic (Artin M) := by
  obtain ⟨u,v,hne,hu,hv,hfree⟩ := visual_trivial_pair_distinct_type M Y Z hIrred false
  apply acylindricallyHyperbolic_of_free_segment (visualGraph M Y Z)
    (visualGraph_isTree M Y Z) (visual_preservesAdj M Y Z) ?_ u v hne ?_ hfree
  · intro x y hxy
    obtain ⟨a,ha,hinj⟩ := visual_infinite_branching M Y Z hxy
    exact ⟨a,ha,hinj⟩
  · intro h
    exact h.1 (hu.trans hv.symm)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_DynamicsUnconditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Paper 082-03, Corollary 1.3, without published hypotheses

For a finite-rank irreducible Artin group whose defining graph is not a
clique, the group is acylindrically hyperbolic and every proper parabolic
subgroup is weakly malnormal. The acylindrical action is constructed from
the genuine visual tree; the algebraic intersection theorem supplies a
segment with trivial stabilizer. All metric, boundary, and malnormality
arguments are proved in the imported development.
-/
namespace HarmonicArtin.ParabolicIntersections
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- The full third main result of *Parabolic intersections in Artin groups*. -/
theorem unconditional_nonclique_dynamics_oai
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S,s≠t ∧ M s t=0) :
    AcylindricallyHyperbolic (Artin M) ∧
      ∀ P : Subgroup (Artin M),IsParabolic M P → P≠⊤ → WeaklyMalnormal P := by
  constructor
  · obtain ⟨s,t,hst,hm⟩ := hInf
    let : Fact (IsVisualSplit M {s}ᶜ {t}ᶜ) := ⟨infinite_pair_visual_split M s t hst hm⟩
    exact visual_acylindricallyHyperbolic M {s}ᶜ {t}ᶜ hIrred
  · exact unconditional_nonclique_weaklyMalnormal M hIrred hInf

end HarmonicArtin.ParabolicIntersections

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics_oai := @OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics_oai

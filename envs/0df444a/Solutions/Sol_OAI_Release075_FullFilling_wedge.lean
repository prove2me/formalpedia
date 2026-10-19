-- Prove2me | solution 1 for OAI.Release075.FullFilling.wedge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:44:52.208524+00:00
-- url     : https://prove2.me/submissions/6efeadb2-a689-403b-bd79-15d771070643

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/FullGluing.lean:L11-L148
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.FullFilling.wedge. The node keeps its source
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
import Theorems.Thm_OAI_Release075_PermCycles_PlanarMap_join_left

-- ---- from OAI.GroupTheory.Hyperbolic.Planarity ----
namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem color_swap {C : Type*} (color : A → C) {a b : A}
    (hab : color a = color b) (z : A) : color (Equiv.swap a b z) = color z := by
  by_cases ha : z = a
  · subst z
    simpa only [Equiv.swap_apply_left] using hab.symm
  by_cases hb : z = b
  · subst z
    simpa only [Equiv.swap_apply_right] using hab
  · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype B] in
theorem components_map (f g : Perm A) (f' g' : Perm B) (e : A → B)
    (hf : ∀ a, e (f a) = f' (e a)) (hg : ∀ a, e (g a) = g' (e a)) :
    components f g ≤ (components f' g').comap e := by
  apply sup_le
  · apply sameCycle_le_of_step
    intro a
    change components f' g' (e a) (e (f a))
    rw [hf]
    exact (show Perm.SameCycle.setoid f' ≤ components f' g' from le_sup_left)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl f' _))
  · apply sameCycle_le_of_step
    intro a
    change components f' g' (e a) (e (g a))
    rw [hg]
    exact (show Perm.SameCycle.setoid g' ≤ components f' g' from le_sup_right)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl g' _))

theorem components_intertwine (f g : Perm A) (f' g' : Perm B) (e : A ≃ B)
    (hf : ∀ a, e (f a) = f' (e a)) (hg : ∀ a, e (g a) = g' (e a)) (a b : A) :
    components f g a b ↔ components f' g' (e a) (e b) := by
  constructor
  · exact fun h => components_map f g f' g' e hf hg h
  · intro h
    have hf' (b : B) : e.symm (f' b) = f (e.symm b) := by
      apply e.injective
      simp only [e.apply_symm_apply,hf]
    have hg' (b : B) : e.symm (g' b) = g (e.symm b) := by
      apply e.injective
      simp only [e.apply_symm_apply,hg]
    have hh := components_map f' g' f g e.symm hf' hg' h
    simpa only [Setoid.comap_rel,e.symm_apply_apply] using hh

theorem componentCount_intertwine (f g : Perm A) (f' g' : Perm B) (e : A ≃ B)
    (hf : ∀ a, e (f a) = f' (e a)) (hg : ∀ a, e (g a) = g' (e a)) :
    componentCount f g = componentCount f' g' :=
  Nat.card_congr (Quotient.congr e (components_intertwine f g f' g' e hf hg))

omit [Fintype A] [Fintype B] in
theorem leftEquiv_intertwine (f : Perm A) (g : Perm B)
    (z : {z : A ⊕ B // leftPred z}) :
    leftEquiv ((f.sumCongr g).subtypePerm (leftPred_sumCongr f g) z) = f (leftEquiv z) := by
  rcases z with ⟨a|b,h⟩; rfl; exact h.elim

omit [Fintype A] [Fintype B] in
theorem rightEquiv_intertwine (f : Perm A) (g : Perm B)
    (z : {z : A ⊕ B // ¬ leftPred z}) :
    rightEquiv ((f.sumCongr g).subtypePerm (p := fun z => ¬leftPred z)
      (fun z => not_congr (leftPred_sumCongr f g z)) z) = g (rightEquiv z) := by
  rcases z with ⟨a|b,h⟩; exact (h True.intro).elim; rfl

theorem cycleCount_sum (f : Perm A) (g : Perm B) :
    cycleCount (f.sumCongr g) = cycleCount f + cycleCount g := by
  rw [cycleCount_partition (f.sumCongr g) leftPred (leftPred_sumCongr f g),
    cycleCount_intertwine _ f leftEquiv (leftEquiv_intertwine f g),
    cycleCount_intertwine _ g rightEquiv (rightEquiv_intertwine f g)]

theorem componentCount_sum (f g : Perm A) (f' g' : Perm B) :
    componentCount (f.sumCongr f') (g.sumCongr g') = componentCount f g + componentCount f' g' := by
  rw [componentCount_partition (f.sumCongr f') (g.sumCongr g') leftPred
    (leftPred_sumCongr f f') (leftPred_sumCongr g g'),
    componentCount_intertwine _ _ f g leftEquiv (leftEquiv_intertwine f f')
      (leftEquiv_intertwine g g'),
    componentCount_intertwine _ _ f' g' rightEquiv (rightEquiv_intertwine f f')
      (rightEquiv_intertwine g g')]

omit [Fintype A] [Fintype B] in
theorem sum_mul (f g : Perm A) (f' g' : Perm B) :
    (f.sumCongr f') * (g.sumCongr g') = (f*g).sumCongr (f'*g') := by
  ext z; cases z <;> rfl

theorem PlanarMap.sum {f g : Perm A} {f' g' : Perm B}
    (h : PlanarMap f g) (h' : PlanarMap f' g') :
    PlanarMap (f.sumCongr f') (g.sumCongr g') := by
  unfold PlanarMap at *
  rw [sum_mul,cycleCount_sum,cycleCount_sum,cycleCount_sum,componentCount_sum,Fintype.card_sum]
  omega

end Release075.PermCycles

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.RePairing ----
namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem components_comm (f g : Perm A) : components f g = components g f := sup_comm _ _

omit [Fintype A] in
theorem componentCount_comm (f g : Perm A) : componentCount f g = componentCount g f := by
  simp only [componentCount,components_comm f g]

theorem PlanarMap.symm {f g : Perm A} (h : PlanarMap f g) : PlanarMap g f := by
  simpa only [PlanarMap,cycleCount_mul_comm g f,componentCount_comm g f,
    Nat.add_comm (cycleCount g) (cycleCount f)] using h

theorem PlanarMap.join_right {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : ¬ components f g a b) : PlanarMap f (Equiv.swap a b * g) := by
  apply PlanarMap.symm
  apply hp.symm.join_left
  rwa [components_comm]

omit [Fintype A] in
theorem swap_color_preserving {C : Type*} (r f : Perm A) (color : A → C)
    (hc : ∀ a, color ((r*f) a) = color a) {a b : A}
    (hab : color (r a) = color (r b)) :
    ∀ z, color ((r*(Equiv.swap a b * f)) z) = color z := by
  intro z
  change (color ∘ r) (Equiv.swap a b (f z)) = color z
  rw [color_swap (color ∘ r) hab]
  exact hc z

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B : Type*} [Fintype A] [Fintype B]

end Release075.PermCycles

namespace Release075
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem formPerm_append_cons (x y : A) (xs ys : List A) :
    (x :: xs ++ y :: ys).formPerm = (x :: xs).formPerm *
      Equiv.swap ((x::xs).getLast (by simp)) y * (y::ys).formPerm := by
  induction xs generalizing x with
  | nil => simp only [List.cons_append,List.nil_append,List.formPerm_cons_cons,List.formPerm_singleton,
      List.getLast_singleton,one_mul]
  | cons z xs ih =>
    simpa only [List.cons_append,List.formPerm_cons_cons,List.getLast_cons_cons,mul_assoc] using
      congrArg (fun p : Perm A => Equiv.swap x z * p) (ih z)

theorem formPerm_concat (x y : A) (xs ys : List A) (hy : y ∉ x::xs) :
    (x :: xs ++ y :: ys).formPerm =
      Equiv.swap x y * ((x::xs).formPerm * (y::ys).formPerm) := by
  rw [formPerm_append_cons,Equiv.mul_swap_eq_swap_mul,
    List.formPerm_apply_getLast,List.formPerm_apply_of_notMem hy,mul_assoc]

theorem IsBoundary.not_mem_iff {f : Perm A} {l : List A} (h : IsBoundary f l) (a : A) :
    f a ∉ l ↔ a ∉ l := not_congr (h.mem_iff a)

theorem IsBoundary.conjugate {B : Type*} {f : Perm A} {g : Perm B} {l : List A}
    (h : IsBoundary f l) (e : A ↪ B) (he : ∀ a, g (e a) = e (f a)) :
    IsBoundary g (l.map e) := by
  refine ⟨h.1.map e.injective,?_⟩
  intro b hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  rw [he,h.2 a ha]
  exact (formPerm_embedding e l a).symm

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

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

theorem same_outside_boundary_pow {f g : Perm A} {l : List A}
    (hb : IsBoundary f l) (he : ∀ z, z ∉ l → g z = f z)
    {a : A} (ha : a ∉ l) (n : ℕ) : (g^n) a = (f^n) a := by
  have ho (k : ℕ) : (f^k) a ∉ l := by
    induction k with
    | zero => exact ha
    | succ k ih =>
      rw [pow_succ',Perm.mul_apply]
      exact (hb.not_mem_iff _).mpr ih
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Perm.mul_apply,ih,he _ (ho n)]

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem components_pred [Fintype A] (r f : Perm A) (p : A → Prop)
    (hr : ∀ a, p (r a) ↔ p a) (hf : ∀ a, p (f a) ↔ p a)
    {a b : A} (h : components r f a b) : p a ↔ p b := by
  have hh : components r f ≤ Setoid.ker p := by
    apply sup_le
    · intro x y h; exact propext (invariant_pred_sameCycle r p hr h)
    · intro x y h; exact propext (invariant_pred_sameCycle f p hf h)
  exact propext_iff.mp (hh h)

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

theorem IsBoundary.join {f : Perm A} {x y : A} {xs ys : List A}
    (hx : IsBoundary f (x::xs)) (hy : IsBoundary f (y::ys))
    (hd : List.Disjoint (x::xs) (y::ys)) :
    IsBoundary (Equiv.swap x y * f) ((x::xs) ++ (y::ys)) := by
  refine ⟨List.nodup_append.mpr ⟨hx.1,hy.1,by rintro z hz t ht rfl; exact hd hz ht⟩,?_⟩
  intro z hz
  rw [formPerm_concat x y xs ys (fun h => hd h (by simp))]
  simp only [Perm.mul_apply]
  congr 1
  rcases List.mem_append.mp hz with hz|hz
  · rw [List.formPerm_apply_of_notMem (fun h => hd hz h),hx.2 z hz]
  · rw [List.formPerm_apply_of_notMem (fun h => hd h (List.formPerm_apply_mem_of_mem hz)),
      hy.2 z hz]

theorem IsBoundary.swap_outside {f : Perm A} {x y : A} {xs ys : List A}
    (hx : IsBoundary f (x::xs)) (hy : IsBoundary f (y::ys))
    (z : A) (hz : z ∉ (x::xs) ++ (y::ys)) :
    (Equiv.swap x y * f) z = f z := by
  have hn := not_or.mp (List.mem_append.not.mp hz)
  apply Equiv.swap_apply_of_ne_of_ne
  · intro he; apply (hx.not_mem_iff z).mpr hn.1; simp [he]
  · intro he; apply (hy.not_mem_iff z).mpr hn.2; simp [he]

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

end Fillable
end Release075

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.FullGluing ----
namespace OAI

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem wedge {w w' : List E} (D : FullFilling flip color face w)
    (D' : FullFilling flip color face w')
    {a : D.Dart} {b : D'.Dart} {l : List D.Dart} {l' : List D'.Dart}
    (ha : D.boundary = a::l) (hb : D'.boundary = b::l')
    (hc : color (flip (D.label a)) = color (flip (D'.label b)))
    (F : E → E → E → M) :
    ∃ C : FullFilling flip color face (w++w'), C.trace F = D.trace F + D'.trace F := by
  let : DecidableEq (D.Dart ⊕ D'.Dart) := Classical.decEq _
  let r := D.reverse.sumCongr D'.reverse
  let f := D.next.sumCongr D'.next
  let lab : D.Dart ⊕ D'.Dart → E := Sum.elim D.label D'.label
  let g := Equiv.swap (Sum.inl a) (Sum.inr b) * f
  let bd := (D.boundary.map Sum.inl) ++ (D'.boundary.map Sum.inr)
  have hleft : IsBoundary f ((a::l).map Sum.inl) :=
    (ha ▸ D.boundary_cycle).conjugate ⟨Sum.inl,Sum.inl_injective⟩ (fun _ => rfl)
  have hright : IsBoundary f ((b::l').map Sum.inr) :=
    (hb ▸ D'.boundary_cycle).conjugate ⟨Sum.inr,Sum.inr_injective⟩ (fun _ => rfl)
  have hdis : List.Disjoint ((a::l).map (@Sum.inl D.Dart D'.Dart))
      ((b::l').map Sum.inr) := by
    intro z hz hz'
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hz'
    cases hy
  have hbd : IsBoundary g bd := by
    dsimp [g,bd]
    rw [ha,hb]
    exact hleft.join hright hdis
  have hsep : ¬ components r f (Sum.inl a) (Sum.inr b) := by
    intro h
    exact (components_pred r f leftPred (leftPred_sumCongr _ _)
      (leftPred_sumCongr _ _) h).mp True.intro
  have hr : ∀ z, lab (r z) = flip (lab z) := by
    intro z; cases z with
    | inl x => exact D.reverse_label x
    | inr x => exact D'.reverse_label x
  have hcol : ∀ z, color (lab ((r*f) z)) = color (lab z) := by
    intro z; cases z with
    | inl x => exact D.color_next x
    | inr x => exact D'.color_next x
  have hcg : ∀ z, color (lab ((r*g) z)) = color (lab z) := by
    apply swap_color_preserving r f (color ∘ lab) hcol
    change color (lab (r (Sum.inl a))) = color (lab (r (Sum.inr b)))
    rw [hr,hr]
    exact hc
  have hsame : ∀ z, z ∉ bd → g z = f z := by
    intro z hz
    apply hleft.swap_outside hright z
    simpa only [bd,ha,hb,List.map_cons] using hz
  let C : FullFilling flip color face (w++w') := {
    Dart := D.Dart ⊕ D'.Dart
    reverse := r
    next := g
    reverse_involutive := by
      intro z
      cases z with
      | inl x => exact congrArg Sum.inl (D.reverse_involutive x)
      | inr x => exact congrArg Sum.inr (D'.reverse_involutive x)
    reverse_ne := by
      intro z he
      cases z with
      | inl x => exact D.reverse_ne x (Sum.inl.inj he)
      | inr x => exact D'.reverse_ne x (Sum.inr.inj he)
    label := lab
    reverse_label := hr
    color_next := hcg
    planar := (D.planar.sum D'.planar).join_right hsep
    boundary := bd
    boundary_cycle := hbd
    boundary_word := by
      simp only [bd,List.map_append,List.map_map]
      change D.boundary.map D.label ++ D'.boundary.map D'.label = w++w'
      rw [D.boundary_word,D'.boundary_word]
    cells := by
      intro z hn
      have hpow (n : ℕ) : (g^n) z = (f^n) z := by
        symm
        apply same_outside_boundary_pow hbd
        · intro z hz; exact (hsame z hz).symm
        · exact hn
      cases z with
      | inl x =>
        have hxn : x ∉ D.boundary := by
          intro hx; apply hn; exact List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
        have he (n : ℕ) : (f^n) (Sum.inl x) = Sum.inl ((D.next^n) x) :=
          (pow_intertwine D.next f Sum.inl (fun _ => rfl) n x).symm
        rcases D.cells x hxn with ht | hb
        · refine Or.inl ⟨?_,?_,?_⟩
          · rw [hpow 3,he 3,ht.1]
          · rw [hsame _ hn]; intro hh; exact ht.2.1 (Sum.inl.inj hh)
          · rw [hsame _ hn,hpow 2,he 2]
            exact ht.2.2
        · refine Or.inr ⟨?_,?_⟩
          · rw [hsame _ hn]; exact congrArg Sum.inl hb.1
          · rw [hpow 2,he 2,hb.2]
      | inr x =>
        have hxn : x ∉ D'.boundary := by
          intro hx; apply hn; exact List.mem_append_right _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
        have he (n : ℕ) : (f^n) (Sum.inr x) = Sum.inr ((D'.next^n) x) :=
          (pow_intertwine D'.next f Sum.inr (fun _ => rfl) n x).symm
        rcases D'.cells x hxn with ht | hb
        · refine Or.inl ⟨?_,?_,?_⟩
          · rw [hpow 3,he 3,ht.1]
          · rw [hsame _ hn]; intro hh; exact ht.2.1 (Sum.inr.inj hh)
          · rw [hsame _ hn,hpow 2,he 2]
            exact ht.2.2
        · refine Or.inr ⟨?_,?_⟩
          · rw [hsame _ hn]; exact congrArg Sum.inr hb.1
          · rw [hpow 2,he 2,hb.2] }
  refine ⟨C,?_⟩
  unfold trace
  rw [Fintype.sum_sum_type]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro x _
    have hx : Sum.inl x ∈ bd ↔ x ∈ D.boundary := by
      simp only [bd,List.mem_append,List.mem_map,Sum.inl.injEq]
      simp only [Sum.inr_ne_inl,exists_false,and_false,or_false,exists_eq_right]
    by_cases hxb : x ∈ D.boundary
    · simp only [C,hx,hxb,ite_true]
    have hn := not_congr hx |>.mpr hxb
    have hpow (n : ℕ) : (g^n) (Sum.inl x) = Sum.inl ((D.next^n) x) := by
      exact (same_outside_boundary_pow hbd (fun z hz => (hsame z hz).symm) hn n).symm.trans
        (pow_intertwine D.next f Sum.inl (fun _ => rfl) n x).symm
    simp only [C,hx,hxb,ite_false,hpow 2,hsame _ hn]
    rfl
  · apply Finset.sum_congr rfl
    intro x _
    have hx : Sum.inr x ∈ bd ↔ x ∈ D'.boundary := by
      simp only [bd,List.mem_append,List.mem_map,Sum.inr.injEq]
      simp only [Sum.inl_ne_inr,exists_false,and_false,false_or,exists_eq_right]
    by_cases hxb : x ∈ D'.boundary
    · simp only [C,hx,hxb,ite_true]
    have hn := not_congr hx |>.mpr hxb
    have hpow (n : ℕ) : (g^n) (Sum.inr x) = Sum.inr ((D'.next^n) x) := by
      exact (same_outside_boundary_pow hbd (fun z hz => (hsame z hz).symm) hn n).symm.trans
        (pow_intertwine D'.next f Sum.inr (fun _ => rfl) n x).symm
    simp only [C,hx,hxb,ite_false,hpow 2,hsame _ hn]
    rfl

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

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M N : Type} [AddCommGroup M] [AddCommGroup N]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.FullFilling.wedge := @_root_.OAI.Release075.FullFilling.wedge

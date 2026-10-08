-- Prove2me | solution 1 for OAI.DeligneDrinfeld.ProjectionKernel.leading_projection_kernel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:54:02.911691+00:00
-- url     : https://prove2.me/submissions/fcaeae26-58b6-4716-b8e0-061eecb67090

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid
import Theorems.Thm_OAI_DeligneDrinfeld_ExactPentagon_row_equation

set_option linter.all false


section

namespace OAI

noncomputable section
namespace DeligneDrinfeld

namespace QuadraticAlphabet
open AssociativeElimination LieAlgebra
attribute [local instance] LieRing.ofAssociativeRing
abbrev F := ZMod 2
inductive Letter | a | c | b deriving DecidableEq
instance (α : Type*) : CharP (A F α) 2 :=
  charP_of_injective_ringHom (algebraMap F (A F α)).injective 2
abbrev S := A F Letter
abbrev T := A F (Option Unit)
def a : S := atom Letter.a
def c : S := atom Letter.c
def b : S := atom Letter.b
def x : T := atom none
def y : T := atom (some ())

def delta : S →ₗ[F] S := deriv (fun | .a => 0 | .c => ⁅a,b⁆ | .b => c)
@[simp] theorem delta_a : delta a=0 := by simp [delta,a]
@[simp] theorem delta_b : delta b=c := by simp [delta,b]
@[simp] theorem delta_c : delta c=⁅a,b⁆ := by simp [delta,c]
@[simp] theorem delta_one : delta 1=0 := deriv_one _
theorem delta_mul (p q : S) : delta (p*q)=delta p*q+p*delta q := deriv_mul _ _ _
theorem delta_lie (p q : S) : delta ⁅p,q⁆=⁅delta p,q⁆+⁅p,delta q⁆ := deriv_lie _ _ _

theorem delta_square_mul (p q : S) :
    delta (delta (p*q))=delta (delta p)*q+p*delta (delta q) := by
  rw [delta_mul,map_add,delta_mul,delta_mul]
  calc
    _ = delta (delta p)*q+p*delta (delta q)+(delta p*delta q+delta p*delta q) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

theorem delta_square (p : S) : delta (delta p)=⁅a,p⁆ := by
  induction p using algebra_induction with
  | h1 => simp [Ring.lie_def]
  | ha l =>
    cases l with
    | a => change delta (delta a)=⁅a,a⁆; simp
    | c => change delta (delta c)=⁅a,c⁆; simp [delta_lie]
    | b => change delta (delta b)=⁅a,b⁆; simp
  | hadd p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hm p q hp hq => rw [delta_square_mul,hp,hq]; simp [Ring.lie_def]; noncomm_ring

def left : S →ₐ[F] Module.End F (S×S) where
  toFun p :=
    { toFun := fun z => (p*z.1,p*z.2)
      map_add' := by intro z w; ext <;> simp [mul_add]
      map_smul' := by intro r z; ext <;> simp }
  map_one' := by ext z <;> simp
  map_mul' := by intro p q; ext z <;> simp [mul_assoc]
  map_zero' := by ext z <;> simp
  map_add' := by intro p q; ext z <;> simp [add_mul]
  commutes' := by intro r; ext z <;> simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem left_apply (p : S) (z : S×S) : left p z=(p*z.1,p*z.2) := rfl

def root : Module.End F (S×S) where
  toFun z := (delta z.1+z.2*a,z.1+delta z.2)
  map_add' := by intro z w; apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,map_add,add_mul] <;> abel
  map_smul' := by intro r z; ext <;> simp [smul_add]
@[simp] theorem root_apply (z : S×S) : root z=(delta z.1+z.2*a,z.1+delta z.2) := rfl

theorem root_comm (p : S) : ⁅root,left p⁆=left (delta p) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp [Ring.lie_def,delta_mul,Module.End.mul_apply,mul_add,mul_assoc]

theorem root_square : root*root=left a := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp only [Module.End.mul_apply,root_apply,left_apply,
    map_add,delta_mul,delta_square,delta_a,mul_zero,add_zero,Ring.lie_def,add_mul]
  · calc
      _ = a*z.1+(delta z.2*a+delta z.2*a) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
  · calc
      _ = a*z.2+(delta z.1+delta z.1) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

def substitution : S →ₐ[F] T := lift (fun | .a => x*x | .c => ⁅x,y⁆ | .b => y)
@[simp] theorem substitution_a : substitution a=x*x := by simp [substitution,a]
@[simp] theorem substitution_c : substitution c=⁅x,y⁆ := by simp [substitution,c]
@[simp] theorem substitution_b : substitution b=y := by simp [substitution,b]

def representation : T →ₐ[F] Module.End F (S×S) :=
  lift (fun | none => root | some _ => left b)
@[simp] theorem representation_x : representation x=root := by simp [representation,x]
@[simp] theorem representation_y : representation y=left b := by simp [representation,y]

theorem representation_substitution : representation.comp substitution=left := by
  apply hom_ext
  intro l
  cases l with
  | a => change representation (substitution a)=left a; simp [root_square]
  | c =>
    change representation (substitution c)=left c
    rw [substitution_c]
    change representation (x*y-y*x)=left c
    rw [map_sub,map_mul,map_mul,representation_x,representation_y]
    change ⁅root,left b⁆=left c
    rw [root_comm,delta_b]
  | b => change representation (substitution b)=left b; simp

theorem left_injective : Function.Injective left := by
  intro p q h
  have hh := congrArg (fun f : Module.End F (S×S) => (f (1,0)).1) h
  simpa using hh

theorem substitution_injective : Function.Injective substitution := by
  intro p q h
  apply left_injective
  rw [← representation_substitution]
  exact congrArg representation h

end QuadraticAlphabet

namespace GenericBraid
open LieAlgebra FreeDerivations
variable {R α : Type*} [CommRing R]

variable [DecidableEq α]

theorem t_base_fiber_left (i j : α) :
    ⁅t (R:=R) (some i) (some j),t (R:=R) none (some i)⁆=⁅t (R:=R) none (some i),t (R:=R) none (some j)⁆ := by
  by_cases hij : i=j
  · subst j; simp
  have h := t_three (R:=R) (none : Option α) (some i) (some j) (by simp) (by simp)
    (fun h => hij (Option.some.inj h))
  rw [lie_add] at h
  grind [lie_skew]

end GenericBraid

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

namespace GenericBraid

section
variable {S α β : Type*} [CommRing S]
def rename {R : Type*} [CommRing R] (e : α ≃ β) : T R α →ₗ⁅R⁆ T R β :=
  lift (fun i j => t (e i) (e j)) (fun i => t_self (e i)) (fun i j => t_comm (e i) (e j))
    (fun i j k l hik hil hjk hjl => t_disjoint (e i) (e j) (e k) (e l)
      (e.injective.ne hik) (e.injective.ne hil) (e.injective.ne hjk) (e.injective.ne hjl))
    (fun i j k hij hik hjk => t_three (e i) (e j) (e k) (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))
@[simp] theorem rename_t {R : Type*} [CommRing R] (e : α ≃ β) (i j : α) :
    rename e (t (R:=R) i j)=t (e i) (e j) := by simp [rename]
variable [DecidableEq α]
end

variable {α : Type*}

end GenericBraid

namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
theorem mem_space_iff {P : FreeMonoid α → Prop} {p : A R α} :
    p∈space P ↔ ∀ w,p.coeff w≠0 → P w := by
  constructor
  · intro hp w hw
    by_contra h
    exact hw (coeff_support hp w h)
  · exact mem_space

theorem deriv_homogeneous {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈homogeneous wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : deriv f p∈homogeneous wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈homogeneous wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := homogeneous_mul (hf a) (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w))
      have h2 := homogeneous_mul (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a)) ih
      simp only [degree_mul,degree_of]
      apply (homogeneous wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  exact map_space (deriv f) _ (by intro w hw'; simpa only [hw'] using hw w) hp

theorem homogeneous_above {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : p∈above wt n := space_mono (by intros; omega) hp

theorem deriv_above {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈above wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : deriv f p∈above wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈above wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := above_mul (hf a) (homogeneous_above (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w)))
      have h2 := above_mul (homogeneous_above (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a))) ih
      simp only [degree_mul,degree_of]
      apply (above wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  apply map_space (deriv f) _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; omega) (hw w)

theorem deriv_sub (f g : α → A R α) (p : A R α) : deriv (fun a => f a-g a) p=deriv f p-deriv g p := by
  have hw (w : FreeMonoid α) : deriv (fun a => f a-g a) (word w)=deriv f (word w)-deriv g (word w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      simp only [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom,ih,mul_sub,sub_mul]
      abel
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add p q hp hq => simp only [map_add,hp,hq]; abel
  | smul c p hp => simp only [map_smul,hp,smul_sub]
end WordGrading

namespace CountTables

section
open AssociativeElimination

open WordGrading

end

open AssociativeElimination
def δ (i : Fin 2) : A K G →ₗ[K] A K G := deriv (fun a => if a=0 ∨ a.val=i.val+1 then C i else 0)

theorem bracket_ad_square (u v : A K G) : bracket u (bracket u v)=bracket (u*u) v := by
  simp only [bracket,sub_eq_add_neg,CharTwo.neg_eq,mul_add,add_mul,mul_assoc]
  calc
    _ = u*(u*v)+v*(u*u)+(u*(v*u)+u*(v*u)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
@[simp] theorem δ_X (i : Fin 2) : δ i X=C i := by simp [δ,X]
@[simp] theorem δ_Y_self (i : Fin 2) : δ i (Y i)=C i := by simp [δ,Y]
@[simp] theorem δ_Y_other (i j : Fin 2) (h : j≠i) : δ i (Y j)=0 := by
  have hv : j.val≠i.val := fun he => h (Fin.ext he)
  simp [δ,Y,hv]
theorem δ_mul (i : Fin 2) (p q : A K G) : δ i (p*q)=δ i p*q+p*δ i q := deriv_mul _ _ _
@[simp] theorem δ_bracket (i : Fin 2) (p q : A K G) : δ i (bracket p q)=bracket (δ i p) q+bracket p (δ i q) := deriv_bracket _ _ _
@[simp] theorem δ_H (i : Fin 2) : δ i (X*X)=bracket (X*X) (Y i) := by
  rw [δ_mul,δ_X,← bracket_ad_square]
  change C i*X+X*C i=bracket X (C i)
  simp [bracket,CharTwo.sub_eq_add,add_comm]
theorem bracket_X_C (i : Fin 2) : bracket X (C i)=bracket (X*X) (Y i) := bracket_ad_square _ _
@[simp] theorem δ_C_self (i : Fin 2) : δ i (C i)=bracket (X*X+C i) (Y i) := by
  change δ i (bracket X (Y i))=_
  rw [δ_bracket,δ_X,δ_Y_self,bracket_X_C,bracket_add_left]
  exact add_comm _ _
@[simp] theorem δ_C_other (i j : Fin 2) (h : j≠i) : δ i (C j)=bracket (C i) (Y j) := by
  rw [C,δ_bracket,δ_X,δ_Y_other i j h,bracket_zero_right,add_zero]

@[simp] theorem δ_square_H (i : Fin 2) : δ i (δ i (X*X))=
    bracket (X*X) (C i)+bracket (bracket (X*X) (Y i)) (Y i) := by
  rw [δ_H,δ_bracket,δ_H,δ_Y_self]
  exact add_comm _ _
@[simp] theorem δ_H_add_C (i : Fin 2) : δ i (X*X+C i)=bracket (C i) (Y i) := by
  rw [map_add,δ_H,δ_C_self,bracket_add_left,CharTwo.add_cancel_left]
@[simp] theorem δ_square_C_self (i : Fin 2) : δ i (δ i (C i))=
    bracket (X*X) (C i)+bracket (bracket (C i) (Y i)) (Y i) := by
  rw [δ_C_self,δ_bracket,δ_H_add_C,δ_Y_self,bracket_add_left,bracket_self,add_zero]
  exact add_comm _ _
@[simp] theorem δ_square_C_other (i j : Fin 2) (h : j≠i) : δ i (δ i (C j))=
    bracket (bracket (X*X+C i) (Y i)) (Y j) := by
  rw [δ_C_other i j h,δ_bracket,δ_C_self,δ_Y_other i j h,bracket_zero_right,add_zero]

attribute [local irreducible] X Y C H U V
end CountTables
namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]

inductive Step (κ : α → α → α → R) (r : α) : α → List α → List α → Prop
  | head (l a : α) (s : List α) (h : κ l a (s.headD r)≠0) : Step κ r l (a::s) s
  | tail (l a : α) (s t : List α) (h : Step κ r a s t) : Step κ r l (a::s) (a::t)

theorem raw_mem_space (κ : α → α → α → R) (l r : α) (s : List α)
    (P : FreeMonoid α → Prop) (h : ∀ t,Step κ r l s t → P (FreeMonoid.ofList t)) :
    raw κ l r s∈space P := by
  classical
  induction s generalizing l P with
  | nil => exact (space P).zero_mem
  | cons a s ih =>
    apply (space P).add_mem
    · by_cases hc : κ l a (s.headD r)=0
      · simp only [hc,zero_smul]; exact (space P).zero_mem
      · exact (space P).smul_mem _ (word_mem _ (h s (.head l a s hc)))
    · have ht := ih a (fun w => P (FreeMonoid.of a*w)) (by
        intro t ht
        simpa only [FreeMonoid.ofList_cons] using h (a::t) (.tail l a s t ht))
      exact map_space (Algebra.lmul R (A R α) (atom a)) (space P) (by
        intro w hw
        change atom a*word w∈space P
        rw [← word_of a,← word_mul]
        exact word_mem _ hw) ht

def count (wt : α → ℕ) (s : List α) : ℕ := (s.map wt).sum
@[simp] theorem count_nil (wt : α → ℕ) : count wt []=0 := rfl
@[simp] theorem count_cons (wt : α → ℕ) (a : α) (s : List α) : count wt (a::s)=wt a+count wt s := rfl

theorem Step.count_bound {κ : α → α → α → R} {r l : α} {s t : List α}
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a≤c)
    (h : Step κ r l s t) : count wt s≤c+count wt t := by
  induction h with
  | head l a s h => simpa only [count_cons] using Nat.add_le_add_right (hc l a _ h) (count wt s)
  | tail l a s t h ih => simp only [count_cons]; omega

theorem raw_count_bound (κ : α → α → α → R) (l r : α) (s : List α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a≤c) :
    raw κ l r s∈space (fun w => count wt s≤c+degree wt w) :=
  raw_mem_space κ l r s _ (by
    intro t ht
    simpa only [degree,FreeMonoid.toList_ofList,count] using ht.count_bound wt c hc)
end WeightedDeletion

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]
variable (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)

theorem algHom_homogeneous (hf : ∀ a,f (atom a)∈homogeneous wb (wa a))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) : f p∈homogeneous wb n := by
  have hw (w : FreeMonoid α) : f (word w)∈homogeneous wb (degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,map_one,degree_one]
      exact word_mem (1 : FreeMonoid β) (degree_one wb)
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      exact homogeneous_mul (hf a) ih
  apply map_space f.toLinearMap _ ?_ hp
  intro w h
  change f (word w)∈homogeneous wb n
  rw [← h]
  exact hw w

theorem algHom_above (hf : ∀ a,f (atom a)∈above wb (wa a))
    {n : ℕ} {p : A R α} (hp : p∈above wa n) : f p∈above wb n := by
  have hw (w : FreeMonoid α) : f (word w)∈above wb (degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,map_one,degree_one]
      exact word_mem (1 : FreeMonoid β) (by simp)
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      exact above_mul (hf a) ih
  apply map_space f.toLinearMap _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; change n≤degree wa w at hn; change degree wa w≤degree wb v at hv; omega) (hw w)

end WordGrading

namespace SourceEnveloping
open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
open scoped TensorProduct

def augment (α : Type*) : Env α →ₐ[K] K := UniversalEnvelopingAlgebra.lift K 0
instance envCharP (α : Type*) : CharP (Env α) 2 :=
  charP_of_injective_algebraMap (R:=K) (by
    intro a b h
    have hh := congrArg (augment α) h
    simpa only [AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply] using hh) 2

theorem chord_comm {α : Type*} (i j : α) : chord i j=chord j i := by
  rw [chord,GenericBraid.t_comm]; rfl

theorem base_fiber_left {α : Type*} [DecidableEq α] (i j : α) :
    ⁅chord (some i) (some j),chord none (some i)⁆=
    ⁅chord none (some i),chord none (some j)⁆ := by
  simp only [chord,← LieHom.map_lie,GenericBraid.t_base_fiber_left]

theorem base_fiber_right {α : Type*} [DecidableEq α] (i j : α) :
    ⁅chord (some i) (some j),chord none (some j)⁆=
    ⁅chord none (some j),chord none (some i)⁆ := by
  rw [chord_comm (some i) (some j)]
  exact base_fiber_left j i

theorem base_fiber_other {α : Type*} [DecidableEq α] (i j k : α) (hi : k≠i) (hj : k≠j) :
    ⁅chord (some i) (some j),chord none (some k)⁆=0 := by
  rw [chord,chord,← LieHom.map_lie]
  rw [GenericBraid.t_disjoint _ _ _ _ (by simp)
    (fun h => hi (Option.some.inj h).symm) (by simp)
    (fun h => hj (Option.some.inj h).symm),map_zero]

end SourceEnveloping
namespace AssociativeAction
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α U : Type*} [CommRing R] [Ring U] [Algebra R U]
theorem of_atoms (f : A R α →ₐ[R] U) (u : U) (d : α → A R α)
    (h : ∀ a,⁅u,f (atom a)⁆=f (d a)) (p : A R α) :
    ⁅u,f p⁆=f (deriv d p) := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp [Ring.lie_def,AssociativeElimination.deriv_one]
  | ha a => simpa only [deriv_atom] using h a
  | hadd p q hp hq => simp only [map_add,lie_add,hp,hq]
  | hs r p hp =>
    rw [map_smul,map_smul,map_smul]
    simpa only [Ring.lie_def,mul_smul_comm,smul_mul_assoc,← smul_sub] using congrArg (r • ·) hp
  | hm p q hp hq =>
    simp only [map_mul,AssociativeElimination.deriv_mul,map_add]
    rw [← hp,← hq]
    simp only [Ring.lie_def]
    noncomm_ring

end AssociativeAction

namespace CharTwoAction
attribute [local instance] LieRing.ofAssociativeRing
variable {U : Type*} [Ring U] [CharP U 2]
theorem symm (u v : U) : ⁅u,v⁆=⁅v,u⁆ := by
  simp only [Ring.lie_def,CharTwo.sub_eq_add,add_comm]
end CharTwoAction

namespace SourceModel

section
open AssociativeElimination AlphabetTransport SourceEnveloping
attribute [local instance] LieRing.ofAssociativeRing

def rawFiber : A K CountTables.G →ₐ[K] Env S3 :=
  GenericBraid.fiberIn.comp (map topLetters)
def baseX (i : Fin 2) : Env S3 := GenericBraid.baseIn (oldX i)
def baseU : Env S3 := GenericBraid.baseIn oldU

@[simp] theorem rawFiber_atom (a : CountTables.G) :
    rawFiber (atom a)=SourceEnveloping.chord none (some (topLetters a)) := by
  change GenericBraid.fiberIn (AlphabetTransport.map topLetters (atom a))=_
  rw [map_atom]
  exact fiber_chord _
@[simp] theorem rawFiber_X : rawFiber CountTables.X=SourceEnveloping.chord none (some root) := by
  simp [CountTables.X,topLetters,root]
@[simp] theorem rawFiber_Y (i : Fin 2) :
    rawFiber (CountTables.Y i)=SourceEnveloping.chord none (some (if i=0 then one else two)) := by
  fin_cases i <;> simp [CountTables.Y,topLetters,one,two]
@[simp] theorem rawFiber_C (i : Fin 2) :
    rawFiber (CountTables.C i)=⁅rawFiber CountTables.X,rawFiber (CountTables.Y i)⁆ := by
  simp [CountTables.C,CountTables.bracket,Ring.lie_def]

@[simp] theorem baseX_zero : baseX 0=SourceEnveloping.chord (some root) (some one) := by simp [baseX,oldX]
@[simp] theorem baseX_one : baseX 1=SourceEnveloping.chord (some root) (some two) := by simp [baseX,oldX]
@[simp] theorem baseU_eq : baseU=SourceEnveloping.chord (some one) (some two) := by simp [baseU,oldU]

theorem raw_delta_atoms (i : Fin 2) (a : CountTables.G) :
    ⁅baseX i,rawFiber (atom a)⁆=rawFiber (CountTables.δ i (atom a)) := by
  fin_cases i <;> fin_cases a <;>
    simp [CountTables.δ,topLetters]
  · exact base_fiber_left root one
  · exact (base_fiber_right root one).trans (CharTwoAction.symm _ _)
  · exact base_fiber_other root one two (by decide) (by decide)
  · exact base_fiber_left root two
  · exact base_fiber_other root two one (by decide) (by decide)
  · exact (base_fiber_right root two).trans (CharTwoAction.symm _ _)

theorem raw_delta (i : Fin 2) (p : A K CountTables.G) :
    ⁅baseX i,rawFiber p⁆=rawFiber (CountTables.δ i p) := by
  exact AssociativeAction.of_atoms rawFiber (baseX i) _
    (fun a => by simpa only [CountTables.δ,deriv_atom] using raw_delta_atoms i a) p

theorem topFiber_eq (p : A K CountTables.F) : topFiber p=rawFiber (CountTables.realize p) := rfl

end

section
open AssociativeElimination AlphabetTransport SourceEnveloping
attribute [local instance] LieRing.ofAssociativeRing

end

open AssociativeElimination PolynomialOrdering
open scoped TensorProduct

end SourceModel

namespace WeightedDeletion

section
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]
theorem Step.sublist {κ : α → α → α → R} {r l : α} {s t : List α}
    (h : Step κ r l s t) : t.Sublist s := by
  induction h with
  | head l a s h => exact List.Sublist.cons _ (List.Sublist.refl _)
  | tail l a s t h ih => exact List.Sublist.cons_cons _ ih

theorem op_above (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a≤c)
    {n : ℕ} {p : A R α} (hp : p∈above wt n) : op κ l r p∈above wt (n-c) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have hr := raw_count_bound κ l r w.toList wt c hc
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply space_mono (P:=fun v => count wt w.toList≤c+degree wt v) ?_ hr
  intro v hv
  change n≤degree wt w at hw
  simp only [count,degree] at hv hw ⊢
  omega

variable {β : Type*}

theorem action_word_above (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (w : FreeMonoid β) {n : ℕ} {p : A R α} (hp : p∈above wt n) :
    action κ l r (word w) p∈above wt (n-degree cost w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa using hp
  | of_mul b w ih =>
    rw [word_mul,word_of,map_mul,action_atom]
    change op (κ b) l r (action κ l r (word w) p)∈_
    have h := op_above (κ b) l r wt (cost b) (hc b) ih
    simpa only [degree_mul,degree_of,Nat.sub_sub,Nat.add_comm] using h

theorem test_word_zero (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (w : FreeMonoid β) (s : FreeMonoid α) (hs : degree cost w<degree wt s) :
    (action κ l r (word w) (word s)).coeff 1=0 := by
  have hp : word (R:=R) s∈above wt (degree wt s) := word_mem s (le_refl _)
  have h := action_word_above κ l r wt cost hc w hp
  apply coeff_support h
  rw [degree_one]
  omega
end

open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]
theorem linear_ext {M : Type*} [AddCommGroup M] [Module R M]
    {f g : A R α →ₗ[R] M} (h : ∀ w : FreeMonoid α,f (word w)=g (word w)) : f=g := by
  apply LinearMap.ext
  intro p
  induction p using MonoidAlgebra.induction_on with
  | of w => exact h w
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem raw_sub (κ μ : α → α → α → R) (l r : α) (s : List α) :
    raw (fun l a b => κ l a b-μ l a b) l r s=raw κ l r s-raw μ l r s := by
  induction s generalizing l with
  | nil => simp [raw]
  | cons a s ih => simp only [raw,ih,sub_smul,mul_sub]; abel

theorem op_sub (κ μ : α → α → α → R) (l r : α) :
    op (fun l a b => κ l a b-μ l a b) l r=op κ l r-op μ l r := by
  apply linear_ext
  intro w
  have h := raw_sub κ μ l r w.toList
  simpa only [← op_word,FreeMonoid.ofList_toList,LinearMap.sub_apply] using h

def cut (κ : β → α → α → α → R) (wt : α → ℕ) (cost : β → ℕ)
    (b : β) (l a r : α) : R := if wt a=cost b then κ b l a r else 0

theorem cut_bound (κ : β → α → α → α → R) (wt : α → ℕ) (cost : β → ℕ)
    (b : β) (l a r : α) (h : cut κ wt cost b l a r≠0) : wt a=cost b := by
  by_contra he
  exact h (if_neg he)

theorem Step.count_eq {κ : α → α → α → R} {r l : α} {s t : List α}
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a=c)
    (h : Step κ r l s t) : count wt s=c+count wt t := by
  induction h with
  | head l a s h => rw [count_cons,hc l a _ h]
  | tail l a s t h ih => simp only [count_cons]; omega

end WeightedDeletion

namespace RowTwo
open AssociativeElimination WordGrading WeightedDeletion
instance : Fintype Letter := ⟨{.o,.e,.p,.w}, by intro x; cases x <;> simp⟩
instance : Fintype Slot := ⟨{.A,.C,.B}, by intro x; cases x <;> simp⟩
open Letter Slot

def Good (s : List Letter) : Prop := s.Pairwise (fun a b => a=.e → b=.e)

theorem head_character : ∀ k l a b,κ k l a b≠0 →
    (a=.e → b=.w) ∧ (l=.e → b=.e ∨ b=.w → a=.e) := by decide

theorem head_good (k : Slot) (l a : Letter) (s : List Letter)
    (hw : .w∉s) (hk : κ k l a (s.headD .w)≠0) (hg : Good (l::s)) :
    Good (l::a::s) := by
  have hc := head_character k l a (s.headD .w) hk
  by_cases ha : a=.e
  · have hs : s=[] := by
      cases s with
      | nil => rfl
      | cons b s =>
        have hb : b=.w := hc.1 ha
        simp only [List.mem_cons,not_or] at hw
        exact False.elim (hw.1 hb.symm)
    subst s
    simp [Good,ha]
  · have hl : l≠.e := by
      intro hl
      apply ha
      apply hc.2 hl
      cases s with
      | nil => exact Or.inr rfl
      | cons b s =>
        left
        exact (List.pairwise_cons.mp hg).1 b (by simp) hl
    rcases List.pairwise_cons.mp hg with ⟨_,hs⟩
    apply List.pairwise_cons.mpr
    refine ⟨?_,List.pairwise_cons.mpr ⟨?_,hs⟩⟩
    · intro b hb he
      exact False.elim (hl he)
    · intro b hb he
      exact False.elim (ha he)

theorem step_good (k : Slot) {l : Letter} {s t : List Letter}
    (h : Step (κ k) .w l s t) (hw : .w∉s) (hg : Good (l::t)) : Good (l::s) := by
  induction h with
  | head l a s hk =>
    exact head_good k l a s (fun h => hw (List.mem_cons_of_mem _ h)) hk hg
  | tail l a s t hs ih =>
    have h1 : Good (a::t) := List.Pairwise.of_cons hg
    have h2 : Good (a::s) := ih (fun h => hw (List.mem_cons_of_mem _ h)) h1
    apply List.pairwise_cons.mpr
    refine ⟨?_,h2⟩
    intro b hb hl
    have ha : a=.e := (List.pairwise_cons.mp hg).1 a (by simp) hl
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact (List.pairwise_cons.mp h2).1 b hb ha

theorem step_bad (k : Slot) {l : Letter} {s t : List Letter}
    (h : Step (κ k) .w l s t) (hw : .w∉s) (hg : ¬Good (l::s)) : ¬Good (l::t) :=
  fun ht => hg (step_good k h hw ht)

def badSpace : Submodule K (A K Letter) :=
  space (fun w => .w∉w.toList ∧ ¬Good (.o::w.toList))

theorem op_bad (k : Slot) {p : A K Letter} (hp : p∈badSpace) :
    op (κ k) .o .w p∈badSpace := by
  apply map_space (op (κ k) .o .w) _ ?_ hp
  intro w hw
  have he : op (κ k) .o .w (word w)=raw (κ k) .o .w w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word (κ k) .o .w w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  simp only [FreeMonoid.toList_ofList]
  exact ⟨fun h => hw.1 (ht.sublist.subset h),step_bad k ht hw.1 hw.2⟩

theorem word_action_bad (v : FreeMonoid Slot) {p : A K Letter} (hp : p∈badSpace) :
    action κ .o .w (word v) p∈badSpace := by
  induction v using FreeMonoid.inductionOn' with
  | one => simpa using hp
  | of_mul k v ih =>
    rw [word_mul,word_of,map_mul,action_atom]
    exact op_bad k ih

theorem action_bad (v : A K Slot) {p : A K Letter} (hp : p∈badSpace) :
    action κ .o .w v p∈badSpace := by
  induction v using MonoidAlgebra.induction_on with
  | of w => exact word_action_bad w hp
  | add v w hv hw =>
    simpa only [map_add,LinearMap.add_apply] using badSpace.add_mem hv hw
  | smul c v hv =>
    simpa only [map_smul,LinearMap.smul_apply] using badSpace.smul_mem c hv

theorem test_zero (v : A K Slot) (s : List Letter) (hw : .w∉s) (hb : ¬Good (.o::s)) :
    (action κ .o .w v (word (FreeMonoid.ofList s))).coeff 1=0 := by
  have hp : word (R:=K) (FreeMonoid.ofList s)∈badSpace :=
    word_mem _ (by simpa only [FreeMonoid.toList_ofList] using And.intro hw hb)
  have h := action_bad v hp
  apply coeff_support h
  intro he
  exact he.2 (by simp [Good])
end RowTwo

namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]

theorem Step.count_lower {κ : α → α → α → R} {r l : α} {s t : List α}
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → c≤wt a)
    (h : Step κ r l s t) : c+count wt t≤count wt s := by
  induction h with
  | head l a s h => simpa only [count_cons] using Nat.add_le_add_right (hc l a _ h) (count wt s)
  | tail l a s t h ih => simp only [count_cons]; omega

theorem op_count_lower (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → c≤wt a)
    {n d : ℕ} {p : A R α} (hp : p∈space (fun w => d+degree wt w≤n)) :
    op κ l r p∈space (fun w => d+c+degree wt w≤n) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hl := ht.count_lower wt c hc
  simp only [FreeMonoid.toList_ofList,degree,count] at hl hw ⊢
  omega

theorem action_count_lower (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (w : FreeMonoid β) {n : ℕ} {p : A R α} (hp : p∈below wt n) :
    action κ l r (word w) p∈space (fun v => degree cost w+degree wt v≤n) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [word_one,map_one,Module.End.one_apply,degree_one,Nat.zero_add,below] using hp
  | of_mul b w ih =>
    rw [word_mul,word_of,map_mul,action_atom,Module.End.mul_apply]
    have h := op_count_lower (κ b) l r wt (cost b) (hc b) ih
    simpa only [degree_mul,degree_of,Nat.add_comm (degree cost w) (cost b)] using h

theorem test_excess_cost (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (w : FreeMonoid β) (s : FreeMonoid α) (hs : degree wt s<degree cost w) :
    (action κ l r (word w) (word s)).coeff 1=0 := by
  have hp : word (R:=R) s∈below wt (degree wt s) := word_mem s (le_refl _)
  have h := action_count_lower κ l r wt cost hc w hp
  apply coeff_support h
  simp only [degree_one,Nat.add_zero]
  omega
end WeightedDeletion

namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]

theorem op_count_exact (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a=c)
    {n d : ℕ} {p : A R α} (hp : p∈space (fun w => d+degree wt w=n)) :
    op κ l r p∈space (fun w => d+c+degree wt w=n) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hl := ht.count_eq wt c hc
  simp only [FreeMonoid.toList_ofList,degree,count] at hl hw ⊢
  omega

theorem op_count_lt (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → c≤wt a)
    {n d : ℕ} {p : A R α} (hp : p∈space (fun w => d+degree wt w<n)) :
    op κ l r p∈space (fun w => d+c+degree wt w<n) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hl := ht.count_lower wt c hc
  simp only [FreeMonoid.toList_ofList,degree,count] at hl hw ⊢
  omega

theorem op_count_lt_of_exact (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → c<wt a)
    {n d : ℕ} {p : A R α} (hp : p∈space (fun w => d+degree wt w=n)) :
    op κ l r p∈space (fun w => d+c+degree wt w<n) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hl := ht.count_lower wt (c+1) hc
  simp only [FreeMonoid.toList_ofList,degree,count] at hl hw ⊢
  omega

theorem diff_lower_bound (κ : β → α → α → α → R) (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a r,κ b l a r≠0 → cost b≤wt a)
    (b : β) (l a r : α) (h : κ b l a r-cut κ wt cost b l a r≠0) : cost b<wt a := by
  by_cases he : wt a=cost b
  · simp only [cut,if_pos he,sub_self,ne_eq,not_true_eq_false] at h
  · rw [cut,if_neg he,sub_zero] at h
    exact lt_of_le_of_ne (hc b l a r h) (Ne.symm he)

theorem exact_allocation_lower (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (w : FreeMonoid β) {n : ℕ} {p : A R α} (hp : p∈homogeneous wt n) :
    action (cut κ wt cost) l r (word w) p∈space (fun v => degree cost w+degree wt v=n) ∧
    action κ l r (word w) p-action (cut κ wt cost) l r (word w) p∈
      space (fun v => degree cost w+degree wt v<n) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    simp only [word_one,map_one,Module.End.one_apply,degree_one,Nat.zero_add,sub_self]
    exact ⟨hp,(space _).zero_mem⟩
  | of_mul b w ih =>
    rw [word_mul,word_of,map_mul,map_mul,action_atom,action_atom]
    change op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)∈_ ∧
      op (κ b) l r (action κ l r (word w) p)-op (cut κ wt cost b) l r
        (action (cut κ wt cost) l r (word w) p)∈_
    constructor
    · have h := op_count_exact (cut κ wt cost b) l r wt (cost b)
        (cut_bound κ wt cost b) ih.1
      simpa only [degree_mul,degree_of,Nat.add_comm (degree cost w) (cost b)] using h
    · have h1 := op_count_lt (κ b) l r wt (cost b) (hc b) ih.2
      have h2 := op_count_lt_of_exact
        (fun l a r => κ b l a r-cut κ wt cost b l a r) l r wt (cost b)
        (diff_lower_bound κ wt cost hc b) ih.1
      rw [op_sub] at h2
      simp only [LinearMap.sub_apply] at h2
      have hh : op (κ b) l r (action κ l r (word w) p)-op (cut κ wt cost b) l r
          (action (cut κ wt cost) l r (word w) p)=
          op (κ b) l r (action κ l r (word w) p-action (cut κ wt cost) l r (word w) p)+
            (op (κ b) l r (action (cut κ wt cost) l r (word w) p)-
             op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)) := by
        rw [map_sub]; abel
      rw [hh]
      apply (space _).add_mem
      · simpa only [degree_mul,degree_of,Nat.add_comm (degree cost w) (cost b)] using h1
      · simpa only [degree_mul,degree_of,Nat.add_comm (degree cost w) (cost b)] using h2

theorem exact_allocation_lower_test (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (w : FreeMonoid β) {p : A R α} (hp : p∈homogeneous wt (degree cost w)) :
    (action κ l r (word w) p).coeff 1=(action (cut κ wt cost) l r (word w) p).coeff 1 := by
  have h := (exact_allocation_lower κ l r wt cost hc w hp).2
  have hz := coeff_support h 1 (by simp [degree_one])
  simpa only [MonoidAlgebra.coeff_sub,Finsupp.sub_apply,sub_eq_zero] using hz

theorem scalar_cut_of_leading (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (s : FreeMonoid α) {p : A R β} (hp : p∈above cost (degree wt s)) :
    scalar κ l r s p=scalar (cut κ wt cost) l r s p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    change degree wt s≤degree cost w at hw
    change (action κ l r (word w) (word s)).coeff 1=
      (action (cut κ wt cost) l r (word w) (word s)).coeff 1
    by_cases he : degree wt s=degree cost w
    · exact exact_allocation_lower_test κ l r wt cost hc w (word_mem s he)
    · have hlt : degree wt s<degree cost w := lt_of_le_of_ne hw he
      rw [test_excess_cost κ l r wt cost hc w s hlt]
      symm
      apply test_excess_cost (cut κ wt cost) l r wt cost ?_ w s hlt
      intro b l a t hb
      exact (cut_bound κ wt cost b l a t hb).ge
  | zero => simp only [map_zero]
  | add p q _ _ hp hq => simp only [map_add,hp,hq]
  | smul c p _ hp => simp only [map_smul,hp]

theorem scalar_zero_of_cost (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a t,κ b l a t≠0 → cost b≤wt a)
    (s : FreeMonoid α) {h : ℕ} (hs : degree wt s<h)
    {p : A R β} (hp : p∈above cost h) : scalar κ l r s p=0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    exact test_excess_cost κ l r wt cost hc w s (lt_of_lt_of_le hs hw)
  | zero => simp only [map_zero]
  | add p q _ _ hp hq => simp only [map_add,hp,hq,add_zero]
  | smul c p _ hp => simp only [map_smul,hp,smul_zero]
end WeightedDeletion

namespace EmbeddedTerminal
open AssociativeElimination WordGrading WeightedDeletion
variable {R α β : Type*} [CommRing R] [DecidableEq α] [DecidableEq β]

def κ (enc : α → β) (r : β) (k : α) (_ a b : β) : R :=
  if a=enc k ∧ b=r then 1 else 0

theorem raw_snoc (enc : α → β) (hi : Function.Injective enc) (r : β)
    (hr : ∀ a,enc a≠r) (k a : α) (l : β) (s : List α) :
    raw (κ (R:=R) enc r k) l r ((s++[a]).map enc)=
      if k=a then word (FreeMonoid.ofList (s.map enc)) else 0 := by
  classical
  induction s generalizing l with
  | nil => simp [raw,κ,hi.eq_iff,eq_comm]
  | cons b s ih =>
    have hh : (((s++[a]).map enc).headD r)≠r := by
      cases s with
      | nil => simpa using hr a
      | cons c s => simpa using hr c
    simp only [List.cons_append,List.map_cons,raw]
    rw [ih]
    simp only [κ,hh,and_false,↓reduceIte,zero_smul,zero_add]
    split_ifs with h
    · rw [← word_of (enc b),← word_mul,← FreeMonoid.ofList_cons]
    · simp

theorem scalar_word (enc : α → β) (hi : Function.Injective enc) (l r : β)
    (hr : ∀ a,enc a≠r) (w s : List α) :
    scalar (κ (R:=R) enc r) l r (FreeMonoid.ofList (s.map enc)) (word (FreeMonoid.ofList w)) =
      if w=s then 1 else 0 := by
  classical
  change (action (κ (R:=R) enc r) l r (word (FreeMonoid.ofList w))
    (word (FreeMonoid.ofList (s.map enc)))).coeff 1= _
  induction w using List.reverseRecOn generalizing s with
  | nil =>
    simp only [FreeMonoid.ofList_nil,word_one,map_one,Module.End.one_apply]
    simp only [word,MonoidAlgebra.coeff_single,Finsupp.single_apply]
    have he : FreeMonoid.ofList (s.map enc)=(1 : FreeMonoid β) ↔ s=[] := by
      constructor
      · intro h
        have hh := congrArg FreeMonoid.toList h
        simpa using hh
      · intro h; subst s; rfl
    simp only [he,eq_comm (a:=[]) (b:=s)]
  | append_singleton w k ih =>
    cases s using List.reverseRecOn with
    | nil =>
      rw [FreeMonoid.ofList_append,word_mul,map_mul,Module.End.mul_apply]
      simp only [FreeMonoid.ofList_singleton,word_of,action_atom]
      change ((action (κ (R:=R) enc r) l r (word (FreeMonoid.ofList w)))
        (op (κ enc r k) l r (word (FreeMonoid.ofList [])))).coeff 1= _
      rw [op_word]
      simp [raw]
    | append_singleton s a =>
      rw [FreeMonoid.ofList_append,word_mul,map_mul,Module.End.mul_apply]
      simp only [FreeMonoid.ofList_singleton,word_of,action_atom,op_word]
      rw [raw_snoc enc hi r hr]
      by_cases h : k=a
      · subst a
        simpa only [↓reduceIte,List.append_cancel_right_eq] using ih s
      · rw [if_neg h,map_zero]
        have he : w++[k]≠s++[a] := by
          intro he
          have := congrArg List.getLast? he
          simp only [List.getLast?_append,List.getLast?_singleton] at this
          exact h (Option.some.inj this)
        simp only [MonoidAlgebra.coeff_zero,Finsupp.zero_apply,if_neg he]

theorem test (enc : α → β) (hi : Function.Injective enc) (l r : β)
    (hr : ∀ a,enc a≠r) (p : A R α) (s : List α) :
    scalar (κ (R:=R) enc r) l r (FreeMonoid.ofList (s.map enc)) p=p.coeff (FreeMonoid.ofList s) := by
  classical
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change scalar (κ (R:=R) enc r) l r (FreeMonoid.ofList (s.map enc)) (word w)=
      (word (R:=R) w).coeff (FreeMonoid.ofList s)
    rw [show word (R:=R) w=word (FreeMonoid.ofList w.toList) from rfl,scalar_word enc hi l r hr]
    simp only [word,MonoidAlgebra.coeff_single,Finsupp.single_apply,FreeMonoid.ofList.injective.eq_iff]
  | add p q hp hq => simp only [map_add,MonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]
  | smul c p hp => simp only [map_smul,MonoidAlgebra.coeff_smul,Finsupp.smul_apply,hp]
end EmbeddedTerminal

namespace WordReversal
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing

def rev : A R α →ₗ[R] A R α :=
  (Finsupp.linearCombination R (fun w : FreeMonoid α => word w.reverse)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem rev_word (w : FreeMonoid α) : rev (word (R:=R) w)=word w.reverse := by
  change Finsupp.linearCombination R (fun monoidWord : FreeMonoid α => word monoidWord.reverse) (Finsupp.single w 1) = _; simp

@[simp] theorem rev_atom (a : α) : rev (atom a : A R α)=atom a := by
  simpa only [word_of,FreeMonoid.reverse_of] using rev_word (R:=R) (FreeMonoid.of a)

@[simp] theorem rev_one : rev (1 : A R α)=1 := rev_word 1

theorem rev_mul (p q : A R α) : rev (p*q)=rev q*rev p := by
  induction p using MonoidAlgebra.induction_on with
  | of u =>
    change rev (word u*q)=rev q*rev (word u)
    induction q using MonoidAlgebra.induction_on with
    | of v =>
      change rev (word u*word v)=rev (word v)*rev (word u)
      rw [← word_mul,rev_word,FreeMonoid.reverse_mul,word_mul,rev_word,rev_word]
    | add p q hp hq => simp only [mul_add,map_add,hp,hq,add_mul]
    | smul c p hp => simp only [mul_smul_comm,map_smul,hp,smul_mul_assoc]
  | add p r hp hr => simp only [add_mul,map_add,hp,hr,mul_add]
  | smul c p hp => simp only [smul_mul_assoc,map_smul,hp,mul_smul_comm]

theorem rev_coeff (p : A R α) (w : FreeMonoid α) :
    (rev p).coeff w=p.coeff w.reverse := by
  classical
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change (rev (word v)).coeff w=(word (R:=R) v).coeff w.reverse
    rw [rev_word]
    simp only [word,MonoidAlgebra.coeff_single,Finsupp.single_apply]
    have he : v.reverse=w ↔ v=w.reverse := by
      constructor
      · intro h
        rw [← h, FreeMonoid.reverse_reverse]
      · intro h
        rw [h, FreeMonoid.reverse_reverse]
    rw [he]
  | add p q hp hq => simp only [map_add,MonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]
  | smul c p hp => simp only [map_smul,MonoidAlgebra.coeff_smul,Finsupp.smul_apply,hp]

theorem rev_lie_charTwo [CharP R 2] (q : FreeLieAlgebra R α) : rev (embed q)=embed q := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp only [map_add,hp,hq]
  | hs r p hp => simp only [map_smul,hp]
  | hl p q hp hq =>
    rw [LieHom.map_lie]
    change rev (embed p*embed q-embed q*embed p)=embed p*embed q-embed q*embed p
    rw [map_sub, rev_mul, rev_mul, hp, hq]
    have hn (z : A R α) : -z=z := by
      ext w
      change -z.coeff w=z.coeff w
      exact CharTwo.neg_eq _
    rw [sub_eq_add_neg, sub_eq_add_neg, hn, hn]
    exact add_comm _ _

theorem coeff_reverse_charTwo [CharP R 2] (q : FreeLieAlgebra R α) (w : FreeMonoid α) :
    (embed q).coeff w.reverse=(embed q).coeff w := by
  rw [← rev_coeff,rev_lie_charTwo]

end WordReversal

namespace RowKernel
open AssociativeElimination WordGrading WeightedDeletion RowTwo
open RowTwo.Letter RowTwo.Slot

theorem enc_injective : Function.Injective enc := by intro a b; cases a <;> cases b <;> decide

theorem enc_not_w (a : Slot) : enc a≠.w := by cases a <;> decide

def aCount (a : Slot) : ℕ := if a=.A then 1 else 0
def cCount (a : Slot) : ℕ := if a=.C then 1 else 0
def eCount (a : Letter) : ℕ := if a=.e then 1 else 0
def pCount (a : Letter) : ℕ := if a=.p then 1 else 0

theorem count_enc_e (s : List Slot) :
    degree eCount (FreeMonoid.ofList (s.map enc))=degree aCount (FreeMonoid.ofList s) := by
  simp only [degree,FreeMonoid.toList_ofList,List.map_map,eCount,enc_eq_e,Function.comp_def]
  rfl

theorem count_enc_p (s : List Slot) :
    degree pCount (FreeMonoid.ofList (s.map enc))=degree cCount (FreeMonoid.ofList s) := by
  simp only [degree,FreeMonoid.toList_ofList,List.map_map,pCount,enc_eq_p,Function.comp_def]
  rfl

theorem a_cost (i : Row) : ∀ k l a b,κ i k l a b≠0 → aCount k≤eCount a := by
  cases i <;> decide

theorem one_cost : ∀ k l a b,κ .one k l a b≠0 → pCount a≤0 := by decide

theorem three_cost : ∀ k l a b,κ .three k l a b≠0 → aCount k≤0 := by decide

theorem cut_two : cut (κ .two) eCount aCount=RowTwo.κ := by
  funext k l a b
  revert k l a b
  decide

theorem cut_four : cut (κ .four) eCount aCount=EmbeddedTerminal.κ enc .w := by
  funext k l a b
  revert k l a b
  decide

def good (s : List Slot) : Prop := s.Pairwise (fun a b => a=.A → b=.A)

theorem good_enc (s : List Slot) : RowTwo.Good (.o::s.map enc) ↔ good s := by
  simp [RowTwo.Good,good,List.pairwise_map]

theorem enc_no_w (s : List Slot) : .w∉s.map enc := by
  intro h
  obtain ⟨a,_,h⟩ := List.mem_map.mp h
  exact enc_not_w a h

theorem test_cut (i : Row) (s : List Slot) {p : A K Slot}
    (hp : p∈above aCount (degree aCount (FreeMonoid.ofList s))) :
    test i s p=scalar (cut (κ i) eCount aCount) .o .w (FreeMonoid.ofList (s.map enc)) p := by
  exact scalar_cut_of_leading (κ i) .o .w eCount aCount (a_cost i) _
    (by simpa only [count_enc_e] using hp)

theorem degree_zero {α : Type*} (w : FreeMonoid α) : degree (fun _ => 0) w=0 := by
  simp [degree,List.map_const']

theorem test_one (s : List Slot) (hs : 0<degree cCount (FreeMonoid.ofList s))
    (p : A K Slot) : test .one s p=0 := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change (action (κ .one) .o .w (word w)
      (word (FreeMonoid.ofList (s.map enc)))).coeff 1=0
    apply test_word_zero (κ .one) .o .w pCount (fun _ => 0) one_cost
    simpa only [degree_zero,count_enc_p] using hs
  | add p q hp hq => simp only [map_add,hp,hq,add_zero]
  | smul c p hp => simp only [map_smul,hp,smul_zero]

theorem test_two (s : List Slot) (hs : ¬good s) {p : A K Slot}
    (hp : p∈above aCount (degree aCount (FreeMonoid.ofList s))) : test .two s p=0 := by
  rw [test_cut .two s hp,cut_two]
  exact RowTwo.test_zero p (s.map enc) (enc_no_w s) (fun h => hs ((good_enc s).mp h))

theorem test_three (s : List Slot) (hs : 0<degree aCount (FreeMonoid.ofList s)) {p : A K Slot}
    (hp : p∈above aCount (degree aCount (FreeMonoid.ofList s))) : test .three s p=0 := by
  apply scalar_zero_of_cost (κ .three) .o .w (fun _ => 0) aCount three_cost _ ?_ hp
  simpa only [degree_zero] using hs

theorem test_four (s : List Slot) {p : A K Slot}
    (hp : p∈above aCount (degree aCount (FreeMonoid.ofList s))) :
    test .four s p=p.coeff (FreeMonoid.ofList s) := by
  rw [test_cut .four s hp,cut_four]
  exact EmbeddedTerminal.test enc enc_injective .o .w enc_not_w p s

theorem coefficient_bad {p : A K Slot} (s : List Slot) (heq : Equation p s)
    (ha : 0<degree aCount (FreeMonoid.ofList s))
    (hc : 0<degree cCount (FreeMonoid.ofList s))
    (hp : p∈above aCount (degree aCount (FreeMonoid.ofList s)))
    (hs : ¬good s) : p.coeff (FreeMonoid.ofList s)=0 := by
  unfold Equation at heq
  rw [test_one s hc p,test_two s hs hp,test_three s ha hp,test_four s hp,
    zero_add,zero_add,zero_add] at heq
  exact heq

theorem degree_reverse {α : Type*} (wt : α → ℕ) (s : List α) :
    degree wt (FreeMonoid.ofList s.reverse)=degree wt (FreeMonoid.ofList s) := by
  simp only [degree,FreeMonoid.toList_ofList,List.map_reverse,List.sum_reverse]

theorem aCount_eq_count (s : List Slot) : degree aCount (FreeMonoid.ofList s)=s.count .A := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [degree,FreeMonoid.toList_ofList,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih,List.count_cons]
    simp [aCount,Nat.add_comm]

theorem cCount_eq_count (s : List Slot) : degree cCount (FreeMonoid.ofList s)=s.count .C := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [degree,FreeMonoid.toList_ofList,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih,List.count_cons]
    simp [cCount,Nat.add_comm]

theorem all_A_of_good_both (s : List Slot) (hg : good s) (hr : good s.reverse)
    (ha : .A∈s) : ∀ b∈s,b=.A := by
  cases s with
  | nil => simp at ha
  | cons a s =>
    obtain ⟨hfirst,_⟩ := List.pairwise_cons.mp hg
    have hback := List.pairwise_cons.mp (List.pairwise_reverse.mp hr)
    have he : a=.A := by
      rcases List.mem_cons.mp ha with h | h
      · exact h.symm
      · exact hback.1 .A h rfl
    intro b hb
    rcases List.mem_cons.mp hb with hb | hb
    · exact hb.trans he
    · exact hfirst b hb he

theorem not_good_reverse (s : List Slot) (hg : good s)
    (ha : 0<degree aCount (FreeMonoid.ofList s))
    (hc : 0<degree cCount (FreeMonoid.ofList s)) : ¬good s.reverse := by
  rw [aCount_eq_count,List.count_pos_iff] at ha
  rw [cCount_eq_count,List.count_pos_iff] at hc
  intro hr
  have h := all_A_of_good_both s hg hr ha .C hc
  cases h

theorem coefficient_minimal (q : FreeLieAlgebra K Slot) (s : List Slot)
    (heq : Equation (embed q) s) (heqr : Equation (embed q) s.reverse)
    (ha : 0<degree aCount (FreeMonoid.ofList s))
    (hc : 0<degree cCount (FreeMonoid.ofList s))
    (hp : embed q∈above aCount (degree aCount (FreeMonoid.ofList s))) :
    (embed q).coeff (FreeMonoid.ofList s)=0 := by
  by_cases hg : good s
  · have ha' : 0<degree aCount (FreeMonoid.ofList s.reverse) := by simpa only [degree_reverse] using ha
    have hc' : 0<degree cCount (FreeMonoid.ofList s.reverse) := by simpa only [degree_reverse] using hc
    have hp' : embed q∈above aCount (degree aCount (FreeMonoid.ofList s.reverse)) := by
      simpa only [degree_reverse] using hp
    have hz := coefficient_bad s.reverse heqr ha' hc' hp' (not_good_reverse s hg ha hc)
    change (embed q).coeff (FreeMonoid.ofList s).reverse=0 at hz
    rwa [WordReversal.coeff_reverse_charTwo] at hz
  · exact coefficient_bad s heq ha hc hp hg

def acCount (k : Slot) : ℕ := aCount k+cCount k

theorem degree_ac (w : FreeMonoid Slot) : degree acCount w=degree aCount w+degree cCount w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul k w ih => simp only [degree_mul,degree_of,acCount,ih]; omega

theorem kernel_support (q : FreeLieAlgebra K Slot) (m r : ℕ)
    (hm : embed q∈homogeneous acCount m) (hr : embed q∈homogeneous bCount r)
    (hzero : ∀ w,degree aCount w=0 → (embed q).coeff w=0)
    (heq : ∀ s,degree acCount (FreeMonoid.ofList s)=m →
      degree bCount (FreeMonoid.ofList s)=r → Equation (embed q) s) :
    embed q∈space (fun w => degree cCount w=0) := by
  classical
  apply mem_space
  intro w hw
  by_contra hc
  have hwm : degree acCount w=m := (mem_space_iff.mp hm) w hw
  have ex : ∃ n,∃ v,(embed q).coeff v≠0 ∧ degree aCount v=n := ⟨_,w,hw,rfl⟩
  obtain ⟨v,hv,hva⟩ := Nat.find_spec ex
  have hmin (u : FreeMonoid Slot) (hu : (embed q).coeff u≠0) : Nat.find ex≤degree aCount u :=
    Nat.find_min' ex ⟨u,hu,rfl⟩
  have hvpos : 0<degree aCount v := by
    have hn : degree aCount v≠0 := fun he => hv (hzero v he)
    omega
  have hvm : degree acCount v=m := (mem_space_iff.mp hm) v hv
  have hvr : degree bCount v=r := (mem_space_iff.mp hr) v hv
  have hvc : 0<degree cCount v := by
    have hle := hmin w hw
    rw [degree_ac] at hwm hvm
    omega
  have hp : embed q∈above aCount (degree aCount v) := by
    apply mem_space
    intro u hu
    rw [hva]
    exact hmin u hu
  have hz := coefficient_minimal q v.toList
    (heq v.toList (by simpa only [FreeMonoid.ofList_toList] using hvm)
      (by simpa only [FreeMonoid.ofList_toList] using hvr))
    (heq v.toList.reverse (by simpa only [degree_reverse,FreeMonoid.ofList_toList] using hvm)
      (by simpa only [degree_reverse,FreeMonoid.ofList_toList] using hvr))
    (by simpa only [FreeMonoid.ofList_toList] using hvpos)
    (by simpa only [FreeMonoid.ofList_toList] using hvc)
    (by simpa only [FreeMonoid.ofList_toList] using hp)
  exact hv (by simpa only [FreeMonoid.ofList_toList] using hz)
end RowKernel

namespace LetterRetraction
open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
variable (P : α → Prop) [DecidablePred P]

def assoc : A R α →ₐ[R] A R α := lift (fun a => if P a then atom a else 0)

@[simp] theorem assoc_atom (a : α) : assoc (R:=R) P (atom a)=if P a then atom a else 0 := by
  simp [assoc]

theorem embed_lie (q : FreeLieAlgebra R α) : embed (lie P q)=assoc P (embed q) := by
  have h : embed.comp (lie (R:=R) P)=(assoc P).toLieHom.comp embed := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp only [LieHom.comp_apply,lie_of,embed_of,AlgHom.toLieHom_apply,assoc_atom]
    split_ifs <;> simp
  exact LieHom.congr_fun h q

theorem assoc_word (w : FreeMonoid α) : assoc (R:=R) P (word w)=
    if ∀ a∈w.toList,P a then word w else 0 := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    rw [word_mul,map_mul,ih]
    rw [word_of,assoc_atom]
    simp only [FreeMonoid.toList_mul,FreeMonoid.toList_of,List.singleton_append,List.mem_cons,
      forall_eq_or_imp]
    split_ifs <;> simp_all

theorem coeff (q : A R α) (w : FreeMonoid α) :
    (assoc P q).coeff w=if ∀ a∈w.toList,P a then q.coeff w else 0 := by
  have h : (assoc (R:=R) P).toLinearMap=project (fun w => ∀ a∈w.toList,P a) := by
    apply LinearMap.ext
    intro q
    induction q using MonoidAlgebra.induction_on with
    | of w => exact (assoc_word P w).trans (project_word (R:=R) (fun w => ∀ a∈w.toList,P a) w).symm
    | add p q hp hq => simp only [map_add,hp,hq]
    | smul c p hp => simp only [map_smul,hp]
  change ((assoc P).toLinearMap q).coeff w=_
  rw [h,project_coeff]

theorem assoc_eq_self {q : A R α} (hq : q∈space (fun w => ∀ a∈w.toList,P a)) : assoc P q=q := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  rw [coeff]
  split_ifs with hw
  · rfl
  · exact (coeff_support hq w hw).symm

theorem lie_eq_self {q : FreeLieAlgebra R α}
    (hq : embed q∈space (fun w => ∀ a∈w.toList,P a)) : lie P q=q := by
  apply UniversalEmbedding.injective
  rw [embed_lie,assoc_eq_self P hq]

def sub : LieSubalgebra R (FreeLieAlgebra R α) :=
  LieSubalgebra.lieSpan R (FreeLieAlgebra R α) {p | ∃ a,P a ∧ p=FreeLieAlgebra.of R a}

theorem lie_mem (q : FreeLieAlgebra R α) : lie P q∈sub P := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg a =>
    rw [lie_of]
    split_ifs with ha
    · exact LieSubalgebra.subset_lieSpan ⟨a,ha,rfl⟩
    · exact (sub P).zero_mem
  | ha p q hp hq => simpa only [map_add] using (sub P).add_mem hp hq
  | hs r p hp => simpa only [map_smul] using (sub P).smul_mem r hp
  | hl p q hp hq => simpa only [LieHom.map_lie] using (sub P).lie_mem hp hq

theorem mem_of_support {q : FreeLieAlgebra R α}
    (hq : embed q∈space (fun w => ∀ a∈w.toList,P a)) : q∈sub P := by
  rw [← lie_eq_self P hq]
  exact lie_mem P q

end LetterRetraction
namespace RowKernel
open AssociativeElimination WordGrading WeightedDeletion RowTwo

theorem degree_indicator_zero {α : Type*} (P : α → Prop) [DecidablePred P] (s : List α) :
    degree (fun a => if P a then 1 else 0) (FreeMonoid.ofList s)=0 ↔ ∀ a∈s,¬P a := by
  induction s with
  | nil => simp [degree]
  | cons a s ih =>
    simp only [degree,FreeMonoid.toList_ofList,List.map_cons,List.sum_cons] at ih ⊢
    simp only [Nat.add_eq_zero_iff,List.mem_cons,forall_eq_or_imp,ih]
    split_ifs <;> simp_all

theorem no_A_coeff {q : FreeLieAlgebra K Slot}
    (hq : LetterRetraction.lie (fun a => a≠Slot.A) q=0)
    (w : FreeMonoid Slot) (hw : degree RowKernel.aCount w=0) : (embed q).coeff w=0 := by
  have hp : ∀ a∈w.toList,a≠Slot.A := by
    exact (degree_indicator_zero (fun a => a=Slot.A) w.toList).mp
      (by rw [FreeMonoid.ofList_toList]; exact hw)
  have h := congrArg (fun p => (embed p).coeff w) hq
  rw [LetterRetraction.embed_lie,LetterRetraction.coeff,if_pos hp] at h
  simpa using h

theorem kernel_no_C (q : FreeLieAlgebra K Slot) (m r : ℕ)
    (hm : embed q∈homogeneous acCount m) (hr : embed q∈homogeneous bCount r)
    (hzero : LetterRetraction.lie (fun a => a≠Slot.A) q=0)
    (heq : ∀ s,degree acCount (FreeMonoid.ofList s)=m →
      degree bCount (FreeMonoid.ofList s)=r → Equation (embed q) s) :
    q∈LetterRetraction.sub (fun a => a≠Slot.C) := by
  apply LetterRetraction.mem_of_support
  have h := kernel_support q m r hm hr (no_A_coeff hzero) heq
  apply space_mono (fun w hw => ?_) h
  exact (degree_indicator_zero (fun a => a=Slot.C) w.toList).mp
    (by rw [FreeMonoid.ofList_toList]; exact hw)

end RowKernel

namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]

theorem algHom_difference_above (f g : A R α →ₐ[R] A R β)
    (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈above wb (wa a))
    (hg : ∀ a,g (atom a)∈homogeneous wb (wa a))
    (he : ∀ a,f (atom a)-g (atom a)∈above wb (wa a+1))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) :
    f p-g p∈above wb (n+1) := by
  have hw (w : FreeMonoid α) : f (word w)-g (word w)∈above wb (degree wa w+1) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      have hfw : f (word w)∈above wb (degree wa w) :=
        algHom_above f wa wb hf (word_mem w (le_refl _))
      have h1 := above_mul (he a) hfw
      have h2 := above_mul (homogeneous_above (hg a)) ih
      have eq : f (atom a)*f (word w)-g (atom a)*g (word w)=
          (f (atom a)-g (atom a))*f (word w)+g (atom a)*(f (word w)-g (word w)) := by noncomm_ring
      rw [eq]
      apply (above wb (wa a+degree wa w+1)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [Nat.add_assoc] using h2
  exact map_space (f.toLinearMap-g.toLinearMap) _ (by intro w h; simpa only [LinearMap.sub_apply,AlgHom.toLinearMap_apply,h] using hw w) hp

end WordGrading

namespace AssociativeEvaluation
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α U : Type*} [CommRing R] [Ring U] [Algebra R U]

theorem map_eval {M N : Type*} [LieRing M] [LieAlgebra R M] [LieRing N] [LieAlgebra R N]
    (f : M →ₗ⁅R⁆ N) (a b : M) (q : FreeLieAlgebra R Bool) :
    f (BaseChangeEquations.eval a b q)=BaseChangeEquations.eval (f a) (f b) q := by
  have h : f.comp (BaseChangeEquations.eval a b)=BaseChangeEquations.eval (f a) (f b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [BaseChangeEquations.eval]
  exact LieHom.congr_fun h q

end AssociativeEvaluation
namespace CharTwoAction
attribute [local instance] LieRing.ofAssociativeRing
variable {U : Type*} [Ring U] [CharP U 2]
theorem square_add (x y : U) : (x+y)*(x+y)=x*x+y*y+⁅x,y⁆ := by
  simp only [Ring.lie_def,CharTwo.sub_eq_add,mul_add,add_mul]
  abel
end CharTwoAction
namespace ExactPentagon
open AssociativeElimination RowTwo RowKernel LeadingRows PolynomialOrdering
open SourceEnveloping SourceModel
attribute [local instance] LieRing.ofAssociativeRing

abbrev U13 : Env S3 := rawFiber (CountTables.Y 0)
abbrev U23 : Env S3 := rawFiber (CountTables.Y 1)
abbrev X1 : Env S3 := baseX 0
abbrev X2 : Env S3 := baseX 1
abbrev U12 : Env S3 := baseU

def algEval {U : Type*} [Ring U] [Algebra K U] (x y : U) : A K Bool →ₐ[K] U :=
  lift (fun i => if i then y else x)

def quadEval {U : Type*} [Ring U] [Algebra K U] (x y : U) : A K Slot →ₐ[K] U :=
  lift (fun | .A => x*x | .C => x*y-y*x | .B => y)

theorem algEval_quad {U : Type*} [Ring U] [Algebra K U] (x y : U) :
    (algEval x y).comp quad=quadEval x y := by
  apply hom_ext
  intro k
  cases k <;> simp [quad,quadEval,algEval]

def interpretation : A K E →ₐ[K] Env S3 := evaluate topFiber topBase

theorem interpretation_base (b : CountTables.B) : interpretation (atom (.inr b))=topBase (atom b) := by
  simp [interpretation,evaluate]
theorem interpretation_fiber (b : CountTables.F) : interpretation (atom (.inl b))=topFiber (atom b) := by
  simp [interpretation,evaluate]

@[simp] theorem interpretation_a1 : interpretation (atom (.inr 0))=X1*X1 := by
  simp only [interpretation_base,topBase,AlgHom.comp_apply,oldBase,lift_atom,map_mul]
  rfl
@[simp] theorem interpretation_a2 : interpretation (atom (.inr 1))=X2*X2 := by
  simp only [interpretation_base,topBase,AlgHom.comp_apply,oldBase,lift_atom,map_mul]
  rfl
@[simp] theorem interpretation_u12 : interpretation u12=U12 := by
  simp only [u12,interpretation_base,topBase,AlgHom.comp_apply,oldBase,lift_atom]
  rfl
@[simp] theorem interpretation_u13 : interpretation (atom (.inl 1))=U13 := by
  rw [interpretation_fiber,topFiber_eq,CountTables.realize_atom_one]
@[simp] theorem interpretation_u23 : interpretation u23=U23 := by
  rw [interpretation_fiber,topFiber_eq,CountTables.realize_atom_two]
@[simp] theorem interpretation_v12 : interpretation (atom (.inr 3))=⁅X1,U12⁆ := by
  simp only [interpretation_base,topBase,AlgHom.comp_apply,oldBase,lift_atom,Ring.lie_def,map_sub,map_mul]
  rfl
@[simp] theorem interpretation_v13 : interpretation (atom (.inl 3))=⁅X1,U13⁆ := by
  rw [interpretation_fiber,topFiber_eq,CountTables.realize_atom_three,raw_delta]
  simp [CountTables.δ,CountTables.Y,CountTables.C]
@[simp] theorem interpretation_v23 : interpretation (atom (.inl 4))=⁅X2,U23⁆ := by
  rw [interpretation_fiber,topFiber_eq,CountTables.realize_atom_four,raw_delta]
  simp [CountTables.δ,CountTables.Y,CountTables.C]

theorem cross13 : ⁅X2,U13⁆=0 := by
  rw [raw_delta]
  simp [CountTables.δ,CountTables.Y]
theorem cross23 : ⁅X1,U23⁆=0 := by
  rw [raw_delta]
  simp [CountTables.δ,CountTables.Y]

theorem base_triple : ⁅X1,X2⁆=⁅X1,U12⁆ := by
  have h := GenericBraid.t_three (R:=K) (some root : S3) (some one) (some two)
    (by decide) (by decide) (by decide)
  have hh := congrArg (UniversalEnvelopingAlgebra.ι K) h
  simp only [map_zero,LieHom.map_lie,map_add] at hh
  change ⁅SourceEnveloping.chord (some root) (some one),
    SourceEnveloping.chord (some root) (some two)+SourceEnveloping.chord (some one) (some two)⁆=0 at hh
  rw [← baseX_zero,← baseX_one,← baseU_eq,lie_add] at hh
  exact CharTwo.add_eq_zero.mp hh

theorem base_triangle : ⁅X2,U12⁆=⁅X1,U12⁆ := by
  have h := GenericBraid.t_three (R:=K) (some one : S3) (some two) (some root)
    (by decide) (by decide) (by decide)
  have hh := congrArg (UniversalEnvelopingAlgebra.ι K) h
  simp only [map_zero,LieHom.map_lie,map_add] at hh
  change ⁅SourceEnveloping.chord (some one) (some two),
    SourceEnveloping.chord (some one) (some root)+SourceEnveloping.chord (some two) (some root)⁆=0 at hh
  rw [SourceEnveloping.chord_comm (some one) (some root),SourceEnveloping.chord_comm (some two) (some root),
    ← baseX_zero,← baseX_one,← baseU_eq,lie_add] at hh
  rw [CharTwoAction.symm U12 X1,CharTwoAction.symm U12 X2] at hh
  exact (CharTwo.add_eq_zero.mp hh).symm

theorem interprets_one : interpretation.comp (subst .one)=quadEval X1 (U12+U13) := by
  apply hom_ext
  intro k
  cases k <;> simp only [AlgHom.comp_apply,subst,lift_atom,slots,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,map_add,interpretation_a1,interpretation_u12,interpretation_u13,
    interpretation_v12,interpretation_v13,quadEval,lift_atom]
  all_goals simp only [Ring.lie_def]; noncomm_ring

theorem interprets_four : interpretation.comp (subst .four)=quadEval X1 U12 := by
  apply hom_ext
  intro k
  cases k <;> simp only [AlgHom.comp_apply,subst,lift_atom,slots,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,interpretation_a1,interpretation_u12,interpretation_v12,quadEval,lift_atom,Ring.lie_def]

theorem interprets_omitted : interpretation.comp omitted=quadEval U12 U23 := by
  apply hom_ext
  intro k
  cases k <;> simp only [AlgHom.comp_apply,omitted,lift_atom,map_mul,map_sub,interpretation_u12,
    interpretation_u23,quadEval,lift_atom]

theorem interprets_two : interpretation.comp exactTwo=quadEval (X2+U12) U23 := by
  apply hom_ext
  intro k
  cases k with
  | A =>
      simp only [AlgHom.comp_apply,exactTwo,lift_atom,subst,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,extra,map_add,map_mul,interpretation_a2,interpretation_v12,interpretation_u12,
        quadEval,lift_atom,CharTwoAction.square_add,base_triangle]
      abel
  | C =>
      simp only [AlgHom.comp_apply,exactTwo,lift_atom,subst,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,extra,map_add,map_mul,map_sub,interpretation_v23,interpretation_u12,
        interpretation_u23,quadEval,lift_atom,Ring.lie_def]
      noncomm_ring
  | B =>
      simp only [AlgHom.comp_apply,exactTwo,lift_atom,subst,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,extra,interpretation_u23,quadEval,lift_atom]

theorem interprets_three : interpretation.comp (subst .three)=quadEval (X1+X2) (U13+U23) := by
  apply hom_ext
  intro k
  cases k with
  | A =>
      simp only [AlgHom.comp_apply,subst,lift_atom,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,map_add,interpretation_a1,interpretation_a2,interpretation_v12,
        quadEval,lift_atom,CharTwoAction.square_add,base_triple]
      abel
  | C =>
      simp only [AlgHom.comp_apply,subst,lift_atom,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,map_add,interpretation_v13,interpretation_v23,quadEval,lift_atom]
      change ⁅X1,U13⁆+⁅X2,U23⁆=⁅X1+X2,U13+U23⁆
      rw [add_lie,lie_add,lie_add,cross13,cross23,add_zero,zero_add]
  | B =>
      simp only [AlgHom.comp_apply,subst,lift_atom,slots,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,map_add,interpretation_u13,interpretation_u23,quadEval,lift_atom]

theorem full_interpretation (p : A K Slot) :
    interpretation (full p)=quadEval X1 (U12+U13) p+quadEval (X2+U12) U23 p+
      quadEval U12 U23 p+quadEval (X1+X2) (U13+U23) p+quadEval X1 U12 p := by
  simp only [full,map_add]
  rw [show interpretation (subst .one p)=quadEval X1 (U12+U13) p from AlgHom.congr_fun interprets_one p,
    show interpretation (exactTwo p)=quadEval (X2+U12) U23 p from AlgHom.congr_fun interprets_two p,
    show interpretation (omitted p)=quadEval U12 U23 p from AlgHom.congr_fun interprets_omitted p,
    show interpretation (subst .three p)=quadEval (X1+X2) (U13+U23) p from AlgHom.congr_fun interprets_three p,
    show interpretation (subst .four p)=quadEval X1 U12 p from AlgHom.congr_fun interprets_four p]

def labels : Fin 4 ≃ S3 where
  toFun | 0 => some root | 1 => some one | 2 => some two | 3 => none
  invFun | some (some (some _)) => 0 | some (some none) => 1 | some none => 2 | none => 3
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by
    cases i with
    | none => rfl
    | some j => cases j with
      | none => rfl
      | some k => cases k with
        | none => rfl
        | some u => cases u; rfl

def sourceHom : GenericBraid.T K (Fin 4) →ₗ⁅K⁆ Env S3 :=
  (UniversalEnvelopingAlgebra.ι K).comp (GenericBraid.rename labels)

@[simp] theorem sourceHom_t (i j : Fin 4) : sourceHom (GenericBraid.t i j)=
    SourceEnveloping.chord (labels i) (labels j) := by
  simp [sourceHom,SourceEnveloping.chord]
@[simp] theorem sourceHom_01 : sourceHom (GenericBraid.t 0 1)=X1 := by
  rw [sourceHom_t]
  exact baseX_zero.symm
@[simp] theorem sourceHom_02 : sourceHom (GenericBraid.t 0 2)=X2 := by
  rw [sourceHom_t]
  exact baseX_one.symm
@[simp] theorem sourceHom_12 : sourceHom (GenericBraid.t 1 2)=U12 := by
  rw [sourceHom_t]
  exact baseU_eq.symm
@[simp] theorem sourceHom_13 : sourceHom (GenericBraid.t 1 3)=U13 := by
  rw [sourceHom_t]
  change SourceEnveloping.chord (some one) none=rawFiber (CountTables.Y 0)
  rw [rawFiber_Y]
  exact SourceEnveloping.chord_comm _ _
@[simp] theorem sourceHom_23 : sourceHom (GenericBraid.t 2 3)=U23 := by
  rw [sourceHom_t]
  change SourceEnveloping.chord (some two) none=rawFiber (CountTables.Y 1)
  rw [rawFiber_Y]
  exact SourceEnveloping.chord_comm _ _

theorem eval_quadratic {ψ : FreeLieAlgebra K Bool} {p : A K Slot}
    (hrep : embed ψ=quad p) (a b : Env S3) :
    BaseChangeEquations.eval a b ψ=quadEval a b p := by
  rw [← show algEval a b (embed ψ)=BaseChangeEquations.eval a b ψ from
    AssociativeEvaluation.lift_embed _ ψ,hrep]
  exact AlgHom.congr_fun (algEval_quad a b) p

theorem full_zero {ψ : FreeLieAlgebra K Bool} {p : A K Slot}
    (hrep : embed ψ=quad p) (hpent : BaseChangeEquations.pentagon ψ=0) :
    interpretation (full p)=0 := by
  have h := congrArg sourceHom hpent
  simp only [BaseChangeEquations.pentagon,map_sub,map_add,map_zero,AssociativeEvaluation.map_eval,
    sourceHom_01,sourceHom_02,sourceHom_12,sourceHom_13,sourceHom_23,
    CharTwo.sub_eq_add,eval_quadratic hrep] at h
  rw [full_interpretation]
  exact h

end ExactPentagon
end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]

theorem piece_mem (wt : α → ℕ) (n : ℕ) (p : A R α) : piece wt n p∈homogeneous wt n :=
  project_mem _ p

theorem project_preserves {P Q : FreeMonoid α → Prop} [DecidablePred Q]
    {p : A R α} (hp : p∈space P) : project Q p∈space P := by
  apply mem_space
  intro w hw
  rw [project_coeff] at hw
  split_ifs at hw with h
  · exact (mem_space_iff.mp hp) w hw
  · exact (hw rfl).elim

theorem subtract_piece_above {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : p-piece wt n p∈above wt (n+1) := by
  apply mem_space
  intro w hw
  change (p-piece wt n p).coeff w≠0 at hw
  simp only [MonoidAlgebra.coeff_sub,Finsupp.sub_apply] at hw
  change p.coeff w-(project (fun w => degree wt w=n) p).coeff w≠0 at hw
  rw [project_coeff] at hw
  have hn : n≤degree wt w := by
    by_contra h
    have hz := coeff_support hp w h
    simp [hz] at hw
  by_cases he : degree wt w=n
  · simp [he] at hw
  · omega
end WordGrading

end

end DeligneDrinfeld

end

end OAI

end


section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
namespace AlphabetTransport
open AssociativeElimination UniversalEmbedding
variable {R α β γ : Type*} [CommRing R]

theorem assoc_retract (f : α → β) (g : β → α) (h : Function.LeftInverse g f) (p : A R α) :
    renameAssoc g (renameAssoc f p)=p := by
  have he : (renameAssoc (R:=R) g).comp (renameAssoc f)=AlgHom.id R (A R α) := by
    apply hom_ext
    intro a
    simp [h a]
  exact AlgHom.congr_fun he p

theorem assoc_injective (f : α → β) (g : β → α) (h : Function.LeftInverse g f) :
    Function.Injective (renameAssoc (R:=R) f) := by
  intro p q hp
  simpa only [assoc_retract f g h] using congrArg (renameAssoc g) hp

end AlphabetTransport
namespace QuadraticLeading
open AssociativeElimination UniversalEmbedding WordGrading AlphabetTransport
open RowTwo RowKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing

def letters : Slot ≃ QuadraticAlphabet.Letter where
  toFun := fun | .A => .a | .C => .c | .B => .b
  invFun := fun | .a => .A | .c => .C | .b => .B
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

theorem quad_transport : (renameAssoc bitOption).comp quad=
    QuadraticAlphabet.substitution.comp (renameAssoc letters) := by
  apply hom_ext
  intro k
  cases k <;> simp [quad,letters,bitOption,QuadraticAlphabet.substitution,
    QuadraticAlphabet.x,QuadraticAlphabet.y,Ring.lie_def]

theorem quad_injective : Function.Injective quad := by
  intro p q hp
  apply assoc_injective letters letters.symm letters.left_inv
  apply QuadraticAlphabet.substitution_injective
  have h := congrArg (renameAssoc bitOption) hp
  exact (AlgHom.congr_fun quad_transport p).symm.trans (h.trans (AlgHom.congr_fun quad_transport q))

theorem under_injective : Function.Injective under := by
  intro p q h
  exact UniversalEmbedding.injective (quad_injective h)

theorem weight_count (w : FreeMonoid Slot) : degree weight w=2*degree acCount w+degree bCount w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    simp only [degree_mul,degree_of,ih]
    cases a <;> simp [weight,acCount,bCount,aCount,cCount] <;> omega

theorem leading_ac {p : A K Slot} {n r m : ℕ} (hp : p∈homogeneous weight n)
    (hb : p∈homogeneous bCount r) (hn : n=2*m+r) : p∈homogeneous acCount m := by
  apply mem_space
  intro w hw
  have h1 := mem_space_iff.mp hp w hw
  have h2 := mem_space_iff.mp hb w hw
  have h3 := weight_count w
  omega

theorem leading_rows {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r : ℕ}
    (hp : under p=embed ψ) (hw : embed p∈homogeneous weight n)
    (hr : r<n) (hb : embed p∈above bCount r) (he : BaseChangeEquations.pentagon ψ=0)
    (s : List Slot) (hs : degree bCount (FreeMonoid.ofList s)=r) :
    RowKernel.Equation (embed (LieGrading.piece bCount r p)) s := by
  rw [LieGrading.embed_piece]
  apply ExactPentagon.row_equation hw hr (piece_mem bCount r (embed p))
    (subtract_piece_above hb) ?_ s hs
  exact full_zero hp.symm he

theorem leading_no_C {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r m : ℕ}
    (hp : under p=embed ψ) (hw : embed p∈homogeneous weight n) (hr : r<n)
    (hb : embed p∈above bCount r) (he : BaseChangeEquations.pentagon ψ=0)
    (hn : n=2*m+r)
    (hz : LetterRetraction.lie (fun a => a≠Slot.A) (LieGrading.piece bCount r p)=0) :
    LieGrading.piece bCount r p∈LetterRetraction.sub (fun a => a≠Slot.C) := by
  refine RowKernel.kernel_no_C _ m r ?_ ?_ hz ?_
  · rw [LieGrading.embed_piece]
    exact leading_ac (project_preserves hw) (piece_mem bCount r (embed p)) hn
  · rw [LieGrading.embed_piece]
    exact piece_mem bCount r (embed p)
  · intro s _ hs
    exact leading_rows hp hw hr hb he s hs

end QuadraticLeading

namespace BaseChangeEquations
open AssociativeEvaluation
variable {R S : Type*} [CommRing R] [CommRing S]

theorem eval_comp (a b c d : FreeLieAlgebra R Bool) (q : FreeLieAlgebra R Bool) :
    eval a b (eval c d q)=eval (eval a b c) (eval a b d) q := AssociativeEvaluation.map_eval _ _ _ _

theorem swapped {q : FreeLieAlgebra R Bool} (hq : antisymmetry q=0)
    (a b : FreeLieAlgebra R Bool) : eval a b q+eval b a q=0 := by
  have h := congrArg (eval a b) hq
  simpa only [antisymmetry,map_add,eval_comp,eval_y,eval_x,map_zero] using h

end BaseChangeEquations
namespace TwoModule
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
theorem add_self (a : M) : a+a=0 := by
  calc a+a=((1 : ZMod 2)+1) • a := by rw [add_smul,one_smul]
       _=0 := by rw [show (1 : ZMod 2)+1=0 from by decide,zero_smul]

theorem neg_eq (a : M) : -a=a := by
  apply neg_eq_iff_add_eq_zero.mpr
  exact add_self a

theorem sub_eq_add (a b : M) : a-b=a+b := by rw [sub_eq_add_neg,neg_eq]

theorem eq_of_add_zero {a b : M} (h : a+b=0) : a=b := by
  have := eq_neg_of_add_eq_zero_left h
  simpa only [neg_eq] using this
end TwoModule
namespace BaseChangeEquations
abbrev K := ZMod 2

theorem deletion_special {q : FreeLieAlgebra K Bool}
    (ha : antisymmetry q=0) (hs : special q=0) :
    ⁅(x : FreeLieAlgebra K Bool),q+eval (x+y) y q⁆+⁅(y : FreeLieAlgebra K Bool),eval (x+y) y q⁆=0 := by
  have hswap : eval y x q=q := by
    exact (TwoModule.eq_of_add_zero ha).symm
  have hswap2 : eval y (x+y) q=eval (x+y) y q :=
    TwoModule.eq_of_add_zero (swapped ha y (x+y))
  simp only [special,TwoModule.neg_eq,TwoModule.sub_eq_add,hswap,hswap2,add_lie] at hs
  simpa only [lie_add,add_assoc] using hs
end BaseChangeEquations

namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]

def lower (wt : α → ℕ) (c n : ℕ) : Submodule R (A R α) := space (fun w => degree wt w+c=n)

theorem lower_mul_homogeneous {wt : α → ℕ} {c n m : ℕ} {p q : A R α}
    (hp : p∈lower wt c n) (hq : q∈homogeneous wt m) : p*q∈lower wt c (n+m) :=
  mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) hp hq

theorem homogeneous_mul_lower {wt : α → ℕ} {c n m : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt n) (hq : q∈lower wt c m) : p*q∈lower wt c (n+m) :=
  mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) hp hq

theorem deriv_lower (wt : α → ℕ) (c : ℕ) (f : α → A R α)
    (hf : ∀ a,f a∈lower wt c (wt a)) {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : deriv f p∈lower wt c n := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈lower wt c (degree wt w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      simp only [degree_mul,degree_of]
      exact (lower wt c _).add_mem
        (lower_mul_homogeneous (hf a) (word_mem w rfl))
        (homogeneous_mul_lower (word_mem (FreeMonoid.of a) (degree_of wt a)) ih)
  exact map_space (deriv f) _ (by intro w h; simpa only [h] using hw w) hp

theorem deriv_lowers_above (wt : α → ℕ) (c : ℕ) (f : α → A R α)
    (hf : ∀ a,f a∈lower wt c (wt a)) {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : deriv f p∈above wt (n-c) := by
  apply map_space (deriv f) _ ?_ hp
  intro w hw
  apply space_mono (P:=fun v => degree wt v+c=degree wt w) ?_
    (deriv_lower wt c f hf (word_mem w rfl))
  intro v hv
  omega

theorem lower_homogeneous {wt : α → ℕ} {c n : ℕ} {p : A R α}
    (hp : p∈lower wt c n) : p∈homogeneous wt (n-c) :=
  space_mono (by intro w hw; omega) hp

theorem piece_zero_of_above {wt : α → ℕ} {n k : ℕ} {p : A R α}
    (hp : p∈above wt n) (hkn : k<n) : piece wt k p=0 :=
  project_eq_zero hp (by intro w hw hk; omega)

theorem homogeneous_add_high_zero {wt : α → ℕ} {n k : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt k) (hq : q∈above wt n) (hkn : k<n) (hz : p+q=0) : p=0 := by
  have h := congrArg (piece wt k) hz
  rw [map_add,piece_homogeneous hp,if_pos rfl,piece_zero_of_above hq hkn,add_zero,map_zero] at h
  exact h

end WordGrading

namespace ResidualKernel

section
open AssociativeElimination UniversalEmbedding WordGrading RowTwo RowKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing

def low : Slot → A K Slot | .B => atom .C | _ => 0
def high : Slot → A K Slot | .C => atom .A*atom .B-atom .B*atom .A | _ => 0
def delta : Slot → A K Slot := fun a => low a+high a

def tau : A K Slot →ₐ[K] A K Slot := lift (fun
  | .A => atom .A+atom .C+atom .B*atom .B | .C => atom .C | .B => atom .B)
def tau0 : A K Slot →ₐ[K] A K Slot := lift (fun
  | .A => atom .A+atom .C | .C => atom .C | .B => atom .B)

theorem deriv_add (f g : Slot → A K Slot) (p : A K Slot) :
    deriv (fun a => f a+g a) p=deriv f p+deriv g p := by
  simpa only [TwoModule.sub_eq_add] using WordGrading.deriv_sub f g p

theorem delta_split (p : A K Slot) : deriv delta p=deriv low p+deriv high p := deriv_add low high p

theorem quad_delta (p : A K Slot) :
    quad (deriv delta p)=atom false*quad p-quad p*atom false := by
  have hg (a : Slot) : quad (delta a)=atom false*quad (atom a)-quad (atom a)*atom false := by
    cases a <;> simp only [delta,low,high,quad,lift_atom,map_add,map_mul,map_zero,
      zero_add,add_zero,TwoModule.sub_eq_add,mul_add,add_mul]
    · simp [mul_assoc,TwoModule.add_self]
    · have h : (atom false*atom true*atom false : A K Bool)+atom false*atom true*atom false=0 := TwoModule.add_self _
      simp only [mul_assoc] at h ⊢
      apply eq_of_sub_eq_zero
      calc _ = -(atom false*(atom true*atom false)+atom false*(atom true*atom false)) := by abel
           _ = 0 := by rw [h,neg_zero]
  have hw (w : FreeMonoid Slot) : quad (deriv delta (word w))=atom false*quad (word w)-quad (word w)*atom false := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,map_add,map_mul,map_mul,deriv_atom,hg,ih,map_mul]
      noncomm_ring
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add p q hp hq => simp only [map_add,hp,hq,mul_add,add_mul]; abel
  | smul c p hp => simp only [map_smul,hp,mul_smul_comm,smul_mul_assoc,smul_sub]

theorem quad_tau : quad.comp tau=(algEval (atom false+atom true) (atom true)).comp quad := by
  apply hom_ext
  intro a
  cases a <;> simp only [AlgHom.comp_apply,tau,quad,algEval,lift_atom,map_add,map_mul,
    Bool.false_eq_true,↓reduceIte,TwoModule.sub_eq_add,mul_add,add_mul]
  · abel
  · have h : (atom true*atom true : A K Bool)+atom true*atom true=0 := TwoModule.add_self _
    apply eq_of_sub_eq_zero
    calc _ = -(atom true*atom true+atom true*atom true) := by abel
         _ = 0 := by rw [h,neg_zero]

theorem embed_eval (a b : FreeLieAlgebra K Bool) (ψ : FreeLieAlgebra K Bool) :
    embed (BaseChangeEquations.eval a b ψ)=algEval (embed a) (embed b) (embed ψ) := by
  rw [AssociativeEvaluation.map_eval,algEval,AssociativeEvaluation.lift_embed]
  rfl

theorem full_equation {ψ : FreeLieAlgebra K Bool} {p : A K Slot}
    (hp : quad p=embed ψ) (ha : BaseChangeEquations.antisymmetry ψ=0)
    (hs : BaseChangeEquations.special ψ=0) :
    deriv delta (p+tau p)+(atom .B*tau p-tau p*atom .B)=0 := by
  apply QuadraticLeading.quad_injective
  rw [map_zero,map_add,quad_delta,map_add,map_sub,map_mul,map_mul]
  have hτ : quad (tau p)=embed (BaseChangeEquations.eval
      (BaseChangeEquations.x+BaseChangeEquations.y) BaseChangeEquations.y ψ) := by
    rw [← AlgHom.comp_apply,quad_tau,AlgHom.comp_apply,hp,embed_eval]
    simp only [map_add,BaseChangeEquations.x,BaseChangeEquations.y,embed_of]
  rw [hp,hτ]
  have h := congrArg embed (BaseChangeEquations.deletion_special ha hs)
  simpa only [map_add,LieHom.map_lie,Ring.lie_def,map_zero,BaseChangeEquations.x,
    BaseChangeEquations.y,embed_of,quad,lift_atom] using h

theorem low_degree (a : Slot) : low a∈lower bCount 1 (bCount a) := by
  cases a <;> simp only [low,bCount]
  · exact (lower bCount 1 0).zero_mem
  · exact (lower bCount 1 0).zero_mem
  · exact word_mem (FreeMonoid.of Slot.C) rfl

theorem high_degree (a : Slot) : high a∈homogeneous bCount (bCount a+1) := by
  have hA : (atom Slot.A : A K Slot)∈homogeneous bCount 0 := word_mem _ rfl
  have hB : (atom Slot.B : A K Slot)∈homogeneous bCount 1 := word_mem _ rfl
  cases a with
  | A => exact (homogeneous bCount 1).zero_mem
  | C =>
    have h1 := homogeneous_mul hA hB
    have h2 := homogeneous_mul hB hA
    exact (homogeneous bCount 1).sub_mem h1 h2
  | B => exact (homogeneous bCount 2).zero_mem

theorem tau0_degree (a : Slot) : tau0 (atom a)∈homogeneous bCount (bCount a) := by
  cases a <;> simp only [tau0,lift_atom,bCount]
  · exact (homogeneous bCount 0).add_mem (word_mem _ rfl) (word_mem _ rfl)
  · exact word_mem _ rfl
  · exact word_mem _ rfl

theorem tau_difference (a : Slot) : tau (atom a)-tau0 (atom a)∈above bCount (bCount a+1) := by
  cases a <;> simp only [tau,tau0,lift_atom,add_sub_cancel_left,sub_self,bCount]
  · have hB : (atom Slot.B : A K Slot)∈homogeneous bCount 1 := word_mem _ rfl
    have h := homogeneous_mul hB hB
    apply space_mono (P:=fun w => degree bCount w=2) ?_ h
    intro w hw
    simp only [ reduceCtorEq,↓reduceIte]
    omega
  · exact (above bCount 1).zero_mem
  · exact (above bCount 2).zero_mem

theorem tau_degree (a : Slot) : tau (atom a)∈above bCount (bCount a) := by
  have h1 := homogeneous_above (tau0_degree a)
  have h2 : tau (atom a)-tau0 (atom a)∈above bCount (bCount a) :=
    space_mono (by intro w hw; omega) (tau_difference a)
  have he : tau (atom a)=(tau (atom a)-tau0 (atom a))+tau0 (atom a) := by abel
  rw [he]
  exact (above bCount _).add_mem h2 h1

theorem leading_equation {p q : A K Slot} {r : ℕ} (hr : 0<r)
    (hq : q∈homogeneous bCount r) (hh : p-q∈above bCount (r+1))
    (he : deriv delta (p+tau p)+(atom .B*tau p-tau p*atom .B)=0) :
    deriv low (q+tau0 q)=0 := by
  have hqt := algHom_homogeneous tau0 bCount bCount tau0_degree hq
  have hlead : deriv low (q+tau0 q)∈homogeneous bCount (r-1) :=
    lower_homogeneous (deriv_lower bCount 1 low low_degree ((homogeneous bCount r).add_mem hq hqt))
  have hdiff : tau p-tau0 q∈above bCount (r+1) := by
    have ht := algHom_above tau bCount bCount tau_degree hh
    have hd := algHom_difference_above tau tau0 bCount bCount tau_degree tau0_degree tau_difference hq
    rw [map_sub] at ht
    have heq : tau p-tau0 q=(tau p-tau q)+(tau q-tau0 q) := by abel
    rw [heq]
    exact (above bCount _).add_mem ht hd
  have hp : p∈above bCount r := by
    have hh' : p-q∈above bCount r := space_mono (by intro w hw; omega) hh
    have heq : p=(p-q)+q := by abel
    rw [heq]
    exact (above bCount _).add_mem hh' (homogeneous_above hq)
  have hpt := algHom_above tau bCount bCount tau_degree hp
  have hdt := (above bCount (r+1)).add_mem hh hdiff
  have hl := deriv_lowers_above bCount 1 low low_degree hdt
  have hhg := deriv_above (fun a => homogeneous_above (high_degree a)) ((above bCount r).add_mem hp hpt)
  have hB : (atom Slot.B : A K Slot)∈above bCount 1 := homogeneous_above (word_mem _ rfl)
  have hbr : atom Slot.B*tau p-tau p*atom Slot.B∈above bCount (r+1) := by
    exact (above bCount _).sub_mem (by simpa only [Nat.add_comm] using above_mul hB hpt) (above_mul hpt hB)
  have hhg' : deriv high (p+tau p)∈above bCount r := space_mono (by intro w hw; omega) hhg
  have hbr' : atom Slot.B*tau p-tau p*atom Slot.B∈above bCount r := space_mono (by intro w hw; omega) hbr
  have hl' : deriv low ((p-q)+(tau p-tau0 q))∈above bCount r := by simpa using hl
  apply homogeneous_add_high_zero hlead ((above bCount r).add_mem ((above bCount r).add_mem hl' hhg') hbr') (by omega)
  rw [delta_split] at he
  convert he using 1; simp only [map_add,map_sub]; abel

end

open AssociativeElimination WordGrading RowTwo RowKernel

def coeff (p : A K Slot) (s : List Slot) : K := p.coeff (FreeMonoid.ofList s)
def monomial (s : List Slot) : A K Slot := word (FreeMonoid.ofList s)

@[simp] theorem monomial_nil : monomial []=1 := rfl
@[simp] theorem monomial_cons (a : Slot) (s : List Slot) : monomial (a::s)=atom a*monomial s := by
  exact word_mul (FreeMonoid.of a) (FreeMonoid.ofList s)
@[simp] theorem coeff_add (p q : A K Slot) (s : List Slot) : coeff (p+q) s=coeff p s+coeff q s := rfl
@[simp] theorem coeff_smul (c : K) (p : A K Slot) (s : List Slot) : coeff (c • p) s=c*coeff p s := rfl
@[simp] theorem coeff_zero (s : List Slot) : coeff 0 s=0 := rfl
@[simp] theorem coeff_monomial (s t : List Slot) : coeff (monomial s) t=if s=t then 1 else 0 := by
  classical
  change (Finsupp.single (FreeMonoid.ofList s) (1 : K)) (FreeMonoid.ofList t)=_
  rw [Finsupp.single_apply]
  simp only [Equiv.apply_eq_iff_eq]
@[simp] theorem coeff_monomial_fun (s : List Slot) : coeff (monomial s)=(fun t => if s=t then 1 else 0) := by
  funext t
  exact coeff_monomial s t
@[simp] theorem coeff_one_nil : coeff 1 []=1 := by exact coeff_monomial [] []
@[simp] theorem coeff_one_cons (a : Slot) (s : List Slot) : coeff 1 (a::s)=0 := by
  simpa using coeff_monomial [] (a::s)

@[simp] theorem coeff_atom_mul_nil (a : Slot) (p : A K Slot) : coeff (atom a*p) []=0 := by
  apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
  intro v hv
  have h := congrArg FreeMonoid.toList hv
  simp at h

@[simp] theorem coeff_atom_mul_cons (a b : Slot) (p : A K Slot) (s : List Slot) :
    coeff (atom a*p) (b::s)=if a=b then coeff p s else 0 := by
  by_cases h : a=b
  · subst b
    change (MonoidAlgebra.single (FreeMonoid.of a) 1*p).coeff (FreeMonoid.of a*FreeMonoid.ofList s)=_
    rw [MonoidAlgebra.coeff_single_mul_mul]
    simp only [one_mul]
    rfl
  · rw [if_neg h]
    apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
    intro v hv
    have he := congrArg FreeMonoid.toList hv
    simp only [FreeMonoid.toList_mul,FreeMonoid.toList_of,FreeMonoid.toList_ofList,List.singleton_append] at he
    exact h (List.cons.inj he).1

def collapse : Slot → Slot | .C => .A | a => a

def fills : List Slot → List (List Slot)
  | [] => []
  | a::s => (if a=.C then [Slot.B::s.map collapse] else []) ++ (fills s).map (collapse a :: ·)

def noC (s : List Slot) : Prop := ∀ a∈s,a≠Slot.C

@[simp] theorem noC_nil : noC [] := by simp [noC]
@[simp] theorem noC_cons (a : Slot) (s : List Slot) : noC (a::s) ↔ a≠Slot.C ∧ noC s := by simp [noC]
@[simp] theorem noC_append (s t : List Slot) : noC (s++t) ↔ noC s ∧ noC t := by simp only [noC,List.mem_append,or_imp,forall_and]

@[simp] theorem tau0_atom (a : Slot) : tau0 (atom a)=match a with
    | .A => atom .A+atom .C | .C => atom .C | .B => atom .B := lift_atom _ a

theorem tau0_monomial_coeff (v : List Slot) (hv : noC v) (s : List Slot) :
    coeff (tau0 (monomial v)) s=coeff (monomial v) (s.map collapse) := by
  induction v generalizing s with
  | nil => cases s <;> simp
  | cons a v ih =>
    obtain ⟨ha,hv'⟩ := noC_cons _ _ |>.mp hv
    cases a with
    | C => exact (ha rfl).elim
    | A =>
      cases s with
      | nil => simp [add_mul]
      | cons b s => cases b <;> simp [add_mul,ih hv' s,collapse]
    | B =>
      cases s with
      | nil => simp
      | cons b s => cases b <;> simp [ih hv' s,collapse]

theorem deriv_tau0_monomial_coeff (v : List Slot) (hv : noC v) (s : List Slot) :
    coeff (deriv low (tau0 (monomial v))) s=((fills s).map (coeff (monomial v))).sum := by
  induction v generalizing s with
  | nil =>
    cases s with
    | nil => simp [fills]
    | cons a s =>
      cases a <;> simp [fills,collapse,List.map_map,Function.comp_def]
  | cons a v ih =>
    obtain ⟨ha,hv'⟩ := noC_cons _ _ |>.mp hv
    cases a with
    | C => exact (ha rfl).elim
    | A =>
      cases s with
      | nil => simp [AssociativeElimination.deriv_mul,add_mul,low,fills]
      | cons b s =>
        cases b <;> simp [AssociativeElimination.deriv_mul,add_mul,low,fills,
          ih hv' s,collapse,List.map_map,Function.comp_def]
    | B =>
      cases s with
      | nil => simp [AssociativeElimination.deriv_mul,low,fills]
      | cons b s =>
        cases b <;> simp [AssociativeElimination.deriv_mul,low,fills,
          ih hv' s,collapse,List.map_map,Function.comp_def,tau0_monomial_coeff v hv' s]

theorem deriv_tau0_coeff {p : A K Slot} (hp : p∈space (fun w => noC w.toList)) (s : List Slot) :
    coeff (deriv low (tau0 p)) s=((fills s).map (coeff p)).sum := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    exact deriv_tau0_monomial_coeff w.toList hw s
  | zero =>
    simp only [map_zero]
    change 0=(List.map (fun _ => (0 : K)) (fills s)).sum
    simp
  | add p q _ _ hp hq =>
    simp only [map_add,coeff_add,hp,hq]
    exact (List.sum_map_add ..).symm
  | smul c p _ hp =>
    simp only [map_smul,coeff_smul,hp]
    exact (List.sum_map_mul_left ..).symm

theorem collapse_eq {a : Slot} (ha : a≠Slot.C) : collapse a=a := by cases a <;> simp_all [collapse]
theorem collapse_noC {s : List Slot} (hs : noC s) : s.map collapse=s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨ha,hs'⟩ := (noC_cons a s).mp hs
    simp [collapse_eq ha,ih hs']

theorem fills_noC {s : List Slot} (hs : noC s) : fills s=[] := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨ha,hs'⟩ := (noC_cons a s).mp hs
    simp [fills,ha,ih hs']

theorem fills_prefix (u s : List Slot) (hu : noC u) : fills (u++s)=(fills s).map (u++·) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    obtain ⟨ha,hu'⟩ := (noC_cons a u).mp hu
    simp [fills,ha,collapse_eq ha,ih hu',List.map_map,Function.comp_def]

theorem fills_two (u v : List Slot) (hu : noC u) (hv : noC v) :
    fills (u++[Slot.C,Slot.C]++v)=[u++[Slot.B,Slot.A]++v,u++[Slot.A,Slot.B]++v] := by
  rw [List.append_assoc,fills_prefix u _ hu]
  simp [fills,collapse,collapse_noC hv,fills_noC hv]

theorem fills_three (u v : List Slot) (hu : noC u) (hv : noC v) :
    fills (u++[Slot.C,Slot.C,Slot.C]++v)=
      [u++[Slot.B,Slot.A,Slot.A]++v,u++[Slot.A,Slot.B,Slot.A]++v,u++[Slot.A,Slot.A,Slot.B]++v] := by
  rw [List.append_assoc,fills_prefix u _ hu]
  simp [fills,collapse,collapse_noC hv,fills_noC hv]

def count (a : Slot) (s : List Slot) : ℕ := degree (fun b => if b=a then 1 else 0) (FreeMonoid.ofList s)
@[simp] theorem count_nil (a : Slot) : count a []=0 := rfl
@[simp] theorem count_cons (a b : Slot) (s : List Slot) : count a (b::s)=(if b=a then 1 else 0)+count a s := rfl
@[simp] theorem count_append (a : Slot) (s t : List Slot) : count a (s++t)=count a s+count a t := by
  exact degree_mul _ _ _

theorem noC_count {s : List Slot} (hs : noC s) : count .C s=0 := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨ha,hs'⟩ := (noC_cons a s).mp hs
    simp [ha,ih hs']

theorem low_c_degree (a : Slot) : low a∈homogeneous cCount (cCount a+1) := by
  cases a with
  | A => exact (homogeneous cCount _).zero_mem
  | C => exact (homogeneous cCount _).zero_mem
  | B => exact word_mem (FreeMonoid.of Slot.C) rfl

theorem low_noC_coeff {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (s : List Slot) (hs : 2≤count .C s) : coeff (deriv low p) s=0 := by
  have h0 : p∈homogeneous cCount 0 := by
    apply space_mono ?_ hp
    intro w hw
    exact noC_count hw
  have h1 := deriv_homogeneous low_c_degree h0
  apply coeff_support h1
  change ¬count .C s=0+1
  omega

theorem fills_sum_zero {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) (s : List Slot) (hs : 2≤count .C s) :
    ((fills s).map (coeff p)).sum=0 := by
  have h := congrArg (fun q => coeff q s) he
  rw [map_add,coeff_add,low_noC_coeff hp s hs,zero_add,deriv_tau0_coeff hp s,coeff_zero] at h
  exact h

theorem adjacent_exchange {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) (u v : List Slot) (hu : noC u) (hv : noC v) :
    coeff p (u++[Slot.A,Slot.B]++v)=coeff p (u++[Slot.B,Slot.A]++v) := by
  have hc : 2≤count .C (u++[Slot.C,Slot.C]++v) := by simp; omega
  have h := fills_sum_zero hp he _ hc
  rw [fills_two u v hu hv] at h
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at h
  exact (TwoModule.eq_of_add_zero h).symm

theorem noC_perm {s t : List Slot} (h : s.Perm t) : noC s ↔ noC t := by
  simp only [noC,h.mem_iff]

theorem coefficient_perm {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) {s t : List Slot} (h : s.Perm t) (hs : noC s)
    (u : List Slot) (hu : noC u) : coeff p (u++s)=coeff p (u++t) := by
  induction h generalizing u with
  | nil => rfl
  | @cons a s t h ih =>
    obtain ⟨ha,hs'⟩ := (noC_cons a s).mp hs
    have huv : noC (u++[a]) := (noC_append _ _).mpr ⟨hu,by simpa using ha⟩
    simpa only [List.append_assoc,List.singleton_append] using ih hs' (u++[a]) huv
  | swap a b s =>
    obtain ⟨ha,hbs⟩ := (noC_cons b (a::s)).mp hs
    obtain ⟨hb,hss⟩ := (noC_cons a s).mp hbs
    cases a <;> cases b
    all_goals try first | exact (ha rfl).elim | exact (hb rfl).elim | rfl
    · simpa only [List.append_assoc,List.cons_append,List.nil_append] using (adjacent_exchange hp he u s hu hss).symm
    · simpa only [List.append_assoc,List.cons_append,List.nil_append] using adjacent_exchange hp he u s hu hss
  | @trans s t v h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ hs u hu).trans (ih₂ ((noC_perm h₁).mp hs) u hu)

attribute [local instance] LieRing.ofAssociativeRing

theorem count_list (a : Slot) (s : List Slot) : count a s=s.count a := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    rw [count_cons,ih,List.count_cons]
    split_ifs with h <;> simp_all [Nat.add_comm]

@[simp] theorem count_replicate (a b : Slot) (n : ℕ) : count a (List.replicate n b)=if b=a then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,ih]; split_ifs <;> omega

theorem perm_of_counts {s t : List Slot} (hs : noC s) (ht : noC t)
    (ha : count .A s=count .A t) (hb : count .B s=count .B t) : s.Perm t := by
  apply List.perm_iff_count.mpr
  intro a
  rw [← count_list,← count_list]
  cases a with
  | A => exact ha
  | C => rw [noC_count hs,noC_count ht]
  | B => exact hb

theorem coefficient_eq_counts {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) {s t : List Slot} (hs : noC s) (ht : noC t)
    (ha : count .A s=count .A t) (hb : count .B s=count .B t) : coeff p s=coeff p t := by
  exact coefficient_perm hp he (perm_of_counts hs ht ha hb) hs [] noC_nil

theorem triple_zero {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) (u : List Slot) (hu : noC u) :
    coeff p (u++[Slot.B,Slot.A,Slot.A])=0 := by
  have hc : 2≤count .C (u++[Slot.C,Slot.C,Slot.C]++[]) := by simp
  have h := fills_sum_zero hp he _ hc
  rw [fills_three u [] hu noC_nil] at h
  simp only [List.append_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at h
  have hn1 : noC (u++[Slot.A,Slot.B,Slot.A]) := by simpa using hu
  have hn2 : noC (u++[Slot.A,Slot.A,Slot.B]) := by simpa using hu
  have hn3 : noC (u++[Slot.B,Slot.A,Slot.A]) := by simpa using hu
  have h1 := coefficient_eq_counts hp he hn1 hn3 (by simp) (by simp)
  have h2 := coefficient_eq_counts hp he hn2 hn3 (by simp) (by simp)
  rw [h1,h2,TwoModule.add_self,add_zero] at h
  exact h

theorem coefficient_zero_two_As {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) (s : List Slot) (hs : noC s)
    (ha : 2≤count .A s) (hb : 1≤count .B s) : coeff p s=0 := by
  let u := List.replicate (count .A s-2) Slot.A ++ List.replicate (count .B s-1) Slot.B
  have hu : noC u := by
    intro a ha
    simp only [u,List.mem_append,List.mem_replicate] at ha
    rcases ha with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  have ht : noC (u++[Slot.B,Slot.A,Slot.A]) := by simpa using hu
  have hA : count .A s=count .A (u++[Slot.B,Slot.A,Slot.A]) := by simp [u]; omega
  have hB : count .B s=count .B (u++[Slot.B,Slot.A,Slot.A]) := by simp [u]; omega
  rw [coefficient_eq_counts hp he hs ht hA hB]
  exact triple_zero hp he u hu

theorem residual_zero {p : A K Slot} {m r : ℕ}
    (hp : p∈space (fun w => noC w.toList))
    (hm : p∈homogeneous aCount m) (hr : p∈homogeneous bCount r)
    (hm2 : 2 ≤ m) (hr1 : 1 ≤ r) (he : deriv low (p+tau0 p)=0) : p=0 := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra hn
  have hw : p.coeff w≠0 := hn
  have h1 := mem_space_iff.mp hp w hw
  have h2 := mem_space_iff.mp hm w hw
  have h3 := mem_space_iff.mp hr w hw
  exact hw (coefficient_zero_two_As hp he w.toList h1 (by unfold count; rw [FreeMonoid.ofList_toList]; change 2 ≤ degree aCount w; omega)
    (by unfold count; rw [FreeMonoid.ofList_toList]; change 1 ≤ degree bCount w; omega))

theorem lie_palindrome_zero (q : FreeLieAlgebra K Slot) (s : List Slot)
    (hs : s.reverse=s) (hlen : s.length≠1) : coeff (embed q) s=0 := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg a =>
    rw [embed_of]
    change coeff (monomial [a]) s=0
    rw [coeff_monomial,if_neg]
    intro h
    exact hlen (h ▸ rfl)
  | ha p q hp hq => simp only [map_add,coeff_add,hp,hq,add_zero]
  | hs c p hp => simp only [map_smul,coeff_smul,hp,mul_zero]
  | hl p q _ _ =>
    rw [LieHom.map_lie]
    change coeff (embed p*embed q-embed q*embed p) s=0
    have h : coeff (embed p*embed q) s=coeff (embed q*embed p) s := by
      have hr := WordReversal.rev_coeff (embed p*embed q) (FreeMonoid.ofList s)
      rw [WordReversal.rev_mul,WordReversal.rev_lie_charTwo,WordReversal.rev_lie_charTwo] at hr
      have hs' : (FreeMonoid.ofList s).reverse=FreeMonoid.ofList s := by
        exact congrArg FreeMonoid.ofList hs
      rw [hs'] at hr
      exact hr.symm
    change coeff (embed p*embed q) s-coeff (embed q*embed p) s=0
    exact sub_eq_zero.mpr h

end ResidualKernel

namespace LetterRetraction
open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
variable (P : α → Prop) [DecidablePred P]

omit [DecidablePred P] in
theorem support_of_mem {q : FreeLieAlgebra R α} (hq : q∈sub P) :
    embed q∈space (fun w => ∀ a∈w.toList,P a) := by
  have hm {p q : A R α}
      (hp : p∈space (fun w => ∀ a∈w.toList,P a))
      (hq : q∈space (fun w => ∀ a∈w.toList,P a)) :
      p*q∈space (fun w => ∀ a∈w.toList,P a) := by
    apply mul_mem ?_ hp hq
    intro u v hu hv a ha
    simp only [FreeMonoid.toList_mul,List.mem_append] at ha
    exact ha.elim (hu a) (hv a)
  induction hq using LieSubalgebra.lieSpan_induction with
  | mem q hq =>
    obtain ⟨a,ha,rfl⟩ := hq
    rw [embed_of]
    exact word_mem _ (by simpa using ha)
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (space _).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (space _).smul_mem c hp
  | lie p q _ _ hp hq =>
    rw [LieHom.map_lie]
    exact (space _).sub_mem (hm hp hq) (hm hq hp)

theorem single_letter (a : α) (q : FreeLieAlgebra R α) [DecidableEq α] :
    ∃ c : R,lie (fun b => b=a) q=c • FreeLieAlgebra.of R a := by
  induction q using freeLie_induction with
  | h0 => exact ⟨0,by simp⟩
  | hg b =>
    by_cases h : b=a
    · subst b; exact ⟨1,by simp⟩
    · exact ⟨0,by simp [h]⟩
  | ha p q hp hq =>
    obtain ⟨c,hc⟩ := hp
    obtain ⟨d,hd⟩ := hq
    exact ⟨c+d,by rw [map_add,hc,hd,add_smul]⟩
  | hs r p hp =>
    obtain ⟨c,hc⟩ := hp
    exact ⟨r*c,by rw [map_smul,hc,mul_smul]⟩
  | hl p q hp hq =>
    obtain ⟨c,hc⟩ := hp
    obtain ⟨d,hd⟩ := hq
    exact ⟨0,by simp only [LieHom.map_lie,hc,hd,lie_smul,smul_lie,lie_self,smul_zero,zero_smul]⟩

theorem homogeneous_single_zero [DecidableEq α] (a : α) {q : FreeLieAlgebra R α}
    {wt : α → ℕ} {n : ℕ} (hn : n≠wt a)
    (hq : embed q∈space (fun w => ∀ b∈w.toList,b=a))
    (hw : embed q∈homogeneous wt n) : q=0 := by
  obtain ⟨c,hc⟩ := single_letter a q
  rw [lie_eq_self (fun b => b=a) hq] at hc
  have hdeg : embed q∈homogeneous wt (wt a) := by
    rw [hc,map_smul,embed_of]
    exact (homogeneous wt (wt a)).smul_mem c (word_mem _ (degree_of wt a))
  apply UniversalEmbedding.injective
  rw [map_zero]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra h
  exact hn ((mem_space_iff.mp hw w h).symm.trans (mem_space_iff.mp hdeg w h))

end LetterRetraction

namespace ProjectionKernel
open AssociativeElimination WordGrading RowTwo RowKernel ExactPentagon QuadraticLeading ResidualKernel
attribute [local instance] LieRing.ofAssociativeRing

theorem degree_congr_word {α : Type*} {f g : α → ℕ} (w : FreeMonoid α)
    (h : ∀ a∈w.toList,f a=g a) : degree f w=degree g w := by
  unfold degree
  congr 1
  exact List.map_congr_left h

theorem degree_scale {α : Type*} (f : α → ℕ) (c : ℕ) (w : FreeMonoid α) :
    degree (fun a => c*f a) w=c*degree f w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih => simp only [degree_mul,degree_of,ih,mul_add]

theorem ac_zero (w : FreeMonoid Slot) (hw : degree acCount w=0) :
    ∀ a∈w.toList,a=Slot.B := by
  have he : acCount=(fun a : Slot => if a≠Slot.B then 1 else 0) := by funext a; cases a <;> rfl
  rw [he] at hw
  have h := (degree_indicator_zero (fun a : Slot => a≠Slot.B) w.toList).mp
    (by simpa using hw)
  intro a ha
  exact not_ne_iff.mp (h a ha)

theorem b_zero (w : FreeMonoid Slot) (hw : degree bCount w=0) :
    ∀ a∈w.toList,a≠Slot.B := by
  exact (degree_indicator_zero (fun a : Slot => a=Slot.B) w.toList).mp
    (by rw [FreeMonoid.ofList_toList]; exact hw)

theorem a_from_ac_noC (w : FreeMonoid Slot) (hw : noC w.toList) :
    degree aCount w=degree acCount w := by
  apply degree_congr_word
  intro a ha
  have hn := hw a ha
  cases a <;> simp_all [aCount,acCount,cCount]

theorem higher_single_B {p q : FreeLieAlgebra K Slot} {n r : ℕ}
    (hn : n=r+2) (hn2 : 2<n)
    (hp : embed p∈homogeneous weight n) (hq : embed q∈homogeneous weight n)
    (hh : embed p-embed q∈above bCount (r+1)) : p=q := by
  have hw : embed (p-q)∈homogeneous weight n := by
    simpa only [map_sub] using (homogeneous weight n).sub_mem hp hq
  have hs : embed (p-q)∈space (fun w => ∀ a∈w.toList,a=Slot.B) := by
    apply mem_space
    intro w hc
    have h1 := mem_space_iff.mp hw w hc
    have h2 := mem_space_iff.mp hh w (by simpa using hc)
    have h3 := weight_count w
    exact ac_zero w (by omega)
  exact sub_eq_zero.mp (LetterRetraction.homogeneous_single_zero Slot.B (by simpa only [weight] using (by omega : n≠1)) hs hw)

def yWeight (b : Bool) : ℕ := if b then 1 else 0
def xSlot : Slot → ℕ | .A => 2 | .C => 1 | .B => 0
def ySlot : Slot → ℕ | .A => 0 | .C => 1 | .B => 1

def swap : A K Bool →ₐ[K] A K Bool := algEval (atom true) (atom false)

@[simp] theorem swap_atom (b : Bool) : swap (atom b)=atom (!b) := by
  cases b <;> simp [swap,algEval]

theorem quad_y (a : Slot) : quad (atom a)∈homogeneous yWeight (ySlot a) := by
  have hx : (atom false : A K Bool)∈homogeneous yWeight 0 := word_mem _ rfl
  have hy : (atom true : A K Bool)∈homogeneous yWeight 1 := word_mem _ rfl
  cases a with
  | A =>
    rw [quad,lift_atom]
    have h := homogeneous_mul hx hx
    exact h
  | C =>
    rw [quad,lift_atom]
    have h1 := homogeneous_mul hx hy
    have h2 := homogeneous_mul hy hx
    exact (homogeneous yWeight 1).sub_mem h1 h2
  | B => simpa only [quad,lift_atom,ySlot] using hy

theorem swap_quad_y (a : Slot) : swap (quad (atom a))∈homogeneous yWeight (xSlot a) := by
  have hx : (atom false : A K Bool)∈homogeneous yWeight 0 := word_mem _ rfl
  have hy : (atom true : A K Bool)∈homogeneous yWeight 1 := word_mem _ rfl
  cases a with
  | A =>
    simp only [quad,lift_atom,map_mul,swap_atom]
    have h := homogeneous_mul hy hy
    exact h
  | C =>
    simp only [quad,lift_atom,map_sub,map_mul,swap_atom]
    have h1 := homogeneous_mul hy hx
    have h2 := homogeneous_mul hx hy
    exact (homogeneous yWeight 1).sub_mem h1 h2
  | B => simpa only [quad,lift_atom,swap_atom,xSlot,Bool.not_true] using hx

theorem symmetry_r_two {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {r : ℕ}
    (hp : under p=embed ψ) (hn : p≠0)
    (hs : embed p∈space (fun w => noC w.toList))
    (ha : embed p∈homogeneous acCount 1) (hb : embed p∈homogeneous bCount r)
    (hanti : BaseChangeEquations.antisymmetry ψ=0) : r=2 := by
  have hY : embed p∈homogeneous ySlot r := by
    apply mem_space
    intro w hw
    rw [degree_congr_word w (g:=bCount) ?_]
    · exact mem_space_iff.mp hb w hw
    · intro a ha
      have h := (mem_space_iff.mp hs w hw) a ha
      cases a <;> simp_all [ySlot,bCount]
  have hX : embed p∈homogeneous xSlot 2 := by
    apply mem_space
    intro w hw
    rw [degree_congr_word w (g:=fun a => 2*acCount a) ?_,degree_scale]
    · rw [mem_space_iff.mp ha w hw]
    · intro a ha
      have h := (mem_space_iff.mp hs w hw) a ha
      cases a <;> simp_all [xSlot,acCount,aCount,cCount]
  have h1 := algHom_homogeneous quad ySlot yWeight quad_y hY
  have h2 := algHom_homogeneous (swap.comp quad) xSlot yWeight swap_quad_y hX
  have he : swap (under p)=under p := by
    rw [hp]
    change ψ+BaseChangeEquations.eval BaseChangeEquations.y BaseChangeEquations.x ψ=0 at hanti
    have h := congrArg embed ((TwoModule.eq_of_add_zero hanti).symm)
    simpa only [ResidualKernel.embed_eval,BaseChangeEquations.x,BaseChangeEquations.y,embed_of,swap] using h
  change swap (under p)∈_ at h2
  rw [he] at h2
  by_contra hne
  apply hn
  apply under_injective
  rw [map_zero]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra hw
  exact hne ((mem_space_iff.mp h1 w hw).symm.trans (mem_space_iff.mp h2 w hw))

theorem one_A_two_B_zero {p : FreeLieAlgebra K Slot}
    (hs : embed p∈space (fun w => noC w.toList))
    (ha : embed p∈homogeneous acCount 1) (hb : embed p∈homogeneous bCount 2)
    (he : deriv low (embed p+tau0 (embed p))=0) : p=0 := by
  apply UniversalEmbedding.injective
  rw [map_zero]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra hw
  have hno := mem_space_iff.mp hs w hw
  have hA : count .A w.toList=1 := by
    unfold count
    rw [FreeMonoid.ofList_toList]
    change degree aCount w=1
    rw [a_from_ac_noC w hno]
    exact mem_space_iff.mp ha w hw
  have hB : count .B w.toList=2 := by
    unfold count
    rw [FreeMonoid.ofList_toList]
    exact mem_space_iff.mp hb w hw
  have hc := coefficient_eq_counts hs he hno (t:=[Slot.B,Slot.A,Slot.B]) (by simp)
    (by simpa using hA) (by simpa using hB)
  have hz := lie_palindrome_zero p [Slot.B,Slot.A,Slot.B] (by rfl) (by decide)
  exact hw (hc.trans hz)

theorem leading_projection_kernel_oai {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot}
    {n r : ℕ} (hn : 2<n) (hp : under p=embed ψ)
    (hw : embed p∈homogeneous weight n) (hfilter : embed p∈above bCount r)
    (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hspecial : BaseChangeEquations.special ψ=0)
    (hpent : BaseChangeEquations.pentagon ψ=0)
    (hzero : LetterRetraction.lie (fun a => a≠Slot.A) (LieGrading.piece bCount r p)=0) :
    LieGrading.piece bCount r p=0 := by
  let q := LieGrading.piece bCount r p
  have hq : embed q=WordGrading.piece bCount r (embed p) := LieGrading.embed_piece _ _ _
  have hqw : embed q∈homogeneous weight n := by rw [hq]; exact project_preserves hw
  have hqb : embed q∈homogeneous bCount r := by rw [hq]; exact piece_mem _ _ _
  have hh : embed p-embed q∈above bCount (r+1) := by rw [hq]; exact subtract_piece_above hfilter
  change q=0
  by_contra hqne
  have hen : embed q≠0 := by intro hz; exact hqne (UniversalEmbedding.injective (hz.trans (map_zero _).symm))
  have hex : ∃ w,(embed q).coeff w≠0 := by
    by_contra h
    push Not at h
    exact hen (MonoidAlgebra.ext (Finsupp.ext h))
  obtain ⟨w,hwne⟩ := hex
  let m := degree acCount w
  have hnr : n=2*m+r := by
    have h1 := mem_space_iff.mp hqw w hwne
    have h2 := mem_space_iff.mp hqb w hwne
    have h3 := weight_count w
    omega
  have hqa : embed q∈homogeneous acCount m := leading_ac hqw hqb hnr
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m=0 := by omega
    have hs : embed q∈space (fun w => ∀ a∈w.toList,a=Slot.B) := by
      apply space_mono ?_ hqa
      intro v hv
      exact ac_zero v (hv.trans hm0)
    exact hqne (LetterRetraction.homogeneous_single_zero Slot.B (by change n≠1; omega) hs hqw)
  have hrn : r < n := by omega
  have hno : embed q∈space (fun w => noC w.toList) :=
    LetterRetraction.support_of_mem (fun a => a≠Slot.C)
      (leading_no_C hp hw hrn hfilter hpent hnr hzero)
  have hr : 0 < r := by
    by_contra hr
    have hr0 : r=0 := by omega
    have hs : embed q∈space (fun w => ∀ a∈w.toList,a=Slot.A) := by
      apply mem_space
      intro v hv a hav
      have hb := b_zero v ((mem_space_iff.mp hqb v hv).trans hr0) a hav
      have hc := (mem_space_iff.mp hno v hv) a hav
      cases a <;> simp_all
    exact hqne (LetterRetraction.homogeneous_single_zero Slot.A (by change n≠2; omega) hs hqw)
  have he := leading_equation hr hqb hh (full_equation hp hanti hspecial)
  by_cases hm2 : 2 ≤ m
  · have ha : embed q∈homogeneous aCount m := by
      apply mem_space
      intro v hv
      rw [a_from_ac_noC v (mem_space_iff.mp hno v hv)]
      exact mem_space_iff.mp hqa v hv
    exact hen (residual_zero hno ha hqb hm2 hr he)
  · have hm1 : m=1 := by omega
    have hn2 : n=r+2 := by omega
    have hpq := higher_single_B hn2 hn hw hqw hh
    have hqψ : under q=embed ψ := by rw [← hpq]; exact hp
    have hqa1 : embed q∈homogeneous acCount 1 := by simpa only [hm1] using hqa
    have hr2 := symmetry_r_two hqψ hqne hno hqa1 hqb hanti
    have hqb2 : embed q∈homogeneous bCount 2 := by simpa only [hr2] using hqb
    exact hqne (one_A_two_B_zero hno hqa1 hqb2 he)

end ProjectionKernel

end DeligneDrinfeld

end

end OAI

end

















section
open OAI.DeligneDrinfeld.ProjectionKernel in
theorem solution : ∀ {ψ : FreeLieAlgebra OAI.DeligneDrinfeld.ProjectionKernel.K Bool}
    {p : FreeLieAlgebra OAI.DeligneDrinfeld.ProjectionKernel.K OAI.DeligneDrinfeld.RowTwo.Slot} {n r : ℕ} (hn : 2 < n)
    (hp : OAI.DeligneDrinfeld.QuadraticLeading.under p = OAI.DeligneDrinfeld.AssociativeElimination.embed ψ)
    (hw :
      OAI.DeligneDrinfeld.AssociativeElimination.embed p ∈
        OAI.DeligneDrinfeld.WordGrading.homogeneous OAI.DeligneDrinfeld.ExactPentagon.weight n)
    (hfilter :
      OAI.DeligneDrinfeld.AssociativeElimination.embed p ∈
        OAI.DeligneDrinfeld.WordGrading.above OAI.DeligneDrinfeld.RowKernel.bCount r)
    (hanti : OAI.DeligneDrinfeld.BaseChangeEquations.antisymmetry ψ = 0)
    (hspecial : OAI.DeligneDrinfeld.BaseChangeEquations.special ψ = 0)
    (hpent : OAI.DeligneDrinfeld.BaseChangeEquations.pentagon ψ = 0)
    (hzero :
      (OAI.DeligneDrinfeld.LetterRetraction.lie fun a ↦ a ≠ OAI.DeligneDrinfeld.RowTwo.Slot.A)
          (OAI.DeligneDrinfeld.LieGrading.piece OAI.DeligneDrinfeld.RowKernel.bCount r p) =
        0),
    OAI.DeligneDrinfeld.LieGrading.piece OAI.DeligneDrinfeld.RowKernel.bCount r p = 0 :=
  @OAI.DeligneDrinfeld.ProjectionKernel.leading_projection_kernel_oai
end

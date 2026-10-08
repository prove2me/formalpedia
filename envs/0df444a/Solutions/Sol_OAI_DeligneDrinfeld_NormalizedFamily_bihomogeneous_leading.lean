-- Prove2me | solution 1 for OAI.DeligneDrinfeld.NormalizedFamily.bihomogeneous_leading
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:54:06.88+00:00
-- url     : https://prove2.me/submissions/a268b6d4-c9e8-4e5f-9bc4-4fac1964217a

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid

set_option linter.all false


section

namespace OAI

noncomputable section
namespace DeligneDrinfeld

namespace AssociativeModel

variable {α : Type*}
attribute [local instance] LieRing.ofAssociativeRing

def homogeneous (n : ℕ) : Submodule ℚ (A α) :=
  Submodule.span ℚ {p | ∃ w : FreeMonoid α,
    w.toList.length = n ∧ p = MonoidAlgebra.single w 1}

end AssociativeModel

namespace Elimination
open LieAlgebra
variable {R α : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing

theorem expand_adWord (n : ℕ) (a : α) :
    expand (adWord n a : G R α) = SemiDirectSum.inl action (E n a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [adWord_succ,LieHom.map_lie,expand_X,ih]
    simp only [SemiDirectSum.lie_eq_mk,SemiDirectSum.inl_eq_mk,SemiDirectSum.inr_eq_mk]
    ext <;> simp [action]

end Elimination

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

theorem ad_square (u v : T) : ⁅u,⁅u,v⁆⁆=⁅u*u,v⁆ := by
  simp only [Ring.lie_def,sub_eq_add_neg,CharTwo.neg_eq,mul_add,add_mul,mul_assoc]
  calc
    _ = u*(u*v)+v*(u*u)+(u*(v*u)+u*(v*u)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

abbrev LABC := FreeLieAlgebra F Letter
def la : LABC := FreeLieAlgebra.of F Letter.a
def lc : LABC := FreeLieAlgebra.of F Letter.c
def lb : LABC := FreeLieAlgebra.of F Letter.b
def under : LABC →ₗ⁅F⁆ T := substitution.toLieHom.comp embed
@[simp] theorem under_a : under la=x*x := by simp [under,la,substitution]
@[simp] theorem under_c : under lc=⁅x,y⁆ := by simp [under,lc,substitution]
@[simp] theorem under_b : under lb=y := by simp [under,lb,substitution]

def lieDelta : LieDerivation F LABC LABC :=
  FreeDerivations.extend (fun | .a => 0 | .c => ⁅la,lb⁆ | .b => lc)
@[simp] theorem lieDelta_a : lieDelta la=0 := by simp [lieDelta,la]
@[simp] theorem lieDelta_c : lieDelta lc=⁅la,lb⁆ := by simp [lieDelta,lc]
@[simp] theorem lieDelta_b : lieDelta lb=lc := by simp [lieDelta,lb]

theorem under_delta (p : LABC) : under (lieDelta p)=⁅x,under p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg l =>
    cases l with
    | a => change under (lieDelta la)=⁅x,under la⁆; simp [Ring.lie_def,mul_assoc]
    | c => change under (lieDelta lc)=⁅x,under lc⁆; simp [LieHom.map_lie,ad_square]
    | b => change under (lieDelta lb)=⁅x,under lb⁆; simp
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [add_comm] using (leibniz_lie x (under p) (under q)).symm

def iter (i : ℕ) : LABC := lieDelta^[i] lb
@[simp] theorem iter_zero : iter 0=lb := rfl
@[simp] theorem iter_succ (i : ℕ) : iter (i+1)=lieDelta (iter i) :=
  Function.iterate_succ_apply' _ _ _

theorem under_iter (i : ℕ) : under (iter i)=embed (Elimination.adWord i () : Elimination.G F Unit) := by
  induction i with
  | zero => simp [Elimination.Y,y]
  | succ i ih =>
    rw [iter_succ,under_delta,ih,Elimination.adWord_succ,LieHom.map_lie]
    simp [Elimination.X,x]

def fiberLift : Elimination.F F Unit →ₗ⁅F⁆ LABC :=
  FreeLieAlgebra.lift F (fun (i,_) => iter i)
theorem under_fiberLift (p : Elimination.F F Unit) :
    under (fiberLift p)=embed (Elimination.collapseFiber p) := by
  have h : under.comp fiberLift = (embed : Elimination.G F Unit →ₗ⁅F⁆ T).comp Elimination.collapseFiber := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨i,u⟩
    cases u
    simp [fiberLift,Elimination.collapseFiber,under_iter]
  exact LieHom.congr_fun h p

def polynomial (p : Elimination.G F Unit) : LABC := fiberLift (Elimination.expand p).left

theorem decompose (p : Elimination.G F Unit) :
    embed p=under (polynomial p)+(Elimination.expand p).right • x := by
  rw [polynomial,under_fiberLift]
  have hx : embed (Elimination.X : Elimination.G F Unit)=x := by simp [Elimination.X,x]
  rw [← hx,← map_smul,← map_add]
  conv_lhs => rw [← Elimination.collapse_expand p]
  rfl

theorem under_injective : Function.Injective under := by
  intro p q h
  exact UniversalEmbedding.injective (substitution_injective h)

theorem represent_unique (p : Elimination.G F Unit)
    (hp : (Elimination.expand p).right=0) : ∃! q : LABC, under q=embed p := by
  refine ⟨polynomial p,?_,?_⟩
  · simpa only [hp,zero_smul,add_zero] using (decompose p).symm
  · intro q hq
    apply under_injective
    rw [hq,decompose,hp,zero_smul,add_zero]

def homogeneous (n : ℕ) : Submodule F (Elimination.G F Unit) :=
  Submodule.span F {p | ∃ t : UniversalEmbedding.Tree (Option Unit), t.leaves.length=n ∧ t.eval=p}

theorem homogeneous_trace_zero {p : Elimination.G F Unit} {n : ℕ}
    (hn : 1<n) (hp : p∈homogeneous n) : (Elimination.expand p).right=0 := by
  have hm : ∀ t : UniversalEmbedding.Tree (Option Unit), 1<t.leaves.length →
      (Elimination.expand (t.eval : Elimination.G F Unit)).right=0 := by
    intro t ht
    cases t with
    | leaf l => simp [UniversalEmbedding.Tree.leaves] at ht
    | node t u =>
      simp [UniversalEmbedding.Tree.eval,LieHom.map_lie,Ring.lie_def,mul_comm]
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨t,ht,rfl⟩ := hp; exact hm t (ht ▸ hn)
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul r p _ hp => simp [hp]

theorem homogeneous_representation {p : Elimination.G F Unit} {n : ℕ}
    (hn : 1<n) (hp : p∈homogeneous n) : ∃! q : LABC, under q=embed p :=
  represent_unique p (homogeneous_trace_zero hn hp)

end QuadraticAlphabet

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

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

theorem below_mul {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈below wt n) (hq : q∈below wt m) : p*q∈below wt (n+m) :=
  mul_mem (by intros; simp_all; omega) hp hq

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
theorem homogeneous_below {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : p∈below wt n := space_mono (by intros; omega) hp

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

namespace TensorGrading
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β : Type*} [CommRing R]
abbrev V := A R α ⊗[R] A R β
def space (P : FreeMonoid α → FreeMonoid β → Prop) : Submodule R (V (R:=R) (α:=α) (β:=β)) :=
  Submodule.span R {z | ∃ u v,P u v ∧ z=word u⊗ₜ word v}

def homogeneous (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => degree wa u+degree wb v=n)

variable {wa : α → ℕ} {wb : β → ℕ} {δ : β → α → A R α}

variable {δ₀ : β → α → A R α}

end TensorGrading

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

theorem algHom_below (hf : ∀ a,f (atom a)∈below wb (wa a))
    {n : ℕ} {p : A R α} (hp : p∈below wa n) : f p∈below wb n := by
  have hw (w : FreeMonoid α) : f (word w)∈below wb (degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,map_one,degree_one]
      exact word_mem (1 : FreeMonoid β) (by simp)
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      exact below_mul (hf a) ih
  apply map_space f.toLinearMap _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; change degree wa w≤n at hn; change degree wb v≤degree wa w at hv; omega) (hw w)

end WordGrading

namespace RowTwo
open AssociativeElimination WordGrading WeightedDeletion
instance : Fintype Slot := ⟨{.A,.C,.B}, by intro x; cases x <;> simp⟩
open Letter Slot

end RowTwo

namespace RowKernel
open AssociativeElimination WordGrading WeightedDeletion RowTwo
open RowTwo.Letter RowTwo.Slot

def aCount (a : Slot) : ℕ := if a=.A then 1 else 0
def cCount (a : Slot) : ℕ := if a=.C then 1 else 0

def acCount (k : Slot) : ℕ := aCount k+cCount k

end RowKernel

namespace LetterRetraction
open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
variable (P : α → Prop) [DecidablePred P]

def assoc : A R α →ₐ[R] A R α := lift (fun a => if P a then atom a else 0)

@[simp] theorem assoc_atom (a : α) : assoc (R:=R) P (atom a)=if P a then atom a else 0 := by
  simp [assoc]

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

end LetterRetraction

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
namespace ExactPentagon
open AssociativeElimination RowTwo RowKernel LeadingRows PolynomialOrdering
open SourceEnveloping SourceModel
attribute [local instance] LieRing.ofAssociativeRing

def algEval {U : Type*} [Ring U] [Algebra K U] (x y : U) : A K Bool →ₐ[K] U :=
  lift (fun i => if i then y else x)

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

theorem piece_eq_self_iff (wt : α → ℕ) (n : ℕ) (p : A R α) :
    piece wt n p=p ↔ p∈homogeneous wt n := by
  constructor
  · intro h; rw [← h]; exact piece_mem wt n p
  · exact project_eq_self

theorem project_degree_homogeneous (wt : α → ℕ) (P : ℕ → Prop) [DecidablePred P]
    {k : ℕ} {p : A R α} (hp : p∈homogeneous wt k) :
    project (fun w => P (degree wt w)) p=if P k then p else 0 := by
  by_cases h : P k
  · rw [if_pos h]
    exact project_eq_self (space_mono (by intro w hw; exact hw ▸ h) hp)
  · rw [if_neg h]
    exact project_eq_zero hp (by intro w hw; simpa only [hw] using h)

theorem algHom_project (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (P : ℕ → Prop) [DecidablePred P]
    (p : A R α) :
    f (project (fun w => P (degree wa w)) p)=project (fun w => P (degree wb w)) (f p) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change f (project _ (word w))=project _ (f (word w))
    rw [project_word,project_degree_homogeneous wb P
      (algHom_homogeneous f wa wb hf (word_mem w rfl))]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem algHom_piece (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (n : ℕ) (p : A R α) :
    f (piece wa n p)=piece wb n (f p) := algHom_project f wa wb hf (fun k => k=n) p

theorem homogeneous_reflect (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (hi : Function.Injective f)
    {n : ℕ} {p : A R α} (hp : f p∈homogeneous wb n) : p∈homogeneous wa n := by
  apply (piece_eq_self_iff wa n p).mp
  apply hi
  rw [algHom_piece f wa wb hf,piece_homogeneous hp,if_pos rfl]

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

namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

theorem homogeneous_iff {wt : α → ℕ} {n : ℕ} {p : FreeLieAlgebra R α} :
    p∈homogeneousLie wt n ↔ embed p∈homogeneous wt n := by
  constructor
  · exact homogeneousLie_embed
  · intro hp
    have h : piece wt n p=p := by
      apply UniversalEmbedding.injective
      rw [embed_piece]
      exact WordGrading.project_eq_self hp
    rw [← h]
    exact (piece_spec wt n p).1

end LieGrading
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

theorem quad_transport_inv : (renameAssoc bitOption.symm).comp QuadraticAlphabet.substitution=
    quad.comp (renameAssoc letters.symm) := by
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

theorem tree_degree_length {α : Type*} (t : UniversalEmbedding.Tree α) :
    LieGrading.treeDegree (fun _ : α => 1) t=t.leaves.length := by
  simp [LieGrading.treeDegree]

theorem representation {ψ : FreeLieAlgebra K Bool} {n : ℕ} (hn : 1<n)
    (hψ : embed ψ∈homogeneous (fun _ => 1) n) :
    ∃! p : FreeLieAlgebra K Slot,under p=embed ψ := by
  have ho : embed (rename bitOption ψ)∈homogeneous (fun _ => 1) n := by
    rw [rename_embed]
    apply algHom_homogeneous (renameAssoc bitOption) (fun _ => 1) (fun _ => 1) ?_ hψ
    intro a
    rw [renameAssoc_atom]
    exact word_mem (FreeMonoid.of (bitOption a)) (degree_of _ _)
  have hl : rename bitOption ψ∈QuadraticAlphabet.homogeneous n := by
    have h := LieGrading.homogeneous_iff.mpr ho
    apply (show (LieGrading.homogeneousLie (fun _ : Option Unit => 1) n :
        Submodule K (FreeLieAlgebra K (Option Unit))) ≤ QuadraticAlphabet.homogeneous n from ?_) h
    apply Submodule.span_le.mpr
    rintro p ⟨t,ht,rfl⟩
    exact Submodule.subset_span ⟨t,(tree_degree_length t) ▸ ht,rfl⟩
  obtain ⟨p,hp,_⟩ := QuadraticAlphabet.homogeneous_representation hn hl
  refine ⟨rename letters.symm p,?_,fun q hq => under_injective (hq.trans ?_)⟩
  · change quad (embed (rename letters.symm p))=embed ψ
    rw [rename_embed]
    rw [← AlgHom.comp_apply,← quad_transport_inv,AlgHom.comp_apply]
    change renameAssoc bitOption.symm (QuadraticAlphabet.under p)=embed ψ
    rw [hp,rename_embed,assoc_retract bitOption bitOption.symm bitOption.left_inv]
  · change embed ψ=quad (embed (rename letters.symm p))
    rw [rename_embed,← AlgHom.comp_apply,← quad_transport_inv,AlgHom.comp_apply]
    change embed ψ=renameAssoc bitOption.symm (QuadraticAlphabet.under p)
    rw [hp,rename_embed,assoc_retract bitOption bitOption.symm bitOption.left_inv]

theorem quad_homogeneous (a : Slot) : quad (atom a)∈homogeneous (fun _ => 1) (weight a) := by
  have hx : (atom false : A K Bool)∈homogeneous (fun _ => 1) 1 := word_mem _ rfl
  have hy : (atom true : A K Bool)∈homogeneous (fun _ => 1) 1 := word_mem _ rfl
  cases a with
  | A =>
    rw [quad,lift_atom]
    have h := homogeneous_mul hx hx
    exact h
  | C =>
    rw [quad,lift_atom]
    have h1 := homogeneous_mul hx hy
    have h2 := homogeneous_mul hy hx
    exact (homogeneous _ 2).sub_mem h1 h2
  | B => simpa only [quad,lift_atom,weight] using hy

theorem representation_weight {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n : ℕ}
    (hψ : embed ψ∈homogeneous (fun _ => 1) n) (hp : under p=embed ψ) :
    embed p∈homogeneous weight n := by
  apply homogeneous_reflect quad weight (fun _ => 1) quad_homogeneous quad_injective
  change under p∈_
  rw [hp]
  exact hψ

theorem weight_count (w : FreeMonoid Slot) : degree weight w=2*degree acCount w+degree bCount w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    simp only [degree_mul,degree_of,ih]
    cases a <;> simp [weight,acCount,bCount,aCount,cCount] <;> omega

end QuadraticLeading

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

end WordGrading

namespace ResidualKernel

section
open AssociativeElimination UniversalEmbedding WordGrading RowTwo RowKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing

def low : Slot → A K Slot | .B => atom .C | _ => 0
def high : Slot → A K Slot | .C => atom .A*atom .B-atom .B*atom .A | _ => 0
def delta : Slot → A K Slot := fun a => low a+high a

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

theorem embed_eval (a b : FreeLieAlgebra K Bool) (ψ : FreeLieAlgebra K Bool) :
    embed (BaseChangeEquations.eval a b ψ)=algEval (embed a) (embed b) (embed ψ) := by
  rw [AssociativeEvaluation.map_eval,algEval,AssociativeEvaluation.lift_embed]
  rfl

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

end

open AssociativeElimination WordGrading RowTwo RowKernel

attribute [local instance] LieRing.ofAssociativeRing

end ResidualKernel

namespace ProjectionKernel
open AssociativeElimination WordGrading RowTwo RowKernel ExactPentagon QuadraticLeading ResidualKernel
attribute [local instance] LieRing.ofAssociativeRing

theorem degree_congr_word {α : Type*} {f g : α → ℕ} (w : FreeMonoid α)
    (h : ∀ a∈w.toList,f a=g a) : degree f w=degree g w := by
  unfold degree
  congr 1
  exact List.map_congr_left h

def xSlot : Slot → ℕ | .A => 2 | .C => 1 | .B => 0

def swap : A K Bool →ₐ[K] A K Bool := algEval (atom true) (atom false)

@[simp] theorem swap_atom (b : Bool) : swap (atom b)=atom (!b) := by
  cases b <;> simp [swap,algEval]

end ProjectionKernel

namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]

theorem above_reflect (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (hi : Function.Injective f)
    {n : ℕ} {p : A R α} (hp : f p∈above wb n) : p∈above wa n := by
  have h1 := algHom_project f wa wb hf (fun k => n≤k) p
  rw [project_eq_self hp] at h1
  have h2 := hi h1
  rw [← h2]
  exact project_mem _ _

end WordGrading
namespace EliminationGraded
open AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

theorem collapse_embed (p : Elimination.F R α) :
    collapse (embed p)=embed (Elimination.collapseFiber p) := by
  have h : collapse.toLieHom.comp embed=(embed : Elimination.G R α →ₗ⁅R⁆ A R (Option α)).comp Elimination.collapseFiber := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨n,a⟩
    simp [Elimination.collapseFiber]
  exact LieHom.congr_fun h p

theorem operator_collapse (p : A R (ℕ×α)) : operator (collapse p)=leftMul p := by
  have h : operator.comp collapse=(leftMul : A R (ℕ×α) →ₐ[R] Module.End R (A R (ℕ×α))) := by
    apply hom_ext
    rintro ⟨n,a⟩
    simp only [AlgHom.comp_apply,collapse_atom,operator_embed,Elimination.expand_adWord,representation_inl]
    simp [Elimination.E]
  exact AlgHom.congr_fun h p

theorem extract_collapse (p : A R (ℕ×α)) : extract (collapse p)=p := by
  change operator (collapse p) 1=p
  rw [operator_collapse,leftMul_apply,mul_one]

theorem collapse_injective : Function.Injective (collapse : A R (ℕ×α) →ₐ[R] A R (Option α)) :=
  Function.LeftInverse.injective extract_collapse

theorem adWord_degree (n : ℕ) (a : α) (wt : Option α → ℕ) :
    embed (Elimination.adWord n a : Elimination.G R α)∈homogeneous wt (n*wt none+wt (some a)) := by
  induction n with
  | zero =>
    simp only [Elimination.adWord_zero,Elimination.Y,embed_of,zero_mul,zero_add]
    exact word_mem _ rfl
  | succ n ih =>
    rw [Elimination.adWord_succ,LieHom.map_lie]
    have hx : embed (Elimination.X : Elimination.G R α)∈homogeneous wt (wt none) := by
      rw [Elimination.X,embed_of]
      exact word_mem _ (degree_of wt _)
    have h1 := homogeneous_mul hx ih
    have h2 := homogeneous_mul ih hx
    change embed Elimination.X*embed (Elimination.adWord n a)-embed (Elimination.adWord n a)*embed Elimination.X∈_
    have he : wt none+(n*wt none+wt (some a))=(n+1)*wt none+wt (some a) := by
      simp only [Nat.add_mul,one_mul]; omega
    rw [← he]
    exact (homogeneous wt _).sub_mem h1 (by simpa only [Nat.add_comm] using h2)

theorem embed_decompose (p : Elimination.G R α) :
    embed p=collapse (embed (Elimination.expand p).left)+(Elimination.expand p).right • atom none := by
  rw [collapse_embed]
  have hx : atom none=embed (Elimination.X : Elimination.G R α) := (embed_of none).symm
  rw [hx,← map_smul,← map_add]
  exact congrArg embed (Elimination.collapse_expand p).symm

theorem trace_homogeneous_zero {p : Elimination.G R α} {wt : Option α → ℕ} {n : ℕ}
    (hn : n≠wt none) (hp : embed p∈homogeneous wt n) : (Elimination.expand p).right=0 := by
  have hL : p∈LieGrading.homogeneousLie wt n := LieGrading.homogeneous_iff.mpr hp
  clear hp
  change p∈Submodule.span R {p | ∃ t : UniversalEmbedding.Tree (Option α),LieGrading.treeDegree wt t=n ∧ t.eval=p} at hL
  induction hL using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,ht,rfl⟩ := hp
    cases t with
    | leaf a =>
      cases a with
      | none => exact (hn (ht.symm)).elim
      | some a => simp [Tree.eval,Elimination.expand]
    | node t u => simp [Tree.eval,LieHom.map_lie,Ring.lie_def,mul_comm]
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul c p _ hp => simp [hp]

end EliminationGraded

namespace OreShift

section
open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]
local instance {α : Type*} [CharP R 2] : CharP (A R α) 2 :=
  charP_of_injective_ringHom (show Function.Injective (algebraMap R (A R α)) from by
    intro r s h
    have hc := congrArg (fun p : A R α => p.coeff 1) h
    simpa using hc) 2
abbrev S (R : Type*) [CommRing R] := A R Bool

def C : S R := atom false
def B : S R := atom true
def wt (b : Bool) : ℕ := if b then 1 else 0

def D : S R →ₗ[R] S R := deriv (fun b => if b then C else 0)
@[simp] theorem D_C : D (C : S R)=0 := by simp [D,C]
@[simp] theorem D_B : D (B : S R)=C := by simp [D,B]
@[simp] theorem D_one : D (1 : S R)=0 := deriv_one _
theorem D_mul (p q : S R) : D (p*q)=D p*q+p*D q := deriv_mul _ _ _
theorem D_lie (p q : S R) : D ⁅p,q⁆=⁅D p,q⁆+⁅p,D q⁆ := deriv_lie _ _ _

theorem D_square [CharP R 2] (p : S R) : D (D p)=0 := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp
  | ha b => cases b <;> simp [D,C]
  | hadd p q hp hq => simp [hp,hq]
  | hs c p hp => simp [hp]
  | hm p q hp hq =>
    rw [D_mul,map_add,D_mul,D_mul,hp,hq]
    simp only [zero_mul,mul_zero,zero_add,add_zero,CharTwo.add_self_eq_zero]

theorem above_zero (p : S R) : p∈above wt 0 := by
  exact mem_space (by intro w _; exact Nat.zero_le _)
theorem above_lie {a b : ℕ} {p q : S R} (hp : p∈above wt a) (hq : q∈above wt b) :
    ⁅p,q⁆∈above wt (a+b) := by
  change p*q-q*p∈_
  exact (above wt _).sub_mem (above_mul hp hq) (by simpa only [Nat.add_comm] using above_mul hq hp)

def P (s : S R) : ℕ → S R
  | 0 => C
  | n+1 => ⁅B+s,P s n⁆

@[simp] theorem P_zero (s : S R) : P s 0=C := rfl
@[simp] theorem P_succ (s : S R) (n : ℕ) : P s (n+1)=⁅B+s,P s n⁆ := rfl

variable {s : S R}

@[simp] theorem D_F (hs : D s=0) : D (B+s)=C := by rw [map_add,D_B,hs,add_zero]

theorem P_one (hc : ⁅(C : S R),s⁆=0) : P s 1=⁅(B : S R),C⁆ := by
  rw [P_succ,P_zero,add_lie]
  have hsc : ⁅s,(C : S R)⁆=0 := by rw [←lie_skew,hc,neg_zero]
  rw [hsc,add_zero]

theorem P_above (hc : ⁅(C : S R),s⁆=0) (n : ℕ) : P s (n+1)∈above wt 1 := by
  induction n with
  | zero =>
    rw [P_one hc]
    have hb : (B : S R)∈above wt 1 := word_mem _ (by simp [degree_of,wt])
    have hh := above_lie hb (above_zero (C : S R))
    simpa only [Nat.add_zero] using hh
  | succ n ih =>
    rw [P_succ]
    have h := above_lie (above_zero (B+s)) ih
    exact h

theorem DP_one (hc : ⁅(C : S R),s⁆=0) : D (P s 1)=0 := by rw [P_one hc,D_lie,D_B,D_C,lie_self,lie_zero,add_zero]

theorem DP_above (hs : D s=0) (hc : ⁅(C : S R),s⁆=0) (n : ℕ) : D (P s n)∈above wt 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => rw [DP_one hc]; exact (above wt 1).zero_mem
    | succ n =>
      rw [P_succ,D_lie,D_F hs]
      have h1 := above_lie (above_zero (C : S R)) (P_above hc n)
      have h2 := above_lie (above_zero (B+s)) ih
      exact (above wt 1).add_mem h1 h2

theorem D_lie_square [CharP R 2] (hs : D s=0) (p : S R) : D ⁅B+s,⁅B+s,p⁆⁆=⁅⁅(C : S R),B+s⁆,p⁆+⁅B+s,⁅B+s,D p⁆⁆ := by
  rw [D_lie,D_lie,D_F hs,lie_add]
  have he := leibniz_lie (B+s) (C : S R) p
  have hsk : ⁅B+s,C⁆=⁅(C : S R),B+s⁆ := by rw [←lie_skew,CharTwo.neg_eq]
  rw [hsk] at he
  rw [he]
  have hz : ⁅(C : S R),⁅B+s,p⁆⁆+⁅(C : S R),⁅B+s,p⁆⁆=0 := CharTwo.add_self_eq_zero _
  calc
    _ = ⁅⁅(C : S R),B+s⁆,p⁆+⁅B+s,⁅B+s,D p⁆⁆+
        (⁅(C : S R),⁅B+s,p⁆⁆+⁅(C : S R),⁅B+s,p⁆⁆) := by abel
    _ = _ := by rw [hz,add_zero]

theorem DP_even [CharP R 2] (hs : D s=0) (hc : ⁅(C : S R),s⁆=0) (n : ℕ) : D (P s (2*n+1))∈above wt 2 := by
  induction n with
  | zero => rw [Nat.mul_zero,Nat.zero_add,DP_one hc]; exact (above wt 2).zero_mem
  | succ n ih =>
    have hn : 2*(n+1)+1=(2*n+1)+1+1 := by omega
    rw [hn,P_succ,P_succ,D_lie_square hs]
    have hcb : ⁅(C : S R),B+s⁆=⁅(C : S R),B⁆ := by rw [lie_add,hc,add_zero]
    rw [hcb]
    have hB : (B : S R)∈above wt 1 := word_mem _ (by simp [degree_of,wt])
    have h1 := above_lie (above_lie (above_zero (C : S R)) hB) (P_above hc (2*n))
    have h2 := above_lie (above_zero (B+s)) (above_lie (above_zero (B+s)) ih)
    exact (above wt 2).add_mem h1 h2

end

open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

def indexWt (a : ℕ×Unit) : ℕ := if a.1%2=0 then 1 else 0

def factor (s : S R) : ℕ → Module.End R (S R)
  | 0 => D
  | n+1 => leftMul (P s n)

def operators (s : S R) : A R (ℕ×Unit) →ₐ[R] Module.End R (S R) := lift (fun a => factor s a.1)
def constant (s : S R) : A R (ℕ×Unit) →ₗ[R] S R :=
  (LinearMap.applyₗ 1).comp (operators s).toLinearMap

@[simp] theorem constant_one (s : S R) : constant s 1=1 := by simp [constant]
@[simp] theorem constant_atom_mul (s : S R) (n : ℕ) (p : A R (ℕ×Unit)) :
    constant s (atom (n,())*p)=factor s n (constant s p) := by
  simp [constant,operators,Module.End.mul_apply]

variable {s : S R} [CharP R 2]
theorem factor_bounds (hs : D s=0) (hc : ⁅(C : S R),s⁆=0) (n : ℕ) :
    P s n∈above wt (indexWt (n+1,())) ∧
    D (P s n)∈above wt (indexWt (n+1,())+1) := by
  by_cases he : (n+1)%2=0
  · have hn : n=n/2*2+1 := by omega
    have hP := P_above hc (n/2*2)
    have hD := DP_even hs hc (n/2)
    have hn' : n=2*(n/2)+1 := by omega
    constructor
    · simpa only [←hn,indexWt,if_pos he] using hP
    · simpa only [←hn',indexWt,if_pos he] using hD
  · simp only [indexWt,if_neg he,zero_add]
    exact ⟨above_zero _,DP_above hs hc n⟩

theorem word_bound (hs : D s=0) (hc : ⁅(C : S R),s⁆=0) (w : FreeMonoid (ℕ×Unit)) :
    constant s (word w)∈above wt (degree indexWt w) ∧
    D (constant s (word w))∈above wt (degree indexWt w+1) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    simp only [word_one,constant_one,D_one,degree_one,Nat.zero_add]
    exact ⟨above_zero _,(above wt 1).zero_mem⟩
  | of_mul a w ih =>
    obtain ⟨n,u⟩ := a
    cases u
    rw [word_mul,word_of,constant_atom_mul,degree_mul,degree_of]
    cases n with
    | zero =>
      change D (constant s (word w))∈above wt (1+degree indexWt w) ∧
        D (D (constant s (word w)))∈above wt (1+degree indexWt w+1)
      constructor
      · simpa only [Nat.add_comm] using ih.2
      · rw [D_square]; exact (above wt _).zero_mem
    | succ n =>
      simp only [factor,leftMul_apply]
      obtain ⟨hp,hd⟩ := factor_bounds hs hc n
      constructor
      · exact above_mul hp ih.1
      · rw [D_mul]
        have h1 := above_mul hd ih.1
        have h2 := above_mul hp ih.2
        apply (above wt (indexWt (n+1,())+degree indexWt w+1)).add_mem
        · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
        · simpa only [Nat.add_assoc] using h2

theorem constant_bound (hs : D s=0) (hc : ⁅(C : S R),s⁆=0) {r : ℕ} {p : A R (ℕ×Unit)}
    (hp : p∈above indexWt r) : constant s p∈above wt r := by
  apply map_space (constant s) _ ?_ hp
  intro w hw
  exact space_mono (by intro v hv; exact hw.trans hv) (word_bound hs hc w).1

end OreShift

namespace EvenIndex

section
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon AlphabetTransport
attribute [local instance] LieRing.ofAssociativeRing

theorem map_lie {R α β : Type*} [CommRing R] (f : A R α →ₐ[R] A R β) (p q : A R α) :
    f ⁅p,q⁆=⁅f p,f q⁆ := by simp only [Ring.lie_def,map_sub,map_mul]

def idx (a : ℕ×Unit) : ℕ×Bool := (a.1/2,decide (a.1%2=1))
def unidx (a : ℕ×Bool) : ℕ×Unit := (2*a.1+if a.2 then 1 else 0,())

theorem idx_left : Function.LeftInverse unidx idx := by
  rintro ⟨n,u⟩
  cases u
  dsimp [idx,unidx]
  split_ifs <;> simp_all only [decide_eq_true_eq] <;> congr <;> omega

def intoABC : A K (ℕ×Unit) →ₐ[K] A K Slot :=
  (renameAssoc abc).comp (EliminationGraded.collapse.comp (renameAssoc idx))

theorem intoABC_injective : Function.Injective intoABC := by
  exact (assoc_injective abc abc.symm abc.left_inv).comp
    (EliminationGraded.collapse_injective.comp (assoc_injective idx unidx idx_left))

@[simp] theorem intoABC_atom (n : ℕ) : intoABC (atom (n,()))=
    renameAssoc abc (embed (Elimination.adWord (n/2) (decide (n%2=1)) : Elimination.G K Bool)) := by
  simp [intoABC,idx]

def evenWt (a : ℕ×Unit) : ℕ := if a.1%2=0 then 1 else 0

theorem intoABC_degree (a : ℕ×Unit) : intoABC (atom a)∈homogeneous bCount (evenWt a) := by
  obtain ⟨n,u⟩ := a
  cases u
  rw [intoABC_atom]
  have h := EliminationGraded.adWord_degree (R:=K) (n/2) (decide (n%2=1)) (bCount ∘ abc)
  have hg : ∀ a : Option Bool,renameAssoc (R:=K) abc (atom a)∈homogeneous bCount ((bCount ∘ abc) a) := by
    intro a
    rw [renameAssoc_atom]
    exact word_mem _ (degree_of _ _)
  have hh := algHom_homogeneous (renameAssoc abc) (bCount ∘ abc) bCount hg h
  have he : n/2*(bCount ∘ abc) none+(bCount ∘ abc) (some (decide (n%2=1)))=evenWt (n,()) := by
    simp only [Function.comp_apply,abc,bCount,evenWt]
    by_cases hn : n%2=1
    · simp [hn]
    · have hn0 : n%2=0 := by omega
      simp [hn0]
  exact he ▸ hh

theorem intoABC_atom_zero : intoABC (atom (0,()))=atom Slot.B := by
  simp [intoABC_atom,Elimination.Y,abc]
theorem intoABC_atom_one : intoABC (atom (1,()))=atom Slot.C := by
  simp [intoABC_atom,Elimination.Y,abc]
theorem intoABC_atom_two (n : ℕ) : intoABC (atom (n+2,()))=⁅(atom Slot.A : A K Slot),intoABC (atom (n,()))⁆ := by
  have hd : (n+2)/2=n/2+1 := by omega
  have hm : (n+2)%2=n%2 := by omega
  rw [intoABC_atom,intoABC_atom,hd,hm]
  rw [Elimination.adWord_succ,LieHom.map_lie]
  change renameAssoc abc ⁅embed (Elimination.X : Elimination.G K Bool),_⁆=_
  rw [map_lie]
  simp [Elimination.X,abc]

theorem input_atom_zero : input (atom (0,()))=atom true := by
  simp [input_atom,Elimination.Y,bitOption]
theorem input_atom_succ (n : ℕ) : input (atom (n+1,()))=⁅(atom false : A K Bool),input (atom (n,()))⁆ := by
  rw [input_atom,input_atom,Elimination.adWord_succ,LieHom.map_lie]
  rw [map_lie]
  simp [Elimination.X,bitOption]

theorem quad_intoABC : quad.comp intoABC=input := by
  apply hom_ext
  rintro ⟨n,u⟩
  cases u
  induction n using Nat.twoStepInduction with
  | zero => rw [AlgHom.comp_apply,intoABC_atom_zero,input_atom_zero]; simp only [quad,lift_atom]
  | one => rw [AlgHom.comp_apply,intoABC_atom_one,input_atom_succ,input_atom_zero]; simp only [quad,lift_atom,Ring.lie_def]
  | more n ih _ =>
    simp only [AlgHom.comp_apply] at ih ⊢
    rw [intoABC_atom_two,map_lie,ih,input_atom_succ,input_atom_succ]
    simp only [quad,lift_atom]
    change ⁅(atom false : A K Bool)*atom false,input (atom (n,()))⁆=⁅atom false,⁅atom false,_⁆⁆
    simp only [Ring.lie_def,sub_eq_add_neg,CharTwo.neg_eq,mul_add,add_mul,mul_assoc]
    symm
    calc
      _ = atom false*(atom false*input (atom (n,())))+input (atom (n,()))*(atom false*atom false)+
          (atom false*(input (atom (n,()))*atom false)+atom false*(input (atom (n,()))*atom false)) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

def fiber (ψ : FreeLieAlgebra K Bool) : A K (ℕ×Unit) :=
  embed (Elimination.expand (rename bitOption ψ)).left

theorem input_fiber {ψ : FreeLieAlgebra K Bool} {n : ℕ} (hn : 1 < n)
    (hψ : embed ψ∈homogeneous (fun _ => 1) n) : input (fiber ψ)=embed ψ := by
  have ho : embed (rename bitOption ψ)∈homogeneous (fun _ => 1) n := by
    rw [rename_embed]
    apply algHom_homogeneous (renameAssoc bitOption) (fun _ => 1) (fun _ => 1) ?_ hψ
    intro b
    rw [renameAssoc_atom]
    exact word_mem _ (degree_of _ _)
  have hz := EliminationGraded.trace_homogeneous_zero (by omega) ho
  have hd := EliminationGraded.embed_decompose (rename bitOption ψ)
  rw [hz,zero_smul,add_zero] at hd
  have h := congrArg (renameAssoc bitOption.symm) hd
  rw [rename_embed,assoc_retract bitOption bitOption.symm bitOption.left_inv] at h
  exact h.symm

theorem intoABC_fiber {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n : ℕ}
    (hn : 1 < n) (hψ : embed ψ∈homogeneous (fun _ => 1) n) (hp : under p=embed ψ) :
    intoABC (fiber ψ)=embed p := by
  apply quad_injective
  calc
    quad (intoABC (fiber ψ)) = input (fiber ψ) := AlgHom.congr_fun quad_intoABC _
    _ = embed ψ := input_fiber hn hψ
    _ = quad (embed p) := hp.symm

theorem termwise_bound {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r : ℕ}
    (hn : 1 < n) (hψ : embed ψ∈homogeneous (fun _ => 1) n) (hp : under p=embed ψ)
    (hr : embed p∈above bCount r) : fiber ψ∈above evenWt r := by
  apply above_reflect intoABC evenWt bCount intoABC_degree intoABC_injective
  rw [intoABC_fiber hn hψ hp]
  exact hr

end

open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon AlphabetTransport ProjectionKernel
attribute [local instance] LieRing.ofAssociativeRing

def xWeight (b : Bool) : ℕ := if b then 0 else 1
def swappedInput : A K (ℕ×Unit) →ₐ[K] A K Bool := swap.comp input

theorem swappedInput_degree (a : ℕ×Unit) :
    swappedInput (atom a)∈homogeneous xWeight 1 := by
  obtain ⟨n,u⟩ := a
  cases u
  induction n with
  | zero =>
    rw [swappedInput,AlgHom.comp_apply,input_atom_zero,swap_atom]
    exact word_mem _ rfl
  | succ n ih =>
    rw [swappedInput,AlgHom.comp_apply,input_atom_succ,map_lie,swap_atom]
    have hy : (atom true : A K Bool)∈homogeneous xWeight 0 := word_mem _ rfl
    change ⁅atom true,swappedInput (atom (n,()))⁆∈_
    change atom true*swappedInput (atom (n,()))-swappedInput (atom (n,()))*atom true∈_
    have h1 := homogeneous_mul hy ih
    have h2 := homogeneous_mul ih hy
    exact (homogeneous xWeight 1).sub_mem h1 h2

theorem quad_x (a : Slot) : quad (atom a)∈homogeneous xWeight (xSlot a) := by
  have hx : (atom false : A K Bool)∈homogeneous xWeight 1 := word_mem _ rfl
  have hy : (atom true : A K Bool)∈homogeneous xWeight 0 := word_mem _ rfl
  cases a with
  | A =>
    rw [quad,lift_atom]
    have h := homogeneous_mul hx hx
    exact h
  | C =>
    rw [quad,lift_atom]
    have h1 := homogeneous_mul hx hy
    have h2 := homogeneous_mul hy hx
    exact (homogeneous xWeight 1).sub_mem h1 h2
  | B => simpa only [quad,lift_atom,xSlot] using hy

theorem swapped_solution {ψ : FreeLieAlgebra K Bool}
    (hanti : BaseChangeEquations.antisymmetry ψ=0) : swap (embed ψ)=embed ψ := by
  change ψ+BaseChangeEquations.eval BaseChangeEquations.y BaseChangeEquations.x ψ=0 at hanti
  have h := congrArg embed ((TwoModule.eq_of_add_zero hanti).symm)
  simpa only [ResidualKernel.embed_eval,BaseChangeEquations.x,BaseChangeEquations.y,embed_of,swap] using h

theorem selected_expression {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n : ℕ}
    (hn : 1 < n) (hψ : embed ψ∈homogeneous (fun _ => 1) n) (hp : under p=embed ψ)
    (hanti : BaseChangeEquations.antisymmetry ψ=0) (m : ℕ) :
    swappedInput (piece (fun _ => 1) m (fiber ψ))=quad (piece xSlot m (embed p)) := by
  rw [algHom_piece swappedInput (fun _ => 1) xWeight swappedInput_degree]
  have he : swappedInput (fiber ψ)=quad (embed p) := by
    change swap (input (fiber ψ))=under p
    rw [input_fiber hn hψ,swapped_solution hanti,hp]
  rw [he,← algHom_piece quad xSlot xWeight quad_x]

end EvenIndex

namespace OreShift

section
open AssociativeElimination WordGrading
open QuadraticLeading RowTwo RowKernel AlphabetTransport ProjectionKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]
local instance {α : Type*} [CharP R 2] : CharP (A R α) 2 :=
  charP_of_injective_ringHom (show Function.Injective (algebraMap R (A R α)) from by
    intro r s h
    have hc := congrArg (fun p : A R α => p.coeff 1) h
    simpa using hc) 2

def evaluate (s : S R) : A R Bool →ₐ[R] Module.End R (S R) :=
  lift (fun b => if b then leftMul (B+s) else D)

@[simp] theorem evaluate_x (s : S R) : evaluate s (atom false)=D := by simp [evaluate]
@[simp] theorem evaluate_y (s : S R) : evaluate s (atom true)=leftMul (B+s) := by simp [evaluate]

def eraseShift (s : S R) : A R Slot →ₐ[R] S R :=
  lift (fun | .A => 0 | .C => C | .B => B+s)

theorem comm_D_left (p : S R) : ⁅(D : Module.End R (S R)),leftMul p⁆=leftMul (D p) := by
  apply LinearMap.ext
  intro q
  change D (p*q)-p*D q=D p*q
  rw [D_mul,add_sub_cancel_right]

theorem left_comm_D [CharP R 2] {s : S R} (hs : D s=0) :
    ⁅leftMul (B+s),(D : Module.End R (S R))⁆=leftMul C := by
  rw [←lie_skew,comm_D_left,D_F hs,←map_neg,CharTwo.neg_eq]

theorem evaluate_quad {s : S (ZMod 2)} (hs : D s=0) :
    (evaluate s).comp quad=leftMul.comp (eraseShift s) := by
  apply hom_ext
  intro a
  cases a with
  | A =>
    simp only [AlgHom.comp_apply,quad,lift_atom,map_mul,eraseShift,map_zero,evaluate_x]
    apply LinearMap.ext
    intro q
    change D (D q)=0
    exact D_square q
  | C =>
    simp only [AlgHom.comp_apply,quad,lift_atom,map_sub,map_mul,eraseShift,evaluate_x,evaluate_y]
    change ⁅(D : Module.End (ZMod 2) (S (ZMod 2))),leftMul (B+s)⁆=leftMul C
    rw [comm_D_left,D_F hs]
  | B => simp [quad,eraseShift,evaluate]

theorem evaluate_lie (s : S R) (p q : A R Bool) :
    evaluate s ⁅p,q⁆=⁅evaluate s p,evaluate s q⁆ := by
  simp only [Ring.lie_def,map_sub,map_mul]

theorem evaluate_swapped {s : S (ZMod 2)} (hs : D s=0) :
    (evaluate s).comp EvenIndex.swappedInput=operators s := by
  apply hom_ext
  rintro ⟨n,u⟩
  cases u
  simp only [AlgHom.comp_apply,operators,lift_atom]
  induction n with
  | zero =>
    rw [EvenIndex.swappedInput,AlgHom.comp_apply,EvenIndex.input_atom_zero,swap_atom]
    simp [evaluate,factor]
  | succ n ih =>
    rw [EvenIndex.swappedInput,AlgHom.comp_apply,EvenIndex.input_atom_succ,EvenIndex.map_lie,swap_atom]
    rw [evaluate_lie]
    simp only [Bool.not_false,evaluate_y]
    change ⁅leftMul (B+s),evaluate s (EvenIndex.swappedInput (atom (n,())))⁆=leftMul (P s n)
    rw [ih]
    cases n with
    | zero => exact left_comm_D hs
    | succ n =>
      change ⁅leftMul (B+s),leftMul (P s n)⁆=leftMul ⁅B+s,P s n⁆
      simp only [Ring.lie_def,map_sub,map_mul]

end

open AssociativeElimination WordGrading UniversalEmbedding
open QuadraticLeading RowTwo RowKernel ExactPentagon ProjectionKernel
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

theorem eraseShift_retract (s : S R) :
    (eraseShift s).comp (LetterRetraction.assoc (fun a => a≠Slot.A))=eraseShift s := by
  apply hom_ext
  intro a
  cases a <;> simp [eraseShift]

theorem eraseShift_word (s : S R) (w : FreeMonoid Slot) (h : ¬∀ a∈w.toList,a≠Slot.A) :
    eraseShift s (word w)=0 := by
  rw [←AlgHom.congr_fun (eraseShift_retract s) (word w),AlgHom.comp_apply,
    LetterRetraction.assoc_word,if_neg h,map_zero]

theorem erase_selector (s : S R) {n m r : ℕ} (hn : n=2*m+r) {p : A R Slot}
    (hp : p∈homogeneous weight n) :
    eraseShift s (piece xSlot m p)=eraseShift s (piece bCount r p) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    by_cases hno : ∀ a∈w.toList,a≠Slot.A
    · have he : degree xSlot w=degree acCount w := by
        apply degree_congr_word
        intro a ha
        have h := hno a ha
        cases a <;> simp_all [xSlot,acCount,aCount,cCount]
      have hwc := weight_count w
      have hi : degree xSlot w=m ↔ degree bCount w=r := by omega
      simp only [piece,project_word,hi]
    · simp only [piece,project_word]
      split_ifs <;> simp [eraseShift_word s w hno]
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq]
  | smul c p _ hp => simp only [map_smul,hp]

def translate (s : S R) : S R →ₐ[R] S R := lift (fun b => if b then B+s else C)

@[simp] theorem translate_C (s : S R) : translate s C=C := by simp [translate,C]
@[simp] theorem translate_B (s : S R) : translate s B=B+s := by simp [translate,B]

theorem translate_erase (s : S R) : (translate s).comp (eraseShift 0)=eraseShift s := by
  apply hom_ext
  intro a
  cases a <;> simp [eraseShift]

theorem selected_constant {s : S (ZMod 2)} (hs : D s=0)
    {q : A (ZMod 2) (ℕ×Unit)} {p : A (ZMod 2) Slot}
    (he : EvenIndex.swappedInput q=quad p) : constant s q=eraseShift s p := by
  change operators s q 1=eraseShift s p
  have h := AlgHom.congr_fun (evaluate_swapped hs) q
  rw [←h,AlgHom.comp_apply,he]
  have h' := AlgHom.congr_fun (evaluate_quad hs) p
  rw [←AlgHom.comp_apply,h',AlgHom.comp_apply,leftMul_apply,mul_one]

theorem shifted_leading_bound {ψ : FreeLieAlgebra (ZMod 2) Bool}
    {p : FreeLieAlgebra (ZMod 2) Slot} {n m r : ℕ}
    (hn : 1<n) (hnm : n=2*m+r) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hp : under p=embed ψ) (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hr : embed p∈above bCount r) {s : S (ZMod 2)} (hs : D s=0) (hc : ⁅(C : S (ZMod 2)),s⁆=0) :
    eraseShift s (piece bCount r (embed p))∈above wt r := by
  rw [←erase_selector s hnm (representation_weight hψ hp)]
  rw [←selected_constant hs (EvenIndex.selected_expression hn hψ hp hanti m)]
  apply constant_bound hs hc
  exact project_preserves (EvenIndex.termwise_bound hn hψ hp hr)

end OreShift

namespace GapWord

abbrev G := ℕ × List ℕ

def encode : G → List Bool
  | (a,[]) => List.replicate a false
  | (a,b::v) => List.replicate a false ++ true::encode (b,v)

end GapWord

namespace GapAlgebra
open AssociativeElimination WordGrading GapWord PositionalDeletion
variable {R : Type*} [CommRing R]
local notation "S" => A R Bool
local notation "C" => (OreShift.C : S)
local notation "B" => (OreShift.B : S)

def alg (g : G) : S := word (FreeMonoid.ofList (encode g))

end GapAlgebra

namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]

theorem algHom_difference_lower (f g : A R α →ₐ[R] A R β)
    (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈below wb (wa a))
    (hg : ∀ a,g (atom a)∈homogeneous wb (wa a))
    (he : ∀ a,f (atom a)-g (atom a)∈space (fun w => degree wb w<wa a))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) :
    f p-g p∈space (fun w => degree wb w<n) := by
  have hw (w : FreeMonoid α) : f (word w)-g (word w)∈space (fun v => degree wb v<degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      have hfw : f (word w)∈below wb (degree wa w) :=
        algHom_below f wa wb hf (word_mem w (le_refl _))
      have h1 : (f (atom a)-g (atom a))*f (word w)∈space (fun v => degree wb v<wa a+degree wa w) := mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) (he a) hfw
      have h2 : g (atom a)*(f (word w)-g (word w))∈space (fun v => degree wb v<wa a+degree wa w) := mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) (hg a) ih
      have eq : f (atom a)*f (word w)-g (atom a)*g (word w)=
          (f (atom a)-g (atom a))*f (word w)+g (atom a)*(f (word w)-g (word w)) := by noncomm_ring
      rw [eq]
      exact (space (fun v => degree wb v<wa a+degree wa w)).add_mem h1 h2
  exact map_space (f.toLinearMap-g.toLinearMap) _
    (by intro w hw'; simpa only [LinearMap.sub_apply,AlgHom.toLinearMap_apply,hw'] using hw w) hp

theorem above_lower_zero {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈above wt n) (hl : p∈space (fun w => degree wt w<n)) : p=0 := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra hn
  have hne : p.coeff w≠0 := by simpa using hn
  have h1 := mem_space_iff.mp hp w hne
  have h2 := mem_space_iff.mp hl w hne
  omega

end WordGrading
namespace OreShift

section
open AssociativeElimination WordGrading UniversalEmbedding
open QuadraticLeading RowTwo RowKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

theorem translate_difference {s : S R} (hs : s∈homogeneous wt 0) {r : ℕ} {p : S R}
    (hp : p∈homogeneous wt r) : translate s p-p∈space (fun w => degree wt w<r) := by
  apply algHom_difference_lower (translate s) (AlgHom.id R (S R)) wt wt ?_ ?_ ?_ hp
  · intro b
    cases b with
    | false =>
      change translate s C∈below wt 0
      rw [translate_C]
      exact homogeneous_below (word_mem _ rfl)
    | true =>
      change translate s B∈below wt 1
      rw [translate_B]
      exact (below wt 1).add_mem (word_mem _ (by simp [degree_of,wt]))
        (space_mono (by intro w hw; omega) hs)
  · intro b
    exact word_mem _ (degree_of wt b)
  · intro b
    cases b with
    | false =>
      change translate s C-C∈_
      rw [translate_C,sub_self]
      exact Submodule.zero_mem _
    | true =>
      change translate s B-B∈space (fun w => degree wt w<1)
      rw [translate_B,add_sub_cancel_left]
      exact space_mono (by intro w hw; omega) hs

theorem erase_degree (a : Slot) : eraseShift (0 : S R) (atom a)∈homogeneous wt (bCount a) := by
  cases a <;> simp only [eraseShift,lift_atom,add_zero]
  · exact Submodule.zero_mem _
  · exact word_mem _ rfl
  · exact word_mem _ rfl

theorem shift_invariant {ψ : FreeLieAlgebra (ZMod 2) Bool}
    {p : FreeLieAlgebra (ZMod 2) Slot} {n m r : ℕ}
    (hn : 1<n) (hnm : n=2*m+r) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hp : under p=embed ψ) (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hr : embed p∈above bCount r) {s : S (ZMod 2)}
    (hs : D s=0) (hc : ⁅(C : S (ZMod 2)),s⁆=0) (hdeg : s∈homogeneous wt 0) :
    eraseShift s (piece bCount r (embed p))=eraseShift 0 (piece bCount r (embed p)) := by
  have hf := algHom_homogeneous (eraseShift (0 : S (ZMod 2))) bCount wt erase_degree
    (piece_mem bCount r (embed p))
  have hd := translate_difference hdeg hf
  rw [←AlgHom.comp_apply,translate_erase] at hd
  apply sub_eq_zero.mp
  exact above_lower_zero ((above wt r).sub_mem
    (shifted_leading_bound hn hnm hψ hp hanti hr hs hc) (homogeneous_above hf)) hd

end

open AssociativeElimination WordGrading
variable {R : Type*} [CommRing R]

def shiftDeriv (s : S R) : S R →ₗ[R] S R := deriv (fun b => if b then s else 0)

@[simp] theorem shiftDeriv_C (s : S R) : shiftDeriv s C=0 := by simp [shiftDeriv,C]
@[simp] theorem shiftDeriv_B (s : S R) : shiftDeriv s B=s := by simp [shiftDeriv,B]
@[simp] theorem shiftDeriv_one (s : S R) : shiftDeriv s 1=0 := deriv_one _
theorem shiftDeriv_mul (s p q : S R) :
    shiftDeriv s (p*q)=shiftDeriv s p*q+p*shiftDeriv s q := deriv_mul _ _ _

theorem shiftDeriv_degree {s : S R} (hs : s∈homogeneous wt 0) {r : ℕ} {p : S R}
    (hp : p∈homogeneous wt r) : shiftDeriv s p∈lower wt 1 r := by
  apply deriv_lower wt 1 _ ?_ hp
  intro b
  cases b with
  | false => exact Submodule.zero_mem _
  | true => exact space_mono (by intro w hw; change degree wt w+1=1; omega) hs

theorem taylor_remainder {s : S R} (hs : s∈homogeneous wt 0) {r : ℕ} {p : S R}
    (hp : p∈homogeneous wt r) :
    translate s p-p-shiftDeriv s p∈space (fun w => degree wt w+1<r) := by
  let E : S R →ₗ[R] S R := (translate s).toLinearMap-LinearMap.id-shiftDeriv s
  have hw (w : FreeMonoid Bool) : E (word w)∈space (fun v => degree wt v+1<degree wt w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp [E]
    | of_mul b w ih =>
      have hh : word (R:=R) w∈homogeneous wt (degree wt w) := word_mem w rfl
      have hd := translate_difference hs hh
      cases b with
      | false =>
        have he : E (word (FreeMonoid.of false*w))=C*E (word w) := by
          simp only [E,LinearMap.sub_apply,AlgHom.toLinearMap_apply,LinearMap.id_apply,
            word_mul,word_of]
          change translate s (C*word w)-C*word w-shiftDeriv s (C*word w)=_
          rw [map_mul,translate_C,shiftDeriv_mul,shiftDeriv_C,zero_mul,zero_add]
          noncomm_ring
        rw [he]
        have hc : (C : S R)∈homogeneous wt 0 := word_mem _ rfl
        have h1 : C*E (word w)∈space (fun v => degree wt v+1<0+degree wt w) :=
          mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) hc ih
        exact h1
      | true =>
        have he : E (word (FreeMonoid.of true*w))=
            B*E (word w)+s*(translate s (word w)-word w) := by
          simp only [E,LinearMap.sub_apply,AlgHom.toLinearMap_apply,LinearMap.id_apply,
            word_mul,word_of]
          change translate s (B*word w)-B*word w-shiftDeriv s (B*word w)=_
          rw [map_mul,translate_B,shiftDeriv_mul,shiftDeriv_B]
          noncomm_ring
        rw [he]
        have hb : (B : S R)∈homogeneous wt 1 := word_mem _ rfl
        have h1 : B*E (word w)∈space (fun v => degree wt v+1<1+degree wt w) :=
          mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) hb ih
        have h2 : s*(translate s (word w)-word w)∈space (fun v => degree wt v+1<1+degree wt w) :=
          mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) hs hd
        exact (space _).add_mem h1 h2
  exact map_space E _ (by intro w hw'; simpa only [hw'] using hw w) hp

theorem shiftDeriv_zero {s : S R} (hs : s∈homogeneous wt 0) {r : ℕ} {p : S R}
    (hp : p∈homogeneous wt r) (he : translate s p=p) : shiftDeriv s p=0 := by
  have hd := shiftDeriv_degree hs hp
  have hl := taylor_remainder hs hp
  rw [he,sub_self,zero_sub] at hl
  have hl' := (space (fun w => degree wt w+1<r)).neg_mem hl
  rw [neg_neg] at hl'
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra hn
  have hne : (shiftDeriv s p).coeff w≠0 := by simpa using hn
  have h1 := mem_space_iff.mp hd w hne
  have h2 := mem_space_iff.mp hl' w hne
  omega

end OreShift

namespace GapSelection
open AssociativeElimination WordGrading PositionalDeletion GapAlgebra
variable {R : Type*} [CommRing R]
local notation "S" => A R Bool
local notation "C" => (OreShift.C : S)

def cwt (b : Bool) : ℕ := if b then 0 else 1

theorem Cpow_degree (j : ℕ) : C^j∈homogeneous OreShift.wt 0 := by
  induction j with
  | zero =>
      rw [pow_zero]
      exact word_mem (1 : FreeMonoid Bool) (show degree OreShift.wt 1=0 from rfl)
  | succ j ih =>
    rw [pow_succ]
    have hc : C∈homogeneous OreShift.wt 0 := word_mem (FreeMonoid.of false) rfl
    exact homogeneous_mul (wt:=OreShift.wt) (n:=0) (m:=0) ih hc

end GapSelection

namespace ImageBound

section
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon AlphabetTransport
attribute [local instance] LieRing.ofAssociativeRing

theorem erase_embed (p : FreeLieAlgebra K Slot) : embed (eraseLie p)=OreShift.eraseShift 0 (embed p) := by
  have h : embed.comp eraseLie=(OreShift.eraseShift (0 : A K Bool)).toLieHom.comp embed := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [eraseLie,OreShift.eraseShift,OreShift.B,OreShift.C]
  exact LieHom.congr_fun h p

@[simp] theorem embed_leading (r : ℕ) (p : FreeLieAlgebra K Slot) :
    embed (leading r p)=OreShift.eraseShift 0 (WordGrading.piece bCount r (embed p)) := by
  rw [leading,erase_embed,LieGrading.embed_piece]

theorem leading_bcount (r : ℕ) (p : FreeLieAlgebra K Slot) :
    embed (leading r p)∈homogeneous OreShift.wt r := by
  rw [embed_leading]
  exact algHom_homogeneous _ bCount OreShift.wt OreShift.erase_degree (piece_mem bCount r (embed p))

def cbWeight (b : Bool) : ℕ := if b then 1 else 2

theorem erase_weight_degree (a : Slot) :
    OreShift.eraseShift (0 : A K Bool) (atom a)∈homogeneous cbWeight (weight a) := by
  cases a <;> simp only [OreShift.eraseShift,lift_atom,add_zero]
  · exact Submodule.zero_mem _
  · exact word_mem (FreeMonoid.of false) rfl
  · exact word_mem (FreeMonoid.of true) rfl

theorem leading_weight {p : FreeLieAlgebra K Slot} {n : ℕ}
    (hp : embed p∈homogeneous weight n) (r : ℕ) : embed (leading r p)∈homogeneous cbWeight n := by
  rw [embed_leading]
  exact algHom_homogeneous _ weight cbWeight erase_weight_degree (project_preserves hp)

theorem weight_count (w : FreeMonoid Bool) : degree cbWeight w=2*degree GapSelection.cwt w+degree OreShift.wt w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | of_mul b w ih =>
    simp only [degree_mul,degree_of]
    cases b <;> simp only [cbWeight,GapSelection.cwt,OreShift.wt,Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem weight_split {p : A K Bool} {n r : ℕ} (hp : p≠0)
    (hn : p∈homogeneous cbWeight n) (hr : p∈homogeneous OreShift.wt r) : ∃ m,n=2*m+r := by
  obtain ⟨w,hw⟩ : ∃ w,p.coeff w≠0 := by
    by_contra h
    apply hp
    ext w
    have := not_exists.mp h w
    simpa using this
  have h1 := mem_space_iff.mp hn w hw
  have h2 := mem_space_iff.mp hr w hw
  exact ⟨degree GapSelection.cwt w,by rw [←h1,weight_count,h2]⟩

theorem D_Cpow (j : ℕ) : OreShift.D ((OreShift.C : A K Bool)^j)=0 := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ,OreShift.D_mul,ih,OreShift.D_C,zero_mul,mul_zero,add_zero]

theorem C_lie_Cpow (j : ℕ) : ⁅(OreShift.C : A K Bool),(OreShift.C : A K Bool)^j⁆=0 := by
  change (OreShift.C : A K Bool)*OreShift.C^j-OreShift.C^j*OreShift.C=0
  rw [←pow_succ',←pow_succ,sub_self]

theorem leading_shift_invariant {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r : ℕ}
    (hn : 1<n) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hp : under p=embed ψ) (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hr : embed p∈above bCount r) (j : ℕ) :
    OreShift.translate ((OreShift.C : A K Bool)^j) (embed (leading r p))=embed (leading r p) := by
  by_cases hz : embed (leading r p)=0
  · rw [hz,map_zero]
  obtain ⟨m,hm⟩ := weight_split hz (leading_weight (representation_weight hψ hp) r) (leading_bcount r p)
  rw [embed_leading,←AlgHom.comp_apply,OreShift.translate_erase]
  exact OreShift.shift_invariant hn hm hψ hp hanti hr (D_Cpow j) (C_lie_Cpow j) (GapSelection.Cpow_degree j)

end

open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon AlphabetTransport
attribute [local instance] LieRing.ofAssociativeRing

theorem leading_D_zero {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r : ℕ}
    (hn : 1<n) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hp : under p=embed ψ) (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hr : embed p∈above bCount r) : OreShift.D (embed (leading r p))=0 := by
  have h := OreShift.shiftDeriv_zero (GapSelection.Cpow_degree (R:=K) 1) (leading_bcount r p)
    (leading_shift_invariant hn hψ hp hanti hr 1)
  have he : OreShift.shiftDeriv ((OreShift.C : A K Bool)^1)=OreShift.D := by
    simp only [pow_one,OreShift.shiftDeriv,OreShift.D]
  rw [he] at h
  exact h

end ImageBound
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
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

theorem homogeneous_lie {wt : α → ℕ} {r s : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt r) (hq : q∈homogeneous wt s) : ⁅p,q⁆∈homogeneous wt (r+s) := by
  change p*q-q*p∈_
  exact (homogeneous wt _).sub_mem (homogeneous_mul hp hq) (by simpa only [Nat.add_comm] using homogeneous_mul hq hp)

theorem above_lie {wt : α → ℕ} {r s : ℕ} {p q : A R α}
    (hp : p∈above wt r) (hq : q∈above wt s) : ⁅p,q⁆∈above wt (r+s) := by
  change p*q-q*p∈_
  exact (above wt _).sub_mem (above_mul hp hq) (by simpa only [Nat.add_comm] using above_mul hq hp)

theorem piece_of_difference_high {wt : α → ℕ} {n : ℕ} {p q : A R α}
    (hq : q∈homogeneous wt n) (hd : p-q∈above wt (n+1)) : piece wt n p=q := by
  have h := piece_zero_of_above hd (Nat.lt_succ_self n)
  rw [map_sub,piece_homogeneous hq,if_pos rfl] at h
  exact sub_eq_zero.mp h

theorem leading_lie {wt : α → ℕ} {r s : ℕ} {p q : A R α}
    (hp : p∈above wt r) (hq : q∈above wt s) :
    piece wt (r+s) ⁅p,q⁆=⁅piece wt r p,piece wt s q⁆ := by
  apply piece_of_difference_high (homogeneous_lie (piece_mem wt r p) (piece_mem wt s q))
  have h1 := above_lie (subtract_piece_above hp) hq
  have h2 := above_lie (homogeneous_above (piece_mem wt r p)) (subtract_piece_above hq)
  have he : ⁅p,q⁆-⁅piece wt r p,piece wt s q⁆=⁅p-piece wt r p,q⁆+⁅piece wt r p,q-piece wt s q⁆ := by
    simp only [sub_lie,lie_sub]; abel
  rw [he]
  exact (above wt (r+s+1)).add_mem (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1)
    (by simpa only [Nat.add_assoc] using h2)

theorem leading_deriv {wt : α → ℕ} {c n : ℕ} {f g : α → A R α}
    (hf : ∀ a,f a∈above wt (wt a+c)) (hg : ∀ a,g a∈homogeneous wt (wt a+c))
    (hd : ∀ a,f a-g a∈above wt (wt a+c+1)) {p : A R α} (hp : p∈above wt n) :
    piece wt (n+c) (deriv f p)=deriv g (piece wt n p) := by
  apply piece_of_difference_high (deriv_homogeneous hg (piece_mem wt n p))
  have h1 := deriv_above hf (subtract_piece_above hp)
  have h2 := deriv_above (c:=c+1) (f:=fun a => f a-g a)
    (by intro a; simpa only [Nat.add_assoc] using hd a) (homogeneous_above (piece_mem wt n p))
  rw [deriv_sub] at h2
  have he : deriv f p-deriv g (piece wt n p)=deriv f (p-piece wt n p)+
      (deriv f (piece wt n p)-deriv g (piece wt n p)) := by rw [map_sub]; abel
  rw [he]
  exact (above wt (n+c+1)).add_mem (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1)
    (by simpa only [Nat.add_assoc] using h2)

end WordGrading
namespace IharaLeading
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon ResidualKernel
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2
local notation "S" => A K Slot
local notation "B" => (atom Slot.B : S)
local notation "C" => (atom Slot.C : S)

def action (p : S) : Slot → S
  | .A => 0 | .B => ⁅B,p⁆ | .C => ⁅C,p⁆+⁅B,deriv delta p⁆
def lowAction (q : S) : Slot → S
  | .A => 0 | .B => ⁅B,q⁆ | .C => ⁅C,q⁆+⁅B,deriv low q⁆

theorem delta_above {p : S} {r : ℕ} (hp : p∈above bCount r) : deriv delta p∈above bCount (r-1) := by
  rw [delta_split]
  apply (above bCount (r-1)).add_mem
  · exact deriv_lowers_above bCount 1 low low_degree hp
  · exact space_mono (by intro w hw; omega) (deriv_above (fun a => homogeneous_above (high_degree a)) hp)

theorem action_above {p : S} {r : ℕ} (hr : 0<r) (hp : p∈above bCount r) (a : Slot) :
    action p a∈above bCount (bCount a+r) := by
  have hb : B∈above bCount 1 := homogeneous_above (word_mem (FreeMonoid.of Slot.B) rfl)
  have hc : C∈above bCount 0 := homogeneous_above (word_mem (FreeMonoid.of Slot.C) rfl)
  cases a with
  | A => exact Submodule.zero_mem _
  | «B» => exact above_lie hb hp
  | «C» =>
    apply (above bCount (0+r)).add_mem (above_lie hc hp)
    convert above_lie hb (delta_above hp) using 1
    congr 1
    omega

theorem lowAction_homogeneous {q : S} {r : ℕ} (hr : 0<r)
    (hq : q∈homogeneous bCount r) (a : Slot) : lowAction q a∈homogeneous bCount (bCount a+r) := by
  have hb : B∈homogeneous bCount 1 := word_mem (FreeMonoid.of Slot.B) rfl
  have hc : C∈homogeneous bCount 0 := word_mem (FreeMonoid.of Slot.C) rfl
  cases a with
  | A => exact Submodule.zero_mem _
  | «B» => exact homogeneous_lie hb hq
  | «C» =>
    apply (homogeneous bCount (0+r)).add_mem (homogeneous_lie hc hq)
    convert homogeneous_lie hb (lower_homogeneous (deriv_lower bCount 1 low low_degree hq)) using 1
    congr 1
    omega

theorem delta_low_difference {p q : S} {r : ℕ} (hp : p∈above bCount r)
    (hd : p-q∈above bCount (r+1)) : deriv delta p-deriv low q∈above bCount r := by
  have hl := deriv_lowers_above bCount 1 low low_degree hd
  have hh := deriv_above (fun a => homogeneous_above (high_degree a)) hp
  rw [delta_split]
  have he : deriv low p+deriv high p-deriv low q=deriv low (p-q)+deriv high p := by rw [map_sub]; abel
  rw [he]
  exact (above bCount r).add_mem (by simpa using hl) (space_mono (by intro w hw; omega) hh)

theorem action_difference {p q : S} {r : ℕ} (hp : p∈above bCount r)
    (hd : p-q∈above bCount (r+1)) (a : Slot) : action p a-lowAction q a∈above bCount (bCount a+r+1) := by
  have hb : B∈above bCount 1 := homogeneous_above (word_mem (FreeMonoid.of Slot.B) rfl)
  have hc : C∈above bCount 0 := homogeneous_above (word_mem (FreeMonoid.of Slot.C) rfl)
  cases a with
  | A => simp only [action,lowAction,sub_self]; exact Submodule.zero_mem _
  | «B» =>
    change ⁅B,p⁆-⁅B,q⁆∈_
    rw [←lie_sub]
    simpa only [Nat.add_assoc,bCount,ite_true] using above_lie hb hd
  | «C» =>
    have he : action p Slot.C-lowAction q Slot.C=⁅C,p-q⁆+⁅B,deriv delta p-deriv low q⁆ := by
      simp only [action,lowAction,lie_sub]; abel
    rw [he]
    exact (above bCount (0+r+1)).add_mem (by simpa only [Nat.add_assoc] using above_lie hc hd)
      (by simpa only [Nat.add_comm,Nat.zero_add] using above_lie hb (delta_low_difference hp hd))

theorem leading_action {p q : S} {r s : ℕ} (hr : 0<r)
    (hp : p∈above bCount r) (hq : q∈above bCount s) :
    piece bCount (r+s) (deriv (action p) q)=deriv (lowAction (piece bCount r p)) (piece bCount s q) := by
  rw [Nat.add_comm r s]
  exact leading_deriv (action_above hr hp) (lowAction_homogeneous hr (piece_mem bCount r p))
    (action_difference hp (subtract_piece_above hp)) hq

end IharaLeading

namespace AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α β : Type*} [CommRing R]

theorem deriv_naturality (F : A R α →ₐ[R] A R β) (f : α → A R α) (g : β → A R β)
    (h : ∀ a,F (f a)=deriv g (F (atom a))) (p : A R α) : F (deriv f p)=deriv g (F p) := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp
  | ha a => rw [deriv_atom,h a]
  | hadd p q hp hq => simp only [map_add,hp,hq]
  | hs c p hp => simp only [map_smul,hp]
  | hm p q hp hq => rw [deriv_mul,map_add,map_mul,map_mul,hp,hq,map_mul,deriv_mul]

theorem deriv_inner_right (p q : A R α) : deriv (fun a => ⁅(atom a : A R α),p⁆) q=⁅q,p⁆ := by
  induction q using QuadraticAlphabet.algebra_induction with
  | h1 => simp [Ring.lie_def]
  | ha a => exact deriv_atom _ _
  | hadd q r hq hr => simp only [map_add,add_lie,hq,hr]
  | hs c q hq => simp only [map_smul,smul_lie,hq]
  | hm q r hq hr => rw [deriv_mul,hq,hr]; simp only [Ring.lie_def]; noncomm_ring

end AssociativeElimination
namespace IharaLeading
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon ResidualKernel
attribute [local instance] LieRing.ofAssociativeRing
local notation "S" => A K Slot
local notation "E" => (OreShift.eraseShift (0 : A K Bool))

theorem erase_low (p : S) : E (deriv low p)=OreShift.D (E p) := by
  apply deriv_naturality E low (fun b => if b then OreShift.C else 0) ?_
  intro a
  cases a <;> simp [low,OreShift.eraseShift,OreShift.C,OreShift.B]

theorem erase_lowAction_inner {p : S} (hp : OreShift.D (E p)=0) (q : S) :
    E (deriv (lowAction p) q)=⁅E q,E p⁆ := by
  rw [←deriv_inner_right]
  apply deriv_naturality E (lowAction p) (fun b => ⁅atom b,E p⁆) ?_
  intro a
  cases a with
  | A => simp [lowAction,OreShift.eraseShift]
  | C =>
    change E (⁅(atom Slot.C : S),p⁆+⁅(atom Slot.B : S),deriv low p⁆)=_
    rw [map_add,EvenIndex.map_lie,EvenIndex.map_lie,erase_low,hp,lie_zero,add_zero]
    simp [OreShift.eraseShift,OreShift.C]
  | B =>
    change E ⁅(atom Slot.B : S),p⁆=_
    rw [EvenIndex.map_lie]
    simp [OreShift.eraseShift,OreShift.B]

def ihara (p q : S) : S := deriv (action p) q-deriv (action q) p+⁅p,q⁆

theorem ihara_above {p q : S} {r s : ℕ} (hr : 0<r) (hs : 0<s)
    (hp : p∈above bCount r) (hq : q∈above bCount s) : ihara p q∈above bCount (r+s) := by
  apply (above bCount (r+s)).add_mem
  · apply (above bCount (r+s)).sub_mem
    · simpa only [Nat.add_comm] using deriv_above (action_above hr hp) hq
    · exact deriv_above (action_above hs hq) hp
  · exact above_lie hp hq

theorem leading_ihara {p q : S} {r s : ℕ} (hr : 0<r) (hs : 0<s)
    (hp : p∈above bCount r) (hq : q∈above bCount s)
    (hDp : OreShift.D (E (piece bCount r p))=0) (hDq : OreShift.D (E (piece bCount s q))=0) :
    E (piece bCount (r+s) (ihara p q))=⁅E (piece bCount r p),E (piece bCount s q)⁆ := by
  simp only [ihara,map_add,map_sub]
  rw [leading_action hr hp hq,show r+s=s+r from Nat.add_comm r s,leading_action hs hq hp]
  rw [show s+r=r+s from Nat.add_comm s r,leading_lie hp hq]
  rw [erase_lowAction_inner hDp,erase_lowAction_inner hDq,EvenIndex.map_lie]
  rw [sub_add_cancel,←lie_skew]
  exact TwoModule.neg_eq _

theorem actual_leading_ihara {ψ φ : FreeLieAlgebra K Bool} {p q : FreeLieAlgebra K Slot} {n m r s : ℕ}
    (hn : 1<n) (hm : 1 < m) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hφ : embed φ∈homogeneous (fun _ => 1) m)
    (hp : under p=embed ψ) (hq : under q=embed φ)
    (hψa : BaseChangeEquations.antisymmetry ψ=0) (hφa : BaseChangeEquations.antisymmetry φ=0)
    (hr : 0<r) (hs : 0<s) (hpr : embed p∈above bCount r) (hqs : embed q∈above bCount s) :
    ihara (embed p) (embed q)∈above bCount (r+s) ∧
    E (piece bCount (r+s) (ihara (embed p) (embed q)))=⁅embed (ImageBound.leading r p),embed (ImageBound.leading s q)⁆ := by
  refine ⟨ihara_above hr hs hpr hqs,?_⟩
  simp only [ImageBound.embed_leading]
  have hDp := ImageBound.leading_D_zero hn hψ hp hψa hpr
  have hDq := ImageBound.leading_D_zero hm hφ hq hφa hqs
  rw [ImageBound.embed_leading] at hDp hDq
  exact leading_ihara hr hs hpr hqs hDp hDq

end IharaLeading

namespace GenericIhara
open AssociativeElimination UniversalEmbedding
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

def assocD (p : A R Bool) : A R Bool →ₗ[R] A R Bool :=
  deriv (fun b => if b then ⁅(atom true : A R Bool),p⁆ else 0)
def assocIhara (p q : A R Bool) := assocD p q-assocD q p+⁅p,q⁆

theorem embed_D (p q : FreeLieAlgebra R Bool) : embed (D p q)=assocD (embed p) (embed q) := by
  rw [←AssociativeDerivations.extend_embed]
  congr 1
  unfold AssociativeDerivations.extend assocD
  congr 1
  funext b
  cases b <;> simp [D]

theorem embed_ihara (p q : FreeLieAlgebra R Bool) : embed (ihara p q)=assocIhara (embed p) (embed q) := by
  simp only [ihara,assocIhara,map_add,map_sub,LieHom.map_lie,embed_D]

end GenericIhara
namespace IharaLeading
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon ResidualKernel
attribute [local instance] LieRing.ofAssociativeRing
local notation "S" => A K Slot
local notation "Q" => A K Bool

theorem quad_action (p q : S) : quad (deriv (action p) q)=GenericIhara.assocD (quad p) (quad q) := by
  apply deriv_naturality quad (action p) (fun b => if b then ⁅(atom true : Q),quad p⁆ else 0) ?_
  intro a
  cases a with
  | A =>
    simp only [action,map_zero,quad,lift_atom,AssociativeElimination.deriv_mul,deriv_atom,
      Bool.false_eq_true,ite_false,zero_mul,mul_zero,add_zero]
  | C =>
    simp only [action,map_add,EvenIndex.map_lie,quad_delta]
    simp only [quad,lift_atom,map_sub,AssociativeElimination.deriv_mul,deriv_atom,
      ite_true,Bool.false_eq_true,ite_false,Ring.lie_def,zero_mul,mul_zero,zero_add,add_zero]
    noncomm_ring
  | B => simp [action,quad,EvenIndex.map_lie]

theorem quad_ihara (p q : S) : quad (ihara p q)=GenericIhara.assocIhara (quad p) (quad q) := by
  simp only [ihara,GenericIhara.assocIhara,map_add,map_sub,EvenIndex.map_lie,quad_action]

def deltaLie : LieDerivation K (FreeLieAlgebra K Slot) (FreeLieAlgebra K Slot) :=
  FreeDerivations.extend (fun (a : Slot) => match a with
    | .A => 0 | .B => FreeLieAlgebra.of K Slot.C
    | .C => ⁅FreeLieAlgebra.of K Slot.A,FreeLieAlgebra.of K Slot.B⁆)

theorem embed_deltaLie (p : FreeLieAlgebra K Slot) : embed (deltaLie p)=deriv delta (embed p) := by
  have h : (fun a => embed (deltaLie (FreeLieAlgebra.of K a)))=delta := by
    funext a
    cases a <;> simp [deltaLie,delta,low,high,Ring.lie_def]
  rw [←AssociativeDerivations.extend_embed]
  change deriv (fun a => embed (deltaLie (FreeLieAlgebra.of K a))) (embed p)=_
  rw [h]

def actionLie (p : FreeLieAlgebra K Slot) : LieDerivation K (FreeLieAlgebra K Slot) (FreeLieAlgebra K Slot) :=
  FreeDerivations.extend (fun (a : Slot) => match a with
    | .A => 0 | .B => ⁅FreeLieAlgebra.of K Slot.B,p⁆
    | .C => ⁅FreeLieAlgebra.of K Slot.C,p⁆+⁅FreeLieAlgebra.of K Slot.B,deltaLie p⁆)

theorem embed_actionLie (p q : FreeLieAlgebra K Slot) :
    embed (actionLie p q)=deriv (action (embed p)) (embed q) := by
  have h : (fun a => embed (actionLie p (FreeLieAlgebra.of K a)))=action (embed p) := by
    funext a
    cases a <;> simp [actionLie,action,embed_deltaLie]
  rw [←AssociativeDerivations.extend_embed]
  change deriv (fun a => embed (actionLie p (FreeLieAlgebra.of K a))) (embed q)=_
  rw [h]

def iharaLie (p q : FreeLieAlgebra K Slot) := actionLie p q-actionLie q p+⁅p,q⁆

theorem embed_iharaLie (p q : FreeLieAlgebra K Slot) : embed (iharaLie p q)=ihara (embed p) (embed q) := by
  simp only [iharaLie,ihara,map_add,map_sub,LieHom.map_lie,embed_actionLie]

theorem actual_ihara_representation {ψ φ : FreeLieAlgebra K Bool} {p q : FreeLieAlgebra K Slot}
    (hp : under p=embed ψ) (hq : under q=embed φ) : under (iharaLie p q)=embed (GenericIhara.ihara ψ φ) := by
  change quad (embed (iharaLie p q))=_
  rw [embed_iharaLie,quad_ihara,GenericIhara.embed_ihara]
  rw [show quad (embed p)=embed ψ from hp,show quad (embed q)=embed φ from hq]

end IharaLeading

namespace GenericIhara

section
open AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

end

open LieAlgebra
variable {R : Type*} [CommRing R]
local notation "FL" => FreeLieAlgebra R Bool
local notation "Der" => LieDerivation R FL FL

theorem erase_lie (p q : Algebra R) : erase ⁅p,q⁆=ihara (erase p) (erase q) := by
  change ⁅p.val.left,q.val.left⁆+p.val.right q.val.left-q.val.right p.val.left=_
  rw [p.property,q.property]
  change ⁅p.val.left,q.val.left⁆+D p.val.left q.val.left-D q.val.left p.val.left =
    D p.val.left q.val.left-D q.val.left p.val.left+⁅p.val.left,q.val.left⁆
  abel

variable {α : Type*}

theorem evalIhara_lie (f : α → FL) (p q : FreeLieAlgebra R α) :
    evalIhara f ⁅p,q⁆=ihara (evalIhara f p) (evalIhara f q) := by
  change erase (lift f ⁅p,q⁆)=_
  rw [LieHom.map_lie,erase_lie]
  rfl

end GenericIhara

namespace LatticeDimension
open scoped TensorProduct
variable {ι : Type*}

def cast : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) where
  toFun u i := u i
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp] theorem cast_apply (u : ι → ℤ) (i : ι) : cast u i=(u i : ℚ) := rfl

def lattice (E : Submodule ℚ (ι → ℚ)) : Submodule ℤ (ι → ℤ) :=
  (E.restrictScalars ℤ).comap cast

@[simp] theorem mem_lattice (E : Submodule ℚ (ι → ℚ)) (u : ι → ℤ) :
    u∈lattice E ↔ cast u∈E := Iff.rfl

variable [Fintype ι]

variable (F : Type*) [Field F]

def scalarMap (E : Submodule ℚ (ι → ℚ)) : F ⊗[ℤ] lattice E →ₗ[F] (ι → F) :=
  (TensorProduct.piScalarRightHom ℤ F F ι).comp ((lattice E).subtype.baseChange F)

omit [Fintype ι] in
@[simp] theorem scalarMap_tmul (E : Submodule ℚ (ι → ℚ)) (r : F) (u : lattice E) :
    scalarMap F E (r ⊗ₜ u)=fun i => (u.val i : F)*r := by
  ext i
  simp [scalarMap]

def reduction (E : Submodule ℚ (ι → ℚ)) : Submodule F (ι → F) :=
  (scalarMap F E).range

end LatticeDimension

namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
variable {R α : Type*} [CommRing R]

def projection (wt : α → ℕ) (n : ℕ) : FreeLieAlgebra R α →ₗ[R] FreeLieAlgebra R α where
  toFun := piece wt n
  map_add' := piece_add wt n
  map_smul' := piece_smul wt n

theorem piece_homogeneous {wt : α → ℕ} {m : ℕ} {p : FreeLieAlgebra R α}
    (hp : p∈homogeneousLie wt m) (n : ℕ) : piece wt n p=if m=n then p else 0 := by
  apply UniversalEmbedding.injective
  rw [embed_piece,WordGrading.piece_homogeneous (homogeneousLie_embed hp)]
  split_ifs <;> simp

variable (F : Type*) [Field F]

end LieGrading
end

section
namespace ReducedDimension
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon ImageBound
attribute [local instance] LieRing.ofAssociativeRing

theorem solutions_hom {n : ℕ} (p : solutions n) :
    p.val∈LieGrading.homogeneousLie (fun _ => 1) n := p.property.1.1.1

theorem solutions_anti {n : ℕ} (p : solutions n) : BaseChangeEquations.antisymmetry p.val=0 := p.property.1.1.2

def representation (n : ℕ) (hn : 1<n) (p : solutions n) : FreeLieAlgebra K Slot :=
  (QuadraticLeading.representation hn (LieGrading.homogeneousLie_embed (solutions_hom p))).choose

theorem representation_under (n : ℕ) (hn : 1<n) (p : solutions n) :
    under (representation n hn p)=embed p.val :=
  (QuadraticLeading.representation hn (LieGrading.homogeneousLie_embed (solutions_hom p))).choose_spec.1

def representationMap (n : ℕ) (hn : 1<n) : solutions n →ₗ[K] FreeLieAlgebra K Slot where
  toFun := representation n hn
  map_add' p q := by
    apply under_injective
    rw [map_add,representation_under,representation_under,representation_under]
    simp only [Submodule.coe_add,map_add]
  map_smul' c p := by
    apply under_injective
    rw [map_smul,representation_under,representation_under]
    simp only [Submodule.coe_smul,map_smul,RingHom.id_apply]

def filtration (n : ℕ) (hn : 1<n) (r : ℕ) : Submodule K (solutions n) :=
  (above bCount r).comap (embed.toLinearMap.comp (representationMap n hn))

end ReducedDimension

open AssociativeElimination UniversalEmbedding WordGrading
open scoped TensorProduct

namespace RationalBound
open ReducedDimension

def reducedCoordinates (n : ℕ) : solutions n →ₗ[K] (Words n → K) :=
  (LieDimension.coordinates K wt n).comp ((solutions n).subtype.codRestrict _ solutions_hom)

end RationalBound
end

end DeligneDrinfeld

end

end OAI

end













section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace SaturatedSolutions
open AssociativeElimination UniversalEmbedding WordGrading
open ReducedDimension
abbrev K := ZMod 2
variable (n : ℕ) (E : Submodule ℚ (Wn n))

def reduction : Submodule K (solutions n) :=
  (LatticeDimension.reduction K (image n E)).comap (RationalBound.reducedCoordinates n)

end SaturatedSolutions

namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
variable {R α : Type*} [CommRing R]

theorem eval_homogeneous (wt : α → ℕ) (t : UniversalEmbedding.Tree α) :
    (t.eval : FreeLieAlgebra R α)∈homogeneousLie wt (treeDegree wt t) :=
  Submodule.subset_span ⟨t,rfl,rfl⟩

theorem piece_tree (wt : α → ℕ) (r : ℕ) (t : UniversalEmbedding.Tree α) :
    piece wt r (t.eval : FreeLieAlgebra R α)=if treeDegree wt t=r then t.eval else 0 :=
  piece_homogeneous (eval_homogeneous wt t) r

def biTreeSpan (wa wb : α → ℕ) (n r : ℕ) : Submodule R (FreeLieAlgebra R α) :=
  Submodule.span R {p | ∃ t : UniversalEmbedding.Tree α,treeDegree wa t=n ∧ treeDegree wb t=r ∧ t.eval=p}

theorem biTreeSpan_eq (wa wb : α → ℕ) (n r : ℕ) :
    biTreeSpan (R:=R) wa wb n r=biPiece wa wb n r := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨t,hn,hr,rfl⟩
    exact ⟨hn ▸ eval_homogeneous wa t,hr ▸ eval_homogeneous wb t⟩
  · intro p hp
    have he : piece wb r p=p := by rw [piece_homogeneous hp.2,if_pos rfl]
    rw [←he]
    have hw : p∈homogeneousLie wa n := hp.1
    clear hp he
    induction hw using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨t,ht,rfl⟩ := hp
      rw [piece_tree]
      split_ifs with h
      · exact Submodule.subset_span ⟨t,ht,h,rfl⟩
      · exact Submodule.zero_mem _
    | zero =>
      have hz : piece wb r (0 : FreeLieAlgebra R α)=0 := (projection wb r).map_zero
      rw [hz]
      exact Submodule.zero_mem _
    | add p q _ _ hp hq => rw [piece_add]; exact Submodule.add_mem _ hp hq
    | smul c p _ hp => rw [piece_smul]; exact Submodule.smul_mem _ c hp

theorem treeDegree_pos {wt : α → ℕ} (h : ∀ a,0<wt a) (t : UniversalEmbedding.Tree α) : 0<treeDegree wt t := by
  induction t with
  | leaf a => simpa only [treeDegree_leaf] using h a
  | node t u ht hu => rw [treeDegree_node]; omega

theorem treeDegree_lower {wt : α → ℕ} {m : ℕ} (h : ∀ a,m≤wt a) (t : UniversalEmbedding.Tree α) : m≤treeDegree wt t := by
  induction t with
  | leaf a => simpa only [treeDegree_leaf] using h a
  | node t u ht hu => rw [treeDegree_node]; omega

end LieGrading

namespace NormalizedFamily
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open ImageBound LieGrading RowTwo RowKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing

variable (g : Data)

def treeSolution (t : UniversalEmbedding.Tree ℕ) : ReducedDimension.solutions (treeDegree oddWeight t) :=
  ⟨GenericIhara.evalIhara g.value t.eval,g.solution _ _ (eval_homogeneous oddWeight t)⟩

theorem treeWeight (t : UniversalEmbedding.Tree ℕ) : 2<treeDegree oddWeight t := by
  have h := treeDegree_lower (m:=3) (wt:=oddWeight) (by intro k; simp [oddWeight]) t
  omega

def treeRep (t : UniversalEmbedding.Tree ℕ) : FreeLieAlgebra K Slot :=
  ReducedDimension.representation (treeDegree oddWeight t) (by have := treeWeight t; omega) (treeSolution g t)

theorem under_treeRep (t : UniversalEmbedding.Tree ℕ) :
    under (treeRep g t)=embed (GenericIhara.evalIhara g.value t.eval) :=
  ReducedDimension.representation_under _ _ _

theorem treeRep_leaf (k : ℕ) : treeRep g (.leaf k)=g.rep k := by
  apply under_injective
  rw [under_treeRep,g.under_rep]
  simp only [Tree.eval,GenericIhara.evalIhara_of]

theorem treeRep_node (t u : UniversalEmbedding.Tree ℕ) :
    treeRep g (.node t u)=IharaLeading.iharaLie (treeRep g t) (treeRep g u) := by
  apply under_injective
  rw [under_treeRep,IharaLeading.actual_ihara_representation (under_treeRep g t) (under_treeRep g u)]
  simp only [Tree.eval,GenericIhara.evalIhara_lie]

theorem tree_leading (t : UniversalEmbedding.Tree ℕ)
    (hactive : ∀ k∈t.leaves,g.active k) :
    embed (treeRep g t)∈above bCount (treeDegree (fun _ => 1) t) ∧
    embed (leading (treeDegree (fun _ => 1) t) (treeRep g t))=positiveInput (embed (t.eval : FreeLieAlgebra K ℕ)) := by
  induction t with
  | leaf k =>
    rw [treeRep_leaf]
    simpa only [treeDegree_leaf,Tree.eval,AssociativeElimination.embed_of] using ⟨g.above_rep k (hactive k (by simp [Tree.leaves])),g.leading_rep k (hactive k (by simp [Tree.leaves]))⟩
  | node t u ht hu =>
    have ht := ht (fun k hk => hactive k (by simp only [Tree.leaves,List.mem_append]; exact Or.inl hk))
    have hu := hu (fun k hk => hactive k (by simp only [Tree.leaves,List.mem_append]; exact Or.inr hk))
    have hs := IharaLeading.actual_leading_ihara
      (ψ:=GenericIhara.evalIhara g.value t.eval) (φ:=GenericIhara.evalIhara g.value u.eval)
      (n:=treeDegree oddWeight t) (m:=treeDegree oddWeight u)
      (by have := treeWeight t; omega) (by have := treeWeight u; omega)
      (homogeneousLie_embed (ReducedDimension.solutions_hom (treeSolution g t)))
      (homogeneousLie_embed (ReducedDimension.solutions_hom (treeSolution g u)))
      (under_treeRep g t) (under_treeRep g u)
      (ReducedDimension.solutions_anti (treeSolution g t))
      (ReducedDimension.solutions_anti (treeSolution g u))
      (treeDegree_pos (wt:=fun _ : ℕ => 1) (by intro k; omega) t) (treeDegree_pos (wt:=fun _ : ℕ => 1) (by intro k; omega) u) ht.1 hu.1
    rw [treeRep_node,treeDegree_node,IharaLeading.embed_iharaLie]
    refine ⟨hs.1,?_⟩
    rw [embed_leading,IharaLeading.embed_iharaLie,hs.2,ht.2,hu.2]
    simp only [Tree.eval,LieHom.map_lie,EvenIndex.map_lie]

theorem bihomogeneous_leading_oai {n r : ℕ} {p : FreeLieAlgebra K ℕ}
    (hp : p∈biPiece oddWeight (fun _ => 1) n r)
    (hactive : ∀ t : UniversalEmbedding.Tree ℕ,treeDegree oddWeight t=n →
      treeDegree (fun _ => 1) t=r → ∀ k∈t.leaves,g.active k) :
    ∃ q : FreeLieAlgebra K Slot,
      under q=embed (GenericIhara.evalIhara g.value p) ∧ embed q∈above bCount r ∧
      embed (leading r q)=positiveInput (embed p) := by
  rw [←biTreeSpan_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,hn,hr,rfl⟩ := hp
    have ht := tree_leading g t (hactive t hn hr)
    exact ⟨treeRep g t,under_treeRep g t,hr ▸ ht.1,hr ▸ ht.2⟩
  | zero => exact ⟨0,by simp,Submodule.zero_mem _,by simp only [embed_leading,map_zero]⟩
  | add p q _ _ hp hq =>
    obtain ⟨p',hp',hpr,hpl⟩ := hp
    obtain ⟨q',hq',hqr,hql⟩ := hq
    refine ⟨p'+q',by simp only [map_add,hp',hq'],?_,?_⟩
    · simpa only [map_add] using (above bCount r).add_mem hpr hqr
    · change embed (eraseLie (LieGrading.piece bCount r (p'+q')))=_
      rw [LieGrading.piece_add,map_add,map_add]
      change embed (leading r p')+embed (leading r q')=_
      rw [hpl,hql,map_add,map_add]
  | smul c p _ hp =>
    obtain ⟨p',hp',hpr,hpl⟩ := hp
    refine ⟨c • p',by simp only [map_smul,hp'],?_,?_⟩
    · simpa only [map_smul] using (above bCount r).smul_mem c hpr
    · change embed (eraseLie (LieGrading.piece bCount r (c • p')))=_
      rw [LieGrading.piece_smul,map_smul,map_smul]
      change c • embed (leading r p')=_
      rw [hpl,map_smul,map_smul]

end NormalizedFamily

end DeligneDrinfeld

end

end OAI

end



section
open OAI.DeligneDrinfeld.NormalizedFamily in
theorem solution : ∀ (g : OAI.DeligneDrinfeld.NormalizedFamily.Data)
    {n r : ℕ} {p : FreeLieAlgebra OAI.DeligneDrinfeld.NormalizedFamily.K ℕ}
    (hp : p ∈ OAI.DeligneDrinfeld.LieGrading.biPiece OAI.DeligneDrinfeld.oddWeight (fun x ↦ 1) n r)
    (hactive :
      ∀ (t : OAI.DeligneDrinfeld.UniversalEmbedding.Tree ℕ),
        OAI.DeligneDrinfeld.LieGrading.treeDegree OAI.DeligneDrinfeld.oddWeight t = n →
          OAI.DeligneDrinfeld.LieGrading.treeDegree (fun x ↦ 1) t = r → ∀ k ∈ t.leaves, g.active k),
    ∃ q,
      OAI.DeligneDrinfeld.QuadraticLeading.under q =
          OAI.DeligneDrinfeld.AssociativeElimination.embed ((OAI.DeligneDrinfeld.GenericIhara.evalIhara g.value) p) ∧
        OAI.DeligneDrinfeld.AssociativeElimination.embed q ∈
            OAI.DeligneDrinfeld.WordGrading.above OAI.DeligneDrinfeld.RowKernel.bCount r ∧
          OAI.DeligneDrinfeld.AssociativeElimination.embed (OAI.DeligneDrinfeld.ImageBound.leading r q) =
            OAI.DeligneDrinfeld.ImageBound.positiveInput (OAI.DeligneDrinfeld.AssociativeElimination.embed p) :=
  @OAI.DeligneDrinfeld.NormalizedFamily.bihomogeneous_leading_oai
end

-- Prove2me | solution 1 for OAI.DeligneDrinfeld.ExactPentagon.row_equation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:54:00.959+00:00
-- url     : https://prove2.me/submissions/da17f035-444e-4e5e-8a9e-dc276588c03a

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid
import Theorems.Thm_OAI_DeligneDrinfeld_ExactCountOrdering_transfer

set_option linter.all false


section

namespace OAI

noncomputable section
namespace DeligneDrinfeld

namespace QuadraticAlphabet
open AssociativeElimination LieAlgebra
attribute [local instance] LieRing.ofAssociativeRing
abbrev F := ZMod 2
instance (α : Type*) : CharP (A F α) 2 :=
  charP_of_injective_ringHom (algebraMap F (A F α)).injective 2

end QuadraticAlphabet

namespace EnvelopingTools
open LieAlgebra
attribute [local instance] LieRing.ofAssociativeRing
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

theorem induction (q : UniversalEnvelopingAlgebra R L)
    {P : UniversalEnvelopingAlgebra R L → Prop}
    (hs : ∀ r, P (algebraMap R _ r))
    (hi : ∀ l, P (UniversalEnvelopingAlgebra.ι R l))
    (ha : ∀ a b, P a → P b → P (a+b))
    (hm : ∀ a b, P a → P b → P (a*b)) : P q := by
  let K : Subalgebra R (UniversalEnvelopingAlgebra R L) :=
    { carrier := {a | P a}
      algebraMap_mem' := hs
      add_mem' := fun ha' hb' => ha _ _ ha' hb'
      mul_mem' := fun ha' hb' => hm _ _ ha' hb' }
  let i : L →ₗ⁅R⁆ K :=
    { (UniversalEnvelopingAlgebra.ι R).toLinearMap.codRestrict K.toSubmodule hi with
      map_lie' := by intro a b; apply Subtype.ext; exact LieHom.map_lie _ a b }
  let f := UniversalEnvelopingAlgebra.lift R i
  have h : K.val.comp f=AlgHom.id R (UniversalEnvelopingAlgebra R L) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro l
    change (f (UniversalEnvelopingAlgebra.ι R l) : UniversalEnvelopingAlgebra R L)=
      UniversalEnvelopingAlgebra.ι R l
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  have hq := (f q).property
  change P ((K.val.comp f) q) at hq
  simpa only [h,AlgHom.id_apply] using hq
end EnvelopingTools

namespace FiberPBW
open AssociativeElimination LieAlgebra
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α G : Type*} [CommRing R] [LieRing G] [LieAlgebra R G]
  (act : G →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α))
local notation "F" => FreeLieAlgebra R α
local notation "B" => UniversalEnvelopingAlgebra R G
abbrev M := SemiDirectSum (R:=R) F G act
local notation "V" => A R α ⊗[R] B

def onLeft (f : Module.End R (A R α)) : Module.End R V :=
  f.rTensor B

def onRight (f : Module.End R B) : Module.End R V :=
  f.lTensor (A R α)

@[simp] theorem onLeft_tmul (f : Module.End R (A R α)) (p : A R α) (b : B) :
    onLeft f (p⊗ₜ b)=f p⊗ₜ b := rfl
@[simp] theorem onRight_tmul (f : Module.End R B) (p : A R α) (b : B) :
    onRight f (p⊗ₜ b)=p⊗ₜ f b := rfl

theorem commute_tensor (f : Module.End R (A R α)) (g : Module.End R B) :
    ⁅onLeft (G:=G) f,onRight (α:=α) g⁆=0 := by
  apply TensorProduct.ext'
  intro p b
  simp

def baseLeft : B →ₐ[R] Module.End R B := Algebra.lsmul R R B

def constant : G →ₗ⁅R⁆ Module.End R V :=
  (Module.End.lTensorAlgHom R B (A R α)).toLieHom.comp
    (baseLeft.toLieHom.comp (UniversalEnvelopingAlgebra.ι R))

def base : G →ₗ⁅R⁆ Module.End R V where
  toFun g := action act g+constant g
  map_add' g h := by simp only [map_add]; abel
  map_smul' r g := by simp only [map_smul,smul_add,RingHom.id_apply]
  map_lie' {g h} := by
    have h1 : ⁅action act g,constant h⁆=0 := commute_tensor _ _
    have h2 : ⁅action act h,constant g⁆=0 := commute_tensor _ _
    change action act ⁅g,h⁆+constant ⁅g,h⁆= _
    rw [LieHom.map_lie,LieHom.map_lie]
    change (action act g*action act h-action act h*action act g)+
      (constant g*constant h-constant h*constant g)=
      (action act g+constant g)*(action act h+constant h)-
      (action act h+constant h)*(action act g+constant g)
    change action act g*constant h-constant h*action act g=0 at h1
    change action act h*constant g-constant g*action act h=0 at h2
    have h1' : action act g*constant h=constant h*action act g := by
      exact (sub_eq_zero (a:=action act g*constant h) (b:=constant h*action act g)).mp h1
    have h2' : action act h*constant g=constant g*action act h := by
      exact (sub_eq_zero (a:=action act h*constant g) (b:=constant g*action act h)).mp h2
    simp only [add_mul,mul_add]
    rw [h1',h2']
    abel

@[simp] theorem base_tmul (g : G) (q : A R α) (b : B) :
    base act g (q⊗ₜ b)=AssociativeDerivations.extend (act g) q⊗ₜ b+
      q⊗ₜ (UniversalEnvelopingAlgebra.ι R g*b) := rfl

theorem compatibility (g : G) (p : F) :
    fiber (G:=G) (act g p)=⁅base act g,fiber (G:=G) p⁆ := by
  apply TensorProduct.ext'
  intro q b
  change fiber (act g p) (q⊗ₜ b)=
    base act g (fiber p (q⊗ₜ b))-fiber p (base act g (q⊗ₜ b))
  simp only [base_tmul,fiber_tmul,map_add,AssociativeDerivations.extend_mul,
    AssociativeDerivations.extend_embed,TensorProduct.add_tmul]
  abel

def representation : M act →ₗ⁅R⁆ Module.End R V :=
  InnerSemiDirect.lift act fiber (base act) (compatibility act)

def operators : UniversalEnvelopingAlgebra R (M act) →ₐ[R] Module.End R V :=
  UniversalEnvelopingAlgebra.lift R (representation act)

def fiberIn : A R α →ₐ[R] UniversalEnvelopingAlgebra R (M act) :=
  lift (fun a => UniversalEnvelopingAlgebra.ι R (SemiDirectSum.inl act (FreeLieAlgebra.of R a)))
def baseIn : B →ₐ[R] UniversalEnvelopingAlgebra R (M act) :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp (SemiDirectSum.inr act))

theorem operators_fiber : (operators act).comp (fiberIn act)=
    (Module.End.rTensorAlgHom R (A R α) B).comp leftMul := by
  apply AssociativeElimination.hom_ext (R:=R) (α:=α)
  intro a
  simp only [AlgHom.comp_apply,fiberIn,lift_atom,operators,UniversalEnvelopingAlgebra.lift_ι_apply,
    representation,InnerSemiDirect.lift_inl,fiber,LieHom.comp_apply,embed_of]
  rfl

theorem operators_base_one (p : B) (b : B) :
    operators act (baseIn act p) ((1 : A R α)⊗ₜ b)=1⊗ₜ (p*b) := by
  induction p using EnvelopingTools.induction generalizing b with
  | hs r => simp [Algebra.algebraMap_eq_smul_one]
  | hi g =>
    simp only [baseIn,UniversalEnvelopingAlgebra.lift_ι_apply,LieHom.comp_apply,
      operators,representation,InnerSemiDirect.lift_inr,base_tmul,
      AssociativeDerivations.extend_one,TensorProduct.zero_tmul,zero_add]
  | ha p q hp hq => simp [hp,hq,add_mul,TensorProduct.tmul_add]
  | hm p q hp hq =>
    simp only [map_mul,Module.End.mul_apply]
    rw [hq,hp,mul_assoc]

def normal : V →ₗ[R] UniversalEnvelopingAlgebra R (M act) :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun b => fiberIn act p*baseIn act b
          map_add' := by intro b c; simp [mul_add]
          map_smul' := by intro r b; simp }
      map_add' := by intro p q; ext b; simp [add_mul]
      map_smul' := by intro r p; ext b; simp }
@[simp] theorem normal_tmul (p : A R α) (b : B) :
    normal act (p⊗ₜ b)=fiberIn act p*baseIn act b := rfl

def extract : UniversalEnvelopingAlgebra R (M act) →ₗ[R] V :=
  (LinearMap.applyₗ ((1 : A R α)⊗ₜ (1 : B))).comp (operators act).toLinearMap

theorem extract_normal (z : V) : extract act (normal act z)=z := by
  have h : (extract act).comp (normal act)=LinearMap.id := by
    apply TensorProduct.ext'
    intro p b
    change operators act (fiberIn act p*baseIn act b) (1⊗ₜ (1 : B))=p⊗ₜ b
    rw [map_mul,Module.End.mul_apply,operators_base_one,mul_one]
    have hh := AlgHom.congr_fun (operators_fiber act) p
    change operators act (fiberIn act p) (1⊗ₜ b)=p⊗ₜ b
    simp only [AlgHom.comp_apply] at hh
    rw [hh]
    change (p*1)⊗ₜ b=p⊗ₜ b
    rw [mul_one]
  exact LinearMap.congr_fun h z

theorem normal_injective : Function.Injective (normal act) :=
  Function.LeftInverse.injective (extract_normal act)

end FiberPBW

namespace GenericBraid
open LieAlgebra FreeDerivations
variable {R α : Type*} [CommRing R]

variable {E : Type*} [LieRing E] [LieAlgebra R E]

variable [DecidableEq α]
local notation "F" => FreeLieAlgebra R α
local notation "SD" => SemiDirectSum F (T R α) action
def fiber (i : α) : SD := SemiDirectSum.inl action (FreeLieAlgebra.of R i)
def base (i j : α) : SD := SemiDirectSum.inr action (t i j)
def chord : Option α → Option α → SD
  | none, none => 0
  | none, some j => fiber j
  | some i, none => fiber i
  | some i, some j => base i j
@[simp] theorem chord_nn : chord (R:=R) (α:=α) none none=0 := rfl
@[simp] theorem chord_ns (i : α) : chord (R:=R) none (some i)=fiber i := rfl
@[simp] theorem chord_sn (i : α) : chord (R:=R) (some i) none=fiber i := rfl
@[simp] theorem chord_ss (i j : α) : chord (R:=R) (some i) (some j)=base i j := rfl
@[simp] theorem chord_self (i : Option α) : chord (R:=R) i i=0 := by
  cases i <;> simp [base]
theorem chord_comm (i j : Option α) : chord (R:=R) i j=chord j i := by
  cases i <;> cases j <;> simp [base,t_comm]
theorem base_fiber (i j k : α) : ⁅base (R:=R) i j,fiber k⁆=
    SemiDirectSum.inl action (pair (R:=R) i j (FreeLieAlgebra.of R k)) := by
  simp [base,fiber]
theorem fiber_base (i j k : α) : ⁅fiber (R:=R) k,base i j⁆=
    -SemiDirectSum.inl action (pair (R:=R) i j (FreeLieAlgebra.of R k)) := by
  rw [← lie_skew,base_fiber]
theorem chord_disjoint (i j k l : Option α)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅chord (R:=R) i j,chord (R:=R) k l⁆=0 := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp_all [base,fiber,t_disjoint]
  all_goals apply pair_of_other <;> intro h <;> subst_vars <;> contradiction
theorem chord_three (i j k : Option α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅chord (R:=R) i j,chord (R:=R) i k+chord (R:=R) j k⁆=0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      cases k with
      | none => exact (hik rfl).elim
      | some k =>
        rw [chord_ns,chord_ns,chord_ss,lie_add,fiber_base]
        simp [fiber]
        grind [lie_skew]
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact (hjk rfl).elim
      | some k =>
        rw [chord_sn,chord_ss,chord_ns,lie_add,fiber_base]
        simp [fiber]
        grind [lie_skew]
    | some j =>
      cases k with
      | none =>
        rw [chord_ss,chord_sn,chord_sn,lie_add,base_fiber,base_fiber]
        simp only [pair_of_left,pair_of_right,← map_add]
        grind [lie_skew]
      | some k =>
        simp only [chord_ss,base,← map_add,← LieHom.map_lie]
        rw [t_three _ _ _ (fun h => hij (congrArg some h))
          (fun h => hik (congrArg some h)) (fun h => hjk (congrArg some h)),map_zero]
def toSemidirect : T R (Option α) →ₗ⁅R⁆ SD :=
  lift chord chord_self chord_comm chord_disjoint chord_three
@[simp] theorem toSemidirect_t (i j : Option α) : toSemidirect (t (R:=R) i j)=chord i j := by
  simp [toSemidirect]
end GenericBraid

namespace RestrictedAlphabet
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
abbrev F := ZMod 2
variable {α : Type*}
abbrev S (α : Type*) := A F (Letter α)
abbrev T (α : Type*) := A F (Option α)
def a : S α := atom .a
def b (i : α) : S α := atom (.b i)
def c (i : α) : S α := atom (.c i)
def y (i : α) : T α := atom (some i)
def x : T α := atom none
def delta : Module.End F (S α) := deriv (fun (l : Letter α) => match l with | .a => 0 | .c i => ⁅(a : S α),b i⁆ | .b i => c i)
@[simp] theorem delta_a : delta (a : S α)=0 := by simp [delta,a]
@[simp] theorem delta_b (i : α) : delta (b i)=c i := by simp [delta,b]
@[simp] theorem delta_c (i : α) : delta (c i)=⁅(a : S α),b i⁆ := by simp [delta,c]
@[simp] theorem delta_one : delta (1 : S α)=0 := deriv_one _
theorem delta_mul (p q : S α) : delta (p*q)=delta p*q+p*delta q := deriv_mul _ _ _
theorem delta_lie (p q : S α) : delta ⁅p,q⁆=⁅delta p,q⁆+⁅p,delta q⁆ := deriv_lie _ _ _
theorem delta_square_mul (p q : S α) :
    delta (delta (p*q))=delta (delta p)*q+p*delta (delta q) := by
  rw [delta_mul,map_add,delta_mul,delta_mul]
  calc
    _ = delta (delta p)*q+p*delta (delta q)+(delta p*delta q+delta p*delta q) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
theorem delta_square (p : S α) : delta (delta p)=⁅(a : S α),p⁆ := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp [Ring.lie_def]
  | ha l =>
    cases l with
    | a => change delta (delta a)=⁅a,a⁆; simp
    | c i => change delta (delta (c i))=⁅a,c i⁆; simp [delta_lie]
    | b i => change delta (delta (b i))=⁅(a : S α),b i⁆; simp
  | hadd p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hm p q hp hq => rw [delta_square_mul,hp,hq]; simp [Ring.lie_def]; noncomm_ring

def left : S α →ₐ[F] Module.End F (S α×S α) where
  toFun p :=
    { toFun := fun z => (p*z.1,p*z.2)
      map_add' := by intro z w; ext <;> simp [mul_add]
      map_smul' := by intro r z; ext <;> simp }
  map_one' := by ext z <;> simp
  map_mul' := by intro p q; ext z <;> simp [mul_assoc]
  map_zero' := by ext z <;> simp
  map_add' := by intro p q; ext z <;> simp [add_mul]
  commutes' := by intro r; ext z <;> simp [Algebra.algebraMap_eq_smul_one]
@[simp] theorem left_apply (p : S α) (z : S α×S α) : left p z=(p*z.1,p*z.2) := rfl

def root : Module.End F (S α×S α) where
  toFun z := (delta z.1+z.2*a,z.1+delta z.2)
  map_add' := by intro z w; apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,map_add,add_mul] <;> abel
  map_smul' := by intro r z; ext <;> simp [smul_add]
@[simp] theorem root_apply (z : S α×S α) : root z=(delta z.1+z.2*a,z.1+delta z.2) := rfl
theorem root_comm (p : S α) : ⁅(root : Module.End F (S α×S α)),left p⁆=left (delta p) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp [Ring.lie_def,delta_mul,Module.End.mul_apply,mul_add,mul_assoc]
theorem root_square : root*root=left (a : S α) := by
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

def substitution : S α →ₐ[F] T α := lift (fun | .a => x*x | .c i => ⁅(x : T α),y i⁆ | .b i => y i)
@[simp] theorem substitution_a : substitution (a : S α)=x*x := by simp [substitution,a]
@[simp] theorem substitution_c (i : α) : substitution (c i)=⁅(x : T α),y i⁆ := by simp [substitution,c]
@[simp] theorem substitution_b (i : α) : substitution (b i)=y i := by simp [substitution,b]
def representation : T α →ₐ[F] Module.End F (S α×S α) :=
  lift (fun | none => root | some i => left (b i))
@[simp] theorem representation_x : representation (x : T α)=root := by simp [representation,x]
@[simp] theorem representation_y (i : α) : representation (y i)=left (b i) := by simp [representation,y]
theorem representation_substitution : representation.comp substitution=left (α:=α) := by
  apply hom_ext
  intro l
  cases l with
  | a => change representation (substitution a)=left a; simp [root_square]
  | c i =>
    change representation (substitution (c i))=left (c i)
    rw [substitution_c]
    change representation (x*y i-y i*x)=left (c i)
    rw [map_sub,map_mul,map_mul,representation_x,representation_y]
    exact (root_comm (b i)).trans (congrArg left (delta_b i))
  | b i => change representation (substitution (b i))=left (b i); simp

theorem injective : Function.Injective (substitution (α:=α)) := by
  intro p q hpq
  have h := congrArg representation hpq
  have hh (v : S α) : representation (substitution v)=left v := AlgHom.congr_fun representation_substitution v
  rw [hh,hh] at h
  have he := congrArg (fun f : Module.End F (S α×S α) => (f (1,0)).1) h
  simpa only [left_apply,mul_one] using he
end RestrictedAlphabet

namespace GenericBraid
open LieAlgebra AssociativeElimination
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R] [DecidableEq α]

omit [DecidableEq α] in
theorem hom_ext {E : Type*} [LieRing E] [LieAlgebra R E]
    {f g : T R α →ₗ⁅R⁆ E} (h : ∀ i j, f (t i j)=g (t i j)) : f=g := by
  let q : Free R α →ₗ⁅R⁆ T R α :=
    { (ideal (R:=R) (α:=α)).mkQ with map_lie' := by intros; rfl }
  have hh : f.comp q=g.comp q := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨i,j⟩
    exact h i j
  apply LieHom.ext
  intro a
  induction a using Submodule.Quotient.induction_on with | _ a =>
    exact LieHom.congr_fun hh a

def toSemi : Env R (Option α) →ₐ[R] UniversalEnvelopingAlgebra R
    (SemiDirectSum (FreeLieAlgebra R α) (T R α) action) :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp toSemidirect)

theorem toSemi_fiber : toSemi.comp fiberIn=FiberPBW.fiberIn (action (R:=R) (α:=α)) := by
  apply AssociativeElimination.hom_ext
  intro i
  simp [toSemi,fiberIn,FiberPBW.fiberIn,fiber]

theorem toSemi_base : toSemi.comp baseIn=FiberPBW.baseIn (action (R:=R) (α:=α)) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply hom_ext
  intro i j
  simp [toSemi,baseIn,FiberPBW.baseIn,base]

def normal : A R α ⊗[R] Env R α →ₗ[R] Env R (Option α) :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun b => fiberIn p*baseIn b
          map_add' := by intro b c; simp [mul_add]
          map_smul' := by intro r b; simp }
      map_add' := by intro p q; ext b; simp [add_mul]
      map_smul' := by intro r p; ext b; simp }
omit [DecidableEq α] in
@[simp] theorem normal_tmul (p : A R α) (b : Env R α) :
    normal (p⊗ₜ b)=fiberIn p*baseIn b := rfl

theorem toSemi_normal : toSemi.toLinearMap.comp normal=
    FiberPBW.normal (action (R:=R) (α:=α)) := by
  apply TensorProduct.ext'
  intro p b
  change toSemi (fiberIn p*baseIn b)=_
  rw [map_mul]
  have hf := AlgHom.congr_fun (toSemi_fiber (R:=R) (α:=α)) p
  have hb := AlgHom.congr_fun (toSemi_base (R:=R) (α:=α)) b
  exact congrArg₂ (·*·) hf hb

theorem normal_injective : Function.Injective (normal (R:=R) (α:=α)) := by
  intro a b h
  apply FiberPBW.normal_injective (action (R:=R) (α:=α))
  have he (z) := LinearMap.congr_fun (toSemi_normal (R:=R) (α:=α)) z
  rw [← he a,← he b]
  exact congrArg toSemi h
end GenericBraid

namespace Deletion

section
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
theorem word_cons (a : α) (s : List α) : word (R:=R) (a::s)=atom a*word s := by
  simp only [word,atom,MonoidAlgebra.single_mul_single,one_mul,FreeMonoid.ofList_cons]

theorem op_cons (ν : α → α → R) (l r a : α) (s : List α) :
    op ν l r (word (a::s))=(ν a (s.headD r)-ν l a) • word s+atom a*op ν a r (word s) := by
  simp only [op_word,raw]
theorem op_mul_word (ν : α → α → R) (l r a : α) (s : List α) :
    op ν l r (atom a*word s)=(ν a (s.headD r)-ν l a) • word s+atom a*op ν a r (word s) := by
  rw [← word_cons,op_cons]

theorem op_two (ν : α → α → R) (l r a b : α) (p : A R α) :
    op ν l r (atom a*(atom b*p))=(ν a b-ν l a) • (atom b*p)+atom a*op ν a r (atom b*p) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    have h := op_cons ν l r a (b::w.toList)
    simp only [word_cons,List.headD_cons] at h
    simpa only [word,FreeMonoid.ofList_toList,MonoidAlgebra.of_apply] using h
  | add p q hp hq => simp only [mul_add,map_add,smul_add,hp,hq]; abel
  | smul c p hp => simp only [mul_smul_comm,map_smul,hp,smul_add,smul_smul]; rw [mul_comm c]

def curvature (ν μ : α → α → R) (l a b c : α) : R :=
  (ν a b-ν l a)*(μ b c-μ l b)+(ν b c-ν a b)*(μ a c-μ l a)-
  (μ a b-μ l a)*(ν b c-ν l b)-(μ b c-μ a b)*(ν a c-ν l a)

theorem comm_cons (ν μ : α → α → R) (l r a b : α) (s : List α) :
    op μ l r (op ν l r (word (a::b::s)))-op ν l r (op μ l r (word (a::b::s)))=
      curvature ν μ l a b (s.headD r) • word s+
        atom a*(op μ a r (op ν a r (word (b::s)))-op ν a r (op μ a r (word (b::s)))) := by
  simp only [word_cons,op_two,op_mul_word,map_add,map_smul,mul_add,mul_smul_comm,
    mul_sub,smul_add,curvature]
  module

end

open AssociativeElimination
variable {R α : Type*} [CommRing R]

theorem op_list_sum {ι : Type*} (ν : ι → α → α → R) (s : List ι) (l r : α) :
    op (fun a b => (s.map (fun i => ν i a b)).sum) l r=(s.map (fun i => op (ν i) l r)).sum := by
  induction s with
  | nil => simp
  | cons i s ih => simpa only [List.map_cons,List.sum_cons,op_add] using congrArg (op (ν i) l r+·) ih
end Deletion

namespace DeletionTable
open Deletion AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
instance : Fintype Letter := ⟨{.o,.e,.p,.w}, by intro x; cases x <;> simp⟩
open Letter Hyperplane

def weight : Hyperplane → Letter → Letter → ℤ
  | .p23, .o, .p | .p23, .p, .o => 1
  | .m23, .o, .p | .m23, .p, .o => -1
  | .p12, .o, .w | .p12, .w, .o => 1
  | .m12, .o, .w | .m12, .w, .o => -1
  | .a3, .e, .p | .a3, .p, .e => 1
  | .m23, .e, .p | .m23, .p, .e => -1
  | .a1, .e, .w | .a1, .w, .e => 1
  | .m12, .e, .w | .m12, .w, .e => -1
  | .a2, .p, .w | .a2, .w, .p => 1
  | .p13, .p, .w | .p13, .w, .p => 1
  | .m12, .p, .w | .m12, .w, .p => -1
  | .m23, .p, .w | .m23, .w, .p => -1
  | _, _, _ => 0

end DeletionTable

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

namespace PolynomialOrdering
open AssociativeElimination
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α β : Type*} [CommRing R]
variable (δ : β → α → A R α)

variable {U : Type*} [Ring U] [Algebra R U]

variable (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)
variable (hδ : ∀ b a,g (atom b)*f (atom a)-f (atom a)*g (atom b)=f (δ b a))
include hδ
theorem commutator (b : β) (p : A R α) :
    g (atom b)*f p-f p*g (atom b)=f (deriv (δ b) p) := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp
  | ha a => simpa using hδ b a
  | hadd p q hp hq => simp only [map_add,mul_add,add_mul]; rw [← hp,← hq]; abel
  | hs r p hp => simp only [map_smul,mul_smul_comm,smul_mul_assoc,← smul_sub,hp]
  | hm p q hp hq =>
    rw [AssociativeElimination.deriv_mul,map_add,map_mul,map_mul,map_mul,← hp,← hq]
    noncomm_ring

theorem interpret_op (s : Sum α β) (z : V (R:=R) (α:=α) (β:=β)) :
    interpret f g (op δ s z)=evaluate f g (atom s)*interpret f g z := by
  have h : (interpret f g).comp (op δ s)=
      (Algebra.lmul R U (evaluate f g (atom s))).comp (interpret f g) := by
    apply TensorProduct.ext'
    intro p q
    cases s with
    | inl a => simp [op,evaluate,mul_assoc]
    | inr b =>
      simp only [LinearMap.comp_apply,op,Sum.elim_inr,baseOp_tmul,map_add,interpret_tmul,
        evaluate,lift_atom,map_mul]
      change f (deriv (δ b) p)*g q+f p*(g (atom b)*g q)=g (atom b)*(f p*g q)
      rw [← commutator δ f g hδ b p]
      noncomm_ring
  exact LinearMap.congr_fun h z

theorem interpret_operators (p : A R (Sum α β)) (z : V (R:=R) (α:=α) (β:=β)) :
    interpret f g (operators δ p z)=evaluate f g p*interpret f g z := by
  induction p using QuadraticAlphabet.algebra_induction generalizing z with
  | h1 => simp
  | ha s => simpa [operators] using interpret_op δ f g hδ s z
  | hadd p q hp hq => simp [hp,hq,add_mul]
  | hs r p hp => simp [hp]
  | hm p q hp hq => simp only [map_mul,Module.End.mul_apply,hp,hq,mul_assoc]

theorem interpret_normalize (p : A R (Sum α β)) :
    interpret f g (normalize δ p)=evaluate f g p := by
  change interpret f g (operators δ p (1⊗ₜ 1))=_
  rw [interpret_operators δ f g hδ,interpret_tmul,map_one,map_one,mul_one,mul_one]

omit hδ

end PolynomialOrdering

namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]

theorem homogeneous_above {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : p∈above wt n := space_mono (by intros; omega) hp

end WordGrading

namespace CountTables

section
open AssociativeElimination

open WordGrading

end

open AssociativeElimination
def δ (i : Fin 2) : A K G →ₗ[K] A K G := deriv (fun a => if a=0 ∨ a.val=i.val+1 then C i else 0)
def ε : A K G →ₗ[K] A K G := deriv (fun a => if a=0 then 0 else bracket (Y 0) (Y 1))
def baseDeriv : B → A K G →ₗ[K] A K G
  | 0 => (δ 0).comp (δ 0)
  | 1 => (δ 1).comp (δ 1)
  | 2 => ε
  | _ => (δ 0).comp ε-ε.comp (δ 0)

theorem bracket_swap (p q : A K G) : bracket p q=bracket q p := by simp [bracket,CharTwo.sub_eq_add,add_comm]
theorem bracket_ad_square (u v : A K G) : bracket u (bracket u v)=bracket (u*u) v := by
  simp only [bracket,sub_eq_add_neg,CharTwo.neg_eq,mul_add,add_mul,mul_assoc]
  calc
    _ = u*(u*v)+v*(u*u)+(u*(v*u)+u*(v*u)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
theorem bracket_leibniz (p q r : A K G) : bracket p (bracket q r)=bracket (bracket p q) r+bracket q (bracket p r) := by
  simp only [bracket]; noncomm_ring
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
theorem bracket_X_Y (i : Fin 2) : bracket X (Y i)=C i := rfl
theorem bracket_X_C (i : Fin 2) : bracket X (C i)=bracket (X*X) (Y i) := bracket_ad_square _ _
@[simp] theorem δ_C_self (i : Fin 2) : δ i (C i)=bracket (X*X+C i) (Y i) := by
  change δ i (bracket X (Y i))=_
  rw [δ_bracket,δ_X,δ_Y_self,bracket_X_C,bracket_add_left]
  exact add_comm _ _
@[simp] theorem δ_C_other (i j : Fin 2) (h : j≠i) : δ i (C j)=bracket (C i) (Y j) := by
  rw [C,δ_bracket,δ_X,δ_Y_other i j h,bracket_zero_right,add_zero]
@[simp] theorem ε_X : ε X=0 := by simp [ε,X]
@[simp] theorem ε_Y (i : Fin 2) : ε (Y i)=bracket (Y 0) (Y 1) := by simp [ε,Y]
@[simp] theorem ε_bracket (p q : A K G) : ε (bracket p q)=bracket (ε p) q+bracket p (ε q) := deriv_bracket _ _ _
@[simp] theorem ε_H : ε (X*X)=0 := by simp [ε,AssociativeElimination.deriv_mul,X]
theorem ε_C (i : Fin 2) : ε (C i)=bracket (C 0) (Y 1)+bracket (Y 0) (C 1) := by
  rw [C,ε_bracket,ε_X,ε_Y,bracket_zero_left,zero_add,bracket_leibniz]
  rfl

def J := baseDeriv 3
@[simp] theorem J_X : J X=bracket (C 0) (Y 1)+bracket (Y 0) (C 1) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_X,map_zero,δ_X,ε_C]
  simp only [zero_sub,CharTwo.neg_eq]
@[simp] theorem J_Y_zero : J (Y 0)=bracket (Y 0) (C 1) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_Y,δ_bracket,δ_Y_self,
    δ_Y_other 0 1 (by decide),bracket_zero_right,add_zero,ε_C]
  simp only [sub_add_eq_sub_sub,sub_self,zero_sub,CharTwo.neg_eq]
@[simp] theorem J_Y_one : J (Y 1)=bracket (Y 1) (C 0) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_Y,δ_bracket,δ_Y_self,
    δ_Y_other 0 1 (by decide),bracket_zero_right,add_zero,map_zero,sub_zero]
  exact bracket_swap _ _
@[simp] theorem J_bracket (p q : A K G) : J (bracket p q)=bracket (J p) q+bracket p (J q) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_bracket,δ_bracket,map_add,
    bracket_sub_left,bracket_sub_right]
  abel
@[simp] theorem J_mul (p q : A K G) : J (p*q)=J p*q+p*J q := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε,δ,AssociativeElimination.deriv_mul,
    map_add,sub_mul,mul_sub]
  abel
@[simp] theorem J_H : J (X*X)=bracket (X*X) (bracket (Y 0) (Y 1)) := by
  rw [J_mul,J_X]
  have h : bracket (C 0) (Y 1)+bracket (Y 0) (C 1)=bracket X (bracket (Y 0) (Y 1)) :=
    (bracket_leibniz X (Y 0) (Y 1)).symm
  rw [h,← bracket_ad_square]
  simp only [bracket,CharTwo.sub_eq_add]
  exact add_comm _ _
@[simp] theorem J_C_zero : J (C 0)=bracket (C 0) (C 1)+
    bracket (bracket (C 0) (Y 1)+bracket (Y 0) (C 1)) (Y 0)+bracket (Y 0) (bracket (X*X) (Y 1)) := by
  change J (bracket X (Y 0))=_
  rw [J_bracket,J_X,J_Y_zero,bracket_leibniz,bracket_X_C]
  rw [bracket_X_Y 0,add_left_comm,← add_assoc]
@[simp] theorem J_C_one : J (C 1)=bracket (C 0) (C 1)+
    bracket (bracket (C 0) (Y 1)+bracket (Y 0) (C 1)) (Y 1)+bracket (Y 1) (bracket (X*X) (Y 0)) := by
  change J (bracket X (Y 1))=_
  rw [J_bracket,J_X,J_Y_one,bracket_leibniz,bracket_X_C]
  rw [bracket_X_Y 1,bracket_swap (C 1) (C 0),add_left_comm,← add_assoc]

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
 theorem source_realization_a0 (a : F) : baseDeriv 0 (realize (atom a))=realize (source 0 a) := by
  fin_cases a <;> simp [source,common,higher,R',Q,baseDeriv,δ_Y_other 0 1 (by decide)]
  · exact add_comm _ _
  · rw [add_add_add_comm,CharTwo.add_self_eq_zero,zero_add]
 theorem source_realization_a1 (a : F) : baseDeriv 1 (realize (atom a))=realize (source 1 a) := by
  fin_cases a <;> simp [source,common,higher,R',Q,baseDeriv,δ_Y_other 1 0 (by decide)]
  · exact add_comm _ _
  · rw [add_add_add_comm,CharTwo.add_self_eq_zero,zero_add]
 theorem source_realization_u (a : F) : baseDeriv 2 (realize (atom a))=realize (source 2 a) := by
  fin_cases a <;> simp [source,common,higher,W,baseDeriv,ε_C]
 theorem source_realization_v (a : F) : baseDeriv 3 (realize (atom a))=realize (source 3 a) := by
  change J (realize (atom a))=_
  fin_cases a <;> simp [source,common,higher,R',W,add_assoc]
  have h := J_H
  rw [J_mul,J_X] at h
  exact h
theorem source_realization (b : B) (a : F) : baseDeriv b (realize (atom a))=realize (source b a) := by
  fin_cases b
  · exact source_realization_a0 a
  · exact source_realization_a1 a
  · exact source_realization_u a
  · exact source_realization_v a
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

namespace PolynomialOrdering
open AssociativeElimination
open scoped TensorProduct
variable {R α β U : Type*} [CommRing R] [Ring U] [Algebra R U]
variable (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)

theorem evaluate_merge (z : V (R:=R) (α:=α) (β:=β)) :
    evaluate f g (merge z)=interpret f g z := by
  have h : (evaluate f g).toLinearMap.comp merge=interpret f g := by
    apply TensorProduct.ext'
    intro p q
    simp
  exact LinearMap.congr_fun h z

theorem evaluate_ordered (δ : β → α → A R α)
    (hδ : ∀ b a,g (atom b)*f (atom a)-f (atom a)*g (atom b)=f (δ b a))
    (p : A R (Sum α β)) : evaluate f g (ordered δ p)=evaluate f g p := by
  change evaluate f g (merge (normalize δ p))=_
  rw [evaluate_merge,interpret_normalize δ f g hδ]

theorem evaluate_baseStage (s : A R β →ₗ[R] A R β) (hs : ∀ q,g (s q)=g q)
    (z : V (R:=R) (α:=α) (β:=β)) : evaluate f g (baseStage s z)=interpret f g z := by
  have h : (evaluate f g).toLinearMap.comp (baseStage s)=interpret f g := by
    apply TensorProduct.ext'
    intro p q
    simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,baseStage_tmul,map_mul,
      evaluate_fiber,evaluate_base,hs,interpret_tmul]
  exact LinearMap.congr_fun h z

theorem evaluate_iterated (δ : β → α → A R α)
    (hδ : ∀ b a,g (atom b)*f (atom a)-f (atom a)*g (atom b)=f (δ b a))
    (s : A R β →ₗ[R] A R β) (hs : ∀ q,g (s q)=g q)
    (p : A R (Sum α β)) : evaluate f g (iterated δ s p)=evaluate f g p := by
  change evaluate f g (baseStage s (normalize δ p))=_
  rw [evaluate_baseStage f g s hs,interpret_normalize δ f g hδ]

end PolynomialOrdering

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

theorem fiberIn_injective (α : Type*) [DecidableEq α] :
    Function.Injective (GenericBraid.fiberIn (R:=K) (α:=α)) := by
  intro p q h
  have hh : p⊗ₜ[K] (1 : Env α)=q⊗ₜ[K] (1 : Env α) := by
    apply GenericBraid.normal_injective
    simpa only [GenericBraid.normal_tmul,map_one,mul_one] using h
  have hh' := congrArg (fun z => TensorProduct.rid K (A K α)
    (TensorProduct.map LinearMap.id (augment α).toLinearMap z)) hh
  simpa only [TensorProduct.map_tmul,LinearMap.id_apply,AlgHom.toLinearMap_apply,map_one,
    TensorProduct.rid_tmul,one_smul] using hh'

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
namespace SourceAlphabet
open AssociativeElimination AlphabetTransport
abbrev K := ZMod 2
variable {α β : Type*}
theorem map_cancel (f : α → β) (g : β → α) (he : ∀ a,g (f a)=a) (p : A K α) :
    map g (map f p)=p := by
  have h : (map (R:=K) g).comp (map f)=AlgHom.id K (A K α) := by
    apply hom_ext
    intro a
    simp [he]
  exact AlgHom.congr_fun h p

theorem map_injective (f : α → β) (g : β → α) (he : ∀ a,g (f a)=a) :
    Function.Injective (map (R:=K) f) :=
  Function.LeftInverse.injective (map_cancel f g he)

theorem realize_factor : (map (R:=K) letter3).comp CountTables.realize=
    RestrictedAlphabet.substitution.comp (map letter5) := by
  apply hom_ext
  intro a
  fin_cases a <;> simp [CountTables.realize,CountTables.X,CountTables.Y,CountTables.C,
    CountTables.bracket,letter3,letter5,RestrictedAlphabet.substitution,RestrictedAlphabet.x,
    RestrictedAlphabet.y,
    Ring.lie_def]

theorem realize_injective : Function.Injective CountTables.realize := by
  intro p q h
  apply (map_injective letter5 letter5.symm letter5.symm_apply_apply)
  apply RestrictedAlphabet.injective
  have he (z) := AlgHom.congr_fun realize_factor z
  simp only [AlgHom.comp_apply] at he
  rw [← he p,← he q]
  exact congrArg (map letter3) h

end SourceAlphabet
namespace SourceModel
open AssociativeElimination AlphabetTransport SourceEnveloping
open scoped TensorProduct

def swap : S1 ≃ S1 where
  toFun | none => some () | some _ => none
  invFun | none => some () | some _ => none
  left_inv s := by cases s with | none => rfl | some a => cases a; rfl
  right_inv s := by cases s with | none => rfl | some a => cases a; rfl

def smallLetters : SecondStage.F ≃ RestrictedAlphabet.Letter Unit where
  toFun | 0 => .a | 1 => .b () | 2 => .c ()
  invFun | .a => 0 | .b _ => 1 | .c _ => 2
  left_inv a := by fin_cases a <;> rfl
  right_inv s := by cases s with | a => rfl | b i => cases i; rfl | c i => cases i; rfl

def secondRealize : A K SecondStage.F →ₐ[K] A K S1 :=
  (map swap).comp (RestrictedAlphabet.substitution.comp (map smallLetters))
theorem secondRealize_injective : Function.Injective secondRealize :=
  (SourceAlphabet.map_injective swap swap.symm swap.symm_apply_apply).comp
    (RestrictedAlphabet.injective.comp
      (SourceAlphabet.map_injective smallLetters smallLetters.symm smallLetters.symm_apply_apply))

def square : A K Unit →ₐ[K] A K Unit := lift (fun _ => atom ()*atom ())
theorem square_injective : Function.Injective square := by
  intro p q h
  apply SourceAlphabet.map_injective (fun _ : Unit => (0 : SecondStage.F)) (fun _ => ())
    (by intro a; cases a; rfl)
  apply secondRealize_injective
  have he : secondRealize.comp (map (fun _ : Unit => (0 : SecondStage.F)))=
      (map (fun _ : Unit => (some () : S1))).comp square := by
    apply hom_ext
    intro a
    simp [secondRealize,smallLetters,swap,RestrictedAlphabet.substitution,
      RestrictedAlphabet.x,square]
  have hp := AlgHom.congr_fun he p
  have hq := AlgHom.congr_fun he q
  simp only [AlgHom.comp_apply] at hp hq
  rw [hp,hq,h]

def tail : A K Unit →ₐ[K] Env S1 := GenericBraid.fiberIn.comp square
theorem tail_injective : Function.Injective tail := fiberIn_injective Unit|>.comp square_injective

def secondFiber : A K SecondStage.F →ₐ[K] Env S2 := GenericBraid.fiberIn.comp secondRealize
def secondBase : A K Unit →ₐ[K] Env S2 := GenericBraid.baseIn.comp tail

def secondNormal : (A K SecondStage.F ⊗[K] A K Unit) →ₗ[K] Env S2 :=
  GenericBraid.normal.comp (TensorProduct.map secondRealize.toLinearMap tail.toLinearMap)
@[simp] theorem secondNormal_tmul (p : A K SecondStage.F) (q : A K Unit) :
    secondNormal (p⊗ₜ[K]q)=secondFiber p*secondBase q := rfl

theorem secondNormal_injective : Function.Injective secondNormal :=
  GenericBraid.normal_injective.comp (TensorProduct.map_injective_of_flat_flat
    secondRealize.toLinearMap tail.toLinearMap secondRealize_injective tail_injective)

def tripleNormal : (A K CountTables.F ⊗[K] (A K SecondStage.F ⊗[K] A K Unit)) →ₗ[K] Env S3 :=
  GenericBraid.normal.comp (TensorProduct.map topRealize.toLinearMap secondNormal)

theorem tripleNormal_injective : Function.Injective tripleNormal :=
  GenericBraid.normal_injective.comp (TensorProduct.map_injective_of_flat_flat
    topRealize.toLinearMap secondNormal
    ((SourceAlphabet.map_injective topLetters topLetters.symm topLetters.symm_apply_apply).comp
      SourceAlphabet.realize_injective) secondNormal_injective)

end SourceModel

namespace CharTwoAction
attribute [local instance] LieRing.ofAssociativeRing
variable {U : Type*} [Ring U] [CharP U 2]
theorem symm (u v : U) : ⁅u,v⁆=⁅v,u⁆ := by
  simp only [Ring.lie_def,CharTwo.sub_eq_add,add_comm]
theorem square (u v : U) : ⁅u*u,v⁆=⁅u,⁅u,v⁆⁆ := by
  simp only [Ring.lie_def,CharTwo.sub_eq_add,mul_add,add_mul,mul_assoc]
  have h : u*(u*v)+v*(u*u)+(u*(v*u)+u*(v*u))=
      u*(u*v)+u*(v*u)+(u*(v*u)+v*(u*u)) := by abel
  simpa only [CharTwo.add_self_eq_zero,add_zero] using h
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

theorem raw_epsilon_atoms (a : CountTables.G) :
    ⁅baseU,rawFiber (atom a)⁆=rawFiber (CountTables.ε (atom a)) := by
  fin_cases a <;>
    simp [CountTables.ε,CountTables.bracket,topLetters]
  · exact base_fiber_other one two root (by decide) (by decide)
  · exact base_fiber_left one two
  · exact (base_fiber_right one two).trans (CharTwoAction.symm _ _)

theorem raw_epsilon (p : A K CountTables.G) :
    ⁅baseU,rawFiber p⁆=rawFiber (CountTables.ε p) := by
  exact AssociativeAction.of_atoms rawFiber baseU _
    (fun a => by simpa only [CountTables.ε,deriv_atom] using raw_epsilon_atoms a) p

theorem baseDeriv_action (b : CountTables.B) (p : A K CountTables.G) :
    ⁅topBase (atom b),rawFiber p⁆=rawFiber (CountTables.baseDeriv b p) := by
  fin_cases b
  · change ⁅topBase (atom 0),rawFiber p⁆=rawFiber (CountTables.δ 0 (CountTables.δ 0 p))
    have h : topBase (atom 0)=baseX 0*baseX 0 := by simp [topBase,oldBase,baseX]
    rw [h,CharTwoAction.square,raw_delta,raw_delta]
  · change ⁅topBase (atom 1),rawFiber p⁆=rawFiber (CountTables.δ 1 (CountTables.δ 1 p))
    have h : topBase (atom 1)=baseX 1*baseX 1 := by simp [topBase,oldBase,baseX]
    rw [h,CharTwoAction.square,raw_delta,raw_delta]
  · change ⁅topBase (atom 2),rawFiber p⁆=rawFiber (CountTables.ε p)
    have h : topBase (atom 2)=baseU := by simp [topBase,oldBase,baseU]
    rw [h,raw_epsilon]
  · change ⁅topBase (atom 3),rawFiber p⁆=rawFiber (CountTables.δ 0 (CountTables.ε p)-CountTables.ε (CountTables.δ 0 p))
    have h : topBase (atom 3)=⁅baseX 0,baseU⁆ := by simp [topBase,oldBase,baseU,baseX,Ring.lie_def]
    rw [h,lie_lie,raw_epsilon,raw_delta,raw_delta,raw_epsilon]
    change _=rawFiber (CountTables.δ 0 (CountTables.ε p)-CountTables.ε (CountTables.δ 0 p))
    rw [map_sub]

theorem topFiber_eq (p : A K CountTables.F) : topFiber p=rawFiber (CountTables.realize p) := rfl

theorem top_action (b : CountTables.B) (a : CountTables.F) :
    topBase (atom b)*topFiber (atom a)-topFiber (atom a)*topBase (atom b)=
      topFiber (CountTables.source b a) := by
  change ⁅topBase (atom b),topFiber (atom a)⁆=topFiber (CountTables.source b a)
  rw [topFiber_eq,baseDeriv_action,CountTables.source_realization,← topFiber_eq]

end

section
open AssociativeElimination AlphabetTransport SourceEnveloping
attribute [local instance] LieRing.ofAssociativeRing

def smallX : A K S1 := atom (some ())
def smallY : A K S1 := atom none
def smallD : Module.End K (A K S1) := deriv (fun _ => ⁅smallX,smallY⁆)
def squash : A K CountTables.G →ₐ[K] A K S1 := lift (fun a => match a with
  | 0 => smallX | 1 => smallY | _ => 0)

theorem squash_delta (p : A K CountTables.G) :
    squash (CountTables.δ 0 p)=smallD (squash p) := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp [CountTables.δ,smallD]
  | ha a =>
    fin_cases a <;>
      simp [CountTables.δ,CountTables.C,CountTables.X,CountTables.Y,CountTables.bracket,
        squash,smallD,smallX,smallY,Ring.lie_def]
  | hadd p q hp hq => simp only [map_add,hp,hq]
  | hs r p hp => simp only [map_smul,hp]
  | hm p q hp hq =>
    simp only [CountTables.δ,AssociativeElimination.deriv_mul,map_add,map_mul] at hp hq ⊢
    rw [hp,hq]
    exact (AssociativeElimination.deriv_mul _ _ _).symm

def smallIndex : SecondStage.F → CountTables.F | 0 => 0 | 1 => 1 | 2 => 3

theorem secondRealize_factor : secondRealize=
    squash.comp (CountTables.realize.comp (map smallIndex)) := by
  apply hom_ext
  intro a
  fin_cases a <;>
    simp [secondRealize,smallLetters,swap,RestrictedAlphabet.substitution,RestrictedAlphabet.x,
      RestrictedAlphabet.y,smallIndex,CountTables.realize,CountTables.X,CountTables.Y,
      CountTables.C,CountTables.bracket,squash,smallX,smallY,Ring.lie_def]

theorem small_source (a : SecondStage.F) :
    map smallIndex (SecondStage.source () a)=CountTables.source 0 (smallIndex a) := by
  fin_cases a <;>
    simp [SecondStage.source,SecondStage.common,SecondStage.higher,SecondStage.H,SecondStage.U,
      SecondStage.V,CountTables.source,CountTables.common,CountTables.higher,CountTables.R',
      CountTables.H,CountTables.U,CountTables.V,CountTables.Q,CountTables.bracket,smallIndex] <;> noncomm_ring

theorem second_realization (a : SecondStage.F) :
    smallD (smallD (secondRealize (atom a)))=secondRealize (SecondStage.source () a) := by
  have hf (p) := AlgHom.congr_fun secondRealize_factor p
  simp only [AlgHom.comp_apply] at hf
  rw [hf,hf,map_atom,← squash_delta,← squash_delta,small_source]
  change squash (CountTables.baseDeriv 0 (CountTables.realize (atom (smallIndex a))))=_
  rw [CountTables.source_realization]

def smallRaw : A K S1 →ₐ[K] Env S2 := GenericBraid.fiberIn
def smallBase : Env S2 := SourceEnveloping.chord (some none) (some (some ()))

theorem small_action (p : A K S1) : ⁅smallBase,smallRaw p⁆=smallRaw (smallD p) := by
  apply AssociativeAction.of_atoms
  intro a
  cases a with
  | none =>
    change ⁅smallBase,GenericBraid.fiberIn (atom none)⁆=smallRaw ⁅smallX,smallY⁆
    simpa only [smallBase,smallRaw,smallX,smallY,Ring.lie_def,map_sub,map_mul,fiber_chord] using
      (base_fiber_left (none : S1) (some ())).trans (CharTwoAction.symm _ _)
  | some a =>
    cases a
    change ⁅smallBase,GenericBraid.fiberIn (atom (some ()))⁆=smallRaw ⁅smallX,smallY⁆
    simpa only [smallBase,smallRaw,smallX,smallY,Ring.lie_def,map_sub,map_mul,fiber_chord] using
      base_fiber_right (none : S1) (some ())

@[simp] theorem secondBase_atom : secondBase (atom ())=smallBase*smallBase := by
  simp only [secondBase,tail,square,AlgHom.comp_apply,lift_atom,map_mul,fiber_chord,base_chord]
  rfl

theorem second_action (b : SecondStage.B) (a : SecondStage.F) :
    secondBase (atom b)*secondFiber (atom a)-secondFiber (atom a)*secondBase (atom b)=
      secondFiber (SecondStage.source b a) := by
  cases b
  change ⁅secondBase (atom ()),secondFiber (atom a)⁆=secondFiber (SecondStage.source () a)
  rw [secondBase_atom,CharTwoAction.square]
  change ⁅smallBase,⁅smallBase,smallRaw (secondRealize (atom a))⁆⁆=
    smallRaw (secondRealize (SecondStage.source () a))
  rw [small_action,small_action,second_realization]

@[simp] theorem secondFiber_H : secondFiber (atom 0)=
    SourceEnveloping.chord none (some (some ()))*SourceEnveloping.chord none (some (some ())) := by
  simp only [secondFiber,secondRealize,AlgHom.comp_apply,map_atom,smallLetters,Equiv.coe_fn_mk]
  simp only [RestrictedAlphabet.substitution,lift_atom,RestrictedAlphabet.x,map_mul,map_atom,
    swap,Equiv.coe_fn_mk,fiber_chord]
@[simp] theorem secondFiber_U : secondFiber (atom 1)=SourceEnveloping.chord none (some none) := by
  simp only [secondFiber,secondRealize,AlgHom.comp_apply,map_atom,smallLetters,Equiv.coe_fn_mk]
  simp only [RestrictedAlphabet.substitution,lift_atom,RestrictedAlphabet.y,map_atom,
    swap,Equiv.coe_fn_mk,fiber_chord]
@[simp] theorem secondFiber_V : secondFiber (atom 2)=
    ⁅SourceEnveloping.chord none (some (some ())),SourceEnveloping.chord none (some none)⁆ := by
  simp only [secondFiber,secondRealize,AlgHom.comp_apply,map_atom,smallLetters,Equiv.coe_fn_mk]
  simp only [RestrictedAlphabet.substitution,lift_atom,RestrictedAlphabet.x,RestrictedAlphabet.y,
    Ring.lie_def,map_sub,map_mul,map_atom,swap,Equiv.coe_fn_mk,fiber_chord]

theorem oldX_zero : oldX 0=smallBase := by
  exact SourceEnveloping.chord_comm _ _
theorem oldX_one : oldX 1=SourceEnveloping.chord none (some (some ())) := by
  exact SourceEnveloping.chord_comm _ _
theorem oldU_eq : oldU=SourceEnveloping.chord none (some none) := by
  exact SourceEnveloping.chord_comm _ _

theorem oldBase_factor : oldBase=
    (PolynomialOrdering.evaluate secondFiber secondBase).comp SecondStage.inward := by
  apply hom_ext
  intro b
  fin_cases b <;> simp [oldBase,SecondStage.inward,SecondStage.fromOld,
    PolynomialOrdering.evaluate,oldX_zero,oldX_one,oldU_eq]
  exact (base_fiber_left (none : S1) (some ())).trans (CharTwoAction.symm _ _)

end

open AssociativeElimination PolynomialOrdering
open scoped TensorProduct

def normal2 : A K CountTables.B →ₗ[K] (A K SecondStage.F ⊗[K] A K Unit) :=
  (normalize SecondStage.source).comp SecondStage.inward.toLinearMap

theorem normal2_correct (q : A K CountTables.B) : secondNormal (normal2 q)=oldBase q := by
  have h : secondNormal=interpret secondFiber secondBase := by
    apply TensorProduct.ext'
    intro p q
    rfl
  rw [h]
  change interpret secondFiber secondBase (normalize SecondStage.source (SecondStage.inward q))=_
  rw [interpret_normalize _ _ _ second_action]
  exact (AlgHom.congr_fun oldBase_factor q).symm

def normal3 : A K ExactCountOrdering.E →ₗ[K]
    (A K CountTables.F ⊗[K] (A K SecondStage.F ⊗[K] A K Unit)) :=
  (TensorProduct.map LinearMap.id normal2).comp (normalize CountTables.source)

@[simp] theorem tripleNormal_tmul (p : A K CountTables.F)
    (z : A K SecondStage.F ⊗[K] A K Unit) :
    tripleNormal (p⊗ₜ[K]z)=topFiber p*GenericBraid.baseIn (secondNormal z) := rfl

theorem normal3_correct (q : A K ExactCountOrdering.E) :
    tripleNormal (normal3 q)=evaluate topFiber topBase q := by
  have h : tripleNormal.comp (TensorProduct.map LinearMap.id normal2)=interpret topFiber topBase := by
    apply TensorProduct.ext'
    intro p q
    simp only [LinearMap.comp_apply,TensorProduct.map_tmul,LinearMap.id_apply,
      tripleNormal_tmul,normal2_correct,interpret_tmul]
    rfl
  change (tripleNormal.comp (TensorProduct.map LinearMap.id normal2)) (normalize CountTables.source q)=_
  rw [h,interpret_normalize _ _ _ top_action]

def collect2 : (A K SecondStage.F ⊗[K] A K Unit) →ₗ[K] A K CountTables.B :=
  SecondStage.outward.toLinearMap.comp merge

def collect3 : (A K CountTables.F ⊗[K] (A K SecondStage.F ⊗[K] A K Unit)) →ₗ[K]
    A K ExactCountOrdering.E := merge.comp (TensorProduct.map LinearMap.id collect2)

theorem collect3_normal3 (q : A K ExactCountOrdering.E) :
    collect3 (normal3 q)=ExactCountOrdering.S q := by
  have h : collect3.comp (TensorProduct.map LinearMap.id normal2)=
      baseStage (SecondStage.order SecondStage.source) := by
    apply TensorProduct.ext'
    intro p q
    rfl
  exact LinearMap.congr_fun h (normalize CountTables.source q)

theorem source_zero (q : A K ExactCountOrdering.E)
    (hq : evaluate topFiber topBase q=0) : ExactCountOrdering.S q=0 := by
  have h : normal3 q=0 := by
    apply tripleNormal_injective
    rw [normal3_correct,hq,map_zero]
  rw [← collect3_normal3,h,map_zero]

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

theorem diff_bound (κ : β → α → α → α → R) (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a r,κ b l a r≠0 → wt a≤cost b)
    (b : β) (l a r : α) (h : κ b l a r-cut κ wt cost b l a r≠0) : wt a<cost b := by
  by_cases he : wt a=cost b
  · simp only [cut,if_pos he,sub_self,ne_eq,not_true_eq_false] at h
  · rw [cut,if_neg he,sub_zero] at h
    exact lt_of_le_of_ne (hc b l a r h) he

theorem Step.count_eq {κ : α → α → α → R} {r l : α} {s t : List α}
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a=c)
    (h : Step κ r l s t) : count wt s=c+count wt t := by
  induction h with
  | head l a s h => rw [count_cons,hc l a _ h]
  | tail l a s t h ih => simp only [count_cons]; omega

theorem Step.count_strict {κ : α → α → α → R} {r l : α} {s t : List α}
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a<c)
    (h : Step κ r l s t) : count wt s<c+count wt t := by
  induction h with
  | head l a s h => simp only [count_cons]; exact Nat.add_lt_add_right (hc l a _ h) _
  | tail l a s t h ih => simp only [count_cons]; omega

theorem op_homogeneous (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a=c)
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wt n) : op κ l r p∈homogeneous wt (n-c) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hb := ht.count_eq wt c hc
  change degree wt (FreeMonoid.ofList t)=n-c
  change degree wt w=n at hw
  simp only [count,degree,FreeMonoid.toList_ofList] at hb hw ⊢
  omega

theorem op_strict (κ : α → α → α → R) (l r : α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a<c)
    {n : ℕ} (hn : c≤n) {p : A R α} (hp : p∈homogeneous wt n) :
    op κ l r p∈above wt (n-c+1) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  have hb := ht.count_strict wt c hc
  change n-c+1≤degree wt (FreeMonoid.ofList t)
  change degree wt w=n at hw
  simp only [count,degree,FreeMonoid.toList_ofList] at hb hw ⊢
  omega

theorem exact_allocation (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (w : FreeMonoid β) {n : ℕ} (hn : degree cost w≤n) {p : A R α} (hp : p∈homogeneous wt n) :
    action (cut κ wt cost) l r (word w) p∈homogeneous wt (n-degree cost w) ∧
    action κ l r (word w) p-action (cut κ wt cost) l r (word w) p∈above wt (n-degree cost w+1) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [word_one,map_one,Module.End.one_apply,degree_one,Nat.sub_zero,sub_self];
           exact ⟨hp,(above wt _).zero_mem⟩
  | of_mul b w ih =>
    have hn' : degree cost w≤n := by
      rw [degree_mul,degree_of] at hn
      omega
    have ih' := ih hn'
    have hb : cost b ≤ n-degree cost w := by simp only [degree_mul,degree_of] at hn; omega
    have he : n-degree cost w-cost b=n-degree cost (FreeMonoid.of b*w) := by
      simp only [degree_mul,degree_of]; omega
    have he' : n-degree cost w+1-cost b=n-degree cost (FreeMonoid.of b*w)+1 := by
      simp only [degree_mul,degree_of] at hn ⊢; omega
    rw [word_mul,word_of,map_mul,map_mul,action_atom,action_atom]
    change op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)∈_ ∧
      op (κ b) l r (action κ l r (word w) p)-op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)∈_
    constructor
    · have h := op_homogeneous (cut κ wt cost b) l r wt (cost b) (cut_bound κ wt cost b) ih'.1
      simpa only [he] using h
    · have h1 := op_above (κ b) l r wt (cost b) (hc b) ih'.2
      have h2 := op_strict (fun l a r => κ b l a r-cut κ wt cost b l a r) l r
        wt (cost b) (diff_bound κ wt cost hc b) hb ih'.1
      rw [op_sub] at h2
      simp only [LinearMap.sub_apply] at h2
      have hh : op (κ b) l r (action κ l r (word w) p)-op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)=
          op (κ b) l r (action κ l r (word w) p-action (cut κ wt cost) l r (word w) p)+
            (op (κ b) l r (action (cut κ wt cost) l r (word w) p)-op (cut κ wt cost b) l r (action (cut κ wt cost) l r (word w) p)) := by
        rw [map_sub]; abel
      rw [hh]
      apply (above wt _).add_mem
      · simpa only [he'] using h1
      · simpa only [he] using h2

theorem exact_allocation_test (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ) (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (w : FreeMonoid β) {p : A R α} (hp : p∈homogeneous wt (degree cost w)) :
    (action κ l r (word w) p).coeff 1=(action (cut κ wt cost) l r (word w) p).coeff 1 := by
  have h := (exact_allocation κ l r wt cost hc w le_rfl hp).2
  have hz := coeff_support h 1 (by simp [degree_one])
  simpa only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply,sub_eq_zero] using hz
end WeightedDeletion

namespace RowTwo
open AssociativeElimination WordGrading WeightedDeletion
instance : Fintype Letter := ⟨{.o,.e,.p,.w}, by intro x; cases x <;> simp⟩
instance : Fintype Slot := ⟨{.A,.C,.B}, by intro x; cases x <;> simp⟩
open Letter Slot

end RowTwo

namespace Deletion
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α ι : Type*} [CommRing R]

def commSum (ν : ι → α → α → R) (pairs : List (ι×ι)) (l r : α) :
    Module.End R (A R α) :=
  (pairs.map (fun ij => ⁅op (ν ij.2) l r,op (ν ij.1) l r⁆)).sum

theorem commSum_apply (ν : ι → α → α → R) (pairs : List (ι×ι)) (l r : α) (p : A R α) :
    commSum ν pairs l r p=
      (pairs.map (fun ij => op (ν ij.2) l r (op (ν ij.1) l r p)-
        op (ν ij.1) l r (op (ν ij.2) l r p))).sum := by
  induction pairs with
  | nil => rfl
  | cons ij s ih =>
    simp only [commSum,List.map_cons,List.sum_cons,LinearMap.add_apply,
      Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply] at ih ⊢
    rw [ih]

theorem commSum_cons (ν : ι → α → α → R) (pairs : List (ι×ι))
    (l r a b : α) (s : List α) :
    commSum ν pairs l r (word (a::b::s))=
      (pairs.map (fun ij => curvature (ν ij.1) (ν ij.2) l a b (s.headD r))).sum • word s+
        atom a*commSum ν pairs a r (word (b::s)) := by
  induction pairs with
  | nil => simp [commSum]
  | cons ij pairs ih =>
    simp only [commSum,List.map_cons,List.sum_cons,LinearMap.add_apply,
      Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply] at ih ⊢
    rw [comm_cons,ih]
    simp only [add_smul,mul_add]
    abel

theorem commSum_eq_zero (ν : ι → α → α → R) (pairs : List (ι×ι))
    (hc : ∀ l a b c,(pairs.map (fun ij => curvature (ν ij.1) (ν ij.2) l a b c)).sum=0)
    (l r : α) : commSum ν pairs l r=0 := by
  apply linear_ext
  intro s
  simp only [LinearMap.zero_apply]
  induction s generalizing l with
  | nil => simp [commSum_apply]
  | cons a s ih =>
    cases s with
    | nil =>
      rw [commSum_apply]
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨ij,_,rfl⟩ := List.mem_map.mp hz
      simp [raw]
    | cons b s => rw [commSum_cons,hc,ih]; simp
end Deletion

namespace TargetDeletion
open AssociativeElimination DeletionTable
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2

def fiber : F → List Hyperplane
  | 0 => [.a3]
  | 1 => [.p13]
  | 2 => [.p23]
  | 3 => [.p13,.m13]
  | 4 => [.p23,.m23]
def base : B → List Hyperplane
  | 0 => [.a1]
  | 1 => [.a2]
  | 2 => [.p12]
  | 3 => [.p12,.m12]
def labels : E → List Hyperplane := Sum.elim fiber base

def ν (i : E) (a b : Letter) : K := ((labels i).map (fun h => (weight h a b : K))).sum

def extra : B → F → List (F×F)
  | 0,0 | 0,3 => [(0,3)]
  | 0,1 => [(0,1),(3,1)]
  | 1,0 | 1,4 => [(0,4)]
  | 1,2 => [(0,2),(4,2)]
  | 2,1 | 2,2 => [(1,2)]
  | 2,3 | 2,4 => [(3,2),(1,4),(3,4)]
  | 3,1 => [(1,4)]
  | 3,2 => [(2,3)]
  | 3,3 | 3,4 => [(3,4)]
  | _,_ => []

def pairs (b : B) (a : F) : List (E×E) :=
  (Sum.inl a,Sum.inr b)::(extra b a).map (fun ij => (Sum.inl ij.2,Sum.inl ij.1))

theorem table_curvature (b : B) (a : F) : ∀ l x y z : Letter,
    ((pairs b a).map (fun ij => Deletion.curvature (ν ij.1) (ν ij.2) l x y z)).sum=0 := by
  revert b a
  decide

theorem target_eq (b : B) (a : F) : CountTables.target b a=
    ((extra b a).map (fun ij => CountTables.bracket (atom ij.1) (atom ij.2))).sum := by
  fin_cases b <;> fin_cases a <;>
    simp [CountTables.target,CountTables.common,CountTables.lower,CountTables.Q,
      CountTables.W,CountTables.H,CountTables.U,CountTables.V,extra,
      CountTables.bracket,add_mul,mul_add] <;> abel

variable {α : Type*}
variable (ν : E → α → α → K)

def evalFiber (l r : α) : A K F →ₐ[K] Module.End K (A K α) :=
  lift (fun a => Deletion.op (ν (.inl a)) l r)
def evalBase (l r : α) : A K B →ₐ[K] Module.End K (A K α) :=
  lift (fun b => Deletion.op (ν (.inr b)) l r)

@[simp] theorem evalFiber_atom (l r : α) (a : F) :
    evalFiber ν l r (atom a)=Deletion.op (ν (.inl a)) l r := lift_atom _ _
@[simp] theorem evalBase_atom (l r : α) (b : B) :
    evalBase ν l r (atom b)=Deletion.op (ν (.inr b)) l r := lift_atom _ _

theorem sum_extra (l r : α) (b : B) (a : F) :
    (((extra b a).map (fun ij : F×F =>
      ⁅Deletion.op (ν (.inl ij.1)) l r,Deletion.op (ν (.inl ij.2)) l r⁆)).sum)=
    evalFiber ν l r (CountTables.target b a) := by
  rw [target_eq,map_list_sum,List.map_map]
  congr 2
  funext ij
  simp only [Function.comp_apply,CountTables.bracket,map_sub,map_mul,evalFiber_atom,Ring.lie_def]

theorem action_table
    (hc : ∀ b a l x y z,((pairs b a).map
      (fun ij => Deletion.curvature (ν ij.1) (ν ij.2) l x y z)).sum=0)
    (l r : α) (b : B) (a : F) :
    evalBase ν l r (atom b)*evalFiber ν l r (atom a)-
      evalFiber ν l r (atom a)*evalBase ν l r (atom b)=evalFiber ν l r (CountTables.target b a) := by
  have h := Deletion.commSum_eq_zero ν (pairs b a) (hc b a) l r
  simp only [Deletion.commSum,pairs,List.map_cons,List.sum_cons,List.map_map,Function.comp_def]
    at h
  rw [sum_extra] at h
  have he := eq_neg_of_add_eq_zero_left h
  rw [← map_neg,CharTwo.neg_eq] at he
  simpa only [Ring.lie_def,evalBase_atom,evalFiber_atom] using he

end TargetDeletion

namespace RowKernel
open AssociativeElimination WordGrading WeightedDeletion RowTwo
open RowTwo.Letter RowTwo.Slot

theorem enc_not_w (a : Slot) : enc a≠.w := by cases a <;> decide

end RowKernel

namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]

theorem edge_raw (ν : α → α → R) (l r : α) (s : List α) :
    raw (fun l a b => ν a b-ν l a) l r s=Deletion.raw ν l r s := by
  induction s generalizing l with
  | nil => rfl
  | cons a s ih => simp only [raw,Deletion.raw,ih]; rfl

theorem edge_op (ν : α → α → R) (l r : α) :
    op (fun l a b => ν a b-ν l a) l r=Deletion.op ν l r := by
  apply linear_ext
  intro w
  have h := edge_raw ν l r w.toList
  simpa only [← op_word,← Deletion.op_word,Deletion.word,word,FreeMonoid.ofList_toList] using h

theorem op_support (κ : α → α → α → R) (l r : α) (P : α → Prop)
    {p : A R α} (hp : p∈space (fun w => ∀ a∈w.toList,P a)) :
    op κ l r p∈space (fun w => ∀ a∈w.toList,P a) := by
  apply map_space (op κ l r) _ ?_ hp
  intro w hw
  have he : op κ l r (word w)=raw κ l r w.toList := by
    simpa only [FreeMonoid.ofList_toList] using op_word κ l r w.toList
  rw [he]
  apply raw_mem_space
  intro t ht
  simp only [FreeMonoid.toList_ofList]
  exact fun a ha => hw a (ht.sublist.subset ha)

theorem action_word_support (κ : β → α → α → α → R) (l r : α) (P : α → Prop)
    (w : FreeMonoid β) {p : A R α} (hp : p∈space (fun w => ∀ a∈w.toList,P a)) :
    action κ l r (word w) p∈space (fun w => ∀ a∈w.toList,P a) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa using hp
  | of_mul b w ih =>
    rw [word_mul,word_of,map_mul,action_atom]
    exact op_support (κ b) l r P ih

theorem raw_congr_on (κ μ : α → α → α → R) (P : α → Prop)
    (he : ∀ l a b,P l → P a → κ l a b=μ l a b) (l r : α) (hl : P l)
    (s : List α) (hs : ∀ a∈s,P a) : raw κ l r s=raw μ l r s := by
  induction s generalizing l with
  | nil => rfl
  | cons a s ih =>
    rw [raw,raw,he l a _ hl (hs a (by simp)),ih a (hs a (by simp))]
    exact fun b hb => hs b (by simp [hb])

theorem op_congr_on (κ μ : α → α → α → R) (P : α → Prop)
    (he : ∀ l a b,P l → P a → κ l a b=μ l a b) (l r : α) (hl : P l)
    {p : A R α} (hp : p∈space (fun w => ∀ a∈w.toList,P a)) : op κ l r p=op μ l r p := by
  have hker : space (fun w => ∀ a∈w.toList,P a) ≤ (op κ l r-op μ l r).ker := by
    rw [space,Submodule.span_le]
    rintro _ ⟨w,hw,rfl⟩
    change op κ l r (word w)-op μ l r (word w)=0
    apply sub_eq_zero.mpr
    have h := raw_congr_on κ μ P he l r hl w.toList hw
    simpa only [← op_word,FreeMonoid.ofList_toList] using h
  exact sub_eq_zero.mp (hker hp)

theorem action_congr_on (κ μ : β → α → α → α → R) (P : α → Prop)
    (he : ∀ k l a b,P l → P a → κ k l a b=μ k l a b) (l r : α) (hl : P l)
    (q : A R β) {p : A R α} (hp : p∈space (fun w => ∀ a∈w.toList,P a)) :
    action κ l r q p=action μ l r q p := by
  have hw (w : FreeMonoid β) : action κ l r (word w) p=action μ l r (word w) p := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul b w ih =>
      rw [word_mul,word_of,map_mul,map_mul,action_atom,action_atom,Module.End.mul_apply,
        Module.End.mul_apply,ih]
      exact op_congr_on (κ b) (μ b) P (he b) l r hl (action_word_support μ l r P w hp)
  induction q using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add q z hq hz => simp only [map_add,LinearMap.add_apply,hq,hz]
  | smul c q hq => simp only [map_smul,LinearMap.smul_apply,hq]

theorem scalar_cut_of_homogeneous (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (s : FreeMonoid α) {p : A R β} (hp : p∈homogeneous cost (degree wt s)) :
    scalar κ l r s p=scalar (cut κ wt cost) l r s p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    exact exact_allocation_test κ l r wt cost hc w (word_mem s hw.symm)
  | zero => simp only [map_zero]
  | add p q _ _ hp hq => simp only [map_add,hp,hq]
  | smul c p _ hp => simp only [map_smul,hp]

theorem scalar_zero_of_low (κ : β → α → α → α → R) (l r : α)
    (wt : α → ℕ) (cost : β → ℕ)
    (hc : ∀ b l a t,κ b l a t≠0 → wt a≤cost b)
    (s : FreeMonoid α) {p : A R β} (hp : p∈strictlyBelow cost (degree wt s)) :
    scalar κ l r s p=0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    exact test_word_zero κ l r wt cost hc w s hw
  | zero => simp only [map_zero]
  | add p q _ _ hp hq => simp only [map_add,hp,hq,add_zero]
  | smul c p _ hp => simp only [map_smul,hp,smul_zero]

end WeightedDeletion

namespace LeadingRows
open AssociativeElimination WordGrading WeightedDeletion RowTwo
open RowKernel

def toLetter : Letter → DeletionTable.Letter | .o => .o | .e => .e | .p => .p | .w => .w

def edge (i : E) (a b : Letter) : K := TargetDeletion.ν i (toLetter a) (toLetter b)

def slotEdge (i : Row) (k : Slot) (a b : Letter) : K :=
  ((slots i k).map (fun e => edge e a b)).sum

def κ₀ (i : Row) (k : Slot) (l a b : Letter) : K := slotEdge i k a b-slotEdge i k l a

def zeroCount (a : Letter) : ℕ := if a=.o then 1 else 0

theorem zero_cost (i : Row) : ∀ k l a b,κ₀ i k l a b≠0 → zeroCount a≤bCount k := by
  cases i <;> decide

theorem cut_table (i : Row) : ∀ k l a b,l≠.w → a≠.w →
    cut (κ₀ i) zeroCount bCount k l a b=RowKernel.κ i k l a b := by
  cases i <;> decide

def operators (l r : Letter) : A K E →ₐ[K] Module.End K (A K Letter) :=
  lift (fun e => Deletion.op (edge e) l r)

theorem substituted_action (i : Row) (l r : Letter) :
    (operators l r).comp (subst i)=action (κ₀ i) l r := by
  apply hom_ext
  intro k
  simp only [AlgHom.comp_apply,subst,lift_atom,map_list_sum,List.map_map,Function.comp_def,operators,lift_atom,
    action_atom]
  change ((slots i k).map (fun e => Deletion.op (edge e) l r)).sum=op (κ₀ i k) l r
  rw [← Deletion.op_list_sum,← edge_op]
  rfl

theorem count_enc_zero (s : List Slot) :
    degree zeroCount (FreeMonoid.ofList (s.map RowKernel.enc))=degree bCount (FreeMonoid.ofList s) := by
  simp only [degree,FreeMonoid.toList_ofList,List.map_map,Function.comp_def]
  congr 2
  funext a
  cases a <;> rfl

theorem scalar_allocated (i : Row) (s : List Slot) {q : A K Slot}
    (hq : q∈homogeneous bCount (degree bCount (FreeMonoid.ofList s))) :
    scalar (κ₀ i) .o .w (FreeMonoid.ofList (s.map RowKernel.enc)) q=RowKernel.test i s q := by
  have h := scalar_cut_of_homogeneous (κ₀ i) .o .w zeroCount bCount (zero_cost i)
    (FreeMonoid.ofList (s.map RowKernel.enc))
    (by simpa only [count_enc_zero] using hq)
  rw [h]
  change (action (cut (κ₀ i) zeroCount bCount) .o .w q
    (word (FreeMonoid.ofList (s.map RowKernel.enc)))).coeff 1=
      (action (RowKernel.κ i) .o .w q (word (FreeMonoid.ofList (s.map RowKernel.enc)))).coeff 1
  apply congrArg (fun p : A K Letter => p.coeff 1)
  apply action_congr_on _ _ (fun a => a≠Letter.w) (cut_table i) _ _ (by decide)
  exact word_mem _ (by
    intro a ha
    simp only [FreeMonoid.toList_ofList] at ha
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp ha
    exact RowKernel.enc_not_w k)

def namedCount : E → ℕ := Sum.elim CountTables.fiberCount CountTables.baseCount
def namedκ (i : E) (l a b : Letter) : K := edge i a b-edge i l a

theorem named_zero_cost : ∀ i l a b,namedκ i l a b≠0 → zeroCount a≤namedCount i := by
  decide

theorem named_action (l r : Letter) : operators l r=action namedκ l r := by
  apply hom_ext
  intro i
  simp only [operators,lift_atom,action_atom]
  exact (edge_op (edge i) l r).symm

def P (q : A K Slot) : A K E := subst .one q+subst .two q+subst .three q+subst .four q

theorem scalar_subst (i : Row) (s : List Slot) (q : A K Slot) :
    scalar namedκ .o .w (FreeMonoid.ofList (s.map RowKernel.enc)) (subst i q)=
      scalar (κ₀ i) .o .w (FreeMonoid.ofList (s.map RowKernel.enc)) q := by
  change (action namedκ .o .w (subst i q) (word _)).coeff 1= _
  rw [← named_action]
  have h := AlgHom.congr_fun (substituted_action i .o .w) q
  change operators .o .w (subst i q)=_ at h
  rw [h]
  rfl

theorem equation_of_low_interpretation (q : A K Slot) (r : ℕ)
    (hq : q∈homogeneous bCount r)
    (z : A K E) (hz : z∈strictlyBelow namedCount r)
    (he : operators .o .w (P q)=operators .o .w z)
    (s : List Slot) (hs : degree bCount (FreeMonoid.ofList s)=r) : RowKernel.Equation q s := by
  have hzero : scalar namedκ .o .w (FreeMonoid.ofList (s.map RowKernel.enc)) z=0 := by
    apply scalar_zero_of_low namedκ .o .w zeroCount namedCount named_zero_cost
    simpa only [count_enc_zero,hs] using hz
  have hval : scalar namedκ .o .w (FreeMonoid.ofList (s.map RowKernel.enc)) (P q)=0 := by
    change (action namedκ .o .w (P q) (word _)).coeff 1=0
    rw [← named_action,he,named_action]
    exact hzero
  have hqs : q∈homogeneous bCount (degree bCount (FreeMonoid.ofList s)) := by
    simpa only [hs] using hq
  simp only [P,map_add,scalar_subst,scalar_allocated _ s hqs] at hval
  exact hval

open PolynomialOrdering
attribute [local instance] LieRing.ofAssociativeRing

def secondExtra : SecondStage.F → List (SecondStage.F×SecondStage.F)
  | 0 | 2 => [(0,2)]
  | 1 => [(0,1),(2,1)]

def secondPairs (a : SecondStage.F) : List (SecondStage.E×SecondStage.E) :=
  (.inl a,.inr ())::(secondExtra a).map (fun ij => (.inl ij.2,.inl ij.1))
def secondEdge (e : SecondStage.E) : Letter → Letter → K := edge (.inr (SecondStage.toOld e))

theorem second_curvature : ∀ a l x y z,((secondPairs a).map
    (fun ij => Deletion.curvature (secondEdge ij.1) (secondEdge ij.2) l x y z)).sum=0 := by
  decide

theorem second_common (b : SecondStage.B) (a : SecondStage.F) : SecondStage.common b a=
    ((secondExtra a).map (fun ij => CountTables.bracket (atom ij.1) (atom ij.2))).sum := by
  fin_cases a <;> simp [SecondStage.common,SecondStage.H,SecondStage.U,SecondStage.V,
    secondExtra,CountTables.bracket]

def secondFiber (l r : Letter) : A K SecondStage.F →ₐ[K] Module.End K (A K Letter) :=
  lift (fun a => Deletion.op (secondEdge (.inl a)) l r)
def secondBase (l r : Letter) : A K SecondStage.B →ₐ[K] Module.End K (A K Letter) :=
  lift (fun b => Deletion.op (secondEdge (.inr b)) l r)

theorem second_sum (l r : Letter) (a : SecondStage.F) :
    ((secondExtra a).map (fun ij => ⁅Deletion.op (secondEdge (.inl ij.1)) l r,
      Deletion.op (secondEdge (.inl ij.2)) l r⁆)).sum=
      secondFiber l r (SecondStage.common () a) := by
  rw [second_common,map_list_sum,List.map_map]
  congr 2
  funext ij
  simp only [Function.comp_apply,CountTables.bracket,map_sub,map_mul,secondFiber,lift_atom,Ring.lie_def]

theorem second_action (l r : Letter) (b : SecondStage.B) (a : SecondStage.F) :
    secondBase l r (atom b)*secondFiber l r (atom a)-
      secondFiber l r (atom a)*secondBase l r (atom b)=
        secondFiber l r (SecondStage.common b a) := by
  cases b
  have h := Deletion.commSum_eq_zero secondEdge (secondPairs a) (second_curvature a) l r
  simp only [Deletion.commSum,secondPairs,List.map_cons,List.sum_cons,List.map_map,Function.comp_def]
    at h
  rw [second_sum] at h
  have he := eq_neg_of_add_eq_zero_left h
  rw [← map_neg,CharTwo.neg_eq] at he
  simpa only [Ring.lie_def,secondBase,secondFiber,lift_atom] using he

theorem second_evaluate (l r : Letter) : (TargetDeletion.evalBase edge l r).comp SecondStage.outward=
    evaluate (secondFiber l r) (secondBase l r) := by
  apply hom_ext
  intro a
  cases a <;> simp only [AlgHom.comp_apply,SecondStage.outward,AlphabetTransport.map_atom,
    TargetDeletion.evalBase_atom,evaluate,lift_atom,Sum.elim_inl,Sum.elim_inr,secondFiber,secondBase]
  all_goals rfl

theorem second_order_correct (l r : Letter) (q : A K CountTables.B) :
    TargetDeletion.evalBase edge l r (SecondStage.order SecondStage.common q)=
      TargetDeletion.evalBase edge l r q := by
  change TargetDeletion.evalBase edge l r (SecondStage.outward
    (ordered SecondStage.common (SecondStage.inward q)))=_
  have h (p : A K SecondStage.E) := AlgHom.congr_fun (second_evaluate l r) p
  change ∀ p,TargetDeletion.evalBase edge l r (SecondStage.outward p)=_ at h
  rw [h,evaluate_ordered _ _ _ (second_action l r),← h,SecondStage.outward_inward]

theorem main_action (l r : Letter) (b : CountTables.B) (a : CountTables.F) :
    TargetDeletion.evalBase edge l r (atom b)*TargetDeletion.evalFiber edge l r (atom a)-
      TargetDeletion.evalFiber edge l r (atom a)*TargetDeletion.evalBase edge l r (atom b)=
        TargetDeletion.evalFiber edge l r (CountTables.target b a) := by
  apply TargetDeletion.action_table
  intro b a l x y z
  exact TargetDeletion.table_curvature b a (toLetter l) (toLetter x) (toLetter y) (toLetter z)

theorem main_evaluate (l r : Letter) :
    evaluate (TargetDeletion.evalFiber edge l r) (TargetDeletion.evalBase edge l r)=operators l r := by
  apply hom_ext
  intro a
  cases a <;> simp [evaluate,operators]

theorem target_order_correct (l r : Letter) (p : A K E) :
    operators l r (ExactCountOrdering.T p)=operators l r p := by
  rw [← main_evaluate]
  exact evaluate_iterated _ _ CountTables.target (main_action l r)
    (SecondStage.order SecondStage.common) (second_order_correct l r) p

theorem equation_from_source_order (q : A K Slot) (r : ℕ)
    (hq : q∈homogeneous bCount r)
    (hp : P q∈homogeneous namedCount r)
    (e : A K E) (he : e∈above namedCount (r+1))
    (hz : ExactCountOrdering.S (P q+e)=0)
    (s : List Slot) (hs : degree bCount (FreeMonoid.ofList s)=r) : RowKernel.Equation q s := by
  have ht := (ExactCountOrdering.transfer r (P q) e hp he hz).2
  exact equation_of_low_interpretation q r hq (ExactCountOrdering.T (P q)) ht
    (target_order_correct .o .w (P q)).symm s hs

end LeadingRows

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
namespace ExactPentagon
open AssociativeElimination WordGrading RowTwo RowKernel LeadingRows
open PolynomialOrdering

theorem atom_homo (a : E) : (atom a : A K E)∈homogeneous namedCount (namedCount a) :=
  word_mem (FreeMonoid.of a) (degree_of namedCount a)

theorem subst_homo (i : Row) (k : Slot) :
    subst i (atom k)∈homogeneous namedCount (bCount k) := by
  rw [subst,lift_atom]
  apply (homogeneous namedCount (bCount k)).toAddSubmonoid.list_sum_mem
  intro a ha
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
  have hc : namedCount e=bCount k := by
    cases i <;> cases k <;> simp [slots] at he <;> rcases he with rfl | rfl | rfl <;> rfl
  rw [← hc]
  exact atom_homo e

theorem P_homogeneous {q : A K Slot} {r : ℕ} (hq : q∈homogeneous bCount r) :
    P q∈homogeneous namedCount r := by
  have h (i : Row) := algHom_homogeneous (subst i) bCount namedCount (subst_homo i) hq
  exact (homogeneous namedCount r).add_mem
    ((homogeneous namedCount r).add_mem ((homogeneous namedCount r).add_mem (h .one) (h .two)) (h .three)) (h .four)

theorem u12_homo : u12∈homogeneous namedCount 1 := atom_homo (.inr 2)
theorem u23_homo : u23∈homogeneous namedCount 1 := atom_homo (.inl 2)

theorem extra_homo (k : Slot) : extra k∈homogeneous namedCount 2 := by
  cases k with
  | A =>
      have h := homogeneous_mul u12_homo u12_homo
      exact h
  | C =>
      have h1 := homogeneous_mul u12_homo u23_homo
      have h2 := homogeneous_mul u23_homo u12_homo
      exact (homogeneous namedCount 2).sub_mem h1 h2
  | B => exact (homogeneous namedCount 2).zero_mem

theorem exactTwo_difference (k : Slot) :
    exactTwo (atom k)-subst .two (atom k)∈above namedCount (bCount k+1) := by
  simp only [exactTwo,lift_atom,add_sub_cancel_left]
  apply space_mono (P:=fun w => degree namedCount w=2) ?_ (extra_homo k)
  intro w hw
  cases k <;> simp_all [bCount]

theorem exactTwo_above (k : Slot) : exactTwo (atom k)∈above namedCount (bCount k) := by
  rw [exactTwo,lift_atom]
  apply (above namedCount _).add_mem (homogeneous_above (subst_homo .two k))
  apply space_mono (P:=fun w => degree namedCount w=2) ?_ (extra_homo k)
  intro w hw
  cases k <;> simp_all [bCount]

theorem omitted_weight (k : Slot) : omitted (atom k)∈homogeneous namedCount (weight k) := by
  simp only [omitted,lift_atom]
  cases k with
  | A =>
      have h := homogeneous_mul u12_homo u12_homo
      exact h
  | C =>
      have h1 := homogeneous_mul u12_homo u23_homo
      have h2 := homogeneous_mul u23_homo u12_homo
      exact (homogeneous namedCount 2).sub_mem h1 h2
  | B => exact u23_homo

theorem full_error {p q : A K Slot} {n r : ℕ}
    (hp : p∈homogeneous weight n) (hr : r<n)
    (hq : q∈homogeneous bCount r) (hhigh : p-q∈above bCount (r+1)) :
    full p-P q∈above namedCount (r+1) := by
  have hi (i : Row) : subst i (p-q)∈above namedCount (r+1) :=
    algHom_above _ bCount namedCount (fun k => homogeneous_above (subst_homo i k)) hhigh
  have htwo := algHom_above exactTwo bCount namedCount exactTwo_above hhigh
  have hdiff := algHom_difference_above exactTwo (subst .two) bCount namedCount
    exactTwo_above (subst_homo .two) exactTwo_difference hq
  have homit : omitted p∈above namedCount (r+1) := by
    exact space_mono (P:=fun w => degree namedCount w=n) (by intro w hw; omega)
      (algHom_homogeneous omitted weight namedCount omitted_weight hp)
  have eq : full p-P q=subst .one (p-q)+exactTwo (p-q)+(exactTwo q-subst .two q)+
      omitted p+subst .three (p-q)+subst .four (p-q) := by
    simp only [full,P,map_sub]
    abel
  rw [eq]
  exact (above namedCount _).add_mem ((above namedCount _).add_mem ((above namedCount _).add_mem
    ((above namedCount _).add_mem ((above namedCount _).add_mem (hi .one) htwo) hdiff) homit) (hi .three)) (hi .four)

theorem row_equation_oai {p q : A K Slot} {n r : ℕ}
    (hp : p∈homogeneous weight n) (hr : r<n)
    (hq : q∈homogeneous bCount r) (hhigh : p-q∈above bCount (r+1))
    (hpent : evaluate SourceModel.topFiber SourceModel.topBase (full p)=0)
    (s : List Slot) (hs : degree bCount (FreeMonoid.ofList s)=r) : RowKernel.Equation q s := by
  apply equation_from_source_order q r hq (P_homogeneous hq) (full p-P q) (full_error hp hr hq hhigh) ?_ s hs
  have eq : P q+(full p-P q)=full p := by abel
  rw [eq]
  exact SourceModel.source_zero _ hpent

end ExactPentagon

end DeligneDrinfeld

end

end OAI

end




















section
open OAI.DeligneDrinfeld.ExactPentagon in
theorem solution : ∀ {p q : OAI.DeligneDrinfeld.AssociativeElimination.A OAI.DeligneDrinfeld.RowTwo.K OAI.DeligneDrinfeld.RowTwo.Slot}
    {n r : ℕ} (hp : p ∈ OAI.DeligneDrinfeld.WordGrading.homogeneous OAI.DeligneDrinfeld.ExactPentagon.weight n)
    (hr : r < n) (hq : q ∈ OAI.DeligneDrinfeld.WordGrading.homogeneous OAI.DeligneDrinfeld.RowKernel.bCount r)
    (hhigh : p - q ∈ OAI.DeligneDrinfeld.WordGrading.above OAI.DeligneDrinfeld.RowKernel.bCount (r + 1))
    (hpent :
      (OAI.DeligneDrinfeld.PolynomialOrdering.evaluate OAI.DeligneDrinfeld.SourceModel.topFiber
            OAI.DeligneDrinfeld.SourceModel.topBase)
          (OAI.DeligneDrinfeld.ExactPentagon.full p) =
        0)
    (s : List OAI.DeligneDrinfeld.RowTwo.Slot)
    (hs : OAI.DeligneDrinfeld.WordGrading.degree OAI.DeligneDrinfeld.RowKernel.bCount (FreeMonoid.ofList s) = r),
    OAI.DeligneDrinfeld.RowKernel.Equation q s :=
  @OAI.DeligneDrinfeld.ExactPentagon.row_equation_oai
end

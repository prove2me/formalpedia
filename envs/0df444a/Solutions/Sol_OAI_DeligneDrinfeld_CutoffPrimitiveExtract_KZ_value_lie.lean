-- Prove2me | solution 1 for OAI.DeligneDrinfeld.CutoffPrimitiveExtract.KZ_value_lie
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:54:16.899322+00:00
-- url     : https://prove2.me/submissions/ad2ba7c1-cc3e-4e23-9094-1d96e22ff604

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid

set_option linter.all false


section

namespace OAI

noncomputable section
namespace DeligneDrinfeld

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

namespace TensorGrading
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β : Type*} [CommRing R]
abbrev V := A R α ⊗[R] A R β
def space (P : FreeMonoid α → FreeMonoid β → Prop) : Submodule R (V (R:=R) (α:=α) (β:=β)) :=
  Submodule.span R {z | ∃ u v,P u v ∧ z=word u⊗ₜ word v}
theorem tmul_word_mem {P : FreeMonoid α → FreeMonoid β → Prop} (u : FreeMonoid α) (v : FreeMonoid β)
    (h : P u v) : word (R:=R) u⊗ₜ word (R:=R) v∈space P :=
  Submodule.subset_span ⟨u,v,h,rfl⟩

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

section

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

namespace TensorProjection
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β : Type*} [CommRing R]

abbrev len {α : Type*} (w : FreeMonoid α) : ℕ := degree (fun _ => 1) w

def totalPiece (n : ℕ) : A R α⊗[R]A R β →ₗ[R] A R α⊗[R]A R β :=
  ∑ i∈Finset.range (n+1),TensorProduct.map (piece i) (piece (n-i))

theorem totalPiece_word (n : ℕ) (u : FreeMonoid α) (v : FreeMonoid β) :
    totalPiece (R:=R) n (word u⊗ₜ[R]word v)=
      if len u+len v=n then word u⊗ₜ[R]word v else 0 := by
  classical
  simp only [totalPiece,LinearMap.sum_apply,TensorProduct.map_tmul,piece,WordGrading.piece,project_word]
  change (∑ i∈Finset.range (n+1),(if len u=i then word u else 0)⊗ₜ[R]
    (if len v=n-i then word v else 0))=_
  by_cases hu : len u≤n
  · rw [Finset.sum_eq_single (len u)]
    · simp only [ite_true]
      by_cases h : len u+len v=n
      · have hv : len v=n-len u := by omega
        rw [if_pos hv,if_pos h]
      · have hv : len v≠n-len u := by omega
        rw [if_neg hv,if_neg h,TensorProduct.tmul_zero]
    · intro b hb hbu
      rw [if_neg (Ne.symm hbu),TensorProduct.zero_tmul]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr (by omega)))
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by have hi' := Finset.mem_range.mp hi; omega),TensorProduct.zero_tmul]

theorem totalPiece_homogeneous {k : ℕ} {p : A R α⊗[R]A R β}
    (hp : p∈TensorGrading.homogeneous (fun _ => 1) (fun _ => 1) k) (n : ℕ) :
    totalPiece n p=if k=n then p else 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,v,huv,rfl⟩ := hp
    change len u+len v=k at huv
    rw [totalPiece_word,huv]
  | zero => simp
  | add p q _ _ hp hq => rw [map_add,hp,hq]; split_ifs <;> simp
  | smul c p _ hp => rw [map_smul,hp]; split_ifs <;> simp

theorem homogeneous_mul {n m : ℕ} {p q : A R α⊗[R]A R β}
    (hp : p∈TensorGrading.homogeneous (fun _ => 1) (fun _ => 1) n)
    (hq : q∈TensorGrading.homogeneous (fun _ => 1) (fun _ => 1) m) :
    p*q∈TensorGrading.homogeneous (fun _ => 1) (fun _ => 1) (n+m) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,v,huv,rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨s,t,hst,rfl⟩ := hq
      rw [Algebra.TensorProduct.tmul_mul_tmul,←word_mul,←word_mul]
      apply TensorGrading.tmul_word_mem
      change len u+len v=n at huv
      change len s+len t=m at hst
      change len (u*s)+len (v*t)=n+m
      simp only [len,degree_mul] at *
      omega
    | zero => simp
    | add q r _ _ hq hr => rw [mul_add]; exact Submodule.add_mem _ hq hr
    | smul c q _ hq => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hq
  | zero => simp
  | add p r _ _ hp hr => rw [add_mul]; exact Submodule.add_mem _ hp hr
  | smul c p _ hp => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hp

def coproduct : A R α →ₐ[R] A R α⊗[R]A R α :=
  AssociativeElimination.lift (fun a => atom a⊗ₜ[R]1+(1:A R α)⊗ₜ[R]atom a)

@[simp] theorem coproduct_atom (a : α) : (coproduct (R:=R) (α:=α)) (atom (R:=R) a)=atom a⊗ₜ[R]1+(1:A R α)⊗ₜ[R]atom a :=
  AssociativeElimination.lift_atom _ _

theorem coproduct_word_homogeneous (u : FreeMonoid α) :
    (coproduct (R:=R) (α:=α)) (word (R:=R) u)∈TensorGrading.homogeneous (fun _ => 1) (fun _ => 1) (len u) := by
  induction u using FreeMonoid.inductionOn' with
  | one =>
    rw [word_one,map_one]
    exact TensorGrading.tmul_word_mem 1 1 (by simp [len])
  | of_mul a u ih =>
    rw [word_mul,word_of,map_mul,coproduct_atom]
    apply homogeneous_mul _ ih
    apply Submodule.add_mem
    · exact TensorGrading.tmul_word_mem (FreeMonoid.of a) 1 (by simp)
    · exact TensorGrading.tmul_word_mem 1 (FreeMonoid.of a) (by simp)

theorem coproduct_piece (n : ℕ) (p : A R α) :
    (coproduct (R:=R) (α:=α)) (piece n p)=totalPiece n ((coproduct (R:=R) (α:=α)) p) := by
  induction p using MonoidAlgebra.induction_on with
  | of u =>
    change (coproduct (R:=R) (α:=α)) (piece n (word u))=totalPiece n ((coproduct (R:=R) (α:=α)) (word u))
    rw [totalPiece_homogeneous (coproduct_word_homogeneous u)]
    rw [piece,WordGrading.piece,project_word]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem totalPiece_left (n : ℕ) (p : A R α) : totalPiece n (p⊗ₜ[R](1:A R β))=piece n p⊗ₜ[R]1 := by
  induction p using MonoidAlgebra.induction_on with
  | of u =>
    change totalPiece n (word u⊗ₜ[R]word 1)=piece n (word u)⊗ₜ[R]1
    rw [totalPiece_word]
    have hz : len (1:FreeMonoid β)=0 := by simp [len]
    rw [hz,Nat.add_zero]
    rw [piece,WordGrading.piece,project_word]
    by_cases h : len u=n
    · rw [if_pos h,if_pos h,word_one]
    · rw [if_neg h,if_neg h,TensorProduct.zero_tmul]
  | add p q hp hq => simp only [TensorProduct.add_tmul,map_add,hp,hq]
  | smul c p hp => simp only [←TensorProduct.smul_tmul',map_smul,hp]

theorem totalPiece_right (n : ℕ) (p : A R β) : totalPiece n ((1:A R α)⊗ₜ[R]p)=1⊗ₜ[R]piece n p := by
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change totalPiece n (word 1⊗ₜ[R]word v)=1⊗ₜ[R]piece n (word v)
    rw [totalPiece_word,piece,WordGrading.piece,project_word]
    simp only [len,degree_one,Nat.zero_add,word_one]
    split_ifs <;> simp
  | add p q hp hq => simp only [TensorProduct.tmul_add,map_add,hp,hq]
  | smul c p hp => simp only [TensorProduct.tmul_smul,map_smul,hp]
end TensorProjection

namespace PrimitiveWords
open AssociativeElimination
variable {R α : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing Classical.propDecidable

abbrev B (R α : Type*) [CommRing R] := MonoidAlgebra R (FreeMonoid α × FreeMonoid α)

def word (w : W α) : A R α := MonoidAlgebra.single w 1

def pair (u v : W α) : B R α := MonoidAlgebra.single (u,v) 1

def bilinear {M : Type*} [AddCommGroup M] [Module R M] (f : W α → W α → M) : B R α →ₗ[R] M :=
  (Finsupp.linearCombination R (fun p => f p.1 p.2)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem bilinear_single {M : Type*} [AddCommGroup M] [Module R M]
    (f : W α → W α → M) (u v : W α) (r : R) : bilinear f (MonoidAlgebra.single (u,v) r)=r • f u v := by
  change Finsupp.linearCombination R (fun pair => f pair.1 pair.2) (Finsupp.single (u,v) r) = _; simp

@[simp] theorem word_one : word (R:=R) (1 : W α)=1 := rfl
@[simp] theorem word_mul (u v : W α) : word (R:=R) (u*v)=word u*word v := by
  simp [word,MonoidAlgebra.single_mul_single]
@[simp] theorem pair_one : pair (R:=R) (1 : W α) 1=1 := rfl
@[simp] theorem pair_mul (u v s t : W α) : pair (R:=R) (u*s) (v*t)=pair u v*pair s t := by
  simp [pair,MonoidAlgebra.single_mul_single]

def coproduct : A R α →ₐ[R] B R α :=
  lift (fun a => pair (FreeMonoid.of a) 1+pair 1 (FreeMonoid.of a))

def left : A R α →ₗ[R] B R α := linear (fun w => pair w 1)
def right : A R α →ₗ[R] B R α := linear (fun w => pair 1 w)

def Primitive (p : A R α) : Prop := coproduct p=left p+right p

def antipodeWord (w : W α) : A R α :=
  (-1 : R)^w.toList.length • word (FreeMonoid.ofList w.toList.reverse)

def counitConvolution : B R α →ₗ[R] A R α := bilinear (fun u v => word u*antipodeWord v)
def dynkinConvolution : B R α →ₗ[R] A R α :=
  bilinear (fun u v => (u.toList.length : R) • (word u*antipodeWord v))

@[simp] theorem antipodeWord_one : antipodeWord (R:=R) (1 : W α)=1 := by simp [antipodeWord]
theorem antipodeWord_cons (a : α) (w : W α) :
    antipodeWord (R:=R) (FreeMonoid.of a*w) = -(antipodeWord w*atom a) := by
  simp only [antipodeWord,FreeMonoid.toList_mul,FreeMonoid.toList_of,List.singleton_append,
    List.length_cons,List.reverse_cons,pow_succ,FreeMonoid.ofList_append]
  simp [word,atom,MonoidAlgebra.single_mul_single]

@[simp] theorem coproduct_atom (a : α) :
    coproduct (atom (R:=R) a)=pair (FreeMonoid.of a) 1+pair 1 (FreeMonoid.of a) := by
  simp [coproduct]

theorem counitConvolution_left (a : α) (b : B R α) :
    counitConvolution (pair (FreeMonoid.of a) 1*b)=atom a*counitConvolution b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp [mul_add,hb,hc]
  | single p r =>
    rcases p with ⟨u,v⟩
    simp only [counitConvolution,pair,MonoidAlgebra.single_mul_single,
      Prod.mk_mul_mk,one_mul,bilinear_single,word_mul]
    change r • ((atom a*word u)*antipodeWord v)=atom a*(r • (word u*antipodeWord v))
    rw [mul_assoc,mul_smul_comm]

theorem counitConvolution_right (a : α) (b : B R α) :
    counitConvolution (pair 1 (FreeMonoid.of a)*b)=-(counitConvolution b*atom a) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [mul_add,map_add,hb,hc,add_mul]; abel
  | single p r =>
    rcases p with ⟨u,v⟩
    simp [counitConvolution,pair,MonoidAlgebra.single_mul_single,antipodeWord_cons,mul_assoc]

theorem dynkinConvolution_left (a : α) (b : B R α) :
    dynkinConvolution (pair (FreeMonoid.of a) 1*b)=
      atom a*dynkinConvolution b+atom a*counitConvolution b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [mul_add,map_add,hb,hc]; abel
  | single p r =>
    rcases p with ⟨u,v⟩
    simp only [dynkinConvolution,counitConvolution,pair,MonoidAlgebra.single_mul_single,
      one_mul,Prod.mk_mul_mk,one_mul,bilinear_single,FreeMonoid.toList_mul,
      FreeMonoid.toList_of,List.singleton_append,List.length_cons,Nat.cast_add,Nat.cast_one,
      add_smul,one_smul,smul_add,word_mul]
    change r • ((u.toList.length : R) • ((atom a*word u)*antipodeWord v))+
      r • ((atom a*word u)*antipodeWord v)=_
    simp only [mul_assoc,mul_smul_comm,smul_smul]

theorem dynkinConvolution_right (a : α) (b : B R α) :
    dynkinConvolution (pair 1 (FreeMonoid.of a)*b)=-(dynkinConvolution b*atom a) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [mul_add,map_add,hb,hc,add_mul]; abel
  | single p r =>
    rcases p with ⟨u,v⟩
    simp [dynkinConvolution,pair,MonoidAlgebra.single_mul_single,antipodeWord_cons,
      mul_assoc]

@[simp] theorem counitConvolution_one : counitConvolution (1 : B R α)=1 := by
  change bilinear _ (MonoidAlgebra.single (1,1) 1)=1
  simp
@[simp] theorem dynkinConvolution_one : dynkinConvolution (1 : B R α)=0 := by
  change bilinear _ (MonoidAlgebra.single (1,1) 1)=0
  simp

@[simp] theorem word_of (a : α) : word (R:=R) (FreeMonoid.of a)=atom a := rfl

theorem counit_coproduct_word (w : W α) :
    counitConvolution (coproduct (word (R:=R) w))=if w=1 then 1 else 0 := by
  classical
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    have hne : FreeMonoid.of a*w≠1 := by
      intro h
      have h' := congrArg FreeMonoid.toList h
      simp at h'
    rw [word_mul,word_of,map_mul,coproduct_atom,add_mul,map_add,
      counitConvolution_left,counitConvolution_right,ih,if_neg hne]
    split_ifs <;> simp

def dynkinWord : List α → FreeLieAlgebra R α
  | [] => 0
  | [a] => FreeLieAlgebra.of R a
  | a::b::w => ⁅FreeLieAlgebra.of R a,dynkinWord (b::w)⁆

def dynkin : A R α →ₗ[R] FreeLieAlgebra R α := linear (fun w => dynkinWord w.toList)

def euler : A R α →ₗ[R] A R α := linear (fun w => (w.toList.length : R) • word w)

theorem dynkin_coproduct_word (w : W α) :
    dynkinConvolution (coproduct (word (R:=R) w))=embed (dynkinWord w.toList) := by
  classical
  induction w using FreeMonoid.inductionOn' with
  | one => simp [dynkinWord]
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,coproduct_atom,add_mul,map_add,
      dynkinConvolution_left,dynkinConvolution_right,ih,counit_coproduct_word]
    by_cases hw : w=1
    · subst w
      simp [dynkinWord]
    · rw [if_neg hw,mul_zero,add_zero]
      have hw' : w.toList≠[] := by
        intro hh
        exact hw (FreeMonoid.toList.injective hh)
      have hc : dynkinWord (R:=R) (a::w.toList)=
          ⁅FreeLieAlgebra.of R a,dynkinWord w.toList⁆ := by
        cases h : w.toList with
        | nil => exact (hw' h).elim
        | cons b v => rfl
      simp only [FreeMonoid.toList_mul,FreeMonoid.toList_of,List.singleton_append,hc,
        LieHom.map_lie,embed_of,Ring.lie_def,sub_eq_add_neg]

theorem dynkin_coproduct (p : A R α) : dynkinConvolution (coproduct p)=embed (dynkin p) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change dynkinConvolution (coproduct (word w))=embed (dynkin (word w))
    simpa only [dynkin,word,linear_single,one_smul] using dynkin_coproduct_word (R:=R) w
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul r p hp => simp only [map_smul,hp]

theorem dynkin_left (p : A R α) : dynkinConvolution (left p)=euler p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | single w r => simp [left,linear_single,pair,dynkinConvolution,euler]

theorem dynkin_right (p : A R α) : dynkinConvolution (right p)=0 := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add,hp,hq,add_zero]
  | single w r => simp [right,linear_single,pair,dynkinConvolution]

theorem dynkin_primitive {p : A R α} (hp : Primitive p) : embed (dynkin p)=euler p := by
  rw [←dynkin_coproduct,hp,map_add,dynkin_left,dynkin_right,add_zero]

theorem euler_homogeneous {p : A R α} {n : ℕ}
    (hp : p∈WordGrading.homogeneous (fun _ => 1) n) : euler p=(n : R) • p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    have hh : w.toList.length=n := by simpa [WordGrading.degree] using hw
    simp [euler,WordGrading.word,hh,word]
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,smul_add]
  | smul r p _ hp => simp only [map_smul,hp,smul_comm r (n : R) p]

theorem exists_lie_of_primitive {K : Type*} [Field K] [CharZero K]
    {p : A K α} {n : ℕ} (hn : 0<n)
    (hh : p∈WordGrading.homogeneous (fun _ => 1) n) (hp : Primitive p) :
    ∃ q : FreeLieAlgebra K α, q∈LieGrading.homogeneousLie (fun _ => 1) n ∧ embed q=p := by
  have hn' : (n : K)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have he : embed ((n : K)⁻¹ • dynkin p)=p := by
    rw [map_smul,dynkin_primitive hp,euler_homogeneous hh,smul_smul,inv_mul_cancel₀ hn',one_smul]
  exact ⟨(n : K)⁻¹ • dynkin p,LieGrading.homogeneous_iff.mpr (by rw [he]; exact hh),he⟩

end PrimitiveWords

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

end

namespace TensorFiltration
open scoped TensorProduct
open FinitePicard
variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

 def space (F : ℕ → Submodule R A) (G : ℕ → Submodule R B) (n : ℕ) : Submodule R (A ⊗[R] B) :=
  Submodule.span R {z | ∃ (i j : ℕ) (a : A) (b : B),n ≤ i + j ∧ a∈F i ∧ b∈G j ∧ z=a⊗ₜ[R]b}

 theorem tmul_mem (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    {n i j : ℕ} {a : A} {b : B} (hn : n ≤ i + j) (ha : a∈F i) (hb : b∈G j) :
    a⊗ₜ[R]b∈space F G n := Submodule.subset_span ⟨i,j,a,b,hn,ha,hb,rfl⟩

 theorem antitone (F : ℕ → Submodule R A) (G : ℕ → Submodule R B) : Antitone (space F G) := by
  intro m n h
  apply Submodule.span_mono
  rintro z ⟨i,j,a,b,hn,ha,hb,rfl⟩
  exact ⟨i,j,a,b,le_trans h hn,ha,hb,rfl⟩

 theorem one (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hF : (1:A)∈F 0) (hG : (1:B)∈G 0) : (1:A⊗[R]B)∈space F G 0 :=
  tmul_mem F G (by omega) hF hG

 theorem mul (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hmF : ∀ i j {a b : A},a∈F i → b∈F j → a*b∈F (i+j))
    (hmG : ∀ i j {a b : B},a∈G i → b∈G j → a*b∈G (i+j))
    {m n : ℕ} {u v : A⊗[R]B} (hu : u∈space F G m) (hv : v∈space F G n) :
    u*v∈space F G (m+n) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i,j,a,b,hij,ha,hb,rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k,l,c,d,hkl,hc,hd,rfl⟩ := hv
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem F G (by omega) (hmF i k ha hc) (hmG j l hb hd)
    | zero => simp only [mul_zero,Submodule.zero_mem]
    | add v w _ _ hv hw => rw [mul_add]; exact Submodule.add_mem _ hv hw
    | smul r v _ hv => rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ r hv
  | zero => simp only [zero_mul,Submodule.zero_mem]
  | add u w _ _ hu hw => rw [add_mul]; exact Submodule.add_mem _ hu hw
  | smul r u _ hu => rw [Algebra.smul_mul_assoc]; exact Submodule.smul_mem _ r hu

 theorem terminal (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hF : Antitone F) (hG : Antitone G) (M N : ℕ) (htF : F (M+1)=⊥) (htG : G (N+1)=⊥) :
    space F G (M+N+1)=⊥ := by
  apply eq_bot_iff.mpr
  apply Submodule.span_le.mpr
  rintro z ⟨i,j,a,b,hij,ha,hb,rfl⟩
  by_cases hi : M + 1 ≤ i
  · have hz := hF hi ha
    rw [htF,Submodule.mem_bot] at hz
    change a⊗ₜ[R]b=0
    simp only [hz,TensorProduct.zero_tmul]
  · have hj : N + 1 ≤ j := by omega
    have hz := hG hj hb
    rw [htG,Submodule.mem_bot] at hz
    change a⊗ₜ[R]b=0
    simp only [hz,TensorProduct.tmul_zero]

variable {C D : Type*} [NormedRing C] [NormedRing D] [NormedAlgebra ℝ C] [NormedAlgebra ℝ D]
  [FiniteDimensional ℝ C] [FiniteDimensional ℝ D]
local instance : NormedRing (C⊗[ℝ]D) := FiniteAlgebraNorm.normedRing _
local instance : NormedAlgebra ℝ (C⊗[ℝ]D) := FiniteAlgebraNorm.normedAlgebra _

def cutoff (F : NilpotentFiltration C) (G : NilpotentFiltration D) : NilpotentFiltration (C⊗[ℝ]D) where
  space := space F.space G.space
  antitone := antitone F.space G.space
  one_mem := one F.space G.space F.one_mem G.one_mem
  mul_mem _ _ := mul F.space G.space F.mul_mem G.mul_mem
  cutoff := F.cutoff+G.cutoff
  terminal := terminal F.space G.space F.antitone G.antitone F.cutoff G.cutoff F.terminal G.terminal

end TensorFiltration

namespace NilpotentFreeLift
open AssociativeElimination WordGrading TruncatedWords FinitePicard
variable {α B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
variable (F : NilpotentFiltration B) (f : α → B) (hf : ∀ a,f a∈F.space 1)
include hf
 theorem eval_preserves {n : ℕ} {p : Q (∅ : Set (A ℝ α)) F.cutoff}
    (hp : p∈filtration ∅ F.cutoff n) : eval F f hf p∈F.space n := by
  obtain ⟨p,hp,rfl⟩ := hp
  change eval F f hf (quotient ∅ F.cutoff p)∈_
  rw [eval_quotient]
  exact lift_mem F f hf hp
end NilpotentFreeLift

end DeligneDrinfeld

end

end OAI

end



section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

namespace FinitePicard
open MeasureTheory Set intervalIntegral
variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedRing B] [NormedAlgebra ℝ B]
variable [FiniteDimensional ℝ A] [CompleteSpace B]

theorem map_term (f : A →ₐ[ℝ] B) {Ω : ℝ → A} {a b : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (N : ℕ) {t : ℝ} (ht : t ∈ uIcc a b) :
    f (term Ω a N t)=term (fun s => f (Ω s)) a N t := by
  induction N generalizing t with
  | zero => simp
  | succ N ih =>
    rw [term_succ,term_succ]
    let fc := f.toLinearMap.toContinuousLinearMap
    have hi' : IntervalIntegrable (fun s => Ω s * term Ω a N s) volume a t :=
      (hi.mul_continuousOn (continuousOn_term hi N)).mono_set (uIcc_subset_uIcc_left ht)
    change fc (∫ s in a..t, Ω s * term Ω a N s)=_
    rw [←fc.intervalIntegral_comp_comm hi']
    apply intervalIntegral.integral_congr
    intro s hs
    have hst : s ∈ uIcc a b := uIcc_subset_uIcc_left ht hs
    change f (Ω s*term Ω a N s)=f (Ω s)*term (fun s => f (Ω s)) a N s
    rw [map_mul,ih hst]

theorem map_transport (f : A →ₐ[ℝ] B) {Ω : ℝ → A} {a b : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (N : ℕ) {t : ℝ} (ht : t ∈ uIcc a b) :
    f (transport Ω a N t)=transport (fun s => f (Ω s)) a N t := by
  simp only [transport,map_sum]
  exact Finset.sum_congr rfl (fun n _ => map_term f hi n ht)

end FinitePicard

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedRing B] [NormedAlgebra ℝ B]

theorem map_gauge (f : A →ₐ[ℝ] B) (X : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    f (gauge X s)=gauge (f X) s := by
  have hY : (f X)^(N+1)=0 := by rw [←map_pow,hX,map_zero]
  rw [gauge_finite X hX,gauge_finite (f X) hY]
  simp only [map_sum,map_smul,map_pow]

theorem map_regularForm (f : A →ₐ[ℝ] B) (X Y : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    f (regularForm X Y s)=regularForm (f X) (f Y) s := by
  have hN : (-X)^(N+1)=0 := by rw [neg_pow,hX,mul_zero]
  simp only [regularForm,map_mul,map_smul,map_gauge f X hX,map_gauge f (-X) hN,map_neg]

variable [FiniteDimensional ℝ A] [CompleteSpace B]

theorem map_normalizedSolution (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B) (hN : F.cutoff=G.cutoff)
    {X : A} (hX : X ∈ F.space 1) (Y : A) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    f (normalizedSolution F X Y s)=normalizedSolution G (f X) (f Y) s := by
  have hi := regularForm_integrable X Y (pow_cutoff_eq_zero F hX) hs hs1
  simp only [normalizedSolution,map_mul,map_gauge f X (pow_cutoff_eq_zero F hX)]
  rw [map_transport f hi F.cutoff right_mem_uIcc,hN]
  have hh : (fun s => f (regularForm X Y s))=regularForm (f X) (f Y) := by
    funext s
    exact map_regularForm f X Y (pow_cutoff_eq_zero F hX) s
  rw [hh]

omit [FiniteDimensional ℝ A] [CompleteSpace B] in
theorem map_unit_inverse (f : A →ₐ[ℝ] B) {x : A} (hx : IsUnit x) :
    f (Ring.inverse x)=Ring.inverse (f x) := by
  calc
    f (Ring.inverse x)=f (Ring.inverse x)*(f x*Ring.inverse (f x)) := by
      rw [Ring.mul_inverse_cancel _ (hx.map f),mul_one]
    _ = (f (Ring.inverse x)*f x)*Ring.inverse (f x) := (mul_assoc _ _ _).symm
    _ = Ring.inverse (f x) := by rw [←map_mul,Ring.inverse_mul_cancel _ hx,map_one,one_mul]

variable [CompleteSpace A]

theorem map_associator (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B) (hN : F.cutoff=G.cutoff)
    {X Y : A} (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) :
    f (associator F X Y)=associator G (f X) (f Y) := by
  rw [associator,map_mul,map_unit_inverse f (rightSolution_isUnit F hX hY (1/2))]
  unfold rightSolution
  rw [map_normalizedSolution f F G hN hY X (by norm_num) (by norm_num),
    map_normalizedSolution f F G hN hX Y (by norm_num) (by norm_num)]
  rfl

end KZCollar

namespace FinitePicard
open MeasureTheory Set
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem transition_constant_closed {f g Ω : ℝ → A} {a b u v : ℝ} (hab : a < b)
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (Ω s*f s) s)
    (hg : ∀ s ∈ Ioo a b, HasDerivAt g (Ω s*g s) s)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hu : ∀ s ∈ Icc a b, IsUnit (f s)) (huv : u ∈ Icc a b) (hvv : v ∈ Icc a b) :
    Ring.inverse (f u)*g u=Ring.inverse (f v)*g v := by
  let c := (a+b)/2
  have hc : c ∈ Ioo a b := ⟨by dsimp [c]; linarith,by dsimp [c]; linarith⟩
  have he : EqOn (fun s => Ring.inverse (f s)*g s)
      (fun _ => Ring.inverse (f c)*g c) (Ioo a b) := by
    intro s hs
    exact transition_constant hf hg (fun s hs => hu s ⟨hs.1.le,hs.2.le⟩) hs hc
  have hi : ContinuousOn (fun s => Ring.inverse (f s)) (Icc a b) := by
    intro s hs
    have hh := NormedRing.inverse_continuousAt (hu s hs).unit
    rw [(hu s hs).unit_spec] at hh
    exact hh.comp_continuousWithinAt (hfc s hs)
  have he' := he.of_subset_closure (hi.mul hgc) continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])
  exact (he' huv).trans (he' hvv).symm

variable [FiniteDimensional ℝ A]

theorem transport_eq_fundamental (F : NilpotentFiltration A) {Ω f : ℝ → A}
    (hΩ : ∀ s, Ω s ∈ F.space 1) {a b : ℝ} (hab : a < b)
    (hi : IntervalIntegrable Ω volume a b) (hc : ContinuousOn Ω (Ioo a b))
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (Ω s*f s) s)
    (hfc : ContinuousOn f (Icc a b)) (hu : ∀ s ∈ Icc a b, IsUnit (f s)) :
    transport Ω a F.cutoff b=f b*Ring.inverse (f a) := by
  have hcont := continuousOn_transport hi F.cutoff
  rw [uIcc_of_le hab.le] at hcont
  have h := transition_constant_closed hab hf
    (fun s hs => derivative_nilpotent_transport F hΩ hi hc hs)
    hfc hcont hu (right_mem_Icc.mpr hab.le) (left_mem_Icc.mpr hab.le)
  rw [transport_base,mul_one] at h
  calc
    transport Ω a F.cutoff b = f b*(Ring.inverse (f b)*transport Ω a F.cutoff b) := by
      rw [←mul_assoc,Ring.mul_inverse_cancel _ (hu b (right_mem_Icc.mpr hab.le)),one_mul]
    _ = f b*Ring.inverse (f a) := congrArg (f b*·) h

end FinitePicard

end

section
namespace FinitePicard
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

 theorem term_above_cutoff (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t,Ω t∈F.space 1) {n : ℕ} (hn : F.cutoff<n) (a t : ℝ) : term Ω a n t=0 := by
  have h := F.antitone hn (term_mem F hΩ a n t)
  simpa only [F.terminal,Submodule.mem_bot] using h

 theorem stabilize (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t,Ω t∈F.space 1) {N : ℕ} (hn : F.cutoff ≤ N) (a t : ℝ) :
    transport Ω a N t=transport Ω a F.cutoff t := by
  unfold transport
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hn 1))
  intro n hnN hnc
  rw [Finset.mem_range,not_lt] at hnc
  exact term_above_cutoff F hΩ (by omega) a t

 def extend (F : NilpotentFiltration A) (N : ℕ) (hN : F.cutoff ≤ N) : NilpotentFiltration A where
  space := F.space
  antitone := F.antitone
  one_mem := F.one_mem
  mul_mem := F.mul_mem
  cutoff := N
  terminal := le_antisymm (le_trans (F.antitone (Nat.add_le_add_right hN 1)) F.terminal.le) bot_le

end FinitePicard
namespace KZCollar
open FinitePicard
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] [CompleteSpace A]

 omit [CompleteSpace A] in
 theorem normalized_extend (F : NilpotentFiltration A) (N : ℕ) (hN : F.cutoff ≤ N)
    {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) (s : ℝ) :
    normalizedSolution (extend F N hN) X Y s=normalizedSolution F X Y s := by
  simp only [normalizedSolution,extend]
  rw [stabilize F (regularForm_mem F hX hY) hN]

 omit [CompleteSpace A] in
 theorem associator_extend (F : NilpotentFiltration A) (N : ℕ) (hN : F.cutoff ≤ N)
    {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    associator (extend F N hN) X Y=associator F X Y := by
  simp only [associator,rightSolution,normalized_extend F N hN hX hY,
    normalized_extend F N hN hY hX]

 variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [FiniteDimensional ℝ B] [CompleteSpace B]

 omit [CompleteSpace A] in
 theorem map_normalized_general (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B)
    {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1)
    (hfX : f X∈G.space 1) (hfY : f Y∈G.space 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s<1) :
    f (normalizedSolution F X Y s)=normalizedSolution G (f X) (f Y) s := by
  let N := max F.cutoff G.cutoff
  rw [←normalized_extend F N (le_max_left _ _) hX hY,
    ←normalized_extend G N (le_max_right _ _) hfX hfY]
  exact map_normalizedSolution f (extend F N (le_max_left _ _))
    (extend G N (le_max_right _ _)) rfl hX Y hs hs1

 theorem map_associator_general (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B)
    {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1)
    (hfX : f X∈G.space 1) (hfY : f Y∈G.space 1) :
    f (associator F X Y)=associator G (f X) (f Y) := by
  let N := max F.cutoff G.cutoff
  rw [←associator_extend F N (le_max_left _ _) hX hY,
    ←associator_extend G N (le_max_right _ _) hfX hfY]
  exact map_associator f (extend F N (le_max_left _ _))
    (extend G N (le_max_right _ _)) rfl hX hY

end KZCollar

end

namespace CutoffDiagonal
open scoped TensorProduct
open CutoffDepth CutoffKZ FinitePicard
local instance (N : ℕ) : NormedRing (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedRing _
local instance (N : ℕ) : NormedAlgebra ℝ (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedAlgebra _

def right (N : ℕ) : Q ℝ N →ₐ[ℝ] Q ℝ N⊗[ℝ]Q ℝ N := Algebra.TensorProduct.includeRight
 theorem commute (N : ℕ) (a b : Q ℝ N) : Commute (left N a) (right N b) := by
  change (a⊗ₜ[ℝ](1:Q ℝ N))*((1:Q ℝ N)⊗ₜ[ℝ]b)=((1:Q ℝ N)⊗ₜ[ℝ]b)*(a⊗ₜ[ℝ](1:Q ℝ N))
  simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
def tensorWeight (N : ℕ) : NilpotentFiltration (Q ℝ N⊗[ℝ]Q ℝ N) :=
  TensorFiltration.cutoff (weight N) (weight N)
 theorem left_mem (N n : ℕ) (u : Q ℝ N) (hu : u∈(weight N).space n) : left N u∈(tensorWeight N).space n :=
  TensorFiltration.tmul_mem _ _ (by omega) hu (weight N).one_mem
 theorem right_mem (N n : ℕ) (u : Q ℝ N) (hu : u∈(weight N).space n) : right N u∈(tensorWeight N).space n :=
  TensorFiltration.tmul_mem _ _ (by omega) (weight N).one_mem hu
def diagonal (N : ℕ) : Q ℝ (N+N) →ₐ[ℝ] Q ℝ N⊗[ℝ]Q ℝ N :=
  NilpotentFreeLift.eval (tensorWeight N) (fun b => left N (gen N b)+right N (gen N b))
    (fun b => ((tensorWeight N).space 1).add_mem (left_mem N 1 _ (gen_weight N b)) (right_mem N 1 _ (gen_weight N b)))
 @[simp] theorem diagonal_gen (N : ℕ) (b : Bool) : diagonal N (gen (N+N) b)=left N (gen N b)+right N (gen N b) :=
  NilpotentFreeLift.eval_gen _ _ _ b
 theorem diagonal_mem (N n : ℕ) (u : Q ℝ (N+N)) (hu : u∈(weight (N+N)).space n) :
    diagonal N u∈(tensorWeight N).space n := NilpotentFreeLift.eval_preserves _ _ _ hu

def drop (M N : ℕ) (h : N ≤ M) : Q ℝ M →ₐ[ℝ] Q ℝ N :=
  NilpotentFreeLift.eval (extend (weight N) M h) (gen N) (gen_weight N)
 @[simp] theorem drop_gen (M N : ℕ) (h : N ≤ M) (b : Bool) : drop M N h (gen M b)=gen N b :=
  NilpotentFreeLift.eval_gen _ _ _ b
 theorem drop_mem (M N : ℕ) (h : N ≤ M) (n : ℕ) (u : Q ℝ M) (hu : u∈(weight M).space n) :
    drop M N h u∈(weight N).space n :=
  NilpotentFreeLift.eval_preserves (extend (weight N) M h) (gen N) (gen_weight N) hu
 theorem drop_associator (M N : ℕ) (h : N ≤ M) :
    drop M N h (KZCollar.associator (weight M) (X M) (Y M))=KZCollar.associator (weight N) (X N) (Y N) := by
  rw [KZCollar.map_associator_general (drop M N h) (weight M) (weight N)
    (gen_weight M false) (gen_weight M true)
    (drop_mem M N h 1 _ (gen_weight M false)) (drop_mem M N h 1 _ (gen_weight M true)),
    drop_gen,drop_gen]
end CutoffDiagonal

namespace KZCollar
open Set Filter PowerAsymptotic Asymptotics
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

variable [CompleteSpace A]

theorem gauge_add_of_commute {X Y : A} (h : Commute X Y) (s : ℝ) :
    gauge (X+Y) s=gauge X s*gauge Y s := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold gauge
  rw [smul_add,NormedSpace.exp_add_of_commute ((h.smul_left _).smul_right _)]

end KZCollar

namespace FinitePicard

section
open MeasureTheory Set KZCollar
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def centralizer (Z : A) : Submodule ℝ A where
  carrier := {a | Commute Z a}
  zero_mem' := Commute.zero_right Z
  add_mem' := fun h h' => h.add_right h'
  smul_mem' := fun r _ h => h.smul_right r

variable [FiniteDimensional ℝ A]

theorem term_commute (Z : A) {Ω : ℝ → A} (hΩ : ∀ t,Commute Z (Ω t)) (a : ℝ) (n : ℕ) (t : ℝ) :
    Commute Z (term Ω a n t) := by
  induction n generalizing t with
  | zero => exact Commute.one_right Z
  | succ n ih =>
    exact integral_mem_submodule (centralizer Z) (fun s => Ω s*term Ω a n s) a t
      (fun s => (hΩ s).mul_right (ih s))

theorem transport_commute (Z : A) {Ω : ℝ → A} (hΩ : ∀ t,Commute Z (Ω t)) (a : ℝ) (N : ℕ) (t : ℝ) :
    Commute Z (transport Ω a N t) :=
  Commute.sum_right (Finset.range (N+1)) _ Z (fun n _ => term_commute Z hΩ a n t)

end

open MeasureTheory Set
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem transport_add_commute (F : NilpotentFiltration A) {Ω Ξ : ℝ → A}
    (hΩ : ∀ s,Ω s∈F.space 1) (hΞ : ∀ s,Ξ s∈F.space 1)
    {a b : ℝ} (hab : a<b) (hiΩ : IntervalIntegrable Ω volume a b)
    (hiΞ : IntervalIntegrable Ξ volume a b)
    (hcΩ : ContinuousOn Ω (Ioo a b)) (hcΞ : ContinuousOn Ξ (Ioo a b))
    (hcomm : ∀ s t,Commute (Ξ s) (Ω t)) :
    transport (fun s => Ω s+Ξ s) a F.cutoff b=
      transport Ω a F.cutoff b*transport Ξ a F.cutoff b := by
  let f := fun t => transport Ω a F.cutoff t*transport Ξ a F.cutoff t
  have hf : ∀ s∈Ioo a b,HasDerivAt f ((Ω s+Ξ s)*f s) s := by
    intro s hs
    apply ((derivative_nilpotent_transport F hΩ hiΩ hcΩ hs).mul
      (derivative_nilpotent_transport F hΞ hiΞ hcΞ hs)).congr_deriv
    dsimp only [f]
    have hh := transport_commute (Ξ s) (hcomm s) a F.cutoff s
    rw [mul_assoc,←mul_assoc (transport Ω a F.cutoff s) (Ξ s),←hh.eq,mul_assoc]
    rw [add_mul]
  have hfc : ContinuousOn f (Icc a b) := by
    have hc₁ := continuousOn_transport hiΩ F.cutoff
    have hc₂ := continuousOn_transport hiΞ F.cutoff
    rw [uIcc_of_le hab.le] at hc₁ hc₂
    exact hc₁.mul hc₂
  have hu : ∀ s∈Icc a b,IsUnit (f s) := fun s _ =>
    (transport_isUnit F hΩ a s F.cutoff).mul (transport_isUnit F hΞ a s F.cutoff)
  rw [transport_eq_fundamental F (fun s => (F.space 1).add_mem (hΩ s) (hΞ s))
    hab (hiΩ.add hiΞ) (hcΩ.add hcΞ) hf hfc hu]
  simp only [f,transport_base,mul_one,Ring.inverse_one]

end FinitePicard

namespace KZProduct
open FinitePicard KZCollar MeasureTheory Set
variable {A B C : Type*} [NormedRing A] [NormedRing B] [NormedRing C]
  [NormedAlgebra ℝ A] [NormedAlgebra ℝ B] [NormedAlgebra ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [CompleteSpace A] [CompleteSpace B] [CompleteSpace C]
variable (f : A →ₐ[ℝ] C) (g : B →ₐ[ℝ] C) (hc : ∀ a b,Commute (f a) (g b))

include hc
omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [CompleteSpace A] [CompleteSpace B] [CompleteSpace C] in
 theorem shuffle (a c : A) (b d : B) :
    (f a*g b)*(f c*g d)=f (a*c)*g (b*d) := by
  rw [(hc c b).symm.mul_mul_mul_comm,map_mul,map_mul]

omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [CompleteSpace A] [CompleteSpace B] in
 theorem gauge_sum {X : A} {Y : B} {M N : ℕ}
    (hX : X^(M+1)=0) (hY : Y^(N+1)=0) (s : ℝ) :
    gauge (f X+g Y) s=f (gauge X s)*g (gauge Y s) := by
  rw [gauge_add_of_commute (hc X Y),←map_gauge f X hX,←map_gauge g Y hY]

omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C] in
 theorem regular_sum {X Y : A} {Z T : B} {M N : ℕ}
    (hX : X^(M+1)=0) (hZ : Z^(N+1)=0) (s : ℝ) :
    regularForm (f X+g Z) (f Y+g T) s=f (regularForm X Y s)+g (regularForm Z T s) := by
  have hXn : (-X)^(M+1)=0 := by rw [neg_pow,hX,mul_zero]
  have hZn : (-Z)^(N+1)=0 := by rw [neg_pow,hZ,mul_zero]
  have hn : -(f X+g Z)=f (-X)+g (-Z) := by rw [map_neg,map_neg,neg_add]
  simp only [regularForm,hn,gauge_sum f g hc hX hZ,gauge_sum f g hc hXn hZn]
  have hm : (s-1)⁻¹ • (f Y+g T)=f ((s-1)⁻¹ • Y)*g 1+f 1*g ((s-1)⁻¹ • T) := by
    simp only [smul_add,map_smul,map_one,mul_one,one_mul]
  rw [hm,mul_add,add_mul,shuffle f g hc,shuffle f g hc,
    shuffle f g hc,shuffle f g hc]
  simp only [mul_one,one_mul,gauge_neg_mul,map_one]

omit [CompleteSpace A] [CompleteSpace B] in
 theorem normalized_sum (F : NilpotentFiltration A) (G : NilpotentFiltration B)
    (H : NilpotentFiltration C) {X Y : A} {Z T : B}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (hZ : Z∈G.space 1) (hT : T∈G.space 1)
    (hfX : f X∈H.space 1) (hfY : f Y∈H.space 1)
    (hgZ : g Z∈H.space 1) (hgT : g T∈H.space 1)
    {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    normalizedSolution H (f X+g Z) (f Y+g T) s=
      f (normalizedSolution F X Y s)*g (normalizedSolution G Z T s) := by
  have hfn : (f X)^(F.cutoff+1)=0 := by rw [←map_pow,pow_cutoff_eq_zero F hX,map_zero]
  have hgn : (g Z)^(G.cutoff+1)=0 := by rw [←map_pow,pow_cutoff_eq_zero G hZ,map_zero]
  have hreg (r : ℝ) : regularForm (f X+g Z) (f Y+g T) r=
      regularForm (f X) (f Y) r+regularForm (g Z) (g T) r := by
    rw [regular_sum f g hc (pow_cutoff_eq_zero F hX) (pow_cutoff_eq_zero G hZ),
      map_regularForm f X Y (pow_cutoff_eq_zero F hX),map_regularForm g Z T (pow_cutoff_eq_zero G hZ)]
  have hcomm (r t : ℝ) : Commute (regularForm (g Z) (g T) r) (regularForm (f X) (f Y) t) := by
    rw [←map_regularForm f X Y (pow_cutoff_eq_zero F hX),
      ←map_regularForm g Z T (pow_cutoff_eq_zero G hZ)]
    exact (hc _ _).symm
  rw [map_normalized_general f F H hX hY hfX hfY hs.le hs1,
    map_normalized_general g G H hZ hT hgZ hgT hs.le hs1]
  simp only [normalizedSolution,gauge_add_of_commute (hc X Z)]
  rw [show regularForm (f X+g Z) (f Y+g T)=(fun r => regularForm (f X) (f Y) r+regularForm (g Z) (g T) r) from funext hreg]
  rw [transport_add_commute H (regularForm_mem H hfX hfY) (regularForm_mem H hgZ hgT) hs
    (regularForm_integrable (f X) (f Y) hfn hs.le hs1)
    (regularForm_integrable (g Z) (g T) hgn hs.le hs1)
    (regularForm_continuous _ _ hs1.le) (regularForm_continuous _ _ hs1.le) hcomm]
  have ht : Commute (gauge (g Z) s) (transport (regularForm (f X) (f Y)) 0 H.cutoff s) := by
    apply transport_commute
    intro r
    rw [←map_gauge g Z (pow_cutoff_eq_zero G hZ),←map_regularForm f X Y (pow_cutoff_eq_zero F hX)]
    exact (hc _ _).symm
  exact ht.mul_mul_mul_comm _ _

 theorem associator_product (F : NilpotentFiltration A) (G : NilpotentFiltration B)
    (H : NilpotentFiltration C) {X Y : A} {Z T : B}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (hZ : Z∈G.space 1) (hT : T∈G.space 1)
    (hfX : f X∈H.space 1) (hfY : f Y∈H.space 1)
    (hgZ : g Z∈H.space 1) (hgT : g T∈H.space 1) :
    associator H (f X+g Z) (f Y+g T)=f (associator F X Y)*g (associator G Z T) := by
  have h₁ := normalized_sum f g hc F G H hX hY hZ hT hfX hfY hgZ hgT
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have h₂ := normalized_sum f g hc F G H hY hX hT hZ hfY hfX hgT hgZ
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  simp only [KZCollar.associator,rightSolution,show (1:ℝ)-1/2=1/2 by norm_num]
  rw [h₁,h₂]
  have hu := (normalizedSolution_isUnit G hT hZ (1/2)).map g
  rw [Ring.inverse_mul (Or.inr hu),←map_unit_inverse f (normalizedSolution_isUnit F hY hX (1/2)),
    ←map_unit_inverse g (normalizedSolution_isUnit G hT hZ (1/2)),
    (hc (Ring.inverse (normalizedSolution F Y X (1/2))) (Ring.inverse (normalizedSolution G T Z (1/2)))).eq.symm,
    shuffle f g hc]

end KZProduct

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace OperatorLog

section
open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem sum_range_extend {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n m : ℕ} (h : n ≤ m)
    (hz : ∀ k,n ≤ k → k < m → f k=0) :
    ∑ k∈Finset.range n,f k=∑ k∈Finset.range m,f k := by
  apply Finset.sum_subset (Finset.range_mono h)
  intro k hkm hkn
  exact hz k (Nat.le_of_not_lt (by simpa using hkn)) (Finset.mem_range.mp hkm)

theorem interpolate_nat (N : ℕ) (T : Module.End ℚ V) (hT : T^(N+1)=0) (m : ℕ) :
    interpolate N T m=(1+T)^m := by
  have hpow : ∀ k,N+1 ≤ k → T^k=0 := fun k hk => by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add,hT,zero_mul]
  have hsmall : ∀ k,m+1 ≤ k → (m.choose k : ℚ) • T^k=0 := by
    intro k hk
    rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_smul]
  unfold interpolate
  simp only [binom_eval_nat]
  rw [sum_range_extend (fun k => (m.choose k : ℚ) • T^k) (m:=N+m+2) (by omega)
    (fun k hk _ => by rw [hpow k hk,smul_zero])]
  rw [←sum_range_extend (fun k => (m.choose k : ℚ) • T^k) (n:=m+1) (m:=N+m+2) (by omega)
    (fun k hk _ => hsmall k hk)]
  rw [add_comm (1:Module.End ℚ V) T,(Commute.one_right T).add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [one_pow,mul_one,Algebra.smul_def,map_natCast]
  exact Nat.cast_comm _ _

def valuePolynomial (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) : ℚ[X] :=
  ∑ k∈Finset.range (N+1),binom k*C (l ((T^k) a))

theorem value_eval (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) (s : ℚ) :
    (valuePolynomial N T a l).eval s=l (interpolate N T s a) := by
  simp [valuePolynomial,interpolate,LinearMap.sum_apply,LinearMap.smul_apply,Polynomial.eval_finsetSum]

theorem value_one (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) :
    (valuePolynomial N T a l).coeff 1=l (logarithm N T a) := by
  simp [valuePolynomial,logarithm,LinearMap.sum_apply,LinearMap.smul_apply]

theorem polynomial_ext_nat {p q : ℚ[X]} (h : ∀ n : ℕ,p.eval (n:ℚ)=q.eval (n:ℚ)) : p=q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R:=ℚ))).mono
  rintro _ ⟨n,rfl⟩
  exact h n

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]

def pairPolynomial (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) : ℚ[X] :=
  ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
    (binom i*binom j)*C (l (B ((T^i) a) ((S^j) b)))

theorem pair_eval (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) (s : ℚ) :
    (pairPolynomial N T S B a b l).eval s=
      l (B (interpolate N T s a) (interpolate N S s b)) := by
  simp only [pairPolynomial,Polynomial.eval_finsetSum,eval_mul,eval_C,interpolate,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem pair_one (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) :
    (pairPolynomial N T S B a b l).coeff 1=
      l (B (logarithm N T a) b+B a (logarithm N S b)) := by
  simp [pairPolynomial,logarithm,LinearMap.sum_apply,LinearMap.smul_apply,mul_coeff_one,
    binom_coeff_zero,add_mul,Finset.sum_add_distrib,ite_mul,mul_ite,add_comm]

end

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

theorem powers_natural (T : Module.End ℚ V) (S : Module.End ℚ W) (f : V →ₗ[ℚ] W)
    (h : ∀ v,f (T v)=S (f v)) (n : ℕ) (v : V) : f ((T^n) v)=(S^n) (f v) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Module.End.mul_apply,h,ih]

theorem logarithm_natural (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (f : V →ₗ[ℚ] W) (h : ∀ v,f (T v)=S (f v)) (v : V) :
    f (logarithm N T v)=logarithm N S (f v) := by
  simp only [logarithm,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    powers_natural T S f h]

end OperatorLog

namespace KZComparison
open CutoffDepth CutoffKZ FinitePicard KZCollar

 theorem negative_val (N : ℕ) : (negative N:Q ℝ N)=associator (weight N) (-X N) (-Y N) := by
  change CutoffScaling.map N (-1:ℝ) (positive N:Q ℝ N)=_
  rw [positive_val,map_associator _ (weight N) (weight N) rfl (gen_weight N false) (gen_weight N true)]
  have h (b : Bool) : CutoffScaling.map N (-1:ℝ) (gen N b)= -gen N b := by
    simpa only [neg_smul,one_smul,gen,TruncatedSubstitution.gen] using CutoffScaling.map_gen N (-1:ℝ) b
  rw [h false,h true]

end KZComparison

namespace KZGroupLike
open scoped TensorProduct
open CutoffDepth CutoffKZ CutoffDiagonal KZCollar
local instance (N : ℕ) : NormedRing (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedRing _
local instance (N : ℕ) : NormedAlgebra ℝ (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedAlgebra _
 theorem associator_diagonal (N : ℕ) :
    diagonal N (associator (weight (N+N)) (X (N+N)) (Y (N+N)))=
    associator (weight N) (X N) (Y N)⊗ₜ[ℝ]associator (weight N) (X N) (Y N) := by
  rw [map_associator_general (diagonal N) (weight (N+N)) (tensorWeight N)
    (gen_weight (N+N) false) (gen_weight (N+N) true)
    (diagonal_mem N 1 _ (gen_weight (N+N) false)) (diagonal_mem N 1 _ (gen_weight (N+N) true)),
    diagonal_gen,diagonal_gen]
  rw [KZProduct.associator_product (left N) (right N) (commute N) (weight N) (weight N) (tensorWeight N)
    (gen_weight N false) (gen_weight N true) (gen_weight N false) (gen_weight N true)
    (left_mem N 1 _ (gen_weight N false)) (left_mem N 1 _ (gen_weight N true))
    (right_mem N 1 _ (gen_weight N false)) (right_mem N 1 _ (gen_weight N true))]
  change (_⊗ₜ[ℝ](1:Q ℝ N))*((1:Q ℝ N)⊗ₜ[ℝ]_)=_
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
 theorem positive_diagonal (N : ℕ) :
    diagonal N (KZComparison.positive (N+N):Q ℝ (N+N))=
      (KZComparison.positive N:Q ℝ N)⊗ₜ[ℝ](KZComparison.positive N:Q ℝ N) := by
  simp only [KZComparison.positive_val,associator_diagonal]
 theorem negative_diagonal (N : ℕ) :
    diagonal N (KZComparison.negative (N+N):Q ℝ (N+N))=
      (KZComparison.negative N:Q ℝ N)⊗ₜ[ℝ](KZComparison.negative N:Q ℝ N) := by
  simp only [KZComparison.negative_val]
  rw [map_associator_general (diagonal N) (weight (N+N)) (tensorWeight N)
    ((weight (N+N)).space 1|>.neg_mem (gen_weight (N+N) false))
    ((weight (N+N)).space 1|>.neg_mem (gen_weight (N+N) true))
    (by rw [map_neg]; exact ((tensorWeight N).space 1).neg_mem (diagonal_mem N 1 _ (gen_weight (N+N) false)))
    (by rw [map_neg]; exact ((tensorWeight N).space 1).neg_mem (diagonal_mem N 1 _ (gen_weight (N+N) true)))]
  simp only [map_neg,diagonal_gen,neg_add]
  rw [←map_neg (left N),←map_neg (right N),←map_neg (left N),←map_neg (right N)]
  rw [KZProduct.associator_product (left N) (right N) (commute N) (weight N) (weight N) (tensorWeight N)
    ((weight N).space 1|>.neg_mem (gen_weight N false)) ((weight N).space 1|>.neg_mem (gen_weight N true))
    ((weight N).space 1|>.neg_mem (gen_weight N false)) ((weight N).space 1|>.neg_mem (gen_weight N true))
    (by simpa only [map_neg] using ((tensorWeight N).space 1).neg_mem (left_mem N 1 _ (gen_weight N false)))
    (by simpa only [map_neg] using ((tensorWeight N).space 1).neg_mem (left_mem N 1 _ (gen_weight N true)))
    (by simpa only [map_neg] using ((tensorWeight N).space 1).neg_mem (right_mem N 1 _ (gen_weight N false)))
    (by simpa only [map_neg] using ((tensorWeight N).space 1).neg_mem (right_mem N 1 _ (gen_weight N true)))]
  change (_⊗ₜ[ℝ](1:Q ℝ N))*((1:Q ℝ N)⊗ₜ[ℝ]_)=_
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
end KZGroupLike

namespace TruncatedSubstitution
open AssociativeElimination TruncatedWords
variable {R α B : Type*} [CommRing R] [Ring B] [Algebra R B]
 theorem hom_ext (N : ℕ) (f g : Q (∅ : Set (A R α)) N →ₐ[R] B)
    (h : ∀ a,f (gen N a)=g (gen N a)) : f=g := by
  have he : f.comp (quotient ∅ N)=g.comp (quotient ∅ N) := by
    apply AssociativeElimination.hom_ext
    exact h
  apply AlgHom.ext
  intro u
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations (∅ : Set (A R α)) N) u
  exact AlgHom.congr_fun he p
end TruncatedSubstitution

namespace ConjugateCoalgebra
open scoped TensorProduct
open CutoffDepth CutoffKZ CutoffDiagonal ConjugateComparison

def tensorUnit {A : Type*} [Ring A] [Algebra ℝ A] (P : Aˣ) : (A⊗[ℝ]A)ˣ where
  val := (P:A)⊗ₜ[ℝ](P:A)
  inv := ((P⁻¹:Aˣ):A)⊗ₜ[ℝ]((P⁻¹:Aˣ):A)
  val_inv := by rw [Algebra.TensorProduct.tmul_mul_tmul,Units.mul_inv,Algebra.TensorProduct.one_def]
  inv_val := by rw [Algebra.TensorProduct.tmul_mul_tmul,Units.inv_mul,Algebra.TensorProduct.one_def]

theorem inverse_diagonal (N : ℕ) (P : (Q ℝ (N+N))ˣ) (p : (Q ℝ N)ˣ)
    (h : diagonal N (P:Q ℝ (N+N))=(p:Q ℝ N)⊗ₜ[ℝ](p:Q ℝ N)) :
    diagonal N ((P⁻¹:(Q ℝ (N+N))ˣ):Q ℝ (N+N))=
      ((p⁻¹:(Q ℝ N)ˣ):Q ℝ N)⊗ₜ[ℝ]((p⁻¹:(Q ℝ N)ˣ):Q ℝ N) := by
  have hu : Units.map (diagonal N).toMonoidHom P=tensorUnit p := Units.ext h
  have hh := congrArg (fun u => ((u⁻¹:(Q ℝ N⊗[ℝ]Q ℝ N)ˣ):Q ℝ N⊗[ℝ]Q ℝ N)) hu
  exact hh

theorem transport_cutoff_gen (N : ℕ) (P : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1) (b : Bool) :
    transport N P hP (gen N b)=family N P b := transport_gen N P hP b

theorem congr_tmul {A : Type*} [Ring A] [Algebra ℝ A] (e : A ≃ₐ[ℝ] A) (a b : A) :
    Algebra.TensorProduct.congr e e (a⊗ₜ[ℝ]b)=e a⊗ₜ[ℝ]e b := rfl

theorem transport_diagonal (N : ℕ) (P : (Q ℝ (N+N))ˣ) (p : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ (N+N))-1∈TruncatedWords.filtration ∅ (N+N) 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : diagonal N (P:Q ℝ (N+N))=(p:Q ℝ N)⊗ₜ[ℝ](p:Q ℝ N)) (u : Q ℝ (N+N)) :
    diagonal N (transport (N+N) P hP u)=
      Algebra.TensorProduct.congr (transport N p hp) (transport N p hp) (diagonal N u) := by
  have he : (diagonal N).comp (transport (N+N) P hP).toAlgHom=
      (Algebra.TensorProduct.congr (transport N p hp) (transport N p hp)).toAlgHom.comp (diagonal N) := by
    apply TruncatedSubstitution.hom_ext (N+N)
    intro b
    change diagonal N (transport (N+N) P hP (gen (N+N) b))=
      Algebra.TensorProduct.congr (transport N p hp) (transport N p hp) (diagonal N (gen (N+N) b))
    rw [transport_cutoff_gen,diagonal_gen]
    cases b
    · simp only [family,left,right,Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply,map_add,congr_tmul,map_one,
        transport_cutoff_gen,ConjugateComparison.family]
      exact diagonal_gen N false
    · change diagonal N (((P⁻¹:(Q ℝ (N+N))ˣ):Q ℝ (N+N))*gen (N+N) true*(P:Q ℝ (N+N)))=_
      rw [map_mul,map_mul,inverse_diagonal N P p h,h,diagonal_gen]
      change (_⊗ₜ[ℝ]_)*(gen N true⊗ₜ[ℝ]1+1⊗ₜ[ℝ]gen N true)*(_⊗ₜ[ℝ]_)=_
      simp only [mul_add,add_mul,Algebra.TensorProduct.tmul_mul_tmul,mul_one,
        Units.inv_mul,map_add,left,right,Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply,congr_tmul,map_one,
        transport_cutoff_gen,family]
      rfl
  exact AlgHom.congr_fun he u

theorem natural_inverse {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    (f : A →ₐ[ℝ] B) (e : A ≃ₐ[ℝ] A) (d : B ≃ₐ[ℝ] B)
    (he : ∀ u,f (e u)=d (f u)) (u : A) : f (e.symm u)=d.symm (f u) := by
  apply d.injective
  rw [d.apply_symm_apply,←he,e.apply_symm_apply]

theorem theta_diagonal (N : ℕ) (P V : (Q ℝ (N+N))ˣ) (p v : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ (N+N))-1∈TruncatedWords.filtration ∅ (N+N) 1)
    (hV : (V:Q ℝ (N+N))-1∈TruncatedWords.filtration ∅ (N+N) 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hv : (v:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hΔP : diagonal N (P:Q ℝ (N+N))=(p:Q ℝ N)⊗ₜ[ℝ](p:Q ℝ N))
    (hΔV : diagonal N (V:Q ℝ (N+N))=(v:Q ℝ N)⊗ₜ[ℝ](v:Q ℝ N)) (u : Q ℝ (N+N)) :
    diagonal N (theta (N+N) P V hP hV u)=
      Algebra.TensorProduct.congr (theta N p v hp hv) (theta N p v hp hv) (diagonal N u) := by
  rw [theta,AlgEquiv.trans_apply,transport_diagonal N V v hV hv hΔV,
    natural_inverse (diagonal N) (transport (N+N) P hP)
      (Algebra.TensorProduct.congr (transport N p hp) (transport N p hp))
      (transport_diagonal N P p hP hp hΔP)]
  generalize diagonal N u=z
  induction z using TensorProduct.induction_on with
  | zero => first | rfl | exact Submodule.zero_mem _ | simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul a b => rfl

theorem arrow_diagonal (N : ℕ) (P V : (Q ℝ (N+N))ˣ) (p v : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ (N+N))-1∈TruncatedWords.filtration ∅ (N+N) 1)
    (hV : (V:Q ℝ (N+N))-1∈TruncatedWords.filtration ∅ (N+N) 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hv : (v:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hΔP : diagonal N (P:Q ℝ (N+N))=(p:Q ℝ N)⊗ₜ[ℝ](p:Q ℝ N))
    (hΔV : diagonal N (V:Q ℝ (N+N))=(v:Q ℝ N)⊗ₜ[ℝ](v:Q ℝ N)) :
    diagonal N (unitArrow (N+N) P V hP hV:Q ℝ (N+N))=
      (unitArrow N p v hp hv:Q ℝ N)⊗ₜ[ℝ](unitArrow N p v hp hv:Q ℝ N) := by
  have ht : diagonal N (Units.map (theta (N+N) P V hP hV).toMonoidHom P:Q ℝ (N+N))=
      (Units.map (theta N p v hp hv).toMonoidHom p:Q ℝ N)⊗ₜ[ℝ]
        (Units.map (theta N p v hp hv).toMonoidHom p:Q ℝ N) := by
    change diagonal N (theta (N+N) P V hP hV (P:Q ℝ (N+N)))=_
    rw [theta_diagonal N P V p v hP hV hp hv hΔP hΔV,hΔP]
    rfl
  simp only [unitArrow,Units.val_mul,map_mul,hΔV,inverse_diagonal N _ _ ht,
    Algebra.TensorProduct.tmul_mul_tmul]
end ConjugateCoalgebra

namespace OperatorLog

section
open scoped TensorProduct
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem logarithm_stable (T : Module.End ℚ V) {N M : ℕ} (hT : T^(N+1)=0) (hNM : N≤M) :
    logarithm N T=logarithm M T := by
  unfold logarithm
  apply sum_range_extend _ (by omega : N+1≤M+1)
  intro k hk hkm
  rw [pow_eq_zero_of_le hk hT,smul_zero]

end

variable {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]

theorem logarithm_diagonal (N : ℕ) (T : Module.End ℚ V) (R : Module.End ℚ W)
    (hT : T^(N+1)=0) (hR : R^(N+1)=0)
    (Δ : V →ₗ[ℚ] Z) (B : W →ₗ[ℚ] W →ₗ[ℚ] Z) (a : V) (b : W)
    (h : ∀ m : ℕ,Δ (((1+T)^m) a)=B (((1+R)^m) b) (((1+R)^m) b)) :
    Δ (logarithm N T a)=B (logarithm N R b) b+B b (logarithm N R b) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro l
  have hp : valuePolynomial N T a (l.comp Δ)=pairPolynomial N R R B b b l := by
    apply polynomial_ext_nat
    intro m
    rw [value_eval,pair_eval,interpolate_nat N T hT,interpolate_nat N R hR]
    exact congrArg l (h m)
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff 1) hp
  rw [value_one,pair_one] at hc
  simpa only [map_sub,sub_eq_zero,LinearMap.comp_apply] using hc

end OperatorLog

namespace KZPrimitiveValue
open scoped TensorProduct
open CutoffDepth CutoffKZ CutoffDiagonal KZComparison

 theorem theta_diagonal (N : ℕ) (u : Q ℝ (N+N)) :
    diagonal N (theta (N+N) u)=
      Algebra.TensorProduct.congr (theta N) (theta N) (diagonal N u) :=
  ConjugateCoalgebra.theta_diagonal N _ _ _ _ _ _ _ _
    (KZGroupLike.positive_diagonal N) (KZGroupLike.negative_diagonal N) u

 theorem arrow_diagonal (N : ℕ) : diagonal N (arrow (N+N):Q ℝ (N+N))=
    (arrow N:Q ℝ N)⊗ₜ[ℝ](arrow N:Q ℝ N) :=
  ConjugateCoalgebra.arrow_diagonal N _ _ _ _ _ _ _ _
    (KZGroupLike.positive_diagonal N) (KZGroupLike.negative_diagonal N)

 def S (N : ℕ) : Module.End ℝ (Q ℝ N) :=
  (LinearMap.mulLeft ℝ (arrow N:Q ℝ N)).comp (theta N).toLinearMap
 @[simp] theorem S_apply (N : ℕ) (u : Q ℝ N) : S N u=(arrow N:Q ℝ N)*theta N u := rfl

 theorem category_S (N : ℕ) : (category N).S false true=(S N).restrictScalars ℚ := by
  apply LinearMap.ext
  intro u
  simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,frames,inv_one,
    Units.val_one,mul_one]
  rfl

 theorem S_diagonal (N : ℕ) (u : Q ℝ (N+N)) :
    diagonal N (S (N+N) u)=TensorProduct.map (S N) (S N) (diagonal N u) := by
  rw [S_apply,map_mul,arrow_diagonal,theta_diagonal]
  generalize diagonal N u=z
  induction z using TensorProduct.induction_on with
  | zero => first | rfl | exact Submodule.zero_mem _ | simp
  | add z w hz hw => simp only [map_add,mul_add,hz,hw]
  | tmul a b =>
    rw [ConjugateCoalgebra.congr_tmul,Algebra.TensorProduct.tmul_mul_tmul]
    rfl

 def tmulQ (N : ℕ) : Q ℝ N →ₗ[ℚ] Q ℝ N →ₗ[ℚ] Q ℝ N⊗[ℝ]Q ℝ N :=
  LinearMap.mk₂ ℚ (fun a b => a⊗ₜ[ℝ]b)
    TensorProduct.add_tmul (fun c a b => (TensorProduct.smul_tmul' c a b).symm)
    TensorProduct.tmul_add TensorProduct.tmul_smul

 theorem orbit_diagonal (N m : ℕ) :
    diagonal N ((((category (N+N)).S false true)^m) (1:Q ℝ (N+N)))=
      ((((category N).S false true)^m) (1:Q ℝ N))⊗ₜ[ℝ]
        ((((category N).S false true)^m) (1:Q ℝ N)) := by
  induction m with
  | zero => simp only [pow_zero,Module.End.one_apply,map_one,Algebra.TensorProduct.one_def]
  | succ m ih =>
    simp only [pow_succ',Module.End.mul_apply]
    rw [category_S]
    change diagonal N (S (N+N) _)=_
    rw [category_S] at ih
    rw [S_diagonal,ih,TensorProduct.map_tmul,category_S]
    rfl

 theorem value_diagonal (N : ℕ) : diagonal N (value (N+N))=
    value N⊗ₜ[ℝ](1:Q ℝ N)+(1:Q ℝ N)⊗ₜ[ℝ]value N := by
  let T := (category (N+N)).S false true-1
  let R := (category N).S false true-1
  have hT : T^(N+N+1+1)=0 := (category (N+N)).nilpotent false true
  have hR : R^(N+1+1)=0 := (category N).nilpotent false true
  have hR' : R^(N+N+1+1)=0 := pow_eq_zero_of_le (by omega) hR
  have hh := OperatorLog.logarithm_diagonal (N+N+1) T R hT hR'
    ((diagonal N).toLinearMap.restrictScalars ℚ) (tmulQ N) 1 1 (by
      intro m
      have ht : 1+T=(category (N+N)).S false true := by dsimp only [T]; abel
      have hr : 1+R=(category N).S false true := by dsimp only [R]; abel
      rw [ht,hr]
      exact orbit_diagonal N m)
  rw [←OperatorLog.logarithm_stable R hR (by omega : N+1≤N+N+1)] at hh
  exact hh

end KZPrimitiveValue

namespace KZCutoffComparison
open CutoffDepth CutoffKZ CutoffDiagonal KZComparison ConjugateComparison

 theorem transport_natural (M N : ℕ) (f : Q ℝ M →ₐ[ℝ] Q ℝ N)
    (hgen : ∀ b,f (gen M b)=gen N b) (P : (Q ℝ M)ˣ) (p : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : Units.map f.toMonoidHom P=p) (u : Q ℝ M) :
    f (transport M P hP u)=transport N p hp (f u) := by
  have hv : f (P:Q ℝ M)=(p:Q ℝ N) := congrArg Units.val h
  have hi : f ((P⁻¹:(Q ℝ M)ˣ):Q ℝ M)=((p⁻¹:(Q ℝ N)ˣ):Q ℝ N) :=
    congrArg (fun v => ((v⁻¹:(Q ℝ N)ˣ):Q ℝ N)) h
  have he : f.comp (transport M P hP).toAlgHom=(transport N p hp).toAlgHom.comp f := by
    apply TruncatedSubstitution.hom_ext M
    intro b
    change f (transport M P hP (gen M b))=transport N p hp (f (gen M b))
    rw [ConjugateCoalgebra.transport_cutoff_gen,hgen,ConjugateCoalgebra.transport_cutoff_gen]
    cases b
    · exact hgen false
    · change f (((P⁻¹:(Q ℝ M)ˣ):Q ℝ M)*gen M true*(P:Q ℝ M))=_
      rw [map_mul,map_mul,hi,hv,hgen]
      rfl
  exact AlgHom.congr_fun he u

 theorem theta_natural (M N : ℕ) (f : Q ℝ M →ₐ[ℝ] Q ℝ N)
    (hgen : ∀ b,f (gen M b)=gen N b) (P V : (Q ℝ M)ˣ) (p v : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hV : (V:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hv : (v:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : Units.map f.toMonoidHom P=p) (k : Units.map f.toMonoidHom V=v) (u : Q ℝ M) :
    f (ConjugateComparison.theta M P V hP hV u)=ConjugateComparison.theta N p v hp hv (f u) := by
  rw [ConjugateComparison.theta,AlgEquiv.trans_apply,transport_natural M N f hgen V v hV hv k,
    ConjugateCoalgebra.natural_inverse f (transport M P hP) (transport N p hp)
      (transport_natural M N f hgen P p hP hp h)]
  rfl

 theorem arrow_natural (M N : ℕ) (f : Q ℝ M →ₐ[ℝ] Q ℝ N)
    (hgen : ∀ b,f (gen M b)=gen N b) (P V : (Q ℝ M)ˣ) (p v : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hV : (V:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hv : (v:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : Units.map f.toMonoidHom P=p) (k : Units.map f.toMonoidHom V=v) :
    Units.map f.toMonoidHom (unitArrow M P V hP hV)=unitArrow N p v hp hv := by
  have ht : Units.map f.toMonoidHom (Units.map (ConjugateComparison.theta M P V hP hV).toMonoidHom P)=
      Units.map (ConjugateComparison.theta N p v hp hv).toMonoidHom p := by
    apply Units.ext
    change f (ConjugateComparison.theta M P V hP hV (P:Q ℝ M))=_
    rw [theta_natural M N f hgen P V p v hP hV hp hv h k,show f (P:Q ℝ M)=(p:Q ℝ N) from congrArg Units.val h]
    rfl
  simp only [unitArrow,map_mul,map_inv,k,ht]

 theorem positive_drop (M N : ℕ) (h : N≤M) :
    Units.map (drop M N h).toMonoidHom (positive M)=positive N := by
  apply Units.ext
  change drop M N h (positive M:Q ℝ M)=(positive N:Q ℝ N)
  rw [positive_val,positive_val,drop_associator]
 theorem negative_drop (M N : ℕ) (h : N≤M) :
    Units.map (drop M N h).toMonoidHom (negative M)=negative N := by
  apply Units.ext
  change drop M N h (negative M:Q ℝ M)=(negative N:Q ℝ N)
  rw [negative_val,negative_val,KZCollar.map_associator_general (drop M N h) (weight M) (weight N)
    ((weight M).space 1|>.neg_mem (gen_weight M false)) ((weight M).space 1|>.neg_mem (gen_weight M true))
    (by simpa only [map_neg,drop_gen] using ((weight N).space 1).neg_mem (gen_weight N false))
    (by simpa only [map_neg,drop_gen] using ((weight N).space 1).neg_mem (gen_weight N true)),map_neg,map_neg,drop_gen,drop_gen]

 theorem theta_drop (M N : ℕ) (h : N≤M) (u : Q ℝ M) :
    drop M N h (KZComparison.theta M u)=KZComparison.theta N (drop M N h u) :=
  theta_natural M N (drop M N h) (drop_gen M N h) _ _ _ _ _ _ _ _
    (positive_drop M N h) (negative_drop M N h) u
 theorem arrow_drop (M N : ℕ) (h : N≤M) : Units.map (drop M N h).toMonoidHom (arrow M)=arrow N :=
  arrow_natural M N (drop M N h) (drop_gen M N h) _ _ _ _ _ _ _ _
    (positive_drop M N h) (negative_drop M N h)
 theorem S_drop (M N : ℕ) (h : N≤M) (u : Q ℝ M) :
    drop M N h ((category M).S false true u)=(category N).S false true (drop M N h u) := by
  simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,frames,inv_one,
    Units.val_one,mul_one]
  change drop M N h ((arrow M:Q ℝ M)*KZComparison.theta M u)=_
  rw [map_mul,theta_drop,show drop M N h (arrow M:Q ℝ M)=(arrow N:Q ℝ N) from congrArg Units.val (arrow_drop M N h)]
  rfl
 theorem value_drop (M N : ℕ) (h : N≤M) : drop M N h (value M)=value N := by
  have hn : ∀ u,drop M N h (((category M).S false true-1) u)=
      ((category N).S false true-1) (drop M N h u) := by
    intro u
    simp only [LinearMap.sub_apply,Module.End.one_apply,map_sub,S_drop]
  have hh := OperatorLog.logarithm_natural (M+1) ((category M).S false true-1)
    ((category N).S false true-1) ((drop M N h).toLinearMap.restrictScalars ℚ) hn 1
  rw [←OperatorLog.logarithm_stable _ ((category N).nilpotent false true) (by omega : N+1≤M+1)] at hh
  change drop M N h (value M)=OperatorLog.logarithm (N+1) _ (drop M N h 1) at hh
  rw [map_one] at hh
  exact hh

end KZCutoffComparison

namespace CutoffPrimitiveExtract
open AssociativeElimination WordGrading TensorProjection
open scoped TensorProduct
variable {R α : Type*} [CommRing R]

theorem piece_trunc (N n : ℕ) (hn : n≤N) (p : A R α) : piece n (truncVal N p)=piece n p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change piece n (project (fun w => len w≤N) (word w))=piece n (word w)
    rw [project_word]
    by_cases hw : len w≤N
    · rw [if_pos hw]
    · rw [if_neg hw,map_zero,TensorProjection.piece,WordGrading.piece,project_word,if_neg (by change len w≠n; omega)]
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem totalPiece_trunc (N n : ℕ) (hn : n≤N) (u : A R α⊗[R]A R α) :
    totalPiece n (TensorProduct.map (truncVal N) (truncVal N) u)=totalPiece n u := by
  induction u using TensorProduct.induction_on with
  | zero => first | rfl | exact Submodule.zero_mem _ | simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul p q =>
    simp only [TensorProduct.map_tmul,totalPiece,LinearMap.sum_apply,TensorProduct.map_tmul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [piece_trunc N i (by have hi' := Finset.mem_range.mp hi; omega),
      piece_trunc N (n-i) (by omega)]

def leftPair : A R α →ₐ[R] PrimitiveWords.B R α :=
  MonoidAlgebra.mapDomainAlgHom R R ((MonoidHom.id _).prod (1:FreeMonoid α →* FreeMonoid α))
def rightPair : A R α →ₐ[R] PrimitiveWords.B R α :=
  MonoidAlgebra.mapDomainAlgHom R R ((1:FreeMonoid α →* FreeMonoid α).prod (MonoidHom.id _))
@[simp] theorem leftPair_word (w : FreeMonoid α) : leftPair (word (R:=R) w)=PrimitiveWords.pair w 1 := by
  simp [leftPair,word,PrimitiveWords.pair,MonoidAlgebra.mapDomainAlgHom]
@[simp] theorem rightPair_word (w : FreeMonoid α) : rightPair (word (R:=R) w)=PrimitiveWords.pair 1 w := by
  simp [rightPair,word,PrimitiveWords.pair,MonoidAlgebra.mapDomainAlgHom]

theorem pair_commute (p q : A R α) : Commute (leftPair p) (rightPair q) := by
  change leftPair p*rightPair q=rightPair q*leftPair p
  induction p using MonoidAlgebra.induction_on with
  | of u =>
    change leftPair (word u)*rightPair q=rightPair q*leftPair (word u)
    induction q using MonoidAlgebra.induction_on with
    | of v =>
      change leftPair (word u)*rightPair (word v)=rightPair (word v)*leftPair (word u)
      simp only [leftPair_word,rightPair_word,←PrimitiveWords.pair_mul,mul_one,one_mul]
    | add q r hq hr => simp only [map_add,mul_add,add_mul,hq,hr]
    | smul c q hq => simp only [map_smul,mul_smul_comm,smul_mul_assoc,hq]
  | add p r hp hr => simp only [map_add,mul_add,add_mul,hp,hr]
  | smul c p hp => simp only [map_smul,mul_smul_comm,smul_mul_assoc,hp]

def pairMap : A R α⊗[R]A R α →ₐ[R] PrimitiveWords.B R α :=
  Algebra.TensorProduct.lift leftPair rightPair pair_commute

theorem pairMap_coproduct (p : A R α) : (pairMap (R:=R) (α:=α)) ((coproduct (R:=R) (α:=α)) p)=PrimitiveWords.coproduct p := by
  have he : (pairMap (R:=R) (α:=α)).comp coproduct=PrimitiveWords.coproduct := by
    apply AssociativeElimination.hom_ext
    intro a
    change (pairMap (R:=R) (α:=α)) ((coproduct (R:=R) (α:=α)) (atom a))=PrimitiveWords.coproduct (atom a)
    rw [TensorProjection.coproduct_atom,PrimitiveWords.coproduct_atom,map_add]
    simp only [pairMap,Algebra.TensorProduct.lift_tmul,map_one,mul_one,one_mul]
    change leftPair (word (FreeMonoid.of a))+rightPair (word (FreeMonoid.of a))=_
    rw [leftPair_word,rightPair_word]
  exact AlgHom.congr_fun he p

theorem leftPair_eq (p : A R α) : leftPair p=PrimitiveWords.left p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change leftPair (word w)=PrimitiveWords.left (word w)
    rw [leftPair_word]
    simp [PrimitiveWords.left,word]
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]
theorem rightPair_eq (p : A R α) : rightPair p=PrimitiveWords.right p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change rightPair (word w)=PrimitiveWords.right (word w)
    rw [rightPair_word]
    simp [PrimitiveWords.right,word]
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem primitive_of_tensor (p : A R α) (h : (coproduct (R:=R) (α:=α)) p=p⊗ₜ[R]1+(1:A R α)⊗ₜ[R]p) :
    PrimitiveWords.Primitive p := by
  unfold PrimitiveWords.Primitive
  have hh := congrArg (pairMap (R:=R) (α:=α)) h
  rw [pairMap_coproduct,map_add] at hh
  simpa only [pairMap,Algebra.TensorProduct.lift_tmul,map_one,mul_one,one_mul,leftPair_eq,rightPair_eq] using hh

open CutoffDepth CutoffKZ CutoffDiagonal

theorem diagonal_quotient (N : ℕ) (p : A ℝ Bool) :
    diagonal N (TruncatedWords.quotient ∅ (N+N) p)=
      TensorProduct.map (TruncatedWords.quotient ∅ N).toLinearMap (TruncatedWords.quotient ∅ N).toLinearMap ((coproduct (R:=ℝ) (α:=Bool)) p) := by
  have he : (diagonal N).comp (TruncatedWords.quotient ∅ (N+N))=
      (Algebra.TensorProduct.map (TruncatedWords.quotient ∅ N) (TruncatedWords.quotient ∅ N)).comp coproduct := by
    apply AssociativeElimination.hom_ext
    intro a
    change diagonal N (gen (N+N) a)=_
    rw [diagonal_gen]
    simp only [AlgHom.comp_apply,coproduct_atom,map_add,Algebra.TensorProduct.map_tmul,map_one]
    rfl
  exact AlgHom.congr_fun he p

theorem drop_quotient (M N : ℕ) (h : N≤M) (p : A ℝ Bool) :
    drop M N h (TruncatedWords.quotient ∅ M p)=TruncatedWords.quotient ∅ N p := by
  have he : (drop M N h).comp (TruncatedWords.quotient ∅ M)=TruncatedWords.quotient ∅ N := by
    apply AssociativeElimination.hom_ext
    intro a
    exact drop_gen M N h a
  exact AlgHom.congr_fun he p

theorem piece_primitive (N n : ℕ) (hn : n≤N) (u : Q ℝ (N+N)) (v : Q ℝ N)
    (hd : diagonal N u=v⊗ₜ[ℝ]1+(1:Q ℝ N)⊗ₜ[ℝ]v)
    (hc : drop (N+N) N (by omega) u=v) :
    PrimitiveWords.Primitive (piece n (normalVal N v)) := by
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (TruncatedWords.relations (∅:Set (A ℝ Bool)) (N+N)) u
  change drop (N+N) N _ (TruncatedWords.quotient ∅ (N+N) p)=v at hc
  rw [drop_quotient] at hc
  subst v
  rw [normalVal_quotient,piece_trunc N n hn]
  apply primitive_of_tensor
  rw [coproduct_piece]
  change diagonal N (TruncatedWords.quotient ∅ (N+N) p)=_ at hd
  have hh := congrArg (fun z => totalPiece n (TensorProduct.map (normalVal N) (normalVal N) z)) hd
  rw [diagonal_quotient] at hh
  have hmap : (TensorProduct.map (normalVal N) (normalVal N)).comp
      (TensorProduct.map (TruncatedWords.quotient ∅ N).toLinearMap (TruncatedWords.quotient ∅ N).toLinearMap)=
      TensorProduct.map (truncVal N) (truncVal N) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change (TensorProduct.map (normalVal N) (normalVal N))
      ((TensorProduct.map (TruncatedWords.quotient ∅ N).toLinearMap (TruncatedWords.quotient ∅ N).toLinearMap) (a⊗ₜ[ℝ]b))=_
    change normalVal N (TruncatedWords.quotient ∅ N a)⊗ₜ[ℝ]
      normalVal N (TruncatedWords.quotient ∅ N b)=truncVal N a⊗ₜ[ℝ]truncVal N b
    rw [normalVal_quotient,normalVal_quotient]
  change totalPiece n (((TensorProduct.map (normalVal N) (normalVal N)).comp _) ((coproduct (R:=ℝ) (α:=Bool)) p))=_ at hh
  rw [hmap,totalPiece_trunc N n hn] at hh
  simpa only [map_add,TensorProduct.map_tmul,normalVal_quotient,normalVal_one,
    totalPiece_left,totalPiece_right,piece_trunc N n hn] using hh

theorem KZ_value_lie_oai (N n : ℕ) (hn : 0<n) (hnN : n≤N) :
    ∃ q : FreeLieAlgebra ℝ Bool,q∈LieGrading.homogeneousLie (fun _ => 1) n ∧
      embed q=piece n (normalVal N (KZComparison.value N)) := by
  apply PrimitiveWords.exists_lie_of_primitive hn
  · exact project_mem _ _
  · exact piece_primitive N n hnN _ _ (KZPrimitiveValue.value_diagonal N)
      (KZCutoffComparison.value_drop (N+N) N (by omega))
end CutoffPrimitiveExtract

end DeligneDrinfeld

end

end OAI

end














section
open OAI.DeligneDrinfeld.CutoffPrimitiveExtract in
theorem solution : ∀ (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N),
    ∃ q ∈ OAI.DeligneDrinfeld.LieGrading.homogeneousLie (fun x ↦ 1) n,
      OAI.DeligneDrinfeld.AssociativeElimination.embed q =
        (OAI.DeligneDrinfeld.TensorProjection.piece n)
          ((OAI.DeligneDrinfeld.CutoffPrimitiveExtract.normalVal N) (OAI.DeligneDrinfeld.KZComparison.value N)) :=
  @OAI.DeligneDrinfeld.CutoffPrimitiveExtract.KZ_value_lie_oai
end

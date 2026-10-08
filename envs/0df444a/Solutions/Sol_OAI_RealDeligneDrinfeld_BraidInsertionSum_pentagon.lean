-- Prove2me | solution 1 for OAI.RealDeligneDrinfeld.BraidInsertionSum.pentagon
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:54:10.790108+00:00
-- url     : https://prove2.me/submissions/508c5f9e-1a0e-4b4d-be38-3afb20a27d28

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid
import Theorems.Thm_OAI_RealDeligneDrinfeld_Differentiation_special_identity

set_option linter.all false





section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

namespace TruncatedWords
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]

variable [Finite α]

variable (P : Set (A ℝ α)) (N : ℕ)

instance normedRing : NormedRing (Q P N) := FiniteAlgebraNorm.normedRing _
instance normedAlgebra : NormedAlgebra ℝ (Q P N) := FiniteAlgebraNorm.normedAlgebra _

end TruncatedWords
end

end DeligneDrinfeld

end

end OAI

end




section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace OperatorExp
open IsNilpotent
open scoped TensorProduct
variable {R V W U : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module ℚ V]
  [AddCommGroup W] [Module R W] [Module ℚ W]
  [AddCommGroup U] [Module R U] [Module ℚ U]

omit [Algebra ℚ R] in
 theorem natural (A : Module.End R V) (B : Module.End R W)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (f : V →ₗ[R] W)
    (h : ∀ v,B (f v)=f (A v)) (v : V) : exp B (f v)=f (exp A v) := by
  apply LinearMap.congr_fun (Module.End.commute_exp_left_of_commute hA hB _) v
  exact LinearMap.ext h

omit [Algebra ℚ R] in
 theorem bilinear (A : Module.End R V) (B : Module.End R W) (C : Module.End R U)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hC : IsNilpotent C)
    (m : V →ₗ[R] W →ₗ[R] U)
    (h : ∀ v w,C (m v w)=m (A v) w+m v (B w)) (v : V) (w : W) :
    exp C (m v w)=m (exp A v) (exp B w) := by
  let X : Module.End R (V⊗[R]W) := A.rTensor W
  let Y : Module.End R (V⊗[R]W) := B.lTensor V
  have hX : IsNilpotent X := hA.map (Module.End.rTensorAlgHom R V W)
  have hY : IsNilpotent Y := hB.map (Module.End.lTensorAlgHom R W V)
  have hc : Commute X Y := by ext; simp [X,Y]
  have hXY : IsNilpotent (X+Y) := hc.isNilpotent_add hX hY
  have hm : ∀ u,C (TensorProduct.lift m u)=TensorProduct.lift m ((X+Y) u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => first | rfl | exact Submodule.zero_mem _ | simp
    | add u z hu hz => simp only [map_add,hu,hz]
    | tmul a b => simpa only [LinearMap.add_apply,LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul,map_add,TensorProduct.lift.tmul,X,Y] using h a b
  have hh := natural (X+Y) C hXY hC (TensorProduct.lift m) hm (v⊗ₜ[R]w)
  rw [exp_add_of_commute hc hX hY] at hh
  have hx : exp X=(exp A).rTensor W := (hA.map_exp (Module.End.rTensorAlgHom R V W)).symm
  have hy : exp Y=(exp B).lTensor V := (hB.map_exp (Module.End.lTensorAlgHom R W V)).symm
  simpa only [hx,hy,Module.End.mul_apply,LinearMap.rTensor_tmul,LinearMap.lTensor_tmul,
    TensorProduct.lift.tmul] using hh

end OperatorExp

namespace CategoryExp

section
open IsNilpotent
variable {R A B O P : Type*} [CommRing R] [Ring A] [Algebra R A] [Module ℚ A]
  [Ring B] [Algebra R B] [Module ℚ B]

 theorem composition (g : Data R A O) (hn : ∀ p q,IsNilpotent (g.D p q))
    (p q r : O) (a b : A) : act g p r (b*a)=act g q r b*act g p q a :=
  OperatorExp.bilinear _ _ _ (hn q r) (hn p q) (hn p r) (LinearMap.mul R A)
    (fun b a => g.comp p q r a b) b a

 omit [Module ℚ A] in
 theorem pow_mem {N : ℕ} (F : FilteredComparison.Filtration R A N)
    (d : Module.End R A) (hd : ∀ n a,a∈F.step n → d a∈F.step (n+1))
    (i n : ℕ) {a : A} (ha : a∈F.step n) : (d^i) a∈F.step (n+i) := by
  induction i with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.add_zero] using ha
  | succ i ih =>
    rw [_root_.pow_succ',Module.End.mul_apply]
    simpa only [Nat.add_assoc] using hd (n+i) _ ih

 omit [Module ℚ A] in
 theorem nilpotent {N : ℕ} (F : FilteredComparison.Filtration R A N)
    (d : Module.End R A) (hd : ∀ n a,a∈F.step n → d a∈F.step (n+1)) : IsNilpotent d := by
  refine ⟨N+1,LinearMap.ext (fun a => ?_)⟩
  have hh := pow_mem F d hd (N+1) 0 (a:=a) (by rw [F.initial]; trivial)
  simpa only [Nat.zero_add,F.terminal,Submodule.mem_bot,LinearMap.zero_apply] using hh

end

open IsNilpotent
variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V]
  [Module R V] [Module ℚ V] [IsScalarTower ℚ R V]
variable {N : ℕ} (F : FilteredComparison.Filtration R V N)
  (d : Module.End R V) (k : ℕ)
  (hd : ∀ n a,a∈F.step n → d a∈F.step (n+k))

include hd

end CategoryExp

namespace TruncatedDerivation
open AssociativeElimination WordGrading TruncatedWords
variable {R α : Type*} [CommRing R]
variable (P : Set (A R α)) (N : ℕ)
local notation "Q" => TruncatedWords.Q P N
local notation "F" => filtration P N

 theorem derivation_mem (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) {n : ℕ} {p : Q} (hp : p∈F n) :
    derivation P N k v hv hP p∈F (n+k) := by
  obtain ⟨p,hp,rfl⟩ := hp
  change derivation P N k v hv hP (quotient P N p)∈_
  rw [derivation_quotient]
  exact raw_mem P N k v hv hp

end TruncatedDerivation

namespace CutoffCategory
open AssociativeElimination WordGrading TruncatedWords
variable {α O : Type*} (P : Set (A ℝ α)) (N : ℕ)

 theorem initial : (TruncatedWords.filtration P N) 0=⊤ := by
  apply top_unique
  intro a _
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (relations P N) a
  exact ⟨p,TruncatedFree.all_ge_zero p,rfl⟩

 def filtration : FilteredComparison.Filtration ℝ (TruncatedWords.Q P N) N where
  step := (TruncatedWords.filtration P N)
  decreasing := filtration_antitone P N
  initial := initial P N
  terminal := filtration_terminal P N

 variable (d : Module.End ℝ (TruncatedWords.Q P N)) (hd : ∀ a b,d (a*b)=d a*b+a*d b) (h1 : d 1=0)
  (h : O → (TruncatedWords.Q P N))

 abbrev data : CategoryExp.Data ℝ (TruncatedWords.Q P N) O := CategoryExp.gauge d hd h1 h

 theorem apply (p q : O) (a : (TruncatedWords.Q P N)) : (data P N d hd h1 h).D p q a=d a+h q*a-a*h p := rfl

 theorem raises (k : ℕ) (hdF : ∀ n a,a∈(TruncatedWords.filtration P N) n → d a∈(TruncatedWords.filtration P N) (n+k)) (hhF : ∀ p,h p∈(TruncatedWords.filtration P N) k)
    (p q : O) (n : ℕ) (a : (TruncatedWords.Q P N)) (ha : a∈(TruncatedWords.filtration P N) n) : (data P N d hd h1 h).D p q a∈(TruncatedWords.filtration P N) (n+k) := by
  rw [apply]
  apply Submodule.sub_mem
  · apply Submodule.add_mem
    · exact hdF n a ha
    · simpa only [Nat.add_comm k n] using filtration_mul P N k n (hhF q) ha
  · exact filtration_mul P N n k ha (hhF p)

end CutoffCategory

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section
namespace RealDeligneDrinfeld

namespace FreeDerivations

variable {R : Type*} [CommRing R]
variable {M : Type*} [LieRing M] [LieAlgebra R M]

structure Jet (R M : Type*) [CommRing R] [LieRing M] [LieAlgebra R M] where
  base : M
  velocity : M

def Jet.equiv : Jet R M ≃ M × M where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Jet R M) := Jet.equiv.addCommGroup
instance : Module R (Jet R M) := Jet.equiv.addEquiv.module R
instance : Bracket (Jet R M) (Jet R M) :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩

@[ext] theorem Jet.ext {a b : Jet R M} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all

@[simp] theorem Jet.base_zero : (0 : Jet R M).base = 0 := rfl
@[simp] theorem Jet.velocity_zero : (0 : Jet R M).velocity = 0 := rfl
@[simp] theorem Jet.base_add (a b : Jet R M) : (a+b).base = a.base+b.base := rfl
@[simp] theorem Jet.velocity_add (a b : Jet R M) :
    (a+b).velocity = a.velocity+b.velocity := rfl
@[simp] theorem Jet.base_smul (q : R) (a : Jet R M) : (q • a).base = q • a.base := rfl
@[simp] theorem Jet.velocity_smul (q : R) (a : Jet R M) :
    (q • a).velocity = q • a.velocity := rfl
@[simp] theorem Jet.base_lie (a b : Jet R M) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl
@[simp] theorem Jet.velocity_lie (a b : Jet R M) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl

instance : LieRing (Jet R M) where
  add_lie a b c := by (ext <;> simp [add_lie]); abel
  lie_add a b c := by (ext <;> simp [lie_add]); abel
  lie_self a := by
    ext
    · simp
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by (ext <;> simp [lie_add, add_lie, lie_lie]); abel
instance : LieAlgebra R (Jet R M) where
  lie_smul q a b := by ext <;> simp [lie_smul, smul_add]

def Jet.baseHom : Jet R M →ₗ⁅R⁆ M where
  toFun := Jet.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {_ _} := rfl

variable {α : Type*}
local notation "F" => FreeLieAlgebra R α

variable [DecidableEq α]

end FreeDerivations

theorem map_eval {M N : Type*} [LieRing M] [LieAlgebra ℝ M]
    [LieRing N] [LieAlgebra ℝ N] (f : M →ₗ⁅ℝ⁆ N) (a b : M) (p : L) :
    f (eval a b p) = eval (f a) (f b) p := by
  have h : f.comp (eval a b) = eval (f a) (f b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [eval]
  exact LieHom.congr_fun h p

theorem eval_commutes {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b z : M) (ha : ⁅z,a⁆ = 0) (hb : ⁅z,b⁆ = 0) (p : L) :
    ⁅z,eval a b p⁆ = 0 := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval, ha, hb]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [LieHom.map_lie, leibniz_lie, hp, hq]

theorem t_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ⁅t i j,t k l⁆ = 0 := by
  rw [t, t, ← LieSubmodule.Quotient.mk_bracket, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inl ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩)

theorem t_three (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅t i j,t i k + t j k⁆ = 0 := by
  change LieSubmodule.Quotient.mk (⁅chord i j, chord i k + chord j k⁆) = (0 : T4)
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)

theorem commute_symm {M : Type*} [LieRing M] {a b : M} (h : ⁅a,b⁆ = 0) : ⁅b,a⁆ = 0 := by
  rw [← lie_skew, h, neg_zero]

theorem evals_commute {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p q : L) :
    ⁅eval a b p,eval c d q⁆ = 0 := by
  apply eval_commutes
  · exact commute_symm (eval_commutes a b c (commute_symm hac) (commute_symm hbc) p)
  · exact commute_symm (eval_commutes a b d (commute_symm had) (commute_symm hbd) p)

theorem eval_add_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p : L) :
    eval (a+c) (b+d) p = eval a b p + eval c d p := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]; abel
  | hs r p hp => simp [hp,smul_add]
  | hl p q hp hq =>
    simp only [LieHom.map_lie, hp, hq, add_lie, lie_add]
    rw [evals_commute a b c d hac had hbc hbd p q,
      commute_symm (evals_commute a b c d hac had hbc hbd q p)]
    simp

theorem eval_vanish_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b : M) (hab : ⁅a,b⁆ = 0) {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a b p = 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    cases hp with
    | generator i => omega
    | @bracket n m p q hp hq =>
      rw [LieHom.map_lie]
      exact evals_commute a b a b (lie_self a) hab (commute_symm hab) (lie_self b) p q
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul r p _ hp => simp [hp]

theorem eval_central_shift {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b c : M) (hac : ⁅a,c⁆ = 0) (hbc : ⁅b,c⁆ = 0)
    {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a (b+c) p = eval a b p := by
  have h := eval_add_of_commuting a b 0 c (lie_zero a) hac (lie_zero b) hbc p
  simpa [eval_vanish_of_commuting 0 c (zero_lie c) hp hn] using h

namespace T4Universal
variable {M : Type*} [LieRing M] [LieAlgebra ℝ M]

def pre (f : Fin 4 → Fin 4 → M) : BraidFree →ₗ⁅ℝ⁆ M :=
  FreeLieAlgebra.lift ℝ (fun e => f e.val.1 e.val.2)

theorem pre_chord (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0) (i j : Fin 4) :
    pre f (chord i j) = f i j := by
  unfold chord
  split_ifs with hij hji
  · simp [pre]
  · simp [pre, hs j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp [hz]

def lift (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0)
    (hd : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      ⁅f i j,f k l⁆ = 0)
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ⁅f i j,f i k+f j k⁆ = 0) : T4 →ₗ⁅ℝ⁆ M := by
  have hker : braidIdeal ≤ (pre f).ker := by
    rw [braidIdeal, LieSubmodule.lieSpan_le]
    intro z hz'
    change pre f z = 0
    rcases hz' with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [LieHom.map_lie, pre_chord f hs hz] using hd i j k l hij hik hil hjk hjl hkl
    · simpa only [LieHom.map_lie, map_add, pre_chord f hs hz] using ht i j k hij hik hjk
  exact { braidIdeal.toSubmodule.liftQ (pre f).toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact (pre f).map_lie a b }

@[simp] theorem lift_t (f : Fin 4 → Fin 4 → M) (hs hz hd ht) (i j : Fin 4) :
    lift f hs hz hd ht (t i j) = f i j := pre_chord f hs hz i j

end T4Universal

def t4Rename (e : Equiv.Perm (Fin 4)) : T4 →ₗ⁅ℝ⁆ T4 :=
  T4Universal.lift (fun i j => t (e i) (e j))
    (fun _ _ => t_comm _ _) (fun _ => t_self _)
    (fun _ _ _ _ hij hik hil hjk hjl hkl => t_disjoint _ _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hil)
      (e.injective.ne hjk) (e.injective.ne hjl) (e.injective.ne hkl))
    (fun _ _ _ hij hik hjk => t_three _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))

@[simp] theorem t4Rename_t (e : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    t4Rename e (t i j) = t (e i) (e j) := T4Universal.lift_t _ _ _ _ _ _ _

theorem solution_swap {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) :
    eval a b p = - eval b a p := by
  have h := congrArg (eval a b) hp.1
  simp only [map_add, map_zero, map_eval, eval_x, eval_y] at h
  exact eq_neg_of_add_eq_zero_left h

theorem solution_three {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) :
    eval a b p + eval b (-a-b) p + eval (-a-b) a p = 0 := by
  have h := congrArg (eval a b) hp.2.1
  simpa only [map_add, map_zero, map_eval, map_sub, map_neg, eval_x, eval_y] using h

namespace Differentiation
open FreeDerivations

variable {M N : Type} [LieRing M] [LieAlgebra ℝ M] [LieRing N] [LieAlgebra ℝ N]

@[simp] theorem Jet.base_neg (p : Jet ℝ M) : (-p).base = -p.base := rfl
@[simp] theorem Jet.velocity_neg (p : Jet ℝ M) : (-p).velocity = -p.velocity := rfl
@[simp] theorem Jet.base_sub (p q : Jet ℝ M) : (p-q).base = p.base-q.base := rfl
@[simp] theorem Jet.velocity_sub (p q : Jet ℝ M) : (p-q).velocity = p.velocity-q.velocity := rfl

@[simp] theorem Jet.mk_add (a b da db : M) :
    (Jet.mk a da : Jet ℝ M) + Jet.mk b db = Jet.mk (a+b) (da+db) := rfl
@[simp] theorem Jet.mk_neg (a da : M) :
    -(Jet.mk a da : Jet ℝ M) = Jet.mk (-a) (-da) := rfl
@[simp] theorem Jet.mk_sub (a b da db : M) :
    (Jet.mk a da : Jet ℝ M) - Jet.mk b db = Jet.mk (a-b) (da-db) := rfl

@[simp] theorem eval_base (a b : Jet ℝ M) (p : L) :
    (eval a b p).base = eval a.base b.base p := map_eval Jet.baseHom a b p

end Differentiation
end RealDeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.WeightBridge
open DeligneDrinfeld.LieGrading DeligneDrinfeld.UniversalEmbedding
variable {α : Type*}

 theorem bracket_mem {wt : α → ℕ} {n m : ℕ} {a b : FreeLieAlgebra ℝ α}
    (ha : a∈weightPiece wt n) (hb : b∈weightPiece wt m) : ⁅a,b⁆∈weightPiece wt (n+m) := by
  apply Submodule.span_induction (p:=fun a _ => ⁅a,b⁆∈weightPiece wt (n+m)) ?_ ?_ ?_ ?_ ha
  · intro a ha
    apply Submodule.span_induction (p:=fun b _ => ⁅a,b⁆∈weightPiece wt (n+m)) ?_ ?_ ?_ ?_ hb
    · intro b hb; exact Submodule.subset_span (WeightedWord.bracket ha hb)
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
    · intro s b _ hb; rw [lie_smul]; exact Submodule.smul_mem _ s hb
  · rw [zero_lie]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_lie]; exact Submodule.add_mem _ ha hb
  · intro s a _ ha; rw [smul_lie]; exact Submodule.smul_mem _ s ha

 theorem map_mem {β : Type*} (f : FreeLieAlgebra ℝ α →ₗ⁅ℝ⁆ FreeLieAlgebra ℝ β)
    (wa : α → ℕ) (wb : β → ℕ) (hf : ∀ a,f (FreeLieAlgebra.of ℝ a)∈weightPiece wb (wa a))
    {n : ℕ} {p : FreeLieAlgebra ℝ α} (hp : p∈weightPiece wa n) : f p∈weightPiece wb n := by
  have hw : ∀ n p,WeightedWord wa n p → f p∈weightPiece wb n := by
    intro n p hp
    induction hp with
    | generator a => exact hf a
    | bracket hp hq ihp ihq => rw [LieHom.map_lie]; exact bracket_mem ihp ihq
  apply Submodule.span_induction (p:=fun p _ => f p∈weightPiece wb n) ?_ ?_ ?_ ?_ hp
  · intro p hp; exact hw n p hp
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro p q _ _ hp hq; rw [map_add]; exact Submodule.add_mem _ hp hq
  · intro s p _ hp; rw [map_smul]; exact Submodule.smul_mem _ s hp

 theorem eval_mem {n : ℕ} {p : L} (hp : p∈Ln n) {a b : L} (ha : a∈Ln 1) (hb : b∈Ln 1) :
    eval a b p∈Ln n := by
  apply map_mem (eval a b) (fun _ => 1) (fun _ => 1) (fun i => ?_) hp
  cases i <;> simpa [eval] using (by assumption : _∈Ln 1)

 theorem x_mem : x∈Ln 1 := Submodule.subset_span (WeightedWord.generator _)

end RealDeligneDrinfeld.WeightBridge

namespace DeligneDrinfeld
end DeligneDrinfeld

namespace DeligneDrinfeld
end DeligneDrinfeld

end

end OAI

end


section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
end DeligneDrinfeld

namespace DeligneDrinfeld.CutoffCategory
open AssociativeElimination WordGrading TruncatedWords
variable {R α B O O' : Type*} [CommRing R] [Ring B] [Algebra R B]
variable (P : Set (A R α)) (N : ℕ)
variable (g : CategoryExp.Data R (TruncatedWords.Q P N) O) (k : CategoryExp.Data R B O')
  (f : TruncatedWords.Q P N →ₐ[R] B) (p : O) (s : O')

 theorem loop_natural (hgen : ∀ a,k.D s s (f (TruncatedDerivation.gen P N a))=
      f (g.D p p (TruncatedDerivation.gen P N a))) (u : TruncatedWords.Q P N) :
    k.D s s (f u)=f (g.D p p u) := by
  have hword (w : FreeMonoid α) :
      k.D s s (f (quotient P N (word w)))=f (g.D p p (quotient P N (word w))) := by
    induction w using FreeMonoid.inductionOn' with
    | one => rw [word_one,map_one,map_one,g.one,k.one,map_zero]
    | of_mul a w ih =>
      rw [word_mul,word_of,map_mul,map_mul,k.comp,g.comp,map_add,map_mul,map_mul,ih]
      rw [show quotient P N (atom a)=TruncatedDerivation.gen P N a from rfl,hgen]
  obtain ⟨u,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations P N) u
  induction u using MonoidAlgebra.induction_on with
  | of w => exact hword w
  | add u v hu hv => simp only [map_add,hu,hv]
  | smul r u hu => simp only [map_smul,hu]

 theorem edge_natural (q : O) (t : O')
    (hunit : k.D s t 1=f (g.D p q 1))
    (hgen : ∀ a,k.D s s (f (TruncatedDerivation.gen P N a))=
      f (g.D p p (TruncatedDerivation.gen P N a))) (u : TruncatedWords.Q P N) :
    k.D s t (f u)=f (g.D p q u) := by
  have hg := g.comp p p q u 1
  have hk := k.comp s s t (f u) 1
  simp only [one_mul] at hg hk
  rw [hg,hk,map_add,map_mul,hunit,loop_natural P N g k f p s hgen]

end DeligneDrinfeld.CutoffCategory

namespace DeligneDrinfeld.PresentedCutoff
open AssociativeElimination WordGrading TruncatedWords
variable {R α M : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]
attribute [local instance] LieRing.ofAssociativeRing
variable (P : Set (A R α)) (N : ℕ)
local notation "Q" => TruncatedWords.Q P N

 theorem raw_embed (d : LieDerivation R M M) (e : FreeLieAlgebra R α →ₗ⁅R⁆ M)
    (j : M →ₗ⁅R⁆ Q) (hj : ∀ a,j (e (FreeLieAlgebra.of R a))=TruncatedDerivation.gen P N a)
    (p : FreeLieAlgebra R α) :
    TruncatedDerivation.raw P N (fun a => j (d (e (FreeLieAlgebra.of R a)))) (embed p)=j (d (e p)) := by
  have he : (quotient P N).toLieHom.comp embed=j.comp e := by
    apply FreeLieAlgebra.hom_ext
    intro a
    change quotient P N (embed (FreeLieAlgebra.of R a))=j (e (FreeLieAlgebra.of R a))
    rw [embed_of,hj]; rfl
  have he' (p : FreeLieAlgebra R α) : quotient P N (embed p)=j (e p) := LieHom.congr_fun he p
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => rw [embed_of,TruncatedDerivation.raw_atom]
  | ha a b ha hb => simp only [map_add,ha,hb]
  | hs r a ha => simp only [map_smul,ha]
  | hl a b ha hb =>
    simp only [LieHom.map_lie,LieDerivation.apply_lie_eq_add,map_add]
    change TruncatedDerivation.raw P N _ (embed a*embed b-embed b*embed a)=_
    rw [map_sub,TruncatedDerivation.raw_mul,TruncatedDerivation.raw_mul,ha,hb,he',he']
    simp only [Ring.lie_def]
    noncomm_ring

 theorem derivation_embed (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈filtration P N (k+1))
    (hP : ∀ p∈P,TruncatedDerivation.raw P N v p=0)
    (d : LieDerivation R M M) (e : FreeLieAlgebra R α →ₗ⁅R⁆ M)
    (j : M →ₗ⁅R⁆ Q) (hj : ∀ a,j (e (FreeLieAlgebra.of R a))=TruncatedDerivation.gen P N a)
    (hv' : ∀ a,v a=j (d (e (FreeLieAlgebra.of R a)))) (p : FreeLieAlgebra R α) :
    TruncatedDerivation.derivation P N k v hv hP (quotient P N (embed p))=j (d (e p)) := by
  rw [TruncatedDerivation.derivation_quotient]
  have he : v=(fun a => j (d (e (FreeLieAlgebra.of R a)))) := funext hv'
  rw [he]
  exact raw_embed P N d e j hj p

end DeligneDrinfeld.PresentedCutoff

end

end OAI

end

section

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.BraidSix
variable {M : Type*} [LieRing M]

def matrix (a b c d e f : M) : Fin 4 → Fin 4 → M :=
  ![![0,a,d,f],![a,0,b,e],![d,b,0,c],![f,e,c,0]]

structure Relations (a b c d e f : M) : Prop where
  central : ∀ u∈({a,b,c,d,e,f}:Set M),⁅u,total a b c d e f⁆=0
  ac : ⁅a,c⁆=0
  de : ⁅d,e⁆=0
  aK : ⁅a,a+b+d⁆=0
  bK : ⁅b,a+b+d⁆=0
  bL : ⁅b,b+c+e⁆=0
  cL : ⁅c,b+c+e⁆=0

variable {a b c d e f : M}

theorem bf (h : Relations a b c d e f) : ⁅b,f⁆=0 := by
  calc
    _=⁅b,total a b c d e f⁆-⁅b,a+b+d⁆-⁅b,b+c+e⁆ := by
      simp only [total,lie_add,lie_self]
      abel
    _=0 := by rw [h.central b (by simp),h.bK,h.bL]; abel

theorem dK (h : Relations a b c d e f) : ⁅d,a+b+d⁆=0 := by
  have hh := lie_self (a+b+d)
  rw [add_lie,add_lie,h.aK,h.bK] at hh
  simpa only [zero_add] using hh

theorem eL (h : Relations a b c d e f) : ⁅e,b+c+e⁆=0 := by
  have hh := lie_self (b+c+e)
  rw [add_lie,add_lie,h.bL,h.cL] at hh
  simpa only [zero_add] using hh

theorem aM (h : Relations a b c d e f) : ⁅a,a+e+f⁆=0 := by
  calc
    _=⁅a,total a b c d e f⁆-⁅a,a+b+d⁆-⁅a,c⁆ := by
      simp only [total,lie_add,lie_self]; abel
    _=0 := by rw [h.central a (by simp),h.aK,h.ac]; abel

theorem eM (h : Relations a b c d e f) : ⁅e,a+e+f⁆=0 := by
  calc
    _=⁅e,total a b c d e f⁆-⁅e,b+c+e⁆+⁅d,e⁆ := by
      simp only [total,lie_add,lie_self]
      rw [←lie_skew d e]
      abel
    _=0 := by rw [h.central e (by simp),eL h,h.de]; abel

theorem fM (h : Relations a b c d e f) : ⁅f,a+e+f⁆=0 := by
  have hh := lie_self (a+e+f)
  rw [add_lie,add_lie,aM h,eM h] at hh
  simpa only [zero_add] using hh

theorem dP (h : Relations a b c d e f) : ⁅d,d+c+f⁆=0 := by
  calc
    _=⁅d,total a b c d e f⁆-⁅d,a+b+d⁆-⁅d,e⁆ := by
      simp only [total,lie_add,lie_self]; abel
    _=0 := by rw [h.central d (by simp),dK h,h.de]; abel

theorem cP (h : Relations a b c d e f) : ⁅c,d+c+f⁆=0 := by
  calc
    _=⁅c,total a b c d e f⁆-⁅c,b+c+e⁆+⁅a,c⁆ := by
      simp only [total,lie_add,lie_self]
      rw [←lie_skew a c]
      abel
    _=0 := by rw [h.central c (by simp),h.cL,h.ac]; abel

theorem fP (h : Relations a b c d e f) : ⁅f,d+c+f⁆=0 := by
  have hh := lie_self (d+c+f)
  rw [add_lie,add_lie,dP h,cP h] at hh
  simpa only [zero_add] using hh

theorem matrix_self (i : Fin 4) : matrix a b c d e f i i=0 := by
  fin_cases i <;> rfl

theorem matrix_symm (i j : Fin 4) : matrix a b c d e f i j=matrix a b c d e f j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem matrix_disjoint_0 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (0:Fin 4)≠k) (hil : (0:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 0 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint_1 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (1:Fin 4)≠k) (hil : (1:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 1 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint_2 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (2:Fin 4)≠k) (hil : (2:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 2 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint_3 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (3:Fin 4)≠k) (hil : (3:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 3 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint (h : Relations a b c d e f) (i j k l : Fin 4)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f i j,matrix a b c d e f k l⁆=0 := by
  fin_cases i
  · exact matrix_disjoint_0 h j k l hik hil hjk hjl
  · exact matrix_disjoint_1 h j k l hik hil hjk hjl
  · exact matrix_disjoint_2 h j k l hik hil hjk hjl
  · exact matrix_disjoint_3 h j k l hik hil hjk hjl

theorem matrix_three_0 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (0:Fin 4)≠j) (hik : (0:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 0 j,matrix a b c d e f 0 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three_1 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (1:Fin 4)≠j) (hik : (1:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 1 j,matrix a b c d e f 1 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three_2 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (2:Fin 4)≠j) (hik : (2:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 2 j,matrix a b c d e f 2 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three_3 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (3:Fin 4)≠j) (hik : (3:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 3 j,matrix a b c d e f 3 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three (h : Relations a b c d e f) (i j k : Fin 4)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f i j,matrix a b c d e f i k+matrix a b c d e f j k⁆=0 := by
  fin_cases i
  · exact matrix_three_0 h j k hij hik hjk
  · exact matrix_three_1 h j k hij hik hjk
  · exact matrix_three_2 h j k hij hik hjk
  · exact matrix_three_3 h j k hij hik hjk

end RealDeligneDrinfeld.BraidSix

namespace RealDeligneDrinfeld.T4Basic
open BraidSix

def f : T4 := t 0 3

 theorem induction {P : T4 → Prop} (hz : P 0) (ht : ∀ i j,P (t i j))
    (ha : ∀ p q,P p → P q → P (p+q)) (hs : ∀ (r : ℝ) p,P p → P (r • p))
    (hl : ∀ p q,P p → P q → P ⁅p,q⁆) (p : T4) : P p := by
  induction p using Submodule.Quotient.induction_on with | _ p =>
    induction p using freeLie_induction with
    | h0 => exact hz
    | hg ij =>
      have hh : (FreeLieAlgebra.of ℝ ij : BraidFree)=chord ij.val.1 ij.val.2 := by
        simp only [chord,dif_pos ij.property]
      rw [hh]
      exact ht _ _
    | ha p q hp hq => exact ha _ _ hp hq
    | hs r p hp => exact hs r _ hp
    | hl p q hp hq => exact hl _ _ hp hq

 theorem hom_ext {M : Type*} [LieRing M] [LieAlgebra ℝ M] {F G : T4 →ₗ⁅ℝ⁆ M}
    (h : ∀ i j,F (t i j)=G (t i j)) : F=G := by
  apply LieHom.ext
  intro p
  induction p using induction with
  | hz => simp
  | ht i j => exact h i j
  | ha p q hp hq => simp only [map_add,hp,hq]
  | hs r p hp => simp only [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]

 theorem matrix_t (i j : Fin 4) : matrix a b c d e f i j=t i j := by
  fin_cases i <;> fin_cases j <;> rfl

 theorem central_a : ⁅a,total a b c d e f⁆=0 := by
  have h₁ := t_three 0 1 2 (by decide) (by decide) (by decide)
  have h₂ := t_three 0 1 3 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 0 1,t 0 2+t 1 2⁆+⁅t 0 1,t 0 3+t 1 3⁆+⁅t 0 1,t 2 3⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_b : ⁅b,total a b c d e f⁆=0 := by
  have h₁ := t_three 1 2 0 (by decide) (by decide) (by decide)
  have h₂ := t_three 1 2 3 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 1 2,t 1 0+t 2 0⁆+⁅t 1 2,t 1 3+t 2 3⁆+⁅t 1 2,t 0 3⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 1 0,t_comm 2 0]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_c : ⁅c,total a b c d e f⁆=0 := by
  have h₁ := t_three 2 3 0 (by decide) (by decide) (by decide)
  have h₂ := t_three 2 3 1 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 2 3,t 2 0+t 3 0⁆+⁅t 2 3,t 2 1+t 3 1⁆+⁅t 2 3,t 0 1⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 2 0,t_comm 2 1,t_comm 3 0,t_comm 3 1]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_d : ⁅d,total a b c d e f⁆=0 := by
  have h₁ := t_three 0 2 1 (by decide) (by decide) (by decide)
  have h₂ := t_three 0 2 3 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 0 2,t 0 1+t 2 1⁆+⁅t 0 2,t 0 3+t 2 3⁆+⁅t 0 2,t 1 3⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 2 1]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_e : ⁅e,total a b c d e f⁆=0 := by
  have h₁ := t_three 1 3 0 (by decide) (by decide) (by decide)
  have h₂ := t_three 1 3 2 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 1 3,t 1 0+t 3 0⁆+⁅t 1 3,t 1 2+t 3 2⁆+⁅t 1 3,t 0 2⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 1 0,t_comm 3 0,t_comm 3 2]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_f : ⁅f,total a b c d e f⁆=0 := by
  have h₁ := t_three 0 3 1 (by decide) (by decide) (by decide)
  have h₂ := t_three 0 3 2 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 0 3,t 0 1+t 3 1⁆+⁅t 0 3,t 0 2+t 3 2⁆+⁅t 0 3,t 1 2⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 3 1,t_comm 3 2]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central (p : T4) : ⁅total a b c d e f,p⁆=0 := by
  induction p using induction with
  | hz => exact lie_zero _
  | ht i j =>
    rw [←matrix_t i j]
    have ha := commute_symm central_a
    have hb := commute_symm central_b
    have hc := commute_symm central_c
    have hd := commute_symm central_d
    have he := commute_symm central_e
    have hf := commute_symm central_f
    fin_cases i <;> fin_cases j <;> simp_all [matrix]
  | ha p q hp hq => rw [lie_add,hp,hq,add_zero]
  | hs r p hp => rw [lie_smul,hp,smul_zero]
  | hl p q hp hq => rw [leibniz_lie,hp,hq,zero_lie,lie_zero,add_zero]

 theorem relations : Relations a b c d e f := by
  constructor
  · intro u _; exact commute_symm (central u)
  · exact t_disjoint 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact t_disjoint 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have h := t_three 0 1 2 (by decide) (by decide) (by decide)
    change ⁅t 0 1,t 0 1+t 1 2+t 0 2⁆=0
    simp only [lie_add,lie_self] at h ⊢
    rw [add_comm] at h
    simpa only [zero_add] using h
  · have h := t_three 1 2 0 (by decide) (by decide) (by decide)
    simpa only [a,b,d,lie_add,lie_self,add_zero,t_comm 1 0,t_comm 2 0] using h
  · have h := t_three 1 2 3 (by decide) (by decide) (by decide)
    change ⁅t 1 2,t 1 2+t 2 3+t 1 3⁆=0
    simp only [lie_add,lie_self] at h ⊢
    rw [add_comm] at h
    simpa only [zero_add] using h
  · have h := t_three 2 3 1 (by decide) (by decide) (by decide)
    simpa only [b,c,e,lie_add,lie_self,add_zero,t_comm 2 1,t_comm 3 1] using h

end RealDeligneDrinfeld.T4Basic

namespace RealDeligneDrinfeld.TangentBraid
open FreeDerivations BraidSix
variable {R M : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]

structure Data (a b c d e f A B C D E H I J P Q : M) : Prop where
  base : BraidSix.Relations a b c d e f
  central : ∀ u : M,⁅total a b c d e f,u⁆=0
  aD : ⁅a,D⁆=0
  bB : ⁅b,B⁆=0
  cE : ⁅c,E⁆=0
  KA : ⁅a+b+d,A⁆=0
  LC : ⁅b+c+e,C⁆=0
  special_d : ⁅b,A⁆+⁅d,A+H⁆=0
  special_e : ⁅c,C⁆+⁅e,C+I⁆=0
  cyclic : C+I=J
  pentagon : D+E=A+B+C
  permuted : P+Q= -H+B+J
  dP : ⁅d,P⁆=0
  eQ : ⁅e,Q⁆=0

variable {a b c d e f A B C D E H I J P Q : M}

 theorem crossing {a b h k p q : M} (hab : ⁅a,b⁆=0)
    (hk : k-h=p+q) (hap : ⁅a,p⁆=0) (hbq : ⁅b,q⁆=0) :
    ⁅⁅a,h⁆,b⁆+⁅a,⁅b,k⁆⁆=0 := by
  calc
    _=⁅a,⁅b,k-h⁆⁆ := by
      rw [lie_sub,lie_sub,leibniz_lie a b h,hab,zero_lie,zero_add,←lie_skew b ⁅a,h⁆]
      abel
    _=0 := by
      rw [hk,lie_add,lie_add,hbq,lie_zero,add_zero,leibniz_lie,hab,hap,zero_lie,lie_zero,add_zero]

 theorem inner_pair {a b h : M} (hab : ⁅a,b⁆=0) :
    ⁅⁅a,h⁆,b⁆+⁅a,⁅b,h⁆⁆=0 := by
  rw [leibniz_lie a b h,hab,zero_lie,zero_add,←lie_skew b ⁅a,h⁆]
  abel

 theorem commute_lie {a b h : M} (ha : ⁅a,h⁆=0) (hb : ⁅b,h⁆=0) : ⁅⁅a,b⁆,h⁆=0 := by
  rw [lie_lie,ha,hb,lie_zero,lie_zero,sub_self]

 def vb (b A : M) : M := ⁅b,A⁆
 def vc (c D : M) : M := ⁅c,D⁆
 def vd (b A : M) : M := -⁅b,A⁆
 def ve (b e A D E : M) : M := ⁅b+e,D+E⁆-⁅b,A⁆
 def vf (b c e A D E : M) : M := -vc c D-ve b e A D E

 theorem vd_tangent (h : Data a b c d e f A B C D E H I J P Q) : vd b A=⁅d,A+H⁆ := by
  exact neg_eq_of_add_eq_zero_right h.special_d

 theorem bC (h : Data a b c d e f A B C D E H I J P Q) : ⁅b,C⁆=⁅e,I⁆ := by
  apply sub_eq_zero.mp
  calc
    _=⁅b+c+e,C⁆-(⁅c,C⁆+⁅e,C+I⁆) := by simp only [add_lie,lie_add]; abel
    _=0 := by rw [h.LC,h.special_e,sub_self]

 theorem ve_tangent (h : Data a b c d e f A B C D E H I J P Q) :
    ve b e A D E=⁅e,A+B+C+I⁆ := by
  rw [ve,h.pentagon]
  simp only [add_lie,lie_add]
  rw [h.bB,bC h]
  abel

 theorem gauge_difference (h : Data a b c d e f A B C D E H I J P Q) :
    (A+B+C+I)-(A+H)=P+Q := by
  rw [h.permuted,←h.cyclic]
  abel

 theorem crossing_de (h : Data a b c d e f A B C D E H I J P Q) :
    ⁅vd b A,e⁆+⁅d,ve b e A D E⁆=0 := by
  rw [vd_tangent h,ve_tangent h]
  exact crossing h.base.de (gauge_difference h) h.dP h.eQ

 theorem velocity_K : (0:M)+vb b A+vd b A=0 := by simp only [vb,vd,zero_add,add_neg_cancel]
 theorem velocity_L (h : Data a b c d e f A B C D E H I J P Q) :
    vb b A+vc c D+ve b e A D E=⁅b+c+e,A+B⁆ := by
  calc
    _=⁅b+c+e,D+E⁆ := by simp only [vb,vc,ve,add_lie,lie_add,h.cE]; abel
    _=⁅b+c+e,A+B⁆ := by rw [h.pentagon,lie_add,h.LC,add_zero]

 theorem velocity_b (h : Data a b c d e f A B C D E H I J P Q) :
    vb b A=⁅b,A+B⁆ := by simp only [vb,lie_add,h.bB,add_zero]
 theorem velocity_c (h : Data a b c d e f A B C D E H I J P Q) :
    vc c D=⁅c,A+B⁆+⁅c,C⁆ := by
  have hh := congrArg (fun u => ⁅c,u⁆) h.pentagon
  simpa only [vc,lie_add,h.cE,add_zero] using hh

 theorem velocity_total :
    total (0:M) (vb b A) (vc c D) (vd b A) (ve b e A D E) (vf b c e A D E)=0 := by
  simp only [total,vb,vc,vd,vf]
  abel

 def ja (a : M) : Jet R M := ⟨a,0⟩
 def jb (b A : M) : Jet R M := ⟨b,vb b A⟩
 def jc (c D : M) : Jet R M := ⟨c,vc c D⟩
 def jd (d b A : M) : Jet R M := ⟨d,vd b A⟩
 def je (e b A D E : M) : Jet R M := ⟨e,ve b e A D E⟩
 def jf (f b c e A D E : M) : Jet R M := ⟨f,vf b c e A D E⟩

 theorem relations (h : Data a b c d e f A B C D E H I J P Q) :
    BraidSix.Relations (ja (R:=R) a) (jb b A) (jc c D) (jd d b A)
      (je e b A D E) (jf f b c e A D E) := by
  constructor
  · intro u _
    apply Jet.ext
    · change ⁅u.base,total a b c d e f⁆=0
      exact commute_symm (h.central u.base)
    · change ⁅u.velocity,total a b c d e f⁆+⁅u.base,
        total 0 (vb b A) (vc c D) (vd b A) (ve b e A D E) (vf b c e A D E)⁆=0
      rw [velocity_total,lie_zero,add_zero]
      exact commute_symm (h.central u.velocity)
  · apply Jet.ext
    · exact h.base.ac
    · change ⁅(0:M),c⁆+⁅a,⁅c,D⁆⁆=0
      rw [zero_lie,zero_add,leibniz_lie,h.base.ac,h.aD,zero_lie,lie_zero,add_zero]
  · apply Jet.ext
    · exact h.base.de
    · exact crossing_de h
  · apply Jet.ext
    · exact h.base.aK
    · change ⁅(0:M),a+b+d⁆+⁅a,(0:M)+vb b A+vd b A⁆=0
      rw [velocity_K,zero_lie,lie_zero,add_zero]
  · apply Jet.ext
    · exact h.base.bK
    · change ⁅⁅b,A⁆,a+b+d⁆+⁅b,(0:M)+vb b A+vd b A⁆=0
      rw [velocity_K,lie_zero,add_zero]
      exact commute_lie h.base.bK (commute_symm h.KA)
  · apply Jet.ext
    · exact h.base.bL
    · change ⁅vb b A,b+c+e⁆+⁅b,vb b A+vc c D+ve b e A D E⁆=0
      rw [velocity_L h,velocity_b h]
      exact inner_pair h.base.bL
  · apply Jet.ext
    · exact h.base.cL
    · change ⁅vc c D,b+c+e⁆+⁅c,vb b A+vc c D+ve b e A D E⁆=0
      rw [velocity_L h,velocity_c h,add_lie]
      have hz := commute_lie h.base.cL (commute_symm h.LC)
      rw [hz,add_zero]
      exact inner_pair h.base.cL

end RealDeligneDrinfeld.TangentBraid

namespace RealDeligneDrinfeld.TriangleSolutions
variable {M : Type} [LieRing M] [LieAlgebra ℝ M]
variable {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n)
variable (u v w : M) (hu : ⁅u,u+v+w⁆=0) (hv : ⁅v,u+v+w⁆=0)

omit [LieAlgebra ℝ M] in
include hu hv in
theorem third : ⁅w,u+v+w⁆=0 := by
  have h := lie_self (u+v+w)
  rw [add_lie,add_lie,hu,hv,zero_add,zero_add] at h
  exact h

include hqn hn hu hv in
theorem shift_u : eval u w q=eval u (-u-v) q := by
  have hsum : w=(-u-v)+(u+v+w) := by abel
  have hneg : ⁅-u-v,u+v+w⁆=0 := by rw [sub_lie,neg_lie,hu,hv,neg_zero,sub_zero]
  conv_lhs => rw [hsum]
  exact eval_central_shift u (-u-v) (u+v+w) hu hneg hqn (by omega)

include hqn hn hu hv in
theorem shift_v : eval v w q=eval v (-u-v) q := by
  have hsum : w=(-u-v)+(u+v+w) := by abel
  have hneg : ⁅-u-v,u+v+w⁆=0 := by rw [sub_lie,neg_lie,hu,hv,neg_zero,sub_zero]
  conv_lhs => rw [hsum]
  exact eval_central_shift v (-u-v) (u+v+w) hv hneg hqn (by omega)

include hq hqn hn hu hv in
theorem cyclic : eval u v q+eval v w q=eval u w q := by
  have h := solution_three hq u v
  rw [solution_swap hq (-u-v) u,←shift_u hqn hn u v w hu hv,
    ←shift_v hqn hn u v w hu hv] at h
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)

include hq hqn hn hu hv in
theorem special : ⁅v,eval u v q⁆+⁅w,eval u v q+eval v w q⁆=0 := by
  have h := Differentiation.special_identity hq hqn hn v u
  have hc : -v-u= -u-v := by abel
  rw [hc,←shift_u hqn hn u v w hu hv] at h
  have hk : ⁅u+v+w,eval u w q⁆=0 :=
    eval_commutes u w (u+v+w) (commute_symm hu) (commute_symm (third u v w hu hv)) q
  have he : ⁅-u-v,eval u w q⁆=⁅w,eval u w q⁆ := by
    have hh : -u-v=w-(u+v+w) := by abel
    rw [hh,sub_lie,hk,sub_zero]
  rw [he] at h
  rw [cyclic hq hqn hn u v w hu hv]
  exact h

end RealDeligneDrinfeld.TriangleSolutions

namespace RealDeligneDrinfeld.T4SolutionData
open T4Basic

def B (q : L) : T4 := eval (a+d) (e+c) q
def C (q : L) : T4 := eval b c q
def D (q : L) : T4 := eval (d+b) c q
def E (q : L) : T4 := eval a (b+e) q
def H (q : L) : T4 := eval b d q
def I (q : L) : T4 := eval c e q
def J (q : L) : T4 := eval b e q
def P (q : L) : T4 := eval (a+b) e q
def Q (q : L) : T4 := eval d (b+c) q

 theorem pentagon {q : L} (hq : q∈W) : D q+E q=A q+B q+C q := by
  calc
    _=E q+D q := add_comm _ _
    _=C q+B q+A q := hq.2.2
    _=_ := by abel

 theorem permuted {q : L} (hq : q∈W) : P q+Q q= -H q+B q+J q := by
  have hh := congrArg (t4Rename (Equiv.swap (1:Fin 4) 2)) hq.2.2
  simp only [map_add,map_eval,t4Rename_t] at hh
  change eval d (b+c) q+eval (a+b) e q=eval b e q+eval (d+a) (c+e) q+eval d b q at hh
  rw [add_comm d a,add_comm c e,solution_swap hq d b] at hh
  calc
    _=Q q+P q := add_comm _ _
    _=J q+B q+(-H q) := hh
    _=_ := by abel

 theorem data {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    TangentBraid.Data a b c d e f (A q) (B q) (C q) (D q) (E q)
      (H q) (I q) (J q) (P q) (Q q) := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using relations.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using relations.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using BraidSix.dK relations
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using relations.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using relations.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using BraidSix.eL relations
  constructor
  · exact relations
  · exact central
  · exact eval_commutes (d+b) c a (by rwa [add_comm]) relations.ac q
  · exact eval_commutes (a+d) (e+c) b hb (by rwa [add_comm]) q
  · exact eval_commutes a (b+e) c (commute_symm relations.ac) hc q
  · exact eval_commutes a b (a+b+d) (commute_symm relations.aK) (commute_symm relations.bK) q
  · exact eval_commutes b c (b+c+e) (commute_symm relations.bL) (commute_symm relations.cL) q
  · exact TriangleSolutions.special hq hqn hn a b d relations.aK relations.bK
  · exact TriangleSolutions.special hq hqn hn b c e relations.bL relations.cL
  · exact TriangleSolutions.cyclic hq hqn hn b c e relations.bL relations.cL
  · exact pentagon hq
  · exact permuted hq
  · exact eval_commutes (a+b) e d hd relations.de q
  · exact eval_commutes d (b+c) e (commute_symm relations.de) he q

end RealDeligneDrinfeld.T4SolutionData

namespace RealDeligneDrinfeld.T4Derivation
open T4Basic T4SolutionData FreeDerivations TangentBraid
variable {n : ℕ} {q : L}

def jets (q : L) : Fin 4 → Fin 4 → Jet ℝ T4 :=
  BraidSix.matrix (ja a) (jb b (A q)) (jc c (T4SolutionData.D q)) (jd d b (A q))
    (je e b (A q) (T4SolutionData.D q) (E q)) (jf f b c e (A q) (T4SolutionData.D q) (E q))

@[simp] theorem jets_base (q : L) (i j : Fin 4) : (jets q i j).base=t i j := by
  rw [←matrix_t i j]
  fin_cases i <;> fin_cases j <;> rfl

def lift (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : T4 →ₗ⁅ℝ⁆ Jet ℝ T4 :=
  T4Universal.lift (jets q) BraidSix.matrix_symm BraidSix.matrix_self
    (fun i j k l _ hik hil hjk hjl _ =>
      BraidSix.matrix_disjoint (TangentBraid.relations (data hq hqn hn)) i j k l hik hil hjk hjl)
    (BraidSix.matrix_three (TangentBraid.relations (data hq hqn hn)))

@[simp] theorem lift_t (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (i j : Fin 4) :
    lift hq hqn hn (t i j)=jets q i j := T4Universal.lift_t _ _ _ _ _ _ _

@[simp] theorem lift_base (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p : T4) :
    (lift hq hqn hn p).base=p := by
  have he : Jet.baseHom.comp (lift hq hqn hn)=LieHom.id := by
    apply T4Basic.hom_ext
    intro i j
    change (lift hq hqn hn (t i j)).base=t i j
    rw [lift_t,jets_base]
  exact LieHom.congr_fun he p

def derivation (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : LieDerivation ℝ T4 T4 where
  toFun p := (lift hq hqn hn p).velocity
  map_add' p r := by change (lift hq hqn hn (p+r)).velocity=_; rw [map_add]; rfl
  map_smul' s p := by change (lift hq hqn hn (s • p)).velocity=_; rw [map_smul]; rfl
  leibniz' p r := by
    change (lift hq hqn hn ⁅p,r⁆).velocity=⁅p,(lift hq hqn hn r).velocity⁆-⁅r,(lift hq hqn hn p).velocity⁆
    rw [LieHom.map_lie,Jet.velocity_lie,lift_base,lift_base,sub_eq_add_neg,lie_skew,add_comm]

@[simp] theorem derivation_t (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (i j : Fin 4) :
    derivation hq hqn hn (t i j)=(jets q i j).velocity := by
  change (lift hq hqn hn (t i j)).velocity=_
  rw [lift_t]

@[simp] theorem derivation_a (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn a=0 := by
  exact derivation_t hq hqn hn 0 1
@[simp] theorem derivation_b (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn b=⁅b,A q⁆ := by
  exact derivation_t hq hqn hn 1 2
@[simp] theorem derivation_c (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn c=⁅c,T4SolutionData.D q⁆ := by
  exact derivation_t hq hqn hn 2 3
@[simp] theorem derivation_d (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn d= -⁅b,A q⁆ := by
  exact derivation_t hq hqn hn 0 2
@[simp] theorem derivation_e (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    derivation hq hqn hn e=⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆ := by
  exact derivation_t hq hqn hn 1 3
@[simp] theorem derivation_f (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    derivation hq hqn hn f= -⁅c,T4SolutionData.D q⁆-(⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆) := by
  exact derivation_t hq hqn hn 0 3

end RealDeligneDrinfeld.T4Derivation

namespace RealDeligneDrinfeld.GaugeCompatibility
open DeligneDrinfeld.CategoryGauge

 theorem intertwine {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (D : LieDerivation ℝ M M) (q : L) (a b : M)
    (hx : D a=0) (hy : D b=⁅b,eval a b q⁆) (p : L) :
    D (eval a b p)=eval a b (derivation q p) := by
  induction p using freeLie_induction with
  | h0 => simp only [map_zero]
  | hg i =>
    cases i
    · change D (eval a b x)=eval a b (derivation q x)
      simp only [eval_x,derivation_apply,D_x,map_zero,hx]
    · change D (eval a b y)=eval a b (derivation q y)
      simp only [eval_y,derivation_apply,D_y,LieHom.map_lie,hy]
  | ha p r hp hr => simp only [map_add,hp,hr]
  | hs s p hp => simp only [map_smul,hp]
  | hl p r hp hr => simp only [LieHom.map_lie,LieDerivation.apply_lie_eq_add,map_add,hp,hr]

end RealDeligneDrinfeld.GaugeCompatibility

namespace RealDeligneDrinfeld.FourSolutionCategory
open T4Basic T4SolutionData DeligneDrinfeld.CategoryGauge
variable {n : ℕ} {q : L}

def data (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : Data ℝ T4 (Fin 5) :=
  ⟨T4Derivation.derivation hq hqn hn,![0,A q,A q+B q,T4SolutionData.D q,T4SolutionData.D q+E q]⟩

 theorem edge (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (X Y : T4) (s t : Fin 5)
    (hu : unit (data hq hqn hn) s t=eval X Y q)
    (hx : loop (data hq hqn hn) s X=0)
    (hy : loop (data hq hqn hn) s Y=⁅Y,eval X Y q⁆) :
    EdgeCompatible (eval X Y) 0 1 s t (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  constructor
  · rw [ThreeSolutionCategory.value]; exact hu
  · intro p
    rw [ThreeSolutionCategory.loop_zero]
    exact GaugeCompatibility.intertwine _ q X Y hx hy p

 theorem AB (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval a b) 0 1 0 1 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  apply edge hq hqn hn
  · simp [data,unit,A]
  · simp [data,loop_apply]
  · simp [data,loop_apply,A]

 theorem AD (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval (d+b) c) 0 1 0 3 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  apply edge hq hqn hn
  · simp [data,unit,T4SolutionData.D]
  · simp only [data,loop_apply,Matrix.cons_val_zero,zero_lie,add_zero,map_add,
      T4Derivation.derivation_d,T4Derivation.derivation_b,neg_add_cancel]
  · simp [data,loop_apply,T4SolutionData.D]

 theorem DE (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval a (b+e)) 0 1 3 4 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  have hd := T4SolutionData.data hq hqn hn
  apply edge hq hqn hn
  · simp [data,unit,E]
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn a+⁅T4SolutionData.D q,a⁆=0
    rw [T4Derivation.derivation_a,zero_add]
    exact commute_symm hd.aD
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn (b+e)+⁅T4SolutionData.D q,b+e⁆=⁅b+e,E q⁆
    rw [map_add,T4Derivation.derivation_b,T4Derivation.derivation_e,lie_add,←lie_skew (b+e) (T4SolutionData.D q)]
    abel

 theorem BC (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval (a+d) (e+c)) 0 1 1 2 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  have hd := T4SolutionData.data hq hqn hn
  apply edge hq hqn hn
  · simp [data,unit,B]
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn (a+d)+⁅A q,a+d⁆=0
    rw [map_add,T4Derivation.derivation_a,T4Derivation.derivation_d,zero_add]
    calc
      _= -⁅a+b+d,A q⁆ := by simp only [add_lie,lie_add]; rw [←lie_skew a (A q),←lie_skew d (A q)]; abel
      _=0 := by rw [hd.KA,neg_zero]
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn (e+c)+⁅A q,e+c⁆=⁅e+c,B q⁆
    rw [map_add,T4Derivation.derivation_e,T4Derivation.derivation_c]
    have hl := TangentBraid.velocity_L hd
    change ⁅b,A q⁆+⁅c,T4SolutionData.D q⁆+(⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆)=⁅b+c+e,A q+B q⁆ at hl
    calc
      _=(⁅b,A q⁆+⁅c,T4SolutionData.D q⁆+(⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆))-⁅b,A q⁆+⁅A q,e+c⁆ := by abel
      _=⁅b+c+e,A q+B q⁆-⁅b,A q⁆+⁅A q,e+c⁆ := by rw [hl]
      _=⁅e+c,B q⁆ := by
        simp only [add_lie,lie_add]
        rw [hd.bB,←lie_skew e (A q),←lie_skew c (A q)]
        abel

 theorem CE (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval b c) 0 1 2 4 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  have hd := T4SolutionData.data hq hqn hn
  apply edge hq hqn hn
  · change (T4SolutionData.D q+E q)-(A q+B q)=C q
    rw [pentagon hq]
    abel
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn b+⁅A q+B q,b⁆=0
    rw [T4Derivation.derivation_b,add_lie,←lie_skew b (A q),commute_symm hd.bB]
    abel
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn c+⁅A q+B q,c⁆=⁅c,C q⁆
    rw [T4Derivation.derivation_c]
    have hc := TangentBraid.velocity_c hd
    change ⁅c,T4SolutionData.D q⁆=⁅c,A q+B q⁆+⁅c,C q⁆ at hc
    rw [hc,←lie_skew c (A q+B q)]
    abel

end RealDeligneDrinfeld.FourSolutionCategory

end

end OAI

end

section

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.FreeCutoffCategory
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords
attribute [local instance] LieRing.ofAssociativeRing

 theorem d_mem {n m : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) {a : Q N} (ha : a∈F N m) :
    d N hq a∈F N (m+n) := DeligneDrinfeld.TruncatedDerivation.derivation_mem P N n _ _ _ ha
 theorem d_j {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p : L) :
    d N hq (j N p)=j N (RealDeligneDrinfeld.derivation q p) :=
  DeligneDrinfeld.PresentedCutoff.derivation_embed P N n _ _ _ (RealDeligneDrinfeld.derivation q)
    (LieHom.id) (j N) (j_of N) (fun _ => rfl) p

 theorem h_mem {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p : Fin 3) : h N q p∈F N n := by
  have hr : CategoricalValues.rotateLie q∈Ln n :=
    WeightBridge.eval_mem hq WeightBridge.y_mem ((Ln 1).sub_mem ((Ln 1).neg_mem WeightBridge.x_mem) WeightBridge.y_mem)
  unfold h ThreeSolutionCategory.data
  fin_cases p
  · change j N 0∈F N n; rw [map_zero]; exact Submodule.zero_mem _
  · exact j_mem hq
  · exact j_mem ((Ln n).add_mem hq hr)

 theorem loop_j {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p : Fin 3) (a : L) :
    (data N hq).D p p (j N a)=j N (DeligneDrinfeld.CategoryGauge.loop (ThreeSolutionCategory.data q) p a) := by
  change d N hq (j N a)+h N q p*j N a-j N a*h N q p=_
  rw [d_j,DeligneDrinfeld.CategoryGauge.loop_apply,map_add,LieHom.map_lie,Ring.lie_def]
  change _=j N (RealDeligneDrinfeld.derivation q a)+(h N q p*j N a-j N a*h N q p)
  abel
 theorem unit_all {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p s : Fin 3) :
    (data N hq).D p s 1=j N (DeligneDrinfeld.CategoryGauge.unit (ThreeSolutionCategory.data q) p s) := by
  change d N hq 1+h N q s*1-1*h N q p=_
  rw [d_one,zero_add,mul_one,one_mul,DeligneDrinfeld.CategoryGauge.unit,map_sub]
  rfl

 theorem raises {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p s : Fin 3)
    (m : ℕ) (a : Q N) (ha : a∈F N m) : (data N hq).D p s a∈F N (m+n) :=
  DeligneDrinfeld.CutoffCategory.raises P N (d N hq) (d_mul N hq) (d_one N hq) (h N q) n
    (fun _ _ ha => d_mem N hq ha) (h_mem N hq) p s m a ha

end RealDeligneDrinfeld.FreeCutoffCategory

namespace RealDeligneDrinfeld.BraidCutoff
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords
attribute [local instance] LieRing.ofAssociativeRing

 theorem projection_relation {p : BraidFree} (hp : p∈braidRelations) : projection p=0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (LieSubmodule.subset_lieSpan hp)

 theorem lie_mem {N r s : ℕ} {a b : Q N} (ha : a∈F N r) (hb : b∈F N s) : ⁅a,b⁆∈F N (r+s) := by
  exact (F N (r+s)).sub_mem (filtration_mul presentation N r s ha hb)
    (by simpa only [Nat.add_comm s r] using filtration_mul presentation N s r hb ha)

 theorem weight_mem {α : Type*} (N : ℕ) (e : FreeLieAlgebra ℝ α →ₗ⁅ℝ⁆ Q N)
    (he : ∀ a,e (FreeLieAlgebra.of ℝ a)∈F N 1) {n : ℕ} {q : FreeLieAlgebra ℝ α}
    (hq : q∈weightPiece (fun _ : α => 1) n) : e q∈F N n := by
  have hw : ∀ n p,WeightedWord (fun _ : α => 1) n p → e p∈F N n := by
    intro n p hp
    induction hp with
    | generator a => exact he a
    | bracket hp hr ihp ihr => rw [LieHom.map_lie]; exact lie_mem ihp ihr
  apply Submodule.span_induction (p:=fun q _ => e q∈F N n) ?_ ?_ ?_ ?_ hq
  · intro p hp
    exact hw n p hp
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro p r _ _ hp hr; rw [map_add]; exact Submodule.add_mem _ hp hr
  · intro s p _ hp; rw [map_smul]; exact Submodule.smul_mem _ s hp

 theorem eval_mem {N n : ℕ} {q : L} (hq : q∈Ln n) {a b : T4}
    (ha : lieMap N a∈F N 1) (hb : lieMap N b∈F N 1) : lieMap N (eval a b q)∈F N n := by
  apply weight_mem N ((lieMap N).comp (eval a b)) (fun i => ?_) hq
  cases i <;> simpa [eval] using (by assumption : lieMap N _∈F N 1)

open T4Basic T4SolutionData
variable {n : ℕ} {q : L}
 theorem A_mem (N : ℕ) (hq : q∈Ln n) : lieMap N (A q)∈F N n :=
  eval_mem hq (t_mem N 0 1) (t_mem N 1 2)
 theorem D_mem (N : ℕ) (hq : q∈Ln n) : lieMap N (T4SolutionData.D q)∈F N n :=
  eval_mem hq (by rw [map_add]; exact Submodule.add_mem _ (t_mem N 0 2) (t_mem N 1 2)) (t_mem N 2 3)
 theorem E_mem (N : ℕ) (hq : q∈Ln n) : lieMap N (E q)∈F N n :=
  eval_mem hq (t_mem N 0 1) (by rw [map_add]; exact Submodule.add_mem _ (t_mem N 1 2) (t_mem N 1 3))

 def velocity (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (a : Edge) : Q N :=
  lieMap N (T4Derivation.derivation hq hqn hn (projection (FreeLieAlgebra.of ℝ a)))

 theorem velocity_mem (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (ij : Edge) :
    velocity N hq hqn hn ij∈F N (n+1) := by
  have hA := A_mem N hqn
  have hD := D_mem N hqn
  have hE := E_mem N hqn
  have hb : lieMap N b∈F N 1 := t_mem N 1 2
  have hc : lieMap N c∈F N 1 := t_mem N 2 3
  have he : lieMap N e∈F N 1 := t_mem N 1 3
  have hbA : ⁅lieMap N b,lieMap N (A q)⁆∈F N (n+1) := by simpa [Nat.add_comm] using lie_mem hb hA
  have hcD : ⁅lieMap N c,lieMap N (T4SolutionData.D q)⁆∈F N (n+1) := by simpa [Nat.add_comm] using lie_mem hc hD
  have heDE : ⁅lieMap N (b+e),lieMap N (T4SolutionData.D q+E q)⁆∈F N (n+1) := by
    rw [map_add,map_add]
    simpa [Nat.add_comm] using lie_mem (Submodule.add_mem _ hb he) (Submodule.add_mem _ hD hE)
  have hall (i j : Fin 4) : lieMap N (T4Derivation.derivation hq hqn hn (t i j))∈F N (n+1) := by
    have ha : lieMap N (T4Derivation.derivation hq hqn hn a)∈F N (n+1) := by simp
    have hb' : lieMap N (T4Derivation.derivation hq hqn hn b)∈F N (n+1) := by
      rw [T4Derivation.derivation_b,LieHom.map_lie]; exact hbA
    have hc' : lieMap N (T4Derivation.derivation hq hqn hn c)∈F N (n+1) := by
      rw [T4Derivation.derivation_c,LieHom.map_lie]; exact hcD
    have hd' : lieMap N (T4Derivation.derivation hq hqn hn d)∈F N (n+1) := by
      rw [T4Derivation.derivation_d,map_neg,LieHom.map_lie]; exact Submodule.neg_mem _ hbA
    have he' : lieMap N (T4Derivation.derivation hq hqn hn e)∈F N (n+1) := by
      rw [T4Derivation.derivation_e,map_sub,LieHom.map_lie,LieHom.map_lie]
      exact Submodule.sub_mem _ heDE hbA
    have hf' : lieMap N (T4Derivation.derivation hq hqn hn f)∈F N (n+1) := by
      rw [T4Derivation.derivation_f,map_sub,map_neg,LieHom.map_lie,map_sub,LieHom.map_lie,LieHom.map_lie]
      exact Submodule.sub_mem _ (Submodule.neg_mem _ hcD) (Submodule.sub_mem _ heDE hbA)
    fin_cases i <;> fin_cases j
    all_goals first | simpa only [t_self,map_zero] using (Submodule.zero_mem (F N (n+1))) | exact ha | exact hb' | exact hc' | exact hd' | exact he' | exact hf'
  unfold velocity
  rw [projection_of]
  exact hall _ _

 theorem relations_killed (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n)
    (p : DeligneDrinfeld.AssociativeElimination.A ℝ Edge) (hp : p∈presentation) :
    DeligneDrinfeld.TruncatedDerivation.raw presentation N (velocity N hq hqn hn) p=0 := by
  obtain ⟨p,hp,rfl⟩ := hp
  unfold velocity
  rw [DeligneDrinfeld.PresentedCutoff.raw_embed presentation N (T4Derivation.derivation hq hqn hn)
    projection (lieMap N) (lieMap_of N) p,projection_relation hp,map_zero,map_zero]

 def derivation (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : Module.End ℝ (Q N) :=
  DeligneDrinfeld.TruncatedDerivation.derivation presentation N n (velocity N hq hqn hn)
    (velocity_mem N hq hqn hn) (relations_killed N hq hqn hn)

 theorem derivation_lieMap (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p : T4) :
    derivation N hq hqn hn (lieMap N p)=lieMap N (T4Derivation.derivation hq hqn hn p) := by
  induction p using Submodule.Quotient.induction_on with | _ p =>
    exact DeligneDrinfeld.PresentedCutoff.derivation_embed presentation N n _ _ _ _ projection
      (lieMap N) (lieMap_of N) (fun _ => rfl) p

end RealDeligneDrinfeld.BraidCutoff

namespace RealDeligneDrinfeld.BraidCategoryExp
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords BraidCutoff T4Basic T4SolutionData
attribute [local instance] LieRing.ofAssociativeRing
variable {n : ℕ} {q : L}
 theorem B_mem (N : ℕ) (hq : q∈Ln n) : lieMap N (B q)∈BraidCutoff.F N n :=
  eval_mem hq (by rw [map_add]; exact Submodule.add_mem _ (t_mem N 0 1) (t_mem N 0 2))
    (by rw [map_add]; exact Submodule.add_mem _ (t_mem N 1 3) (t_mem N 2 3))

 def h (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p : Fin 5) : BraidCutoff.Q N :=
  lieMap N ((FourSolutionCategory.data hq hqn hn).h p)
 theorem h_mem (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p : Fin 5) : h N hq hqn hn p∈BraidCutoff.F N n := by
  unfold h FourSolutionCategory.data
  fin_cases p
  · change lieMap N 0∈BraidCutoff.F N n; rw [map_zero]; exact Submodule.zero_mem _
  · exact A_mem N hqn
  · change lieMap N (A q+B q)∈_; rw [map_add]
    exact Submodule.add_mem _ (A_mem N hqn) (B_mem N hqn)
  · exact D_mem N hqn
  · change lieMap N (T4SolutionData.D q+E q)∈_; rw [map_add]
    exact Submodule.add_mem _ (D_mem N hqn) (E_mem N hqn)

 theorem d_one (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : BraidCutoff.derivation N hq hqn hn 1=0 :=
  DeligneDrinfeld.TruncatedDerivation.derivation_one presentation N n _ _ _
 theorem d_mul (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (a b : BraidCutoff.Q N) :
    BraidCutoff.derivation N hq hqn hn (a*b)=BraidCutoff.derivation N hq hqn hn a*b+a*BraidCutoff.derivation N hq hqn hn b :=
  DeligneDrinfeld.TruncatedDerivation.derivation_mul presentation N n _ _ _ a b
 theorem d_mem (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) {m : ℕ} {a : BraidCutoff.Q N} (ha : a∈BraidCutoff.F N m) :
    BraidCutoff.derivation N hq hqn hn a∈BraidCutoff.F N (m+n) :=
  DeligneDrinfeld.TruncatedDerivation.derivation_mem presentation N n _ _ _ ha

 def data (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : DeligneDrinfeld.CategoryExp.Data ℝ (BraidCutoff.Q N) (Fin 5) :=
  DeligneDrinfeld.CategoryExp.gauge (BraidCutoff.derivation N hq hqn hn) (d_mul N hq hqn hn) (d_one N hq hqn hn) (h N hq hqn hn)

 theorem raises (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p s : Fin 5) (m : ℕ) (a : BraidCutoff.Q N)
    (ha : a∈BraidCutoff.F N m) : (data N hq hqn hn).D p s a∈BraidCutoff.F N (m+n) :=
  DeligneDrinfeld.CutoffCategory.raises presentation N _ _ _ _ n
    (fun _ _ ha => d_mem N hq hqn hn ha) (h_mem N hq hqn hn) p s m a ha

 theorem loop_lieMap (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p : Fin 5) (a : T4) :
    (data N hq hqn hn).D p p (lieMap N a)=
      lieMap N (DeligneDrinfeld.CategoryGauge.loop (FourSolutionCategory.data hq hqn hn) p a) := by
  change BraidCutoff.derivation N hq hqn hn (lieMap N a)+h N hq hqn hn p*lieMap N a-lieMap N a*h N hq hqn hn p=_
  rw [derivation_lieMap]
  rw [DeligneDrinfeld.CategoryGauge.loop_apply,map_add,LieHom.map_lie,Ring.lie_def]
  change _= _+(h N hq hqn hn p*lieMap N a-lieMap N a*h N hq hqn hn p)
  change lieMap N (T4Derivation.derivation hq hqn hn a)+h N hq hqn hn p*lieMap N a-lieMap N a*h N hq hqn hn p=
    lieMap N (T4Derivation.derivation hq hqn hn a)+(h N hq hqn hn p*lieMap N a-lieMap N a*h N hq hqn hn p)
  abel

 theorem unit (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p s : Fin 5) :
    (data N hq hqn hn).D p s 1=lieMap N (DeligneDrinfeld.CategoryGauge.unit (FourSolutionCategory.data hq hqn hn) p s) := by
  change BraidCutoff.derivation N hq hqn hn 1+h N hq hqn hn s*1-1*h N hq hqn hn p=_
  rw [d_one,zero_add,mul_one,one_mul,DeligneDrinfeld.CategoryGauge.unit,map_sub]
  rfl
end RealDeligneDrinfeld.BraidCategoryExp

namespace RealDeligneDrinfeld.BraidInsertionExp
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords DeligneDrinfeld.CategoryGauge
attribute [local instance] LieRing.ofAssociativeRing
variable (N : ℕ) (X Y : T4)
  (hX : BraidCutoff.lieMap N X∈BraidCutoff.F N 1) (hY : BraidCutoff.lieMap N Y∈BraidCutoff.F N 1)
 theorem insert_gen (a : Bool) : insert N X Y hX hY (DeligneDrinfeld.TruncatedDerivation.gen ∅ N a)=family N X Y a :=
  DeligneDrinfeld.PresentedSubstitution.subst_gen _ _ _ _ a
 theorem insert_j (p : L) : insert N X Y hX hY (FreeCutoffCategory.j N p)=BraidCutoff.lieMap N (eval X Y p) := by
  have he : (insert N X Y hX hY).toLieHom.comp (FreeCutoffCategory.j N)=
      (BraidCutoff.lieMap N).comp (eval X Y) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    change insert N X Y hX hY (FreeCutoffCategory.j N (FreeLieAlgebra.of ℝ a))=_
    rw [FreeCutoffCategory.j_of,insert_gen]
    cases a <;> simp [family,eval]
  exact LieHom.congr_fun he p

 variable {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n)

 open T4Basic

end RealDeligneDrinfeld.BraidInsertionExp

namespace DeligneDrinfeld.CategoryExp
variable {R A B O P I : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Ring B] [Algebra R B]
 theorem sum_apply (s : Finset I) (g : I → Data R A O) (p q : O) (a : A) :
    (sum s g).D p q a=∑ i∈s,(g i).D p q a := LinearMap.sum_apply _ _ _
 theorem sum_raises {N : ℕ} (F : FilteredComparison.Filtration R A N)
    (s : Finset I) (g : I → Data R A O)
    (hg : ∀ i∈s,∀ p q m a,a∈F.step m → (g i).D p q a∈F.step (m+1))
    (p q : O) (m : ℕ) (a : A) (ha : a∈F.step m) :
    (sum s g).D p q a∈F.step (m+1) := by
  rw [sum_apply]
  exact Submodule.sum_mem _ (fun i hi => hg i hi p q m a ha)
 theorem sum_natural (s : Finset I) (g : I → Data R A O) (k : I → Data R B P)
    (f : A →ₗ[R] B) (p q : O) (r t : P)
    (hf : ∀ i∈s,∀ a,(k i).D r t (f a)=f ((g i).D p q a)) (a : A) :
    (sum s k).D r t (f a)=f ((sum s g).D p q a) := by
  rw [sum_apply,sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun i hi => hf i hi a)
 theorem exp_sum_natural [Module ℚ A] [Module ℚ B]
    (s : Finset I) (g : I → Data R A O) (k : I → Data R B P)
    (f : A →ₗ[R] B) (p q : O) (r t : P)
    (hg : IsNilpotent ((sum s g).D p q)) (hk : IsNilpotent ((sum s k).D r t))
    (hf : ∀ i∈s,∀ a,(k i).D r t (f a)=f ((g i).D p q a)) (a : A) :
    act (sum s k) r t (f a)=f (act (sum s g) p q a) :=
  OperatorExp.natural _ _ hg hk f (sum_natural s g k f p q r t hf) a
end DeligneDrinfeld.CategoryExp

section
namespace RealDeligneDrinfeld.BraidInsertionExp
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords DeligneDrinfeld.CategoryGauge
variable (N : ℕ) (X Y : T4)
  (hX : BraidCutoff.lieMap N X∈BraidCutoff.F N 1) (hY : BraidCutoff.lieMap N Y∈BraidCutoff.F N 1)
  {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n)
 theorem edge_derivative (s t : Fin 5)
    (he : EdgeCompatible (eval X Y) 0 1 s t (ThreeSolutionCategory.data q) (FourSolutionCategory.data hq hqn hn))
    (a : FreeCutoffCategory.Q N) :
    (BraidCategoryExp.data N hq hqn hn).D s t (insert N X Y hX hY a)=
      insert N X Y hX hY ((FreeCutoffCategory.data N hqn).D 0 1 a) := by
  apply DeligneDrinfeld.CutoffCategory.edge_natural FreeCutoffCategory.P N
    (FreeCutoffCategory.data N hqn) (BraidCategoryExp.data N hq hqn hn) (insert N X Y hX hY) 0 s 1 t
  · rw [BraidCategoryExp.unit,FreeCutoffCategory.unit_all,insert_j,he.1]
  · intro b
    rw [←FreeCutoffCategory.j_of,insert_j,BraidCategoryExp.loop_lieMap,FreeCutoffCategory.loop_j,insert_j,he.2]
end RealDeligneDrinfeld.BraidInsertionExp

namespace RealDeligneDrinfeld.BraidInsertionSum
open DeligneDrinfeld.CategoryExp
open BraidInsertionExp
variable {I : Type*} (N : ℕ) (s : Finset I) (q : I → L) (n : I → ℕ)
  (hq : ∀ i,q i∈W) (hqn : ∀ i,q i∈Ln (n i)) (hn : ∀ i,2<n i)
 def braid : Data ℝ (BraidCutoff.Q N) (Fin 5) := sum s (fun i => BraidCategoryExp.data N (hq i) (hqn i) (hn i))
 include hn in
 theorem free_raises (p r : Fin 3) (m : ℕ) (a : FreeCutoffCategory.Q N) (ha : a∈FreeCutoffCategory.F N m) :
    (free N s q n hqn).D p r a∈FreeCutoffCategory.F N (m+1) := by
  apply sum_raises (DeligneDrinfeld.CutoffCategory.filtration ∅ N) s _ _ p r m a ha
  intro i _hi p r m a ha
  exact DeligneDrinfeld.TruncatedWords.filtration_antitone ∅ N (by have := hn i; omega)
    (FreeCutoffCategory.raises N (hqn i) p r m a ha)
 theorem braid_raises (p r : Fin 5) (m : ℕ) (a : BraidCutoff.Q N) (ha : a∈BraidCutoff.F N m) :
    (braid N s q n hq hqn hn).D p r a∈BraidCutoff.F N (m+1) := by
  apply sum_raises (DeligneDrinfeld.CutoffCategory.filtration BraidCutoff.presentation N) s _ _ p r m a ha
  intro i _hi p r m a ha
  exact DeligneDrinfeld.TruncatedWords.filtration_antitone _ N (by have := hn i; omega)
    (BraidCategoryExp.raises N (hq i) (hqn i) (hn i) p r m a ha)
 include hn in
 theorem free_nilpotent (p r : Fin 3) : IsNilpotent ((free N s q n hqn).D p r) :=
  nilpotent (DeligneDrinfeld.CutoffCategory.filtration ∅ N) _ (free_raises N s q n hqn hn p r)
 theorem braid_nilpotent (p r : Fin 5) : IsNilpotent ((braid N s q n hq hqn hn).D p r) :=
  nilpotent (DeligneDrinfeld.CutoffCategory.filtration BraidCutoff.presentation N) _ (braid_raises N s q n hq hqn hn p r)
 theorem edge (X Y : T4)
    (hX : BraidCutoff.lieMap N X∈BraidCutoff.F N 1) (hY : BraidCutoff.lieMap N Y∈BraidCutoff.F N 1)
    (p r : Fin 5)
    (he : ∀ i,DeligneDrinfeld.CategoryGauge.EdgeCompatible (eval X Y) 0 1 p r
      (ThreeSolutionCategory.data (q i)) (FourSolutionCategory.data (hq i) (hqn i) (hn i)))
    (a : FreeCutoffCategory.Q N) :
    act (braid N s q n hq hqn hn) p r (insert N X Y hX hY a)=
      insert N X Y hX hY (act (free N s q n hqn) 0 1 a) := by
  exact exp_sum_natural s _ _ (insert N X Y hX hY).toLinearMap 0 1 p r
    (free_nilpotent N s q n hqn hn 0 1) (braid_nilpotent N s q n hq hqn hn p r)
    (fun i _hi a => edge_derivative N X Y hX hY (hq i) (hqn i) (hn i) p r (he i) a) a
 include hq hn in
 theorem pentagon_oai (a : FreeCutoffCategory.Q N)
    (ha : IDE N a*IAD N a=ICE N a*IBC N a*IAB N a) :
    let a' := act (free N s q n hqn) 0 1 a
    IDE N a'*IAD N a'=ICE N a'*IBC N a'*IAB N a' := by
  let F := act (braid N s q n hq hqn hn)
  let a' := act (free N s q n hqn) 0 1 a
  have hh := congrArg (F 0 4) ha
  have hn' := braid_nilpotent N s q n hq hqn hn
  rw [composition _ hn' 0 3 4,composition _ hn' 0 1 4,composition _ hn' 1 2 4] at hh
  have hDE : F 3 4 (IDE N a)=IDE N a' := edge N s q n hq hqn hn _ _ _ _ 3 4 (fun i => FourSolutionCategory.DE (hq i) (hqn i) (hn i)) a
  have hAD : F 0 3 (IAD N a)=IAD N a' := edge N s q n hq hqn hn _ _ _ _ 0 3 (fun i => FourSolutionCategory.AD (hq i) (hqn i) (hn i)) a
  have hCE : F 2 4 (ICE N a)=ICE N a' := edge N s q n hq hqn hn _ _ _ _ 2 4 (fun i => FourSolutionCategory.CE (hq i) (hqn i) (hn i)) a
  have hBC : F 1 2 (IBC N a)=IBC N a' := edge N s q n hq hqn hn _ _ _ _ 1 2 (fun i => FourSolutionCategory.BC (hq i) (hqn i) (hn i)) a
  have hAB : F 0 1 (IAB N a)=IAB N a' := edge N s q n hq hqn hn _ _ _ _ 0 1 (fun i => FourSolutionCategory.AB (hq i) (hqn i) (hn i)) a
  rw [hDE,hAD,hCE,hBC,hAB] at hh
  exact hh
end RealDeligneDrinfeld.BraidInsertionSum

end

end

end OAI

end








universe u_1
section
open OAI.RealDeligneDrinfeld.BraidInsertionSum in
theorem solution : ∀ {I : Type u_1} (N : ℕ) (s : Finset I)
    (q : I → OAI.RealDeligneDrinfeld.L) (n : I → ℕ) (hq : ∀ (i : I), q i ∈ OAI.RealDeligneDrinfeld.W)
    (hqn : ∀ (i : I), q i ∈ OAI.RealDeligneDrinfeld.Ln (n i)) (hn : ∀ (i : I), 2 < n i)
    (a : OAI.RealDeligneDrinfeld.FreeCutoffCategory.Q N)
    (ha :
      (OAI.RealDeligneDrinfeld.BraidInsertionExp.IDE N) a * (OAI.RealDeligneDrinfeld.BraidInsertionExp.IAD N) a =
        (OAI.RealDeligneDrinfeld.BraidInsertionExp.ICE N) a * (OAI.RealDeligneDrinfeld.BraidInsertionExp.IBC N) a *
          (OAI.RealDeligneDrinfeld.BraidInsertionExp.IAB N) a),
    let a' := (OAI.DeligneDrinfeld.CategoryExp.act (OAI.RealDeligneDrinfeld.BraidInsertionSum.free N s q n hqn) 0 1) a;
    (OAI.RealDeligneDrinfeld.BraidInsertionExp.IDE N) a' * (OAI.RealDeligneDrinfeld.BraidInsertionExp.IAD N) a' =
      (OAI.RealDeligneDrinfeld.BraidInsertionExp.ICE N) a' * (OAI.RealDeligneDrinfeld.BraidInsertionExp.IBC N) a' *
        (OAI.RealDeligneDrinfeld.BraidInsertionExp.IAB N) a' :=
  @OAI.RealDeligneDrinfeld.BraidInsertionSum.pentagon_oai
end

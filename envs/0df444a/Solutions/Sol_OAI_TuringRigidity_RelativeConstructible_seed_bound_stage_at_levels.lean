-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:17:02.983048+00:00
-- url     : https://prove2.me/submissions/49fb3275-f0af-4ab0-807f-91397286c0a0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_definablePower_mem
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_ground_relative_context
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_hierarchyGraph_sigmaDefinable
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_hierarchy_checked_at_levels
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_internal_hierarchyGraph_collection
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_uniform_hierarchy_certificate

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem omega_transitive : Transitive ZFSet.omega.{u} := by
  intro x hx y hy
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  obtain ⟨i,_,rfl⟩ := (mem_natSet n y).mp hy
  exact (mem_omega _).mpr ⟨i,rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelReals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelReals
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding
universe u
noncomputable section

theorem omega_exists (P : ZFSet.{u} → Prop) :
    (∃ x ∈ ZFSet.omega, P x) ↔ ∃ n, P (natSet n) := by
  constructor
  · rintro ⟨x,hx,hP⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨n,hP⟩
  · rintro ⟨n,hP⟩
    exact ⟨_,(mem_omega _).mpr ⟨n,rfl⟩,hP⟩

end
end TuringRigidity.SetModelReals

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section

variable {M : ZFSet.{u}} (C : Context M)
include C

theorem Context.omega_mem : ZFSet.omega.{u} ∈ M :=
  BoundedSetTheory.omega_mem M C.transitive C.separation C.infinity

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
universe u
noncomputable section

theorem parity_ext {α : Sort*} {f g : ℕ → α} (he : ∀ n, f (2*n) = g (2*n))
    (ho : ∀ n, f (2*n+1) = g (2*n+1)) : f = g := by
  funext n
  have hm : n%2 < 2 := Nat.mod_lt n (by decide)
  by_cases h : n%2=0
  · have hn : n=2*(n/2) := by omega
    rw [hn]
    exact he _
  · have hn : n=2*(n/2)+1 := by omega
    rw [hn]
    exact ho _

@[simp] theorem mix_slotMap (e d : ℕ → ZFSet.{u}) (r s : ℕ → ℕ) :
    mix e d ∘ slotMap r s = mix (e ∘ r) (d ∘ s) := by
  apply parity_ext <;> intro n <;> simp

variable {M : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem Definable.congr (h : Definable M P) (he : ∀ e, P e ↔ Q e) : Definable M Q := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨p,d,hd,fun e => (hp e).trans (he e)⟩

theorem Definable.neg (h : Definable M P) : Definable M (fun e => ¬ P e) := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨.neg p,d,hd,fun e => not_congr (hp e)⟩

theorem Definable.and (hP : Definable M P) (hQ : Definable M Q) :
    Definable M (fun e => P e ∧ Q e) := by
  obtain ⟨p,d,hd,hp⟩ := hP
  obtain ⟨q,c,hc,hq⟩ := hQ
  refine ⟨.conj (p.rename (slotMap id (fun i => 2*i)))
    (q.rename (slotMap id (fun i => 2*i+1))),mix d c,?_,?_⟩
  · intro i
    unfold mix
    split <;> first | exact hd _ | exact hc _
  · intro e
    simp only [Formula.Eval,Formula.eval_rename_comp,mix_slotMap,Function.comp_id]
    have hd' : mix d c ∘ (fun i => 2*i) = d := by funext i; simp
    have hc' : mix d c ∘ (fun i => 2*i+1) = c := by funext i; simp
    rw [hd',hc',hp,hq]

theorem bind_mix (x : ZFSet.{u}) (e d : ℕ → ZFSet.{u}) :
    cons x (mix e d) ∘ bindSlots = mix (cons x e) d := by
  apply parity_ext
  · intro n
    cases n with
    | zero => rfl
    | succ n => simp
  · intro n
    simp [show 2*n+2 = (2*n+1)+1 from by omega]

theorem Definable.existsMem (h : Definable M P) (i : ℕ) :
    Definable M (fun e => ∃ x ∈ e i, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.existsMem (2*i) (p.rename bindSlots),d,hd,?_⟩
  intro e
  simp only [Formula.Eval,mix_even,Formula.eval_rename_comp,bind_mix,hp]

theorem member_definable (C : Context M) (i j : ℕ) : Definable M (fun e => e i ∈ e j) :=
  ⟨.member (2*i) (2*j),fun _ => ZFSet.omega,fun _ => C.omega_mem,fun e => by simp [Formula.Eval]⟩

theorem equal_param {a : ZFSet.{u}} (ha : a ∈ M) (i : ℕ) :
    Definable M (fun e => e i = a) :=
  ⟨.equal (2*i) 1,fun _ => a,fun _ => ha,fun e => by simp [Formula.Eval,mix]⟩

theorem Definable.sep_mem (C : Context M) (h : Definable M P) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) {a : ZFSet.{u}} (ha : a ∈ M) :
    ZFSet.sep (fun x => P (cons x e)) a ∈ M := by
  obtain ⟨p,d,hd,hp⟩ := h
  let q := p.rename bindSlots
  have hm : ∀ i, mix e d i ∈ M := by
    intro i
    unfold mix
    split <;> first | exact he _ | exact hd _
  have hs := BoundedSetTheory.sep_mem M C.transitive C.separation q (mix e d) hm ha
  have hh : ZFSet.sep (fun x => q.Eval (cons x (mix e d))) a =
      ZFSet.sep (fun x => P (cons x e)) a := by
    apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_sep,q,Formula.eval_rename_comp,bind_mix,hp]
  exact hh ▸ hs

end
end TuringRigidity.BoundedDefinability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory
universe u

namespace SentenceForm

theorem finite_support (p : SentenceForm) (D : Set ZFSet.{u})
    (e f : ℕ → ZFSet.{u}) (h : ∀ i, i < p.bound → e i = f i) :
    p.Sat D e ↔ p.Sat D f := by
  induction p generalizing e f with
  | equal i j =>
    have hi := h i (by simp only [bound]; omega)
    have hj := h j (by simp only [bound]; omega)
    simp only [Sat,hi,hj]
  | member i j =>
    have hi := h i (by simp only [bound]; omega)
    have hj := h j (by simp only [bound]; omega)
    simp only [Sat,hi,hj]
  | conj p q ihp ihq =>
    exact and_congr (ihp e f (fun i hi => h i (by simp only [bound]; omega)))
      (ihq e f (fun i hi => h i (by simp only [bound]; omega)))
  | neg p ih => exact not_congr (ih e f h)
  | ex p ih =>
    apply exists_congr; intro x
    apply and_congr_right; intro _
    apply ih
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (by simp only [bound] at h ⊢; omega)

theorem sat_rename (p : SentenceForm) (v : ℕ → ℕ)
    (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (p.rename v).Sat D e ↔ p.Sat D (fun i => e (v i)) := by
  induction p generalizing v e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp v e) (ihq v e)
  | neg p ih => exact not_congr (ih v e)
  | ex p ih =>
    apply exists_congr; intro x
    apply and_congr_right; intro _
    have he : (fun i => cons x e (match i with | 0 => 0 | j+1 => v j+1)) =
        cons x (fun i => e (v i)) := by funext i; cases i <;> rfl
    exact (ih _ _).trans (he ▸ Iff.rfl)
end SentenceForm

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel

theorem encode_equal (i j : ℕ) :
    Encodable.encode (SentenceForm.equal i j) = binary 0 (atom i) (atom j) := rfl
theorem encode_member (i j : ℕ) :
    Encodable.encode (SentenceForm.member i j) = binary 1 (atom i) (atom j) := rfl
theorem encode_conj (p q : SentenceForm) :
    Encodable.encode (SentenceForm.conj p q) = binary 2 (Encodable.encode p) (Encodable.encode q) := rfl
theorem encode_neg (p : SentenceForm) :
    Encodable.encode (SentenceForm.neg p) = unary 3 (Encodable.encode p) := rfl
theorem encode_ex (p : SentenceForm) :
    Encodable.encode (SentenceForm.ex p) = unary 4 (Encodable.encode p) := rfl

theorem cell_left_lt (a b : ℕ) : a < cell a b := by
  have h := Nat.left_le_pair (a+1) b
  unfold cell; omega

theorem cell_right_le (a b : ℕ) : b ≤ cell a b := Nat.right_le_pair _ _

theorem binary_left_lt (t a b : ℕ) : a < binary t a b :=
  lt_of_lt_of_le (cell_left_lt a _) (cell_right_le _ _)
theorem binary_right_lt (t a b : ℕ) : b < binary t a b :=
  lt_of_lt_of_le (cell_left_lt b _) (le_trans (cell_right_le _ _) (cell_right_le _ _))
theorem unary_child_lt (t a : ℕ) : a < unary t a :=
  lt_of_lt_of_le (cell_left_lt a _) (cell_right_le _ _)

theorem step_encode (C : ℕ → Prop) (p : SentenceForm) :
    Step C (Encodable.encode p) ↔ Children C p := by
  cases p <;>
    simp [Step,Children,encode_equal,encode_member,encode_conj,encode_neg,encode_ex,
      binary,unary,cell,atom,Nat.pair_eq_pair]

theorem Closed.valid {C : ℕ → Prop} (h : Closed C) (c : ℕ) (hc : C c) :
    ∃ p : SentenceForm, c = Encodable.encode p := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    rcases h c hc with he|hm|ha|hn|hx
    · obtain ⟨i,j,rfl⟩ := he; exact ⟨.equal i j,(encode_equal i j).symm⟩
    · obtain ⟨i,j,rfl⟩ := hm; exact ⟨.member i j,(encode_member i j).symm⟩
    · obtain ⟨a,b,rfl,ha,hb⟩ := ha
      obtain ⟨p,rfl⟩ := ih a (binary_left_lt _ _ _) ha
      obtain ⟨q,rfl⟩ := ih b (binary_right_lt _ _ _) hb
      exact ⟨.conj p q,(encode_conj p q).symm⟩
    · obtain ⟨a,rfl,ha⟩ := hn
      obtain ⟨p,rfl⟩ := ih a (unary_child_lt _ _) ha
      exact ⟨.neg p,(encode_neg p).symm⟩
    · obtain ⟨a,rfl,ha⟩ := hx
      obtain ⟨p,rfl⟩ := ih a (unary_child_lt _ _) ha
      exact ⟨.ex p,(encode_ex p).symm⟩

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceCodeDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions SetModelSyntax
universe u

variable {M : ZFSet.{u}}

theorem defOr {P Q : (ℕ → ZFSet.{u}) → Prop}
    (hP : Definable M P) (hQ : Definable M Q) : Definable M (fun e => P e ∨ Q e) :=
  (hP.neg.and hQ.neg).neg.congr (fun _ => by tauto)

theorem defImp {P Q : (ℕ → ZFSet.{u}) → Prop}
    (hP : Definable M P) (hQ : Definable M Q) : Definable M (fun e => P e → Q e) :=
  (hP.and hQ.neg).neg.congr (fun _ => by tauto)

theorem defAllMem {P : (ℕ → ZFSet.{u}) → Prop}
    (h : Definable M P) (i : ℕ) : Definable M (fun e => ∀ x ∈ e i, P (cons x e)) :=
  (h.neg.existsMem i).neg.congr (fun _ => by simp)

theorem defSubset (C : Context M) (i j : ℕ) : Definable M (fun e => e i ⊆ e j) :=
  defAllMem (member_definable C 0 (j+1)) i

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_DefinablePower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem mem_definedSubset (A x : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) :
    x ∈ definedSubset A p v ↔ x ∈ A ∧ p.Sat (A : Set ZFSet) (cons x (tupleEnv v)) :=
  ZFSet.mem_sep

theorem definableOver_subset {A S : ZFSet.{u}} (h : DefinableOver A S) : S ⊆ A := by
  obtain ⟨n,p,v,_,_,rfl⟩ := h
  exact fun _ hx => (mem_definedSubset A _ p v).mp hx |>.1

theorem mem_definablePower (A S : ZFSet.{u}) :
    S ∈ definablePower A ↔ DefinableOver A S := by
  rw [definablePower,ZFSet.mem_sep]
  exact ⟨And.right,fun h => ⟨ZFSet.mem_powerset.mpr (definableOver_subset h),h⟩⟩

theorem subset_of_mem_definablePower {A S : ZFSet.{u}}
    (h : S ∈ definablePower A) : S ⊆ A :=
  definableOver_subset ((mem_definablePower A S).mp h)

theorem separation_mem_definablePower (A : ZFSet.{u}) (p : SentenceForm)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, i < p.bound → e i ∈ A) :
    A.sep (fun x => p.Sat (A : Set ZFSet) (cons x e)) ∈ definablePower A := by
  apply (mem_definablePower A _).mpr
  let v : Fin p.bound → ZFSet.{u} := fun i => e i
  refine ⟨p.bound,p,v,by omega,fun i => he i i.isLt,?_⟩
  apply ZFSet.ext; intro x
  rw [ZFSet.mem_sep,mem_definedSubset]
  apply and_congr_right; intro _
  apply p.finite_support
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    change e i = tupleEnv v i
    simp [tupleEnv,v,show i < p.bound by omega]

theorem self_mem_definablePower (A : ZFSet.{u}) : A ∈ definablePower A := by
  apply (mem_definablePower A A).mpr
  refine ⟨0,.equal 0 0,Fin.elim0,by decide,fun i => Fin.elim0 i,?_⟩
  apply ZFSet.ext; intro x
  simp [mem_definedSubset,SentenceForm.Sat]

theorem subset_definablePower {A : ZFSet.{u}} (hA : Transitive A) : A ⊆ definablePower A := by
  intro S hS
  apply (mem_definablePower A S).mpr
  refine ⟨1,.member 0 1,fun _ => S,by decide,fun _ => hS,?_⟩
  apply ZFSet.ext; intro x
  simp only [mem_definedSubset,SentenceForm.Sat,cons_zero,cons_succ]
  simp only [tupleEnv,show 0 < 1 by decide,dite_eq_left]
  exact ⟨fun hx => ⟨hA S hS x hx,hx⟩,And.right⟩

theorem definablePower_transitive {A : ZFSet.{u}} (hA : Transitive A) :
    Transitive (definablePower A) := by
  intro S hS x hx
  exact subset_definablePower hA (subset_of_mem_definablePower hS hx)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleSatisfaction
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem tupleCode_length {n m : ℕ} (v : Fin n → ZFSet.{u}) (w : Fin m → ZFSet.{u})
    (h : tupleCode v = tupleCode w) : n = m :=
  natSet_injective (ZFSet.pair_inj.mp h).1

theorem tupleCode_injective (n : ℕ) : Function.Injective (@tupleCode.{u} n) := by
  intro v w h
  have hg := (ZFSet.pair_inj.mp h).2
  funext i
  have hi : ZFSet.pair (natSet i.val) (v i) ∈
      ZFSet.range (fun j : Fin n => ZFSet.pair (natSet j.val) (w j)) := by
    rw [← hg]
    exact ZFSet.mem_range_self (f := fun index : Fin n => ZFSet.pair (natSet index.val) (v index)) i
  obtain ⟨j,hj⟩ := ZFSet.mem_range.mp hi
  obtain ⟨he,hv⟩ := ZFSet.pair_inj.mp hj
  have hji : j = i := Fin.ext (natSet_injective he)
  subst j
  exact hv.symm

theorem satisfactionSet_spec (A : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (hb : p.bound ≤ n) :
    ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ satisfactionSet A ↔
      p.Sat (A : Set ZFSet) (tupleEnv v) := by
  rw [satisfactionSet,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨m,q,w⟩,hqm,hq⟩,he⟩
    obtain ⟨hp,ht⟩ := ZFSet.pair_inj.mp he
    have hqp : q = p := Encodable.encode_injective (natSet_injective hp)
    subst q
    have hmn : m = n := tupleCode_length _ _ ht
    subst m
    have hwv := tupleCode_injective n ht
    rwa [hwv] at hq
  · intro hs
    let w : Fin n → Conditions A := fun i => equivShrink A ⟨v i,hv i⟩
    have hw : (fun i => label A (w i)) = v := by
      funext i; simp [w,label]
    refine ⟨⟨⟨n,p,w⟩,hb,?_⟩,?_⟩
    · rwa [hw]
    · exact congrArg (fun v' => ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v')) hw

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel
universe u

theorem mem_seed (R x : ZFSet.{u}) :
    x ∈ seed R ↔ ∃ n : ℕ, x ∈ iterUnion n ({R} : ZFSet) := by
  rw [seed,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨n,rfl⟩ := ZFSet.mem_range.mp ha
    exact ⟨n,hx⟩
  · rintro ⟨n,hx⟩
    exact ⟨_,ZFSet.mem_range_self (f := fun index : ℕ => iterUnion index ({R} : ZFSet.{u})) n,hx⟩

theorem parameter_mem_seed (R : ZFSet.{u}) : R ∈ seed R :=
  (mem_seed R R).mpr ⟨0,ZFSet.mem_singleton.mpr rfl⟩

theorem seed_transitive (R : ZFSet.{u}) : Transitive (seed R) := by
  intro x hx y hy
  obtain ⟨n,hn⟩ := (mem_seed R x).mp hx
  exact (mem_seed R y).mpr ⟨n+1,ZFSet.mem_sUnion.mpr ⟨x,hn,hy⟩⟩

theorem parameter_subset_seed (R : ZFSet.{u}) : R ⊆ seed R :=
  fun x hx => seed_transitive R R (parameter_mem_seed R) x hx

theorem seed_minimal (R M : ZFSet.{u}) (hM : Transitive M) (hR : R ∈ M) : seed R ⊆ M := by
  intro x hx
  obtain ⟨n,hn⟩ := (mem_seed R x).mp hx
  have sub : ∀ n : ℕ, iterUnion n ({R} : ZFSet) ⊆ M := by
    intro n
    induction n with
    | zero => intro y hy; obtain rfl := ZFSet.mem_singleton.mp hy; exact hR
    | succ n ih =>
      intro y hy
      obtain ⟨z,hz,hy⟩ := ZFSet.mem_sUnion.mp hy
      exact hM z (ih hz) y hy
  exact sub n hn

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleStages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel
universe u

theorem mem_stage (R o x : ZFSet.{u}) :
    x ∈ stage R o ↔ x ∈ seed R ∨ ∃ i ∈ o, x ∈ definablePower (stage R i) := by
  rw [stage,ZFSet.mem_union,ZFSet.mem_sUnion]
  apply or_congr_right
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp ha
    exact ⟨_,((equivShrink o).symm i).property,hx⟩
  · rintro ⟨i,hi,hx⟩
    refine ⟨_,ZFSet.mem_range.mpr ⟨equivShrink o ⟨i,hi⟩,rfl⟩,?_⟩
    simpa using hx

theorem seed_subset_stage (R o : ZFSet.{u}) : seed R ⊆ stage R o :=
  fun x hx => (mem_stage R o x).mpr (Or.inl hx)

theorem stage_zero (R : ZFSet.{u}) : stage R ∅ = seed R := by
  apply ZFSet.ext; intro x
  simp [mem_stage]

theorem stage_transitive (R o : ZFSet.{u}) : Transitive (stage R o) := by
  induction o using ZFSet.inductionOn with
  | h o ih =>
    intro x hx y hy
    rcases (mem_stage R o x).mp hx with hx|⟨i,hi,hx⟩
    · exact seed_subset_stage R o (seed_transitive R x hx y hy)
    · exact (mem_stage R o y).mpr (Or.inr ⟨i,hi,definablePower_transitive (ih i hi) x hx y hy⟩)

theorem stage_mono (R : ZFSet.{u}) {i j : ZFSet.{u}} (hij : i ⊆ j) : stage R i ⊆ stage R j := by
  intro x hx
  rcases (mem_stage R i x).mp hx with hx|⟨k,hk,hx⟩
  · exact seed_subset_stage R j hx
  · exact (mem_stage R j x).mpr (Or.inr ⟨k,hij hk,hx⟩)

theorem definablePower_subset_stage (R : ZFSet.{u}) {i j : ZFSet.{u}} (hi : i ∈ j) :
    definablePower (stage R i) ⊆ stage R j :=
  fun x hx => (mem_stage R j x).mpr (Or.inr ⟨i,hi,hx⟩)

theorem stage_mem_stage (R : ZFSet.{u}) {i j : ZFSet.{u}} (hi : i ∈ j) :
    stage R i ∈ stage R j :=
  definablePower_subset_stage R hi (self_mem_definablePower _)

theorem stage_succ (R o : ZFSet.{u}) :
    stage R (insert o o) = definablePower (stage R o) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    rcases (mem_stage R (insert o o) x).mp hx with hseed|⟨i,hi,hdef⟩
    · exact subset_definablePower (stage_transitive R o) (seed_subset_stage R o hseed)
    · rcases ZFSet.mem_insert_iff.mp hi with he|hi
      · simpa only [he] using hdef
      · exact subset_definablePower (stage_transitive R o) (definablePower_subset_stage R hi hdef)
  · intro hx; exact definablePower_subset_stage R (ZFSet.mem_insert o o) hx

theorem level_zero (R : ZFSet.{u}) : level R 0 = seed R := by
  rw [level,Ordinal.toZFSet_zero,stage_zero]

theorem level_succ (R : ZFSet.{u}) (o : Ordinal.{u}) :
    level R (o+1) = definablePower (level R o) := by
  simp only [level,Ordinal.toZFSet_add_one,stage_succ]

theorem level_mono (R : ZFSet.{u}) {i j : Ordinal.{u}} (hij : i ≤ j) : level R i ⊆ level R j :=
  stage_mono R (Ordinal.toZFSet_monotone hij)

theorem level_mem_level (R : ZFSet.{u}) {i j : Ordinal.{u}} (hij : i < j) : level R i ∈ level R j :=
  stage_mem_stage R (Ordinal.toZFSet_mem_toZFSet_iff.mpr hij)

theorem level_transitive (R : ZFSet.{u}) (o : Ordinal.{u}) : Transitive (level R o) :=
  stage_transitive R o.toZFSet

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleSuccessorCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem tupleEnv_cons {n : ℕ} (x : ZFSet.{u}) (v : Fin n → ZFSet.{u}) :
    tupleEnv (Fin.cases x v) = cons x (tupleEnv v) := by
  funext i
  cases i with
  | zero => simp [tupleEnv,cons]
  | succ i =>
    by_cases hi : i < n
    · simp only [tupleEnv,cons_succ,Nat.succ_lt_succ_iff,hi,dite_eq_left]
      rfl
    · simp [tupleEnv,cons_succ,hi]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleTupleSpace
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem mem_tupleSpace (A t : ZFSet.{u}) :
    t ∈ tupleSpace A ↔ ∃ (n : ℕ) (v : Fin n → ZFSet.{u}),
      (∀ i, v i ∈ A) ∧ t = tupleCode v := by
  rw [tupleSpace,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨n,v⟩,ht⟩
    exact ⟨n,fun i => label A (v i),fun i => label_mem A (v i),ht.symm⟩
  · rintro ⟨n,v,hv,rfl⟩
    let w : Fin n → Conditions A := fun i => equivShrink A ⟨v i,hv i⟩
    refine ⟨⟨n,w⟩,?_⟩
    congr 1; funext i; simp [w,label]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SetSatisfactionBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem setBounded_eval (p : SentenceForm) (a : ℕ) (v : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) :
    (setBounded p a v).Eval e ↔ p.Sat (e a : Set ZFSet) (fun i => e (v i)) := by
  induction p generalizing a v e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp a v e) (ihq a v e)
  | neg p ih => exact not_congr (ih a v e)
  | ex p ih =>
    simp only [setBounded,Formula.Eval,SentenceForm.Sat]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    have he : (fun i => cons x e (match i with | 0 => 0 | j+1 => v j+1)) =
        cons x (fun i => e (v i)) := by funext i; cases i <;> rfl
    exact (ih (a+1) _ (cons x e)).trans (he ▸ Iff.rfl)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSatisfactionSlice
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem natSet_subset_iff (k n : ℕ) : natSet.{u} k ⊆ natSet n ↔ k ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hk : n < k := by omega
    have hn' := (natSet_mem_natSet n n).mp (h ((natSet_mem_natSet n k).mpr hk))
    omega
  · intro h x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet k x).mp hx
    exact (natSet_mem_natSet i n).mpr (by omega)

theorem satisfactionSet_record (A : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) :
    ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ satisfactionSet A ↔
      p.bound ≤ n ∧ p.Sat (A : Set ZFSet) (tupleEnv v) := by
  constructor
  · intro h
    obtain ⟨⟨⟨m,q,w⟩,hqm,hq⟩,he⟩ := ZFSet.mem_range.mp h
    obtain ⟨hp,ht⟩ := ZFSet.pair_inj.mp he
    have hqp : q = p := Encodable.encode_injective (natSet_injective hp)
    subst q
    have hmn : m = n := tupleCode_length _ _ ht
    subst m
    have hwv := tupleCode_injective n ht
    rw [hwv] at hq
    exact ⟨hqm,hq⟩
  · rintro ⟨hb,hs⟩
    exact (satisfactionSet_spec A p v hv hb).mpr hs

theorem truthSlice_record (A : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) :
    tupleCode v ∈ truthSlice A p ↔ p.bound ≤ n ∧ p.Sat (A : Set ZFSet) (tupleEnv v) := by
  rw [truthSlice,ZFSet.mem_sep,satisfactionSet_record A p v hv]
  exact and_iff_right ((mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_FiniteSatisfactionCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem self_mem_subformulas (p : SentenceForm) : p ∈ subformulas p := by
  cases p <;> simp [subformulas]

theorem subformulas_closed (p q : SentenceForm) (hq : q ∈ subformulas p) :
    ∀ r ∈ subformulas q, r ∈ subformulas p := by
  induction p with
  | equal i j =>
    have he : q = .equal i j := by simpa [subformulas] using hq
    subst q; exact fun _ hr => hr
  | member i j =>
    have he : q = .member i j := by simpa [subformulas] using hq
    subst q; exact fun _ hr => hr
  | conj p s ihp ihs =>
    simp only [subformulas,List.mem_cons,List.mem_append] at hq ⊢
    rcases hq with rfl|hq|hq
    · intro r hr; simpa only [subformulas,List.mem_cons,List.mem_append] using hr
    · intro r hr; exact Or.inr (Or.inl (ihp hq r hr))
    · intro r hr; exact Or.inr (Or.inr (ihs hq r hr))
  | neg p ih =>
    simp only [subformulas,List.mem_cons] at hq ⊢
    rcases hq with rfl|hq
    · intro r hr; simpa only [subformulas,List.mem_cons] using hr
    · intro r hr; exact Or.inr (ih hq r hr)
  | ex p ih =>
    simp only [subformulas,List.mem_cons] at hq ⊢
    rcases hq with rfl|hq
    · intro r hr; simpa only [subformulas,List.mem_cons] using hr
    · intro r hr; exact Or.inr (ih hq r hr)

theorem mem_finiteSatisfaction (A z : ZFSet.{u}) (ps : List SentenceForm) :
    z ∈ finiteSatisfaction A ps ↔ ∃ p ∈ ps, ∃ t ∈ truthSlice A p,
      z = ZFSet.pair (natSet (Encodable.encode p)) t := by
  rw [finiteSatisfaction,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨s,hs,hz⟩
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hs
    obtain ⟨k,hk,t,ht,hz⟩ := ZFSet.mem_prod.mp hz
    rw [ZFSet.mem_singleton] at hk
    subst k
    exact ⟨ps[i],List.getElem_mem i.isLt,t,ht,hz⟩
  · rintro ⟨p,hp,t,ht,rfl⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hp
    refine ⟨_,ZFSet.mem_range_self ⟨i,hi⟩,?_⟩
    exact ZFSet.mem_prod.mpr ⟨_,ZFSet.mem_singleton.mpr rfl,t,ht,rfl⟩

theorem finiteSatisfaction_record (A : ZFSet.{u}) (ps : List SentenceForm)
    (p : SentenceForm) {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) :
    ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ finiteSatisfaction A ps ↔
      p ∈ ps ∧ p.bound ≤ n ∧ p.Sat (A : Set ZFSet) (tupleEnv v) := by
  rw [mem_finiteSatisfaction]
  constructor
  · rintro ⟨q,hq,t,ht,he⟩
    obtain ⟨hc,ht'⟩ := ZFSet.pair_inj.mp he
    have hpq : p = q := Encodable.encode_injective (natSet_injective hc)
    subst q; subst t
    exact ⟨hq,(truthSlice_record A p v hv).mp ht⟩
  · rintro ⟨hp,hb,hs⟩
    exact ⟨p,hp,tupleCode v,(truthSlice_record A p v hv).mpr ⟨hb,hs⟩,rfl⟩

theorem finiteSatisfaction_covers (A : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) :
    ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ finiteSatisfaction A (subformulas p) ↔
      ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ satisfactionSet A := by
  rw [finiteSatisfaction_record A _ p v hv,satisfactionSet_record A p v hv]
  exact and_iff_right (self_mem_subformulas p)

theorem certificate_correct (A : ZFSet.{u}) (root p : SentenceForm)
    (hp : p ∈ subformulas root) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ A) (hb : p.bound ≤ n) :
    accepts (finiteSatisfaction A (subformulas root)) p v ↔ p.Sat (A : Set ZFSet) (tupleEnv v) := by
  rw [accepts,finiteSatisfaction_record A _ p v hv]
  exact ⟨fun h => h.2.2,fun h => ⟨hp,hb,h⟩⟩

theorem certificate_conj (A : ZFSet.{u}) (root p q : SentenceForm)
    (hp : SentenceForm.conj p q ∈ subformulas root) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ A) (hb : (SentenceForm.conj p q).bound ≤ n) :
    accepts (finiteSatisfaction A (subformulas root)) (.conj p q) v ↔
      accepts (finiteSatisfaction A (subformulas root)) p v ∧
      accepts (finiteSatisfaction A (subformulas root)) q v := by
  have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
  have hq' := subformulas_closed root _ hp q (by simp [subformulas,self_mem_subformulas])
  have hbp : p.bound ≤ n := by simp only [SentenceForm.bound] at hb; omega
  have hbq : q.bound ≤ n := by simp only [SentenceForm.bound] at hb; omega
  rw [certificate_correct A root _ hp v hv hb,certificate_correct A root p hp' v hv hbp,
    certificate_correct A root q hq' v hv hbq]
  rfl

theorem certificate_neg (A : ZFSet.{u}) (root p : SentenceForm)
    (hp : SentenceForm.neg p ∈ subformulas root) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ A) (hb : p.bound ≤ n) :
    accepts (finiteSatisfaction A (subformulas root)) (.neg p) v ↔
      ¬ accepts (finiteSatisfaction A (subformulas root)) p v := by
  have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
  rw [certificate_correct A root _ hp v hv hb,certificate_correct A root p hp' v hv hb]
  rfl

theorem certificate_ex (A : ZFSet.{u}) (root p : SentenceForm)
    (hp : SentenceForm.ex p ∈ subformulas root) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ A) (hb : (SentenceForm.ex p).bound ≤ n) :
    accepts (finiteSatisfaction A (subformulas root)) (.ex p) v ↔
      ∃ x ∈ A, accepts (finiteSatisfaction A (subformulas root)) p (Fin.cases x v) := by
  have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
  have hbp : p.bound ≤ n+1 := by simp only [SentenceForm.bound] at hb; omega
  rw [certificate_correct A root _ hp v hv hb]
  change (∃ x ∈ A, p.Sat (A : Set ZFSet) (cons x (tupleEnv v))) ↔ _
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  rw [certificate_correct A root p hp' (Fin.cases x v) (fun i => Fin.cases hx hv i) hbp,
    tupleEnv_cons]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceCodeFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
universe u

theorem mem_family (p : SentenceForm) (z : ZFSet.{u}) :
    z ∈ family p ↔ ∃ q ∈ subformulas p, z = natSet (Encodable.encode q) := by
  rw [family,ZFSet.mem_range]
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨_,List.getElem_mem i.isLt,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hq
    exact ⟨⟨i,hi⟩,rfl⟩

theorem code_mem_family (p q : SentenceForm) :
    natSet.{u} (Encodable.encode q) ∈ family p ↔ q ∈ subformulas p := by
  rw [mem_family]
  constructor
  · rintro ⟨r,hr,he⟩
    have h : q = r := Encodable.encode_injective (natSet_injective he)
    exact h ▸ hr
  · intro h; exact ⟨q,h,rfl⟩

theorem family_subset_omega (p : SentenceForm) : family p ⊆ ZFSet.omega.{u} := by
  intro z hz
  obtain ⟨q,_,rfl⟩ := (mem_family p z).mp hz
  exact (mem_omega _).mpr ⟨_,rfl⟩

theorem family_closed (p : SentenceForm) :
    Closed (fun n => natSet.{u} n ∈ family p) := by
  intro n hn
  obtain ⟨q,hq,he⟩ := (mem_family p _).mp hn
  have he' := natSet_injective he
  subst n
  rw [step_encode]
  have hc := subformulas_closed p q hq
  cases q with
  | equal i j => trivial
  | member i j => trivial
  | conj a b =>
    exact ⟨(code_mem_family p a).mpr (hc a (by simp [subformulas,self_mem_subformulas])),
      (code_mem_family p b).mpr (hc b (by simp [subformulas,self_mem_subformulas]))⟩
  | neg a => exact (code_mem_family p a).mpr (hc a (by simp [subformulas,self_mem_subformulas]))
  | ex a => exact (code_mem_family p a).mpr (hc a (by simp [subformulas,self_mem_subformulas]))

theorem Closed.subformulas {C : ℕ → Prop} (h : Closed C) (p : SentenceForm)
    (hp : C (Encodable.encode p)) : ∀ q ∈ subformulas p, C (Encodable.encode q) := by
  induction p with
  | equal i j => simpa [RelativeConstructible.subformulas] using hp
  | member i j => simpa [RelativeConstructible.subformulas] using hp
  | conj p r ihp ihr =>
    have hc := (step_encode C (.conj p r)).mp (h _ hp)
    intro q hq
    simp only [RelativeConstructible.subformulas,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|hq|hq
    · exact hp
    · exact ihp hc.1 q hq
    · exact ihr hc.2 q hq
  | neg p ih =>
    have hc := (step_encode C (.neg p)).mp (h _ hp)
    intro q hq
    simp only [RelativeConstructible.subformulas,List.mem_cons] at hq
    rcases hq with rfl|hq
    · exact hp
    · exact ih hc q hq
  | ex p ih =>
    have hc := (step_encode C (.ex p)).mp (h _ hp)
    intro q hq
    simp only [RelativeConstructible.subformulas,List.mem_cons] at hq
    rcases hq with rfl|hq
    · exact hp
    · exact ih hc q hq

theorem family_setClosed (p : SentenceForm) : SetClosed (family.{u} p) :=
  ⟨family_subset_omega p,family_closed p⟩

theorem family_least (p : SentenceForm) (S : ZFSet.{u}) (hS : SetClosed S)
    (hp : natSet (Encodable.encode p) ∈ S) : family p ⊆ S := by
  intro z hz
  obtain ⟨q,hq,rfl⟩ := (mem_family p z).mp hz
  exact hS.2.subformulas p hp q hq

theorem leastFamily_spec (Q S : ZFSet.{u}) (p : SentenceForm) (hQ : family p ∈ Q) :
    LeastFamily Q (natSet (Encodable.encode p)) S ↔ S = family p := by
  constructor
  · rintro ⟨hc,hs,hm⟩
    exact ZFSet.ext (fun z => ⟨fun hz => hm _ hQ
      ((code_mem_family p p).mpr (self_mem_subformulas p)) (family_setClosed p) hz,
      fun hz => family_least p S hs hc hz⟩)
  · rintro rfl
    exact ⟨(code_mem_family p p).mpr (self_mem_subformulas p),family_setClosed p,
      fun T _ hc hs => family_least p T hs hc⟩

theorem setClosed_valid (S : ZFSet.{u}) (hS : SetClosed S) (c : ZFSet.{u}) (hc : c ∈ S) :
    ∃ p : SentenceForm, c = natSet (Encodable.encode p) := by
  obtain ⟨n,rfl⟩ := (mem_omega c).mp (hS.1 hc)
  obtain ⟨p,rfl⟩ := hS.2.valid n hc
  exact ⟨p,rfl⟩

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceSupportCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
universe u

theorem mem_supportGraph (p : SentenceForm) (z : ZFSet.{u}) :
    z ∈ supportGraph p ↔ ∃ q ∈ subformulas p,
      z = ZFSet.pair (natSet (Encodable.encode q)) (natSet q.bound) := by
  rw [supportGraph,ZFSet.mem_range]
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨_,List.getElem_mem i.isLt,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hq
    exact ⟨⟨i,hi⟩,rfl⟩

theorem supportGraph_bound (p q : SentenceForm) (n : ℕ) :
    HasBound (supportGraph.{u} p) q n ↔ q ∈ subformulas p ∧ n = q.bound := by
  rw [HasBound,mem_supportGraph]
  constructor
  · rintro ⟨r,hr,he⟩
    obtain ⟨hc,hb⟩ := ZFSet.pair_inj.mp he
    have hqr : q = r := Encodable.encode_injective (natSet_injective hc)
    subst r
    exact ⟨hr,natSet_injective hb⟩
  · rintro ⟨hq,rfl⟩; exact ⟨q,hq,rfl⟩

theorem supportGraph_recursion (root : SentenceForm) : SupportRecursion root (supportGraph.{u} root) := by
  constructor
  · intro z hz
    obtain ⟨p,hp,rfl⟩ := (mem_supportGraph root z).mp hz
    exact ⟨p,hp,p.bound,rfl⟩
  · intro p hp n
    rw [supportGraph_bound, and_iff_right hp]
    have hc := subformulas_closed root p hp
    cases p with
    | equal i j => rfl
    | member i j => rfl
    | conj p q =>
      have hp' := hc p (by simp [subformulas,self_mem_subformulas])
      have hq' := hc q (by simp [subformulas,self_mem_subformulas])
      simp [SupportStep,supportGraph_bound,hp',hq',SentenceForm.bound]
    | neg p =>
      have hp' := hc p (by simp [subformulas,self_mem_subformulas])
      simp [SupportStep,supportGraph_bound,hp',SentenceForm.bound]
    | ex p =>
      have hp' := hc p (by simp [subformulas,self_mem_subformulas])
      simp [SupportStep,supportGraph_bound,hp',SentenceForm.bound]

theorem SupportRecursion.correct {root : SentenceForm} {G : ZFSet.{u}}
    (h : SupportRecursion root G) (p : SentenceForm) (hp : p ∈ subformulas root) (n : ℕ) :
    HasBound G p n ↔ n = p.bound := by
  induction p generalizing n with
  | equal i j => exact h.2 _ hp n
  | member i j => exact h.2 _ hp n
  | conj p q ihp ihq =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    have hq' := subformulas_closed root _ hp q (by simp [subformulas,self_mem_subformulas])
    rw [h.2 _ hp n]
    simp [SupportStep,ihp hp',ihq hq',SentenceForm.bound]
  | neg p ih =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    exact (h.2 _ hp n).trans (ih hp' n)
  | ex p ih =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    rw [h.2 _ hp n]
    simp [SupportStep,ih hp',SentenceForm.bound]

theorem SupportRecursion.unique {root : SentenceForm} {G : ZFSet.{u}}
    (h : SupportRecursion root G) : G = supportGraph root := by
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨p,hp,n,rfl⟩ := h.1 z hz
    exact (supportGraph_bound root p n).mpr ⟨hp,(h.correct p hp n).mp hz⟩
  · intro hz
    obtain ⟨p,hp,rfl⟩ := (mem_supportGraph root z).mp hz
    exact (h.correct p hp p.bound).mpr rfl

theorem supportGraph_subset (p : SentenceForm) :
    supportGraph p ⊆ ZFSet.prod ZFSet.omega.{u} ZFSet.omega := by
  intro z hz
  obtain ⟨q,_,rfl⟩ := (mem_supportGraph p z).mp hz
  exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨_,rfl⟩,_,(mem_omega _).mpr ⟨_,rfl⟩,rfl⟩

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceSupportFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
open BoundedDefinability SetModelFunctions SetModelReals
universe u

variable {M : ZFSet.{u}}

theorem setSupportStep_encode (G : ZFSet.{u}) (p : SentenceForm) (b : ℕ) :
    SetSupportStep G (natSet (Encodable.encode p)) (natSet b) ↔ SupportStep G p b := by
  unfold SetSupportStep
  simp_rw [omega_exists]
  simp only [BinaryGraph,UnaryGraph,natSet_injective.eq_iff]
  cases p <;>
    simp [SupportStep,HasBound,encode_equal,encode_member,encode_conj,encode_neg,encode_ex,
      binary,unary,cell,atom,Nat.pair_eq_pair]

theorem defPairMem (C : Context M) (i j g : ℕ) :
    Definable M (fun e => ZFSet.pair (e i) (e j) ∈ e g) :=
  ⟨.pairMem (2*i) (2*j) (2*g),fun _ => ZFSet.omega,fun _ => C.omega_mem,
    fun e => by simp only [Formula.eval_pairMem,mix_even]⟩

theorem setSupportRecursion_spec (root : SentenceForm) (G : ZFSet.{u}) :
    SetSupportRecursion (family root) G ↔ SupportRecursion root G := by
  constructor
  · rintro ⟨hn,hr⟩
    constructor
    · intro z hz
      obtain ⟨c,hc,b,hb,rfl⟩ := hn z hz
      obtain ⟨p,hp,rfl⟩ := (mem_family root c).mp hc
      obtain ⟨n,rfl⟩ := (mem_omega b).mp hb
      exact ⟨p,hp,n,rfl⟩
    · intro p hp n
      exact (hr _ ((code_mem_family root p).mpr hp) _ ((mem_omega _).mpr ⟨n,rfl⟩)).trans
        (setSupportStep_encode G p n)
  · rintro ⟨hn,hr⟩
    constructor
    · intro z hz
      obtain ⟨p,hp,n,rfl⟩ := hn z hz
      exact ⟨_,(code_mem_family root p).mpr hp,_,(mem_omega _).mpr ⟨n,rfl⟩,rfl⟩
    · intro c hc b hb
      obtain ⟨p,hp,rfl⟩ := (mem_family root c).mp hc
      obtain ⟨n,rfl⟩ := (mem_omega b).mp hb
      exact (hr p hp n).trans (setSupportStep_encode G p n).symm

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformSentenceSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

theorem boundWitness_spec (Q B c b : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B) :
    BoundWitness Q B c b ↔
      ∃ p : SentenceForm, c = natSet (Encodable.encode p) ∧ b = natSet p.bound := by
  constructor
  · rintro ⟨F,_,G,_,hf,hg,hcb⟩
    obtain ⟨p,rfl⟩ := setClosed_valid F hf.2.1 c hf.1
    have hF := (leastFamily_spec Q F p (hQ p)).mp hf
    subst F
    have hG := ((setSupportRecursion_spec p G).mp hg).unique
    rw [hG] at hcb
    obtain ⟨q,_,he⟩ := (mem_supportGraph p _).mp hcb
    obtain ⟨hc,hb⟩ := ZFSet.pair_inj.mp he
    have hpq : p = q := Encodable.encode_injective (natSet_injective hc)
    subst q
    exact ⟨p,rfl,hb⟩
  · rintro ⟨p,rfl,rfl⟩
    exact ⟨family p,hQ p,supportGraph p,hB p,
      (leastFamily_spec Q (family p) p (hQ p)).mpr rfl,
      (setSupportRecursion_spec p _).mpr (supportGraph_recursion p),
      (supportGraph_bound p p p.bound).mpr ⟨self_mem_subformulas p,rfl⟩⟩

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TuplePrefixSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem prefixGraphs_spec (A g m h x : ZFSet.{u}) {n : ℕ}
    (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (hx : x ∈ A)
    (hg : g = tupleGraph v) :
    PrefixGraphs A (natSet n) g m h x ↔
      m = natSet (n+1) ∧ h = tupleGraph (Fin.cases (motive := fun _ => ZFSet.{u}) x v) := by
  subst g
  constructor
  · rintro ⟨rfl,hh,hzero,hshift⟩
    have hn : insert (natSet.{u} n) (natSet n) = natSet (n+1) := rfl
    rw [hn] at hh
    obtain ⟨w,hw,rfl⟩ := functionGraph_tuple A h (n+1) hh
    have hwv : w = Fin.cases (motive := fun _ => ZFSet.{u}) x v := by
      funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · exact ((tupleGraph_pair w 0 x).mp hzero).symm
      · obtain ⟨j,_,hj,ht⟩ := hshift (natSet k.val) ((natSet_mem_natSet _ _).mpr k.isLt)
        have hpair := ht (v k) (hv k) ((tupleGraph_pair v k _).mpr rfl)
        rw [hj] at hpair
        exact ((tupleGraph_pair w k.succ (v k)).mp hpair).symm
    rw [hwv]
    exact ⟨rfl,rfl⟩
  · rintro ⟨hm,hh⟩
    rw [hm,hh]
    unfold PrefixGraphs
    refine ⟨rfl,?_,?_,?_⟩
    · apply tupleGraph_function
      intro i
      exact Fin.cases hx hv i
    · change ZFSet.pair (natSet 0) x ∈ ZFSet.range
        (fun i : Fin (n+1) => ZFSet.pair (natSet i.val) ((Fin.cases (motive := fun _ => ZFSet.{u}) x v : Fin (n+1) → ZFSet.{u}) i))
      exact ZFSet.mem_range_self
        (f := fun i : Fin (n+1) => ZFSet.pair (natSet i.val)
          (Fin.cases (motive := fun _ => ZFSet.{u}) x v i))
        (⟨0,Nat.zero_lt_succ n⟩ : Fin (n+1))
    · intro i hi
      obtain ⟨k,hk,rfl⟩ := (mem_natSet n i).mp hi
      refine ⟨natSet (k+1),(natSet_mem_natSet _ _).mpr (Nat.succ_lt_succ hk),rfl,?_⟩
      intro y _ hy
      have he := (tupleGraph_pair v ⟨k,hk⟩ y).mp hy
      exact (tupleGraph_pair (Fin.cases (motive := fun _ => ZFSet.{u}) x v) (Fin.succ ⟨k,hk⟩) y).mpr he

theorem tuplePrefixFormula_spec (A o Q t x u z : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hz : e z = natSet 0)
    (hQ : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ e A) → tupleGraph v ∈ e Q)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ e A)
    (ht : e t = tupleCode v) (hx : e x ∈ e A) :
    (tuplePrefixFormula A o Q t x u z).Eval e ↔ e u = tupleCode (Fin.cases (motive := fun _ => ZFSet.{u}) (e x) v) := by
  simp only [tuplePrefixFormula,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ]
  simp only [prefixGraphsFormula,Formula.Eval,Formula.eval_successor,Formula.eval_functionGraph,
    Formula.eval_pairMem,Formula.eval_allMem,Formula.eval_imp,cons_zero,cons_succ,hz]
  change (∃ n' ∈ e o, ∃ g ∈ e Q, ∃ m ∈ e o, ∃ h ∈ e Q,
    e t = ZFSet.pair n' g ∧ e u = ZFSet.pair m h ∧ PrefixGraphs (e A) n' g m h (e x)) ↔ _
  rw [ho]
  constructor
  · rintro ⟨n',_,g,_,m,_,h,_,ht',hu,hp⟩
    have he := ZFSet.pair_inj.mp (ht.symm.trans ht')
    have hn : n' = natSet n := he.1.symm
    have hg : g = tupleGraph v := he.2.symm
    rw [hn] at hp
    obtain ⟨hm,hh⟩ := (prefixGraphs_spec (e A) g m h (e x) v hv hx hg).mp hp
    rw [hu,hm,hh]; rfl
  · intro hu
    refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hQ n v hv,
      natSet (n+1),(mem_omega _).mpr ⟨n+1,rfl⟩,tupleGraph (Fin.cases (motive := fun _ => ZFSet.{u}) (e x) v),
      hQ (n+1) _ (fun i => Fin.cases hx hv i),ht,hu,?_⟩
    exact (prefixGraphs_spec (e A) _ _ _ _ v hv hx rfl).mpr ⟨rfl,rfl⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TupleLookupAdequacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

theorem tupleLookup_spec (G : ZFSet.{u}) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hG : tupleGraph v ∈ G) (i x : ZFSet.{u}) :
    TupleLookup G (tupleCode v) i x ↔ ∃ k : Fin n, i = natSet k.val ∧ x = v k := by
  constructor
  · rintro ⟨m,_,g,_,he,hx⟩
    have hg : g = tupleGraph v := (ZFSet.pair_inj.mp he).2.symm
    rw [hg] at hx
    obtain ⟨k,hk⟩ := ZFSet.mem_range.mp hx
    obtain ⟨hi,hx⟩ := ZFSet.pair_inj.mp hk
    exact ⟨k,hi.symm,hx.symm⟩
  · rintro ⟨k,rfl,rfl⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hG,rfl,
      (tupleGraph_pair v k _).mpr rfl⟩

theorem tupleLookup_nat (G : ZFSet.{u}) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hG : tupleGraph v ∈ G) (i : ℕ) (x : ZFSet.{u}) :
    TupleLookup G (tupleCode v) (natSet i) x ↔ i < n ∧ x = tupleEnv v i := by
  rw [tupleLookup_spec G v hG]
  constructor
  · rintro ⟨k,hi,rfl⟩
    have he := natSet_injective hi
    subst i
    exact ⟨k.isLt,by simp [tupleEnv]⟩
  · rintro ⟨hi,hx⟩
    exact ⟨⟨i,hi⟩,rfl,by simpa [tupleEnv,hi] using hx⟩

theorem tupleAdequate_spec (Q B G : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hG : tupleGraph v ∈ G) :
    TupleAdequate Q B G (natSet (Encodable.encode p)) (tupleCode v) ↔ p.bound ≤ n := by
  constructor
  · rintro ⟨m,_,g,_,b,_,he,hb,hle⟩
    have hm : m = natSet n := (ZFSet.pair_inj.mp he).1.symm
    obtain ⟨q,hq,rfl⟩ := (boundWitness_spec Q B _ b hQ hB).mp hb
    have hpq : p = q := Encodable.encode_injective (natSet_injective hq)
    subst q
    rw [hm] at hle
    exact (natSet_subset_iff p.bound n).mp hle
  · intro hb
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hG,
      natSet p.bound,(mem_omega _).mpr ⟨p.bound,rfl⟩,rfl,
      (boundWitness_spec Q B _ _ hQ hB).mpr ⟨p,rfl,rfl⟩,
      (natSet_subset_iff p.bound n).mpr hb⟩

theorem tuplePrefix_spec (A G : ZFSet.{u})
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (x s : ZFSet.{u}) (hx : x ∈ A) :
    TuplePrefix A G (tupleCode v) x s ↔ s = tupleCode (Fin.cases x v) :=
  tuplePrefixFormula_spec 0 1 2 3 4 5 6 _ rfl rfl hG v hv rfl hx

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SatisfactionRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem finiteSatisfaction_recursion (A : ZFSet.{u}) (root : SentenceForm) :
    TruthRecursion A root (finiteSatisfaction A (subformulas root)) := by
  constructor
  · intro z hz
    obtain ⟨p,hp,t,ht,rfl⟩ := (mem_finiteSatisfaction A z _).mp hz
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp (ZFSet.mem_sep.mp ht).1
    exact ⟨p,hp,n,v,hv,((truthSlice_record A p v hv).mp ht).1,rfl⟩
  · intro p hp n v hv hb
    cases p with
    | equal i j => exact certificate_correct A root _ hp v hv hb
    | member i j => exact certificate_correct A root _ hp v hv hb
    | conj p q => exact certificate_conj A root p q hp v hv hb
    | neg p => exact certificate_neg A root p hp v hv hb
    | ex p => exact certificate_ex A root p hp v hv hb

theorem TruthRecursion.correct {A S : ZFSet.{u}} {root : SentenceForm}
    (h : TruthRecursion A root S) (p : SentenceForm) (hp : p ∈ subformulas root)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (hb : p.bound ≤ n) :
    accepts S p v ↔ p.Sat (A : Set ZFSet) (tupleEnv v) := by
  induction p generalizing n with
  | equal i j => exact h.2 _ hp n v hv hb
  | member i j => exact h.2 _ hp n v hv hb
  | conj p q ihp ihq =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    have hq' := subformulas_closed root _ hp q (by simp [subformulas,self_mem_subformulas])
    have hbp : p.bound ≤ n := by simp only [SentenceForm.bound] at hb; omega
    have hbq : q.bound ≤ n := by simp only [SentenceForm.bound] at hb; omega
    exact (h.2 _ hp n v hv hb).trans (and_congr (ihp hp' v hv hbp) (ihq hq' v hv hbq))
  | neg p ih =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    exact (h.2 _ hp n v hv hb).trans (not_congr (ih hp' v hv hb))
  | ex p ih =>
    have hp' := subformulas_closed root _ hp p (by simp [subformulas,self_mem_subformulas])
    have hbp : p.bound ≤ n+1 := by simp only [SentenceForm.bound] at hb; omega
    refine (h.2 (.ex p) hp n v hv hb).trans ?_
    simp only [truthStep,SentenceForm.Sat]
    apply exists_congr; intro x
    apply and_congr_right; intro hx
    rw [ih hp' (Fin.cases x v) (fun i => Fin.cases hx hv i) hbp,tupleEnv_cons]

theorem TruthRecursion.unique {A S T : ZFSet.{u}} {root : SentenceForm}
    (hS : TruthRecursion A root S) (hT : TruthRecursion A root T) : S = T := by
  have sub {U V : ZFSet.{u}} (hU : TruthRecursion A root U) (hV : TruthRecursion A root V) : U ⊆ V := by
    intro z hz
    obtain ⟨p,hp,n,v,hv,hb,rfl⟩ := hU.1 z hz
    exact (hV.correct p hp v hv hb).mpr ((hU.correct p hp v hv hb).mp hz)
  exact ZFSet.ext (fun _ => ⟨fun hz => sub hS hT hz,fun hz => sub hT hS hz⟩)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformTruthStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions SetModelReals
universe u

variable {M : ZFSet.{u}}

theorem setTruthStep_encode (A G S : ZFSet.{u})
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (p : SentenceForm) {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A)
    (hb : p.bound ≤ n) :
    SetTruthStep A G (tupleSpace A) S (natSet (Encodable.encode p)) (tupleCode v) ↔
      truthStep A S v p := by
  unfold SetTruthStep
  simp_rw [omega_exists]
  simp only [BinaryGraph,UnaryGraph,natSet_injective.eq_iff]
  cases p with
  | equal i j =>
    have hi : i < n := by simp only [SentenceForm.bound] at hb; omega
    have hj : j < n := by simp only [SentenceForm.bound] at hb; omega
    simp [encode_equal,binary,unary,cell,atom,Nat.pair_eq_pair,
      tupleLookup_nat G v (hG n v hv),hi,hj,truthStep,eq_comm,
      show tupleEnv v j ∈ A from by simpa [tupleEnv,hj] using hv ⟨j,hj⟩]
  | member i j =>
    have hi : i < n := by simp only [SentenceForm.bound] at hb; omega
    have hj : j < n := by simp only [SentenceForm.bound] at hb; omega
    simp [encode_member,binary,unary,cell,atom,Nat.pair_eq_pair,
      tupleLookup_nat G v (hG n v hv),hi,hj,truthStep,
      show tupleEnv v i ∈ A from by simpa [tupleEnv,hi] using hv ⟨i,hi⟩,
      show tupleEnv v j ∈ A from by simpa [tupleEnv,hj] using hv ⟨j,hj⟩]
  | conj p q =>
    simp [encode_conj,binary,unary,cell,atom,Nat.pair_eq_pair,truthStep,accepts]
  | neg p =>
    simp [encode_neg,binary,unary,cell,atom,Nat.pair_eq_pair,truthStep,accepts]
  | ex p =>
    simp [encode_ex,binary,unary,cell,atom,Nat.pair_eq_pair]
    apply exists_congr; intro x
    apply and_congr_right; intro hx
    simp only [tuplePrefix_spec A G hG v hv x _ hx]
    change (∃ s ∈ tupleSpace A, s = tupleCode (Fin.cases x v) ∧
      ZFSet.pair (natSet (Encodable.encode p)) s ∈ S) ↔ _
    constructor
    · rintro ⟨s,_,rfl,hs⟩; exact hs
    · intro hs
      let w : Fin (n+1) → ZFSet.{u} := Fin.cases (motive := fun _ => ZFSet.{u}) x v
      have hw : ∀ i : Fin (n+1), w i ∈ A := fun i => Fin.cases hx hv i
      have ht : tupleCode w ∈ tupleSpace A := (mem_tupleSpace A (tupleCode w)).mpr ⟨n+1,w,hw,rfl⟩
      exact ⟨tupleCode w,ht,rfl,hs⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformTruthRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

theorem setTruthRecursion_spec (Q B G A S : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (root : SentenceForm) :
    SetTruthRecursion Q B G A (tupleSpace A) (family root) S ↔ TruthRecursion A root S := by
  constructor
  · rintro ⟨hn,hr⟩
    constructor
    · intro z hz
      obtain ⟨c,hc,t,ht,ha,rfl⟩ := hn z hz
      obtain ⟨p,hp,rfl⟩ := (mem_family root c).mp hc
      obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
      exact ⟨p,hp,n,v,hv,(tupleAdequate_spec Q B G hQ hB p v (hG n v hv)).mp ha,rfl⟩
    · intro p hp n v hv hb
      have ht := (mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩
      have ha := (tupleAdequate_spec Q B G hQ hB p v (hG n v hv)).mpr hb
      exact (hr _ ((code_mem_family root p).mpr hp) _ ht ha).trans
        (setTruthStep_encode A G S hG p v hv hb)
  · rintro ⟨hn,hr⟩
    constructor
    · intro z hz
      obtain ⟨p,hp,n,v,hv,hb,rfl⟩ := hn z hz
      exact ⟨_,(code_mem_family root p).mpr hp,_,(mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩,
        (tupleAdequate_spec Q B G hQ hB p v (hG n v hv)).mpr hb,rfl⟩
    · intro c hc t ht ha
      obtain ⟨p,hp,rfl⟩ := (mem_family root c).mp hc
      obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
      have hb := (tupleAdequate_spec Q B G hQ hB p v (hG n v hv)).mp ha
      exact (hr p hp n v hv hb).trans (setTruthStep_encode A G S hG p v hv hb).symm

theorem truthWitness_spec (Q B G A c S : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G) :
    TruthWitness Q B G A (tupleSpace A) c S ↔
      ∃ root : SentenceForm, c = natSet (Encodable.encode root) ∧ TruthRecursion A root S := by
  constructor
  · rintro ⟨F,_,hf,hr⟩
    obtain ⟨root,rfl⟩ := setClosed_valid F hf.2.1 c hf.1
    have he := (leastFamily_spec Q F root (hQ root)).mp hf
    subst F
    exact ⟨root,rfl,(setTruthRecursion_spec Q B G A S hQ hB hG root).mp hr⟩
  · rintro ⟨root,rfl,hr⟩
    exact ⟨family root,hQ root,(leastFamily_spec Q _ root (hQ root)).mpr rfl,
      (setTruthRecursion_spec Q B G A S hQ hB hG root).mpr hr⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformInternalSatisfaction
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

theorem satisfactionWitness_spec (Q B G H A z : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (hH : ∀ p : SentenceForm, finiteSatisfaction A (subformulas p) ∈ H) :
    SatisfactionWitness Q B G H A (tupleSpace A) z ↔ z ∈ satisfactionSet A := by
  constructor
  · rintro ⟨c,_,t,ht,S,_,hw,hs,rfl⟩
    obtain ⟨p,rfl,hr⟩ := (truthWitness_spec Q B G A c S hQ hB hG).mp hw
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    have he := hr.unique (finiteSatisfaction_recursion A p)
    rw [he] at hs
    exact (finiteSatisfaction_covers A p v hv).mp hs
  · intro hz
    obtain ⟨⟨⟨n,p,w⟩,hb,hp⟩,rfl⟩ := ZFSet.mem_range.mp hz
    let v : Fin n → ZFSet.{u} := fun i => label A (w i)
    have hv : ∀ i, v i ∈ A := fun i => label_mem A (w i)
    refine ⟨_,(mem_omega _).mpr ⟨Encodable.encode p,rfl⟩,
      tupleCode v,(mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩,
      finiteSatisfaction A (subformulas p),hH p,?_,?_,rfl⟩
    · exact (truthWitness_spec Q B G A _ _ hQ hB hG).mpr
        ⟨p,rfl,finiteSatisfaction_recursion A p⟩
    · exact (certificate_correct A p p (self_mem_subformulas p) v hv hb).mpr hp

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_DefinableSubsetCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

theorem parameterAdequate_spec (Q B G c : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hG : tupleGraph v ∈ G) :
    ParameterAdequate Q B G c (tupleCode v) ↔
      ∃ p : SentenceForm, c = natSet (Encodable.encode p) ∧ p.bound ≤ n+1 := by
  constructor
  · rintro ⟨m,_,g,_,b,_,he,hb,hle⟩
    have hm : m = natSet n := (ZFSet.pair_inj.mp he).1.symm
    obtain ⟨p,hp,rfl⟩ := (boundWitness_spec Q B c b hQ hB).mp hb
    refine ⟨p,hp,(natSet_subset_iff p.bound (n+1)).mp ?_⟩
    intro x hx
    have h := hle x hx
    rw [hm] at h
    exact ZFSet.mem_insert_iff.mpr h.symm
  · rintro ⟨p,rfl,hp⟩
    refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hG,
      natSet p.bound,(mem_omega _).mpr ⟨p.bound,rfl⟩,rfl,
      (boundWitness_spec Q B _ _ hQ hB).mpr ⟨p,rfl,rfl⟩,?_⟩
    intro x hx
    have hs := (natSet_subset_iff p.bound (n+1)).mpr hp hx
    exact (ZFSet.mem_insert_iff.mp hs).symm

theorem definesSubset_spec (A G S : ZFSet.{u})
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (p : SentenceForm) {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A)
    (hb : p.bound ≤ n+1) :
    DefinesSubset A G (tupleSpace A) (satisfactionSet A)
      (natSet (Encodable.encode p)) (tupleCode v) S ↔ S = definedSubset A p v := by
  have hstep (x : ZFSet.{u}) (hx : x ∈ A) :
      (∃ s ∈ tupleSpace A, TuplePrefix A G (tupleCode v) x s ∧
        ZFSet.pair (natSet (Encodable.encode p)) s ∈ satisfactionSet A) ↔
      p.Sat (A : Set ZFSet) (cons x (tupleEnv v)) := by
    let w : Fin (n+1) → ZFSet.{u} := Fin.cases (motive := fun _ => ZFSet.{u}) x v
    have hw : ∀ i : Fin (n+1), w i ∈ A := fun i => Fin.cases hx hv i
    have ht : tupleCode w ∈ tupleSpace A := (mem_tupleSpace A _).mpr ⟨n+1,w,hw,rfl⟩
    have he : tupleEnv w = cons x (tupleEnv v) := tupleEnv_cons x v
    constructor
    · rintro ⟨s,_,hs,hp⟩
      have hs' := (tuplePrefix_spec A G hG v hv x s hx).mp hs
      rw [hs'] at hp
      exact he ▸ (satisfactionSet_spec A p w hw hb).mp hp
    · intro hp
      refine ⟨tupleCode w,ht,(tuplePrefix_spec A G hG v hv x _ hx).mpr rfl,?_⟩
      exact (satisfactionSet_spec A p w hw hb).mpr (he ▸ hp)
  constructor
  · rintro ⟨hsub,hdef⟩
    apply ZFSet.ext; intro x
    rw [mem_definedSubset]
    exact ⟨fun hx => ⟨hsub hx,(hstep x (hsub hx)).mp ((hdef x (hsub hx)).mp hx)⟩,
      fun ⟨hx,hp⟩ => (hdef x hx).mpr ((hstep x hx).mpr hp)⟩
  · rintro rfl
    refine ⟨fun x hx => (mem_definedSubset A x p v).mp hx |>.1,?_⟩
    intro x hx
    rw [mem_definedSubset]
    exact (and_iff_right hx).trans (hstep x hx).symm

theorem definitionWitness_spec (Q B G A S : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G) :
    DefinitionWitness Q B G A (tupleSpace A) (satisfactionSet A) S ↔ DefinableOver A S := by
  constructor
  · rintro ⟨c,_,t,ht,ha,hd⟩
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    obtain ⟨p,rfl,hp⟩ := (parameterAdequate_spec Q B G c hQ hB v (hG n v hv)).mp ha
    exact ⟨n,p,v,hp,hv,(definesSubset_spec A G S hG p v hv hp).mp hd⟩
  · rintro ⟨n,p,v,hp,hv,rfl⟩
    exact ⟨_,(mem_omega _).mpr ⟨Encodable.encode p,rfl⟩,
      _,(mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩,
      (parameterAdequate_spec Q B G _ hQ hB v (hG n v hv)).mpr ⟨p,rfl,hp⟩,
      (definesSubset_spec A G _ hG p v hv hp).mpr rfl⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TupleSystemCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem tuplePrefix_sound (A G x s : ZFSet.{u}) {n : ℕ}
    (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (hx : x ∈ A)
    (hs : TuplePrefix A G (tupleCode v) x s) :
    s = tupleCode (Fin.cases (motive := fun _ => ZFSet.{u}) x v) := by
  unfold TuplePrefix at hs
  simp only [tuplePrefixFormula,Formula.Eval,Formula.eval_orderedPair,
    cons_zero,cons_succ] at hs
  simp only [prefixGraphsFormula,Formula.Eval,Formula.eval_successor,
    Formula.eval_functionGraph,Formula.eval_pairMem,Formula.eval_allMem,
    Formula.eval_imp,cons_zero,cons_succ] at hs
  change ∃ n' ∈ ZFSet.omega, ∃ g ∈ G, ∃ m ∈ ZFSet.omega, ∃ h ∈ G,
    tupleCode v = ZFSet.pair n' g ∧ s = ZFSet.pair m h ∧
      PrefixGraphs A n' g m h x at hs
  obtain ⟨n',_,g,_,m,_,h,_,he,hs,hp⟩ := hs
  obtain ⟨hn,hg⟩ := ZFSet.pair_inj.mp he
  rw [← hn] at hp
  obtain ⟨hm,hh⟩ := (prefixGraphs_spec A g m h x v hv hx hg.symm).mp hp
  rw [hs,hm,hh]
  rfl

theorem TupleSystem.exact {A G T : ZFSet.{u}} (h : TupleSystem A G T) :
    T = tupleSpace A ∧ ∀ (n : ℕ) (v : Fin n → ZFSet.{u}),
      (∀ i, v i ∈ A) → tupleGraph v ∈ G := by
  have hin : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleCode v ∈ T := by
    intro n
    induction n with
    | zero =>
      intro v _
      have hg : tupleGraph v = (∅ : ZFSet.{u}) := by
        apply ZFSet.ext; intro z
        simp [tupleGraph]
      change ZFSet.pair (natSet 0) (tupleGraph v) ∈ T
      rw [hg]
      exact h.2.1
    | succ n ih =>
      intro v hv
      let w : Fin n → ZFSet.{u} := fun i => v i.succ
      obtain ⟨s,hs,hp⟩ := h.2.2 (tupleCode w) (ih w (fun i => hv i.succ)) (v 0) (hv 0)
      have he := tuplePrefix_sound A G (v 0) s w (fun i => hv i.succ) (hv 0) hp
      have hvw : (Fin.cases (motive := fun _ => ZFSet.{u}) (v 0) w) = v := by
        funext i; exact Fin.cases rfl (fun _ => rfl) i
      rwa [he,hvw] at hs
  constructor
  · apply ZFSet.ext; intro t
    constructor
    · intro ht
      obtain ⟨n,hn,g,_,he,hg⟩ := h.1 t ht
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      obtain ⟨v,hv,rfl⟩ := functionGraph_tuple A g n hg
      exact (mem_tupleSpace A t).mpr ⟨n,v,hv,he⟩
    · intro ht
      obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
      exact hin n v hv
  · intro n v hv
    obtain ⟨m,_,g,hg,he,_⟩ := h.1 (tupleCode v) (hin n v hv)
    have he' : tupleGraph v = g := (ZFSet.pair_inj.mp he).2
    rwa [← he'] at hg

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SatisfactionSystemCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem SatisfactionSystem.exact {Q B A G T H Z : ZFSet.{u}}
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (h : SatisfactionSystem Q B A G T H Z) :
    T = tupleSpace A ∧ Z = satisfactionSet A ∧
      (∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G) ∧
      ∀ p : SentenceForm, finiteSatisfaction A (subformulas p) ∈ H := by
  obtain ⟨ht,hg⟩ := h.1.exact
  subst T
  have hh (p : SentenceForm) : finiteSatisfaction A (subformulas p) ∈ H := by
    obtain ⟨S,hS,hs⟩ := h.2.1 _ ((mem_omega _).mpr ⟨Encodable.encode p,rfl⟩)
      (family p) (hQ p) ((leastFamily_spec Q _ p (hQ p)).mpr rfl)
    have he := ((setTruthRecursion_spec Q B G A S hQ hB hg p).mp hs).unique
      (finiteSatisfaction_recursion A p)
    exact he ▸ hS
  refine ⟨rfl,?_,hg,hh⟩
  apply ZFSet.ext; intro z
  rw [← satisfactionWitness_spec Q B G H A z hQ hB hg hh]
  constructor
  · exact h.2.2.1 z
  · rintro ⟨c,hc,t,ht,S,hS,hs,hct,rfl⟩
    exact h.2.2.2 c hc t ht S hS hs hct

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_DefSystemCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem DefSystem.exact {Q B A G T H Z D : ZFSet.{u}}
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (h : DefSystem Q B A G T H Z D) : D = definablePower A := by
  obtain ⟨ht,hz,hg,_⟩ := h.1.exact hQ hB
  subst T; subst Z
  apply ZFSet.ext; intro S
  rw [mem_definablePower]
  constructor
  · intro hS
    exact (definitionWitness_spec Q B G A S hQ hB hg).mp (h.2.1 S hS)
  · rintro ⟨n,p,v,hp,hv,rfl⟩
    obtain ⟨S,hS,hs⟩ := h.2.2 _ ((mem_omega _).mpr ⟨Encodable.encode p,rfl⟩)
      _ ((mem_tupleSpace A _).mpr ⟨n,v,hv,rfl⟩)
      ((parameterAdequate_spec Q B G _ hQ hB v (hg n v hv)).mpr ⟨p,rfl,hp⟩)
    exact (definesSubset_spec A G S hg p v hv hp).mp hs ▸ hS

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaParameterized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u

variable {M : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem Definable.toSigma (hM : Transitive M) (h : Definable M P) : SigmaDefinable M P := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.bounded p,d,hd,?_⟩
  intro e he
  exact (p.absolute M hM (mix e d) (by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _)).trans (hp e)

theorem SigmaDefinable.existsSet (h : SigmaDefinable M P) :
    SigmaDefinable M (fun e => ∃ x ∈ M, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.existsSet (p.rename bindSlots),d,hd,?_⟩
  intro e he
  simp only [SigmaFormula.Realize,SigmaFormula.realize_rename]
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  have hh := bind_mix x e d
  change (p.Realize M (cons x (mix e d) ∘ bindSlots)) ↔ _
  rw [hh]
  exact hp (cons x e) (by intro i; cases i; exact hx; exact he _)

theorem SigmaDefinable.congr (h : SigmaDefinable M P)
    (hPQ : ∀ e, (∀ i, e i ∈ M) → (P e ↔ Q e)) : SigmaDefinable M Q := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨p,d,hd,fun e he => (hp e he).trans (hPQ e he)⟩

end TuringRigidity.BoundedDefinability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_HierarchyGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem HierarchyGraph.correct {M R d r f : ZFSet.{u}}
    (h : HierarchyGraph M (seed R) d r f) (x : ZFSet.{u}) (hx : x ∈ d)
    (v : ZFSet.{u}) (hv : v ∈ r) (hfv : ZFSet.pair x v ∈ f) :
    v = definablePower (stage R x) := by
  induction x using ZFSet.inductionOn generalizing v with
  | h x ih =>
    obtain ⟨A,_,hs,rfl⟩ := h.2.2 x hx v hv hfv
    congr 1
    apply ZFSet.ext; intro z
    rw [mem_stage]
    constructor
    · intro hz
      rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
      · exact Or.inl hz
      · rw [ih y hy (h.1 x hx y hy) w hw hfw] at hz
        exact Or.inr ⟨y,hy,hz⟩
    · rintro (hz|⟨y,hy,hz⟩)
      · exact hs.1 hz
      · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1 x hx y hy)
        rw [← ih y hy (h.1 x hx y hy) w hw hfw] at hz
        exact hs.2.2 y hy w hw hfw hz

theorem HierarchyGraph.mem_iff {M R d r f : ZFSet.{u}}
    (h : HierarchyGraph M (seed R) d r f) (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (definablePower (stage R x)) := by
  constructor
  · intro hz
    obtain ⟨x,hx,v,hv,rfl⟩ := h.2.1.1 z hz
    exact ⟨x,hx,by rw [h.correct x hx v hv hz]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := h.2.1.2 x hx
    rw [← h.correct x hx v hv hfv]
    exact hfv

theorem HierarchyGraph.unique {M N R d r t f g : ZFSet.{u}}
    (hf : HierarchyGraph M (seed R) d r f) (hg : HierarchyGraph N (seed R) d t g) : f = g := by
  apply ZFSet.ext; intro z
  exact (hf.mem_iff z).trans (hg.mem_iff z).symm

theorem mem_stageImage (s x f z : ZFSet.{u}) :
    z ∈ stageImage s x f ↔ z ∈ s ∨ ∃ y ∈ x, ∃ w, ZFSet.pair y w ∈ f ∧ z ∈ w := by
  rw [stageImage,ZFSet.mem_union,ZFSet.mem_sep]
  apply or_congr_right
  constructor
  · rintro ⟨_,y,hy,w,_,hf,hz⟩; exact ⟨y,hy,w,hf,hz⟩
  · rintro ⟨y,hy,w,hf,hz⟩
    have hw := second_mem_doubleUnion hf
    exact ⟨ZFSet.mem_sUnion.mpr ⟨w,hw,hz⟩,y,hy,w,hw,hf,hz⟩

theorem stageImage_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {s x f : ZFSet.{u}} (hs : s ∈ M) (hx : x ∈ M) (hf : f ∈ M) : stageImage s x f ∈ M := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hr := iterUnion_mem M hM hT.union hf 2
  have hd := (((defPairMem C 1 0 4).and (member_definable C 2 0)).existsMem 4).existsMem 1
  let e := cons x (cons f (fun _ => iterUnion 2 f))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i; exact hx; exact hf; exact hr
  exact binary_union_mem M hM hT.pairing hT.union hs
    (hd.sep_mem C e he (union_mem M hM hT.union hr))

theorem hierarchyGraph_of_mem_iff (M R d f : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hs : seed R ∈ M) (hdM : d ∈ M) (hfM : f ∈ M) (hd : Transitive d)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (definablePower (stage R x))) :
    HierarchyGraph M (seed R) d (iterUnion 2 f) f := by
  have hpair (x v : ZFSet.{u}) : ZFSet.pair x v ∈ f ↔ x ∈ d ∧ v = definablePower (stage R x) := by
    rw [hf]
    constructor
    · rintro ⟨y,hy,he⟩
      obtain ⟨rfl,hv⟩ := ZFSet.pair_inj.mp he
      exact ⟨hy,hv⟩
    · rintro ⟨hx,rfl⟩; exact ⟨x,hx,rfl⟩
  refine ⟨hd,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,_,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    have hp := (hpair x _).mpr ⟨hx,rfl⟩
    exact ⟨_,second_mem_doubleUnion hp,hp,fun v _ hv => (hpair x v).mp hv |>.2⟩
  · intro x hx v _ hv
    have he := (hpair x v).mp hv |>.2
    subst v
    have hA : stageImage (seed R) x f = stage R x := by
      apply ZFSet.ext; intro z
      rw [mem_stageImage,mem_stage]
      apply or_congr_right
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        rw [(hpair y w).mp hw |>.2] at hz
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hpair y _).mpr ⟨hd x hx y hy,rfl⟩,hz⟩
    refine ⟨stage R x,hA ▸ stageImage_mem M hM hT hs (hM d hdM x hx) hfM,?_,rfl⟩
    refine ⟨seed_subset_stage R x,?_,?_⟩
    · intro z hz
      rcases (mem_stage R x z).mp hz with hz|⟨y,hy,hz⟩
      · exact Or.inl hz
      · have hp := (hpair y _).mpr ⟨hd x hx y hy,rfl⟩
        exact Or.inr ⟨y,hy,_,second_mem_doubleUnion hp,hp,hz⟩
    · intro y hy w _ hw
      rw [(hpair y w).mp hw |>.2]
      exact definablePower_subset_stage R hy

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaParameterizedClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u
variable {M : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem SigmaDefinable.and (hP : SigmaDefinable M P) (hQ : SigmaDefinable M Q) :
    SigmaDefinable M (fun e => P e ∧ Q e) := by
  obtain ⟨p,d,hd,hp⟩ := hP
  obtain ⟨q,c,hc,hq⟩ := hQ
  refine ⟨.conj (p.rename (slotMap id (fun i => 2*i)))
    (q.rename (slotMap id (fun i => 2*i+1))),mix d c,?_,?_⟩
  · intro i; unfold mix; split <;> first | exact hd _ | exact hc _
  · intro e he
    rw [SigmaFormula.realize_conj,SigmaFormula.realize_rename,SigmaFormula.realize_rename]
    have hd' : mix d c ∘ (fun i => 2*i) = d := by funext i; simp
    have hc' : mix d c ∘ (fun i => 2*i+1) = c := by funext i; simp
    change p.Realize M (mix e (mix d c) ∘ slotMap id (fun i => 2*i)) ∧
      q.Realize M (mix e (mix d c) ∘ slotMap id (fun i => 2*i+1)) ↔ _
    rw [mix_slotMap,mix_slotMap,Function.comp_id,hd',hc',hp e he,hq e he]

end TuringRigidity.BoundedDefinability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_HierarchySyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u
variable {M : ZFSet.{u}}

theorem stageStep_definable (C : Context M) (s f r x A : ℕ) :
    Definable M (fun e => StageStep (e s) (e f) (e r) (e x) (e A)) := by
  have hn := defAllMem (defOr (member_definable C 0 (s+1))
    ((((defPairMem C 1 0 (f+3)).and (member_definable C 2 0)).existsMem (r+2)).existsMem (x+1))) A
  have hc := defAllMem (defAllMem (defImp (defPairMem C 1 0 (f+2))
    (defSubset C 0 (A+2))) (r+1)) x
  exact (defSubset C s A).and (hn.and hc)

theorem sigma_binary_relation (P : ZFSet.{u} → ZFSet.{u} → Prop)
    (h : SigmaDefinable M (fun e => P (e 1) (e 0))) :
    ∃ p : SigmaFormula, ∃ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ M) ∧
      ∀ x ∈ M, ∀ y ∈ M, p.Realize M (cons y (cons x a)) ↔ P x y := by
  obtain ⟨p,a,ha,hp⟩ := h
  let r : ℕ → ℕ := fun i => if i % 2 = 0 then (if i / 2 = 0 then 0 else 1) else i/2+2
  refine ⟨p.rename r,a,ha,?_⟩
  intro x hx y hy
  rw [SigmaFormula.realize_rename]
  have he : cons y (cons x a) ∘ r = mix (cons y (fun _ => x)) a := by
    apply parity_ext
    · intro n
      cases n with
      | zero => rfl
      | succ n => simp [r,show ¬ 2 * (n+1) ≤ 1 by omega]
    · intro n; simp [r,Nat.add_div]
  change p.Realize M (cons y (cons x a) ∘ r) ↔ _
  rw [he]
  exact hp (cons y (fun _ => x)) (by intro i; cases i; exact hy; exact hx)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementarySatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

theorem bounded_sat (p : Formula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fromBounded p).Sat (M : Set ZFSet) e ↔ p.Realize M e := by
  induction p generalizing e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp e) (ihq e)
  | neg p ih => exact not_congr (ih e)
  | existsMem i p ih =>
    simp only [fromBounded,SentenceForm.Sat,Formula.Realize,cons_zero,cons_succ]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => and_congr_right (fun _ => ih (cons x e)))

theorem sigma_sat (p : SigmaFormula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fromSigma p).Sat (M : Set ZFSet) e ↔ p.Realize M e := by
  induction p generalizing e with
  | bounded p => exact bounded_sat p M e
  | existsSet p ih =>
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (cons x e))

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel SentenceForm BoundedSetTheory TransitiveNameModel
universe u

theorem shifted_parameters (p : SentenceForm) (D : Set ZFSet.{u})
    (x a : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (p.rename parameterShift).Sat D (cons x (cons a e)) ↔ p.Sat D (cons x e) := by
  rw [sat_rename]
  have he : (fun i => cons x (cons a e) (parameterShift i)) = cons x e := by
    funext i; cases i <;> rfl
  rw [he]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleGroundReals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

theorem mem_groundReals (M x : ZFSet.{u}) :
    x ∈ groundReals M ↔ x ∈ M ∧ x ⊆ ZFSet.omega := by
  rw [groundReals,ZFSet.mem_sep,ZFSet.mem_powerset,and_comm]

theorem groundReals_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    groundReals M ∈ M := by
  obtain ⟨R,hR,hdef⟩ := internal_power M hM hT.powerSet (sourceT_omega_mem M hM hT)
  have heq : R = groundReals M := by
    apply ZFSet.ext; intro x
    exact (hdef x).trans (mem_groundReals M x).symm
  exact heq ▸ hR

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalHierarchyRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem internal_hierarchyGraph (M R d q : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) (x : ZFSet.{u}) (hx : x ∈ d) :
    ∃ f ∈ M, HierarchyGraph M (seed R) (_root_.OAI.TuringRigidity.BoundedSetTheory.hull d q x) (iterUnion 2 f) f := by
  let hP := hT.pairing
  let hU := hT.union
  let hS := hT.separation.finitePrefix.bounded
  let hR := hT.replacement.finitePrefix
  obtain ⟨p,e,he,hp⟩ := uniform_hierarchy_certificate M R d q hM hT hs hdM hqM hd hq
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have hxM := hM d hdM x hx
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) :
        p.Realize M (cons f (cons y e)) ↔
          ∃ r ∈ M, HierarchyGraph M (seed R) (_root_.OAI.TuringRigidity.BoundedSetTheory.hull d q y) r f :=
      hp y (hd x hx y hy) f hf
    obtain ⟨b,hb,hbdef⟩ := hR p e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M hM hU hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, HierarchyGraph M (seed R) (_root_.OAI.TuringRigidity.BoundedSetTheory.hull d q y) r f := by
      constructor
      · intro hf
        have hfM := hM b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (hd x hx y hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M hM hU hb
    have hg (z : ZFSet.{u}) : z ∈ g ↔
        ∃ y ∈ x, ∃ w ∈ _root_.OAI.TuringRigidity.BoundedSetTheory.hull d q y, z = ZFSet.pair w (definablePower (stage R w)) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,r,_,hfg⟩ := (hbg f).mp hf
        exact ⟨y,hy,(hfg.mem_iff z).mp hzf⟩
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M hM hU hf 2,hfg⟩,(hfg.mem_iff z).mpr ⟨w,hw,hz⟩⟩
    have hvalue : stageImage (seed R) x g = stage R x := by
      apply ZFSet.ext; intro z
      rw [mem_stageImage,mem_stage]
      apply or_congr_right
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨a,_,v,_,hp⟩ := (hg _).mp hw
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hg _).mpr
          ⟨y,hy,y,self_mem_hull d q (hd x hx y hy),rfl⟩,hz⟩
    have hvM : definablePower (stage R x) ∈ M := definablePower_mem M _ hM hT
      (hvalue ▸ stageImage_mem M hM hT hs hxM hgM)
    let f := g ∪ ({ZFSet.pair x (definablePower (stage R x))} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hP hU hgM
      (singleton_mem M hM hP (orderedPair_mem M hM hP hxM hvM))
    refine ⟨f,hfM,hierarchyGraph_of_mem_iff M R _ f hM hT hs
      (hull_mem M d q hM hS hdM hqM hxM) hfM (hull_transitive d q x hd) ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (definablePower (stage R x))} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,w,hw,hz⟩|hz)
      · exact ⟨w,(hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mpr
          (Or.inr ⟨y,hy,hw⟩),hz⟩
      · exact ⟨x,self_mem_hull d q hx,hz⟩
    · rintro ⟨w,hw,hz⟩
      rcases (hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mp hw with rfl|⟨y,hy,hw⟩
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,w,hw,hz⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalConstructibleHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem seed_mem (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) :
    seed R ∈ M := by
  obtain ⟨b,hb,hdef⟩ := collect_unionIterates M hM hT.pairing hT.union
    hT.replacement.finitePrefix (sourceT_omega_mem M hM hT)
    (singleton_mem M hM hT.pairing hR)
  have he : ZFSet.sUnion b = seed R := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sUnion,mem_seed]
    constructor
    · rintro ⟨a,ha,hz⟩
      obtain ⟨n,rfl⟩ := (hdef a).mp ha
      exact ⟨n,hz⟩
    · rintro ⟨n,hz⟩
      exact ⟨_,(hdef _).mpr ⟨n,rfl⟩,hz⟩
  exact he ▸ union_mem M hM hT.union hb

theorem internal_hierarchy_cover (M R o : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (ho : o ∈ M) :
    ∃ d ∈ M, ∃ f ∈ M, o ∈ d ∧
      HierarchyGraph M (seed R) d (iterUnion 2 f) f := by
  obtain ⟨c,hc,hct,hoc⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity ho
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hT.powerSet hc
  obtain ⟨f,hf,hfg⟩ := internal_hierarchyGraph M R c q hM hT (seed_mem M R hM hT hR)
    hc hq hct hqdef o hoc
  exact ⟨hull c q o,hull_mem M c q hM hT.separation.finitePrefix.bounded hc hq ho,
    f,hf,self_mem_hull c q hoc,hfg⟩

theorem stage_mem (M R o : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (ho : o ∈ M) : stage R o ∈ M := by
  obtain ⟨d,_,f,hf,hod,hfg⟩ := internal_hierarchy_cover M R o hM hT hR ho
  obtain ⟨v,hv,hfv,_⟩ := hfg.2.1.2 o hod
  have hvM : v ∈ M := hM _ (iterUnion_mem M hM hT.union hf 2) v hv
  rw [hfg.correct o hod v hv hfv] at hvM
  exact hM _ hvM _ (self_mem_definablePower (stage R o))

theorem level_mem (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : level R o ∈ M :=
  stage_mem M R o.toZFSet hM hT hR ho

theorem level_subset_model (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : level R o ⊆ M :=
  fun x hx => hM _ (level_mem M R hM hT hR o ho) x hx

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_CollectionHierarchyInternal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u
theorem seed_mem_collection (M R : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hR : R ∈ M) :
    seed R ∈ M := by
  obtain ⟨b,hb,hdef⟩ := collect_unionIterates M C.transitive C.pairing C.union
    hRep (C.omega_mem)
    (singleton_mem M C.transitive C.pairing hR)
  have he : ZFSet.sUnion b = seed R := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sUnion,mem_seed]
    constructor
    · rintro ⟨a,ha,hz⟩
      obtain ⟨n,rfl⟩ := (hdef a).mp ha
      exact ⟨n,hz⟩
    · rintro ⟨n,hz⟩
      exact ⟨_,(hdef _).mpr ⟨n,rfl⟩,hz⟩
  exact he ▸ union_mem M C.transitive C.union hb

theorem internal_hierarchy_cover_collection (M R o : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (hR : R ∈ M) (ho : o ∈ M) :
    ∃ d ∈ M, ∃ f ∈ M, o ∈ d ∧
      HierarchyGraph M (seed R) d (iterUnion 2 f) f := by
  obtain ⟨c,hc,hct,hoc⟩ := internal_transitive_container M C.transitive C.pairing C.union
    C.separation hRep C.infinity ho
  obtain ⟨q,hq,hqdef⟩ := internal_power M C.transitive C.power hc
  obtain ⟨f,hf,hfg⟩ := internal_hierarchyGraph_collection M R c q C hRep hColl (seed_mem_collection M R C hRep hR)
    hc hq hct hqdef o hoc
  exact ⟨hull c q o,hull_mem M c q C.transitive C.separation hc hq ho,
    f,hf,self_mem_hull c q hoc,hfg⟩

theorem stage_mem_collection (M R o : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (hR : R ∈ M) (ho : o ∈ M) : stage R o ∈ M := by
  obtain ⟨d,_,f,hf,hod,hfg⟩ := internal_hierarchy_cover_collection M R o C hRep hColl hR ho
  obtain ⟨v,hv,hfv,_⟩ := hfg.2.1.2 o hod
  have hvM : v ∈ M := C.transitive _ (iterUnion_mem M C.transitive C.union hf 2) v hv
  rw [hfg.correct o hod v hv hfv] at hvM
  exact C.transitive _ hvM _ (self_mem_definablePower (stage R o))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

theorem relativeModel_subset (M R : ZFSet.{u}) : relativeModel M R ⊆ M :=
  fun _ hx => (ZFSet.mem_sep.mp hx).1

theorem InRelativeModel.mem_ground {M R x : ZFSet.{u}}
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M)
    (hx : InRelativeModel M R x) : x ∈ M := by
  obtain ⟨o,ho,hx⟩ := hx
  exact level_subset_model M R hM hT hR o ho hx

theorem mem_relativeModel (M R x : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) :
    x ∈ relativeModel M R ↔ InRelativeModel M R x := by
  rw [relativeModel,ZFSet.mem_sep]
  exact ⟨And.right,fun hx => ⟨hx.mem_ground hM hT hR,hx⟩⟩

theorem InRelativeModel.transitive {M R x y : ZFSet.{u}}
    (hx : InRelativeModel M R x) (hy : y ∈ x) : InRelativeModel M R y := by
  obtain ⟨o,ho,hx⟩ := hx
  exact ⟨o,ho,level_transitive R o x hx y hy⟩

theorem relativeModel_transitive (M R : ZFSet.{u}) (hM : Transitive M) :
    Transitive (relativeModel M R) := by
  intro x hx y hy
  obtain ⟨hxM,hx⟩ := ZFSet.mem_sep.mp hx
  exact ZFSet.mem_sep.mpr ⟨hM x hxM y hy,hx.transitive hy⟩

theorem internal_ordinal_zero (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    (0 : Ordinal.{u}).toZFSet ∈ M := by
  rw [Ordinal.toZFSet_zero]
  exact hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero

theorem internal_ordinal_succ (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : (o+1).toZFSet ∈ M := by
  rw [Ordinal.toZFSet_add_one]
  have eq : insert o.toZFSet o.toZFSet = ({o.toZFSet} : ZFSet.{u}) ∪ o.toZFSet := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
  rw [eq]
  exact binary_union_mem M hM hT.pairing hT.union
    (singleton_mem M hM hT.pairing ho) ho

theorem internal_ordinal_max (M : ZFSet.{u}) {i j : Ordinal.{u}}
    (hi : i.toZFSet ∈ M) (hj : j.toZFSet ∈ M) : (max i j).toZFSet ∈ M := by
  rcases le_total i j with h|h
  · simpa only [max_eq_right h] using hj
  · simpa only [max_eq_left h] using hi

theorem parameter_in_relativeModel (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) : InRelativeModel M R R :=
  ⟨0,internal_ordinal_zero M hM hT,level_zero R ▸ parameter_mem_seed R⟩

theorem level_in_relativeModel (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) :
    InRelativeModel M R (level R o) :=
  ⟨o+1,internal_ordinal_succ M hM hT o ho,
    level_mem_level R (lt_add_one o)⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel
universe u

theorem ground_seed_shape (M : ZFSet.{u}) (hM : Transitive M) :
    seed (groundReals M) = insert (groundReals M) (groundReals M) := by
  let R := groundReals M
  have htrans : Transitive (insert R R) := by
    intro a ha b hb
    rcases ZFSet.mem_insert_iff.mp ha with rfl|ha
    · exact ZFSet.mem_insert_iff.mpr (Or.inr hb)
    · obtain ⟨haM,haω⟩ := (mem_groundReals M a).mp ha
      have hbω := haω hb
      have hbsub : b ⊆ ZFSet.omega := fun z hz => omega_transitive b hbω z hz
      exact ZFSet.mem_insert_iff.mpr (Or.inr ((mem_groundReals M b).mpr ⟨hM a haM b hb,hbsub⟩))
  apply ZFSet.ext; intro x
  constructor
  · exact fun hx => seed_minimal R _ htrans (ZFSet.mem_insert R R) hx
  · intro hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · exact parameter_mem_seed R
    · exact parameter_subset_seed R hx

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformHierarchyStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem HierarchyGraph.stageStep_iff {M R d r f : ZFSet.{u}}
    (h : HierarchyGraph M (seed R) d r f) (x : ZFSet.{u}) (hx : x ∈ d) (A : ZFSet.{u}) :
    StageStep (seed R) f r x A ↔ A = stage R x := by
  constructor
  · intro hs
    apply ZFSet.ext; intro z
    rw [mem_stage]
    constructor
    · intro hz
      rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
      · exact Or.inl hz
      · rw [h.correct y (h.1 x hx y hy) w hw hfw] at hz
        exact Or.inr ⟨y,hy,hz⟩
    · rintro (hz|⟨y,hy,hz⟩)
      · exact hs.1 hz
      · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1 x hx y hy)
        rw [← h.correct y (h.1 x hx y hy) w hw hfw] at hz
        exact hs.2.2 y hy w hw hfw hz
  · rintro rfl
    refine ⟨seed_subset_stage R x,?_,?_⟩
    · intro z hz
      rcases (mem_stage R x z).mp hz with hz|⟨y,hy,hz⟩
      · exact Or.inl hz
      · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1 x hx y hy)
        rw [← h.correct y (h.1 x hx y hy) w hw hfw] at hz
        exact Or.inr ⟨y,hy,w,hw,hfw,hz⟩
    · intro y hy w hw hfw
      rw [h.correct y (h.1 x hx y hy) w hw hfw]
      exact definablePower_subset_stage R hy

theorem stage_sigmaDefinable (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) : SigmaDefinable M (fun e => e 0 = stage R (e 1)) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hg : SigmaDefinable M (fun e => HierarchyGraph M (seed R) (e 2) (e 0) (e 1)) := by
    have h := hierarchyGraph_sigmaDefinable hM hT 0 3 1 2
    have eq := (equal_param (seed_mem M R hM hT hR) 0).toSigma hM
    exact (eq.and h).existsSet.congr (fun e _ => by simp [seed_mem M R hM hT hR])
  have hs : SigmaDefinable M (fun e => StageStep (seed R) (e 1) (e 0) (e 4) (e 3)) := by
    have h := (stageStep_definable C 0 2 1 5 4).toSigma hM
    have eq := (equal_param (seed_mem M R hM hT hR) 0).toSigma hM
    exact (eq.and h).existsSet.congr (fun e _ => by simp [seed_mem M R hM hT hR])
  have hc := ((member_definable C 4 2).toSigma hM).and (hg.and hs)
  apply hc.existsSet.existsSet.existsSet.congr
  intro e he
  change (∃ d ∈ M, ∃ f ∈ M, ∃ r ∈ M, e 1 ∈ d ∧
    HierarchyGraph M (seed R) d r f ∧ StageStep (seed R) f r (e 1) (e 0)) ↔ _
  constructor
  · rintro ⟨d,_,f,_,r,_,hx,hg,hs⟩
    exact (hg.stageStep_iff (e 1) hx (e 0)).mp hs
  · intro hv
    obtain ⟨d,hd,f,hf,hx,hg⟩ := internal_hierarchy_cover M R (e 1) hM hT hR (he 1)
    exact ⟨d,hd,f,hf,_,iterUnion_mem M hM hT.union hf 2,hx,hg,
      (hg.stageStep_iff (e 1) hx (e 0)).mpr hv⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModelSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
universe u

theorem eval_ordinalFormula (i : ℕ) (e : ℕ → ZFSet.{u}) :
    (ordinalFormula i).Eval e ↔ (e i).IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  simp only [ordinalFormula,Formula.Eval,Formula.eval_transitive,
    Formula.eval_allMem,cons_zero]
  rfl

theorem ordinal_definable {M : ZFSet.{u}} (C : Context M) (i : ℕ) :
    Definable M (fun e => (e i).IsOrdinal) :=
  ⟨ordinalFormula (2*i),fun _ => ZFSet.omega,fun _ => C.omega_mem,
    fun e => by rw [eval_ordinalFormula,mix_even]⟩

theorem relativeLevel_sigmaDefinable (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) :
    SigmaDefinable M (fun e => (e 0).IsOrdinal ∧ e 1 ∈ stage R (e 0)) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  have h := (stage_sigmaDefinable M R hM hT hR).and
    (((ordinal_definable C 1).toSigma hM).and ((member_definable C 2 0).toSigma hM))
  apply h.existsSet.congr
  intro e he
  change (∃ A ∈ M, A = stage R (e 0) ∧ (e 0).IsOrdinal ∧ e 1 ∈ A) ↔ _
  constructor
  · rintro ⟨A,_,rfl,ho,hx⟩; exact ⟨ho,hx⟩
  · rintro ⟨ho,hx⟩
    exact ⟨_,stage_mem M R (e 0) hM hT hR (he 0),rfl,ho,hx⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions InternalRank
universe u

theorem relative_level_bound (M R a : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (ha : a ∈ M)
    (h : ∀ x ∈ a, InRelativeModel M R x) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ a ⊆ level R o := by
  obtain ⟨p,e,he,hp⟩ := sigma_binary_relation
    (fun x o : ZFSet.{u} => o.IsOrdinal ∧ x ∈ stage R o)
    (relativeLevel_sigmaDefinable M R hM hT hR)
  obtain ⟨W,hW,hbound⟩ := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
    p e he a ha (by
      intro x hx
      obtain ⟨o,ho,hxo⟩ := h x hx
      exact ⟨o.toZFSet,ho,(hp x (hM a ha x hx) o.toZFSet ho).mpr
        ⟨ZFSet.isOrdinal_toZFSet o,hxo⟩⟩)
  have hr : W.rank.toZFSet ∈ M := by
    rw [← rankSet_eq_ordinal]
    exact rankSet_mem_ground M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hW
  refine ⟨W.rank,hr,?_⟩
  intro x hx
  obtain ⟨o,ho,hxo⟩ := hbound x hx
  obtain ⟨hord,hxo⟩ := (hp x (hM a ha x hx) o (hM W hW o ho)).mp hxo
  have hxl : x ∈ level R o.rank := by
    change x ∈ stage R o.rank.toZFSet
    rwa [hord.toZFSet_rank_eq]
  exact level_mono R (ZFSet.rank_lt_of_mem ho).le hxl

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModelClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

theorem finite_parameters_in_relative_level (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (e : ℕ → ZFSet.{u}) (n : ℕ)
    (he : ∀ i, i < n → InRelativeModel M R (e i)) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ ∀ i, i < n → e i ∈ level R o := by
  induction n with
  | zero => exact ⟨0,internal_ordinal_zero M hM hT,fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  | succ n ih =>
    obtain ⟨o,ho,hoe⟩ := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
    obtain ⟨p,hp,hpe⟩ := he n (Nat.lt_succ_self n)
    refine ⟨max o p,internal_ordinal_max M ho hp,fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
    · exact level_mono R (le_max_left o p) (hoe i hi)
    · exact level_mono R (le_max_right o p) hpe

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_CheckedDefSuccessor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem CheckedDefSuccessor.sound {N A D : ZFSet.{u}}
    (hf : ∀ p : SentenceForm, family p ∈ N)
    (hs : ∀ p : SentenceForm, supportGraph p ∈ N)
    (h : CheckedDefSuccessor N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) A D) :
    D = definablePower A := by
  obtain ⟨Q,_,B,_,hb,G,_,T,_,H,_,Z,_,hd⟩ := h
  exact hd.exact (fun p => (hb.1 _).mpr ⟨hf p,family_subset_omega p⟩)
    (fun p => (hb.2 _).mpr ⟨hs p,supportGraph_subset p⟩)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeSigmaWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
open ElementaryModel SentenceForm
universe u

theorem relative_level_subset (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) {o : Ordinal.{u}} (ho : o.toZFSet ∈ M) :
    level R o ⊆ relativeModel M R :=
  fun x hx => (mem_relativeModel M R x hM hT hR).mpr ⟨o,ho,hx⟩

theorem relative_sigma_level_witness (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (i : Ordinal.{u}) (hi : i.toZFSet ∈ M)
    (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ n, e n ∈ level R i)
    (hφ : φ.Realize (relativeModel M R) e) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ level R i ⊆ level R o ∧
      φ.Realize (level R o) e := by
  obtain ⟨xs,hlen,hxs,hmat⟩ := (φ.realize_iff_prefix _ e).mp hφ
  have hsM := FiniteTuple.elements_mem M hM hT.pairing hT.union
    (by simpa only [Ordinal.toZFSet_zero] using internal_ordinal_zero M hM hT) xs
    (fun x hx => relativeModel_subset M R (hxs x hx))
  obtain ⟨j,hj,hjs⟩ := relative_level_bound M R (FiniteTuple.elements xs) hM hT hR hsM
    (fun x hx => (mem_relativeModel M R x hM hT hR).mp
      (hxs x ((FiniteTuple.mem_elements x xs).mp hx)))
  have hlist : ∀ x ∈ xs, x ∈ level R (max i j) := fun x hx =>
    level_mono R (le_max_right i j) (hjs ((FiniteTuple.mem_elements x xs).mpr hx))
  have heL : ∀ n, e n ∈ level R (max i j) := fun n => level_mono R (le_max_left i j) (he n)
  have heN := fun n => relative_level_subset M R hM hT hR hi (he n)
  refine ⟨max i j,internal_ordinal_max M hi hj,level_mono R (le_max_left i j),
    (φ.realize_iff_prefix _ e).mpr ⟨xs,hlen,hlist,?_⟩⟩
  exact (φ.matrix.absolute _ (level_transitive R _) _ (SigmaFormula.feed_mem xs e _ hlist heL)).mpr
    ((φ.matrix.absolute _ (relativeModel_transitive M R hM) _
      (SigmaFormula.feed_mem xs e _ hxs heN)).mp hmat)

theorem sigmaDefinable_request_bound {M : ZFSet.{u}}
    {P : (ℕ → ZFSet.{u}) → Prop} (h : SigmaDefinable M P)
    (hM : Transitive M) (hT : SourceT M) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ W ∈ M, ∀ x ∈ a, (∃ y ∈ M, P (cons y (cons x e))) →
      ∃ y ∈ W, P (cons y (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  let q := (p.rename bindSlots).rename (liftMap bindSlots)
  have hm : ∀ i, mix e d i ∈ M := by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _
  have hq (x y : ZFSet.{u}) (hx : x ∈ M) (hy : y ∈ M) :
      q.Realize M (cons y (cons x (mix e d))) ↔ P (cons y (cons x e)) := by
    dsimp only [q]
    rw [SigmaFormula.realize_rename]
    have eq : (fun n => cons y (cons x (mix e d)) (liftMap bindSlots n)) =
        cons y (mix (cons x e) d) := by
      funext n; cases n with
      | zero => rfl
      | succ n => exact congrFun (bind_mix x e d) n
    rw [eq,SigmaFormula.realize_rename]
    change p.Realize M (cons y (mix (cons x e) d) ∘ bindSlots) ↔ _
    rw [bind_mix]
    exact hp _ (by
      intro i
      rcases i with _|i; exact hy
      rcases i with _|i; exact hx
      exact he i)
  obtain ⟨W,hW,hw⟩ := internal_sigma_request_bound M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice q (mix e d) hm ha
  refine ⟨W,hW,?_⟩
  intro x hx hxy
  have hxM := hM a ha x hx
  obtain ⟨y,hy,hqxy⟩ := hw x hx (by
    obtain ⟨y,hy,hxy⟩ := hxy
    exact ⟨y,hy,(hq x y hxM hy).mpr hxy⟩)
  exact ⟨y,hy,(hq x y hxM (hM W hW y hy)).mp hqxy⟩

theorem relative_sigma_request_definable (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (φ : SigmaFormula) :
    SigmaDefinable M (fun e => (e 0).IsOrdinal ∧ e 2 ⊆ stage R (e 0) ∧
      φ.Realize (stage R (e 0)) (cons (e 1) (fun i => e (i+3)))) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  let v : ℕ → ℕ := fun n => match n with | 0 => 4 | k+1 => 2*(k+4)
  have hs : Definable M (fun e => φ.Realize (e 0) (cons (e 2) (fun i => e (i+4)))) := by
    refine ⟨setBounded (fromSigma φ) 0 v,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e
    rw [setBounded_eval,show mix e (fun _ => ZFSet.omega) 0 = e 0 from rfl,sigma_sat]
    have eq : (fun i => mix e (fun _ => ZFSet.omega) (v i)) =
        cons (e 2) (fun i => e (i+4)) := by
      funext i; cases i with
      | zero => exact mix_even e (fun _ => ZFSet.omega) 2
      | succ i => simp [v]
    rw [eq]
  have h := (stage_sigmaDefinable M R hM hT hR).and
    (((ordinal_definable C 1).toSigma hM).and
      (((SentenceCoding.defSubset C 3 0).toSigma hM).and (hs.toSigma hM)))
  apply h.existsSet.congr
  intro e he
  change (∃ A ∈ M, A = stage R (e 0) ∧ (e 0).IsOrdinal ∧ e 2 ⊆ A ∧
    φ.Realize A (cons (e 1) (fun i => e (i+3)))) ↔ _
  constructor
  · rintro ⟨A,_,rfl,ho,ht,hφ⟩; exact ⟨ho,ht,hφ⟩
  · rintro ⟨ho,ht,hφ⟩
    exact ⟨_,stage_mem M R (e 0) hM hT hR (he 0),rfl,ho,ht,hφ⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeSigmaReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel InternalRank
universe u

theorem relative_sigma_reflection (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (i : Ordinal.{u}) (hi : i.toZFSet ∈ M)
    (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ n, e n ∈ level R i)
    (a : ZFSet.{u}) (ha : a ∈ level R i) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ level R i ⊆ level R o ∧
      ∀ x ∈ a, φ.Realize (relativeModel M R) (cons x e) ↔
        φ.Realize (level R o) (cons x e) := by
  have ht := level_mem M R hM hT hR i hi
  have haM := hM _ ht a ha
  have heM : ∀ n, cons (level R i) e n ∈ M := by
    intro n; cases n; exact ht; exact hM _ ht _ (he _)
  obtain ⟨W,hW,hw⟩ := sigmaDefinable_request_bound
    (relative_sigma_request_definable M R hM hT hR φ) hM hT (cons (level R i) e) heM haM
  have hr : W.rank.toZFSet ∈ M := by
    rw [← rankSet_eq_ordinal]
    exact rankSet_mem_ground M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hW
  let o := max i W.rank
  have ho : o.toZFSet ∈ M := internal_ordinal_max M hi hr
  have hio : level R i ⊆ level R o := level_mono R (le_max_left i W.rank)
  refine ⟨o,ho,hio,?_⟩
  intro x hx
  have heI : ∀ n, cons x e n ∈ level R i := by
    intro n; cases n; exact level_transitive R i a ha x hx; exact he _
  constructor
  · intro hφ
    obtain ⟨j,hj,hij,hφj⟩ := relative_sigma_level_witness M R hM hT hR i hi φ (cons x e) heI hφ
    obtain ⟨z,hz,hord,htz,hφz⟩ := hw x hx ⟨j.toZFSet,hj,ZFSet.isOrdinal_toZFSet j,hij,hφj⟩
    change z.IsOrdinal at hord
    change level R i ⊆ stage R z at htz
    change φ.Realize (stage R z) (cons x e) at hφz
    have heq : stage R z = level R z.rank := by
      change stage R z = stage R z.rank.toZFSet
      rw [hord.toZFSet_rank_eq]
    rw [heq] at htz hφz
    exact φ.transitive_upward (level_transitive R _) (level_transitive R _)
      (level_mono R ((ZFSet.rank_lt_of_mem hz).le.trans (le_max_right i W.rank)))
      (cons x e) (fun n => htz (heI n)) hφz
  · intro hφ
    exact φ.transitive_upward (level_transitive R o) (relativeModel_transitive M R hM)
      (relative_level_subset M R hM hT hR ho) (cons x e) (fun n => hio (heI n)) hφ

theorem relative_sigma_parameter_bound (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (φ : SigmaFormula) (e : ℕ → ZFSet.{u})
    (he : ∀ n, InRelativeModel M R (e n)) (a : ZFSet.{u})
    (ha : InRelativeModel M R a) :
    ∃ i : Ordinal.{u}, i.toZFSet ∈ M ∧ a ∈ level R i ∧
      ∃ e' : ℕ → ZFSet.{u}, (∀ n, e' n ∈ level R i) ∧ (∀ n, n < φ.scope → e' n = e n) ∧
        ∀ N x : ZFSet.{u}, φ.Realize N (cons x e') ↔ φ.Realize N (cons x e) := by
  obtain ⟨i,hi,hia⟩ := ha
  obtain ⟨j,hj,hje⟩ := finite_parameters_in_relative_level M R hM hT e φ.scope (fun n _ => he n)
  let e' := fun n => if n < φ.scope then e n else a
  have haL : a ∈ level R (max i j) := level_mono R (le_max_left i j) hia
  refine ⟨max i j,internal_ordinal_max M hi hj,haL,e',?_,?_,?_⟩
  · intro n
    dsimp [e']; split
    next hn => exact level_mono R (le_max_right i j) (hje n hn)
    next => exact haL
  · intro n hn; exact ite_eq_left hn
  · intro N x
    apply φ.realize_congr; intro n hn
    cases n with
    | zero => rfl
    | succ n => exact ite_eq_left (show n < φ.scope by omega)

theorem relativeModel_sigma_collection (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : SigmaCollection (relativeModel M R) := by
  intro φ e he a ha htotal
  obtain ⟨i,hi,hia,e',he',heq,hcongr⟩ := relative_sigma_parameter_bound M R hM hT
    (.existsSet φ) e (fun n => (mem_relativeModel M R _ hM hT hR).mp (he n)) a
    ((mem_relativeModel M R _ hM hT hR).mp ha)
  obtain ⟨o,ho,hio,hφ⟩ := relative_sigma_reflection M R hM hT hR i hi (.existsSet φ) e' he' a hia
  have hlevel := relative_level_subset M R hM hT hR ho
  refine ⟨level R o,(mem_relativeModel M R _ hM hT hR).mpr
    (level_in_relativeModel M R hM hT o ho),?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := (hφ x hx).mp ((hcongr _ x).mpr (htotal x hx))
  have hup : φ.Realize (relativeModel M R) (cons y (cons x e')) :=
    φ.transitive_upward (level_transitive R o) (relativeModel_transitive M R hM)
      hlevel (cons y (cons x e')) (by
        intro n; rcases n with _|n; exact hy
        rcases n with _|n; exact hio (level_transitive R i a hia x hx)
        exact hio (he' n)) hxy
  refine ⟨y,hy,?_⟩
  apply (φ.realize_congr (relativeModel M R) (cons y (cons x e')) (cons y (cons x e)) ?_).mp hup
  intro n hn
  rcases n with _|n; rfl
  rcases n with _|n; rfl
  exact heq n (by change n < φ.scope-1; omega)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeSigmaSchemas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

theorem relativeModel_sigma_separation (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : SigmaSeparation (relativeModel M R) := by
  intro φ e he a ha
  let N := relativeModel M R
  obtain ⟨i,hi,hia,e',he',_,hcongr⟩ := relative_sigma_parameter_bound M R hM hT φ e
    (fun n => (mem_relativeModel M R _ hM hT hR).mp (he n)) a
    ((mem_relativeModel M R _ hM hT hR).mp ha)
  obtain ⟨o,ho,hio,hφ⟩ := relative_sigma_reflection M R hM hT hR i hi φ e' he' a hia
  let A := level R o
  let ψ := SentenceForm.conj (.member 0 1) ((fromSigma φ).rename parameterShift)
  have haA : a ∈ A := hio hia
  have hψ := separation_mem_definablePower A ψ (cons a e') (by
    intro n _; cases n; exact haA; exact hio (he' _))
  let b := a.sep (fun x => φ.Realize N (cons x e))
  have eq : A.sep (fun x => ψ.Sat (A : Set ZFSet) (cons x (cons a e'))) = b := by
    apply ZFSet.ext; intro x
    simp only [b,ZFSet.mem_sep,ψ,Sat,cons_zero,cons_succ,shifted_parameters,sigma_sat]
    constructor
    · rintro ⟨_,hxa,hψ⟩
      exact ⟨hxa,(hcongr N x).mp ((hφ x hxa).mpr hψ)⟩
    · rintro ⟨hxa,hψ⟩
      exact ⟨level_transitive R o a haA x hxa,hxa,(hφ x hxa).mp ((hcongr N x).mpr hψ)⟩
  have hb : b ∈ N := by
    apply (mem_relativeModel M R b hM hT hR).mpr
    refine ⟨o+1,internal_ordinal_succ M hM hT o ho,?_⟩
    rw [level_succ,← eq]
    exact hψ
  exact ⟨b,hb,fun _ _ => ZFSet.mem_sep⟩

theorem replacementImageFormula_spec (φ : SigmaFormula) (N a y : ZFSet.{u})
    (hN : Transitive N) (ha : a ∈ N) (e : ℕ → ZFSet.{u}) :
    (replacementImageFormula φ).Realize N (cons y (cons a e)) ↔
      ∃ x ∈ a, φ.Realize N (cons y (cons x e)) := by
  simp only [replacementImageFormula,SigmaFormula.Realize,SigmaFormula.realize_andBounded,
    Formula.Realize,cons_zero,cons_succ,SigmaFormula.realize_rename]
  have eq (x : ZFSet.{u}) : (fun i => cons x (cons y (cons a e)) (replacementImageVars i)) =
      cons y (cons x e) := by
    funext i; rcases i with _|i; rfl
    rcases i with _|i <;> rfl
  simp only [eq]
  exact ⟨fun ⟨x,_,hx,hφ⟩ => ⟨x,hx,hφ⟩,
    fun ⟨x,hx,hφ⟩ => ⟨x,hN a ha x hx,hx,hφ⟩⟩

theorem relativeModel_sigma_replacement (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : SigmaReplacement (relativeModel M R) := by
  intro φ e he a ha htotal
  let N := relativeModel M R
  have hN := relativeModel_transitive M R hM
  obtain ⟨W,hW,hw⟩ := relativeModel_sigma_collection M R hM hT hR φ e he a ha
    (fun x hx => by obtain ⟨y,hy,hφ,_⟩ := htotal x hx; exact ⟨y,hy,hφ⟩)
  obtain ⟨b,hb,hbdef⟩ := relativeModel_sigma_separation M R hM hT hR
    (replacementImageFormula φ) (cons a e) (by intro n; cases n; exact ha; exact he _) W hW
  refine ⟨b,hb,?_⟩
  intro y hy
  rw [hbdef y hy,replacementImageFormula_spec φ N a y hN ha e]
  constructor
  · exact And.right
  · rintro ⟨x,hx,hφ⟩
    obtain ⟨z,hz,hφz⟩ := hw x hx
    obtain ⟨w,hw,_,hu⟩ := htotal x hx
    have hyz : y = z := (hu y hy hφ).trans (hu z (hN W hW z hz) hφz).symm
    exact ⟨hyz ▸ hz,x,hx,hφ⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_CheckedHierarchySyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem CheckedHierarchyGraph.sound {N s d r f : ZFSet.{u}}
    (hf : ∀ p : SentenceForm, family p ∈ N)
    (hs : ∀ p : SentenceForm, supportGraph p ∈ N)
    (h : CheckedHierarchyGraph N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) s d r f) :
    HierarchyGraph N s d r f := by
  refine ⟨h.1,h.2.1,?_⟩
  intro x hx v hv hpair
  obtain ⟨A,hA,hstep,hdef⟩ := h.2.2 x hx v hv hpair
  exact ⟨A,hA,hstep,hdef.sound hf hs⟩

theorem CheckedHierarchyGraph.stage_exact {N R d r f x A : ZFSet.{u}}
    (hf : ∀ p : SentenceForm, family p ∈ N)
    (hs : ∀ p : SentenceForm, supportGraph p ∈ N)
    (h : CheckedHierarchyGraph N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega)
      (seed R) d r f) (hx : x ∈ d) (hstep : StageStep (seed R) f r x A) :
    A = stage R x :=
  ((h.sound hf hs).stageStep_iff x hx A).mp hstep

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeHierarchyInternal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem relative_internal_hierarchy_cover (M x : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (hx : x ∈ relativeModel M (groundReals M)) :
    ∃ d ∈ relativeModel M (groundReals M), ∃ f ∈ relativeModel M (groundReals M),
      x ∈ d ∧ HierarchyGraph (relativeModel M (groundReals M)) (seed (groundReals M))
        d (iterUnion 2 f) f := by
  have hR := groundReals_mem M hM hT
  exact internal_hierarchy_cover_collection _ _ x (ground_relative_context M hM hT)
    (relativeModel_sigma_replacement M _ hM hT hR)
    (relativeModel_sigma_collection M _ hM hT hR)
    ((mem_relativeModel M _ _ hM hT hR).mpr (parameter_in_relativeModel M _ hM hT)) hx

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_SeedBoundStageSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem SeedBoundStage.sound {M N x A : ZFSet.{u}} (hM : Transitive M)
    (hf : ∀ p : SentenceForm, family p ∈ N)
    (hs : ∀ p : SentenceForm, supportGraph p ∈ N)
    (h : SeedBoundStage N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega)
      (groundReals M) x A) : A = stage (groundReals M) x := by
  obtain ⟨s,_,d,_,f,_,r,_,he,hx,hg,hstep⟩ := h
  have heq : s = seed (groundReals M) := he.trans (ground_seed_shape M hM).symm
  rw [heq] at hg hstep
  exact hg.stage_exact hf hs hx hstep

theorem seed_bound_stage_at_levels_oai (M x : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hx : x ∈ relativeModel M (groundReals M)) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
        x ∈ level (groundReals M) δ ∧ stage (groundReals M) x ∈ level (groundReals M) δ ∧
        ∀ A : ZFSet.{u}, SeedBoundStage (level (groundReals M) δ) ZFSet.omega
          (ZFSet.prod ZFSet.omega ZFSet.omega) (groundReals M) x A ↔ A = stage (groundReals M) x := by
  let R := groundReals M
  have hR := groundReals_mem M hM hT
  have C := ground_relative_context M hM hT
  have hRep := relativeModel_sigma_replacement M R hM hT hR
  have hColl := relativeModel_sigma_collection M R hM hT hR
  have hRN : R ∈ relativeModel M R :=
    (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
  have hs := seed_mem_collection _ R C hRep hRN
  obtain ⟨d,hd,f,hf,hxd,hg⟩ := relative_internal_hierarchy_cover M x hM hT hx
  have hr := iterUnion_mem _ C.transitive C.union hf 2
  obtain ⟨α,hα,hαspec⟩ := hierarchy_checked_at_levels M (seed R) d _ f hM hT hs hd hr hf hg
  have hA := stage_mem_collection _ R x C hRep hColl hRN hx
  obtain ⟨β,hβ,hβA⟩ := (mem_relativeModel M R _ hM hT hR).mp hA
  refine ⟨max α β,internal_ordinal_max M hα hβ,?_⟩
  intro δ hδ hle
  obtain ⟨hsL,hdL,hrL,hfL,_,_,hfamily,hsupport,hchecked⟩ :=
    hαspec δ hδ ((le_max_left α β).trans hle)
  have hxL := level_transitive R δ d hdL x hxd
  refine ⟨hxL,level_mono R ((le_max_right α β).trans hle) hβA,?_⟩
  intro A
  constructor
  · exact SeedBoundStage.sound hM hfamily hsupport
  · rintro rfl
    exact ⟨seed R,hsL,d,hdL,f,hfL,_,hrL,ground_seed_shape M hM,hxd,hchecked,
      (hg.stageStep_iff x hxd _).mpr rfl⟩

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution.{u} : type_of% @OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels_oai.{u} := @OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels_oai.{u}

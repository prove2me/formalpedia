-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.internal_defSystem_of_context
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:15:04.801955+00:00
-- url     : https://prove2.me/submissions/3360357e-5c94-479e-be64-5a6a3d0797bc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A006
import Definitions.Def_OAIQ064A007

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

end SentenceForm

end TuringRigidity.ElementaryModel

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

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleSatisfaction
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
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
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem tupleGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ M) : tupleGraph v ∈ M := by
  have hn (k : ℕ) : natSet.{u} k ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨k,rfl⟩)
  exact finite_range_mem M hM hP hU (hn 0) n _
    (fun i => orderedPair_mem M hM hP (hn i.val) (hv i))

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

theorem tupleFormula_spec (o A Q t : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega)
    (hQ : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ e A) → tupleGraph v ∈ e Q) :
    (tupleFormula o A Q t).Eval e ↔ e t ∈ tupleSpace (e A) := by
  simp only [tupleFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_functionGraph,
    cons_zero,cons_succ]
  rw [ho,mem_tupleSpace]
  constructor
  · rintro ⟨n,hn,g,_,ht,hg⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨v,hv,rfl⟩ := functionGraph_tuple (e A) g n hg
    exact ⟨n,v,hv,ht⟩
  · rintro ⟨n,v,hv,ht⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hQ n v hv,ht,
      tupleGraph_function (e A) v hv⟩

end TuringRigidity.RelativeConstructible

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelIteration
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section

theorem finiteGraph_zero (f : ℕ → ZFSet.{u}) : finiteGraph 0 f = ∅ := by
  apply ZFSet.ext
  intro z
  simp only [mem_finiteGraph,Nat.not_lt_zero,false_and,exists_false,ZFSet.notMem_empty]

theorem finiteGraph_succ (n : ℕ) (f : ℕ → ZFSet.{u}) :
    finiteGraph (n+1) f = insert (ZFSet.pair (natSet n) (f n)) (finiteGraph n f) := by
  apply ZFSet.ext
  intro z
  simp only [mem_finiteGraph,ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨i,hi,he⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · exact Or.inr ⟨i,hi,he⟩
    · exact Or.inl he
  · rintro (he|⟨i,hi,he⟩)
    · exact ⟨n,Nat.lt_succ_self n,he⟩
    · exact ⟨i,Nat.lt_succ_of_lt hi,he⟩

theorem finiteGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    (n : ℕ) (f : ℕ → ZFSet.{u}) (hf : ∀ i < n, f i ∈ M) : finiteGraph n f ∈ M := by
  induction n with
  | zero =>
    rw [finiteGraph_zero]
    exact hM _ hω _ ZFSet.omega_zero
  | succ n ih =>
    rw [finiteGraph_succ]
    have hn := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
    have hp := orderedPair_mem M hM hP hn (hf n (Nat.lt_succ_self n))
    have hs := singleton_mem M hM hP hp
    have hu := binary_union_mem M hM hP hU hs (ih (fun i hi => hf i (Nat.lt_succ_of_lt hi)))
    have he : ({ZFSet.pair (natSet n) (f n)} : ZFSet.{u}) ∪ finiteGraph n f =
        insert (ZFSet.pair (natSet n) (f n)) (finiteGraph n f) := by
      apply ZFSet.ext
      intro z
      simp only [ZFSet.mem_union,ZFSet.mem_singleton,ZFSet.mem_insert_iff]
    exact he ▸ hu

theorem eval_traceFormula (n x y p v g w z : ℕ) (e : ℕ → ZFSet.{u})
    (k : ℕ) (hn : e n = natSet k) (hw : e w = ZFSet.omega) (hz : e z = natSet 0) :
    (traceFormula n x y p v g w z).Eval e ↔ Trace (e v) (e g) k (e x) (e y) (e p) := by
  simp only [traceFormula,Formula.Eval,Formula.eval_pairMem,Formula.eval_allMem,
    Formula.eval_imp,Formula.eval_successor,cons_zero,cons_succ,hn,hw,hz,Trace]
  apply and_congr Iff.rfl
  apply and_congr _ Iff.rfl
  constructor
  · intro h i hi a ha hp
    obtain ⟨s,_,hs,b,hb,hpb,hgb⟩ := h (natSet i) ((natSet_mem_natSet i k).mpr hi) a ha hp
    exact ⟨b,hb,by simpa only [hs,natSet] using hpb,hgb⟩
  · intro h i hi a ha hp
    obtain ⟨j,hj,rfl⟩ := (mem_natSet k i).mp hi
    obtain ⟨b,hb,hpb,hgb⟩ := h j hj a ha hp
    exact ⟨natSet (j+1),(mem_omega _).mpr ⟨j+1,rfl⟩,rfl,b,hb,hpb,hgb⟩

theorem iterate_mem {v : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v) {x : ZFSet.{u}} (hx : x ∈ v) (n : ℕ) : F^[n] x ∈ v := by
  induction n with
  | zero => exact hx
  | succ n ih => simpa only [Function.iterate_succ_apply'] using hF _ ih

theorem trace_correct {v g : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x)
    {n : ℕ} {x y p : ZFSet.{u}} (hx : x ∈ v) (ht : Trace v g n x y p) : y = F^[n] x := by
  have hp (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (F^[i] x) ∈ p := by
    induction i with
    | zero => exact ht.1
    | succ i ih =>
      have hv := iterate_mem F hF hx i
      obtain ⟨b,hb,hpb,hgb⟩ := ht.2.1 i (by omega) _ hv (ih (by omega))
      have he := (hg _ hv b hb).mp hgb
      simpa only [he,Function.iterate_succ_apply'] using hpb
  exact (ht.2.2 _ (iterate_mem F hF hx n) (hp n le_rfl)).symm

theorem finiteGraph_trace {v g : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x)
    {x : ZFSet.{u}} (hx : x ∈ v) (n : ℕ) :
    Trace v g n x (F^[n] x) (finiteGraph (n+1) (fun i => F^[i] x)) := by
  refine ⟨(pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,?_,?_⟩
  · intro i hi a ha hpa
    have he := ((pair_mem_finiteGraph _ _ _ _).mp hpa).2
    subst a
    refine ⟨F^[i+1] x,iterate_mem F hF hx (i+1),
      (pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,?_⟩
    apply (hg _ (iterate_mem F hF hx i) _ (iterate_mem F hF hx (i+1))).mpr
    exact Function.iterate_succ_apply' F i x
  · intro b _ hpb
    exact ((pair_mem_finiteGraph _ _ _ _).mp hpb).2

end
end TuringRigidity.SetModelIteration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelIteration
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section

theorem mem_iterationSet {v : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v) (z : ZFSet.{u}) :
    z ∈ iterationSet v F ↔ ∃ n : ℕ, ∃ x ∈ v,
      z = ZFSet.pair (ZFSet.pair (natSet n) x) (F^[n] x) := by
  rw [iterationSet,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨n,x,hx,rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨ZFSet.pair_mem_prod.mpr
      ⟨(mem_omega _).mpr ⟨n,rfl⟩,hx⟩,iterate_mem F hF hx n⟩,⟨n,x,hx,rfl⟩⟩

theorem eval_iterationFormula (z v g p d : ZFSet.{u}) :
    iterationFormula.Eval (cons z (cons ZFSet.omega (cons v (cons g
      (cons p (cons (natSet 0) (fun _ => d))))))) ↔
    ∃ n : ℕ, ∃ x ∈ v, ∃ y ∈ v, ∃ t ∈ d, ∃ s ∈ p,
      z = ZFSet.pair t y ∧ t = ZFSet.pair (natSet n) x ∧ Trace v g n x y s := by
  simp only [iterationFormula,Formula.Eval,cons_zero,cons_succ]
  rw [omega_exists]
  apply exists_congr
  intro n
  apply exists_congr
  intro x
  apply and_congr Iff.rfl
  apply exists_congr
  intro y
  apply and_congr Iff.rfl
  apply exists_congr
  intro t
  apply and_congr Iff.rfl
  apply exists_congr
  intro s
  apply and_congr Iff.rfl
  simp only [Formula.eval_orderedPair,cons_zero,cons_succ]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  exact eval_traceFormula _ _ _ _ _ _ _ _ _ n rfl rfl rfl

theorem iterationSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    {v g : ZFSet.{u}} (hv : v ∈ M) (hgM : g ∈ M)
    (F : ZFSet.{u} → ZFSet.{u}) (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x) :
    iterationSet v F ∈ M := by
  have hω := omega_mem M hM hS hI
  have h0 : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  let d := ZFSet.prod ZFSet.omega v
  have hd : d ∈ M := product_mem M hM hP hU hPow hS hω hv
  obtain ⟨p,hp,hpdef⟩ := internal_power M hM hPow hd
  have hprod := product_mem M hM hP hU hPow hS hd hv
  let e := cons ZFSet.omega (cons v (cons g (cons p (cons (natSet 0) (fun _ => d)))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hv
    · exact hgM
    · exact hp
    · exact h0
    · exact hd
  have hs := sep_mem M hM hS iterationFormula e he hprod
  have eq : ZFSet.sep (fun z => iterationFormula.Eval (cons z e)) (ZFSet.prod d v) =
      iterationSet v F := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,mem_iterationSet F hF,
      show iterationFormula.Eval (cons z e) ↔ _ from eval_iterationFormula z v g p d]
    constructor
    · rintro ⟨_,n,x,hx,y,hy,t,ht,s,hs,hz,htx,htrace⟩
      exact ⟨n,x,hx,by rw [hz,htx,trace_correct F hF hg hx htrace]⟩
    · rintro ⟨n,x,hx,rfl⟩
      let s := finiteGraph (n+1) (fun i => F^[i] x)
      have hsM : s ∈ M := finiteGraph_mem M hM hP hU hω _ _
        (fun i _ => hM v hv _ (iterate_mem F hF hx i))
      have hsD : s ⊆ d := by
        intro z hz
        obtain ⟨i,hi,rfl⟩ := (mem_finiteGraph _ _ _).mp hz
        exact ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨i,rfl⟩,iterate_mem F hF hx i⟩
      have hsP := (hpdef s).mpr ⟨hsM,hsD⟩
      have htD : ZFSet.pair (natSet n) x ∈ d :=
        ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨n,rfl⟩,hx⟩
      refine ⟨ZFSet.pair_mem_prod.mpr ⟨htD,iterate_mem F hF hx n⟩,
        n,x,hx,_,iterate_mem F hF hx n,_,htD,s,hsP,rfl,rfl,?_⟩
      exact finiteGraph_trace F hF hg hx n
  exact eq ▸ hs

end
end TuringRigidity.SetModelIteration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem setSucc_nat (n : ℕ) : setSucc (natSet.{u} n) = natSet (n+1) := rfl

theorem setSucc_omega : ∀ x ∈ ZFSet.omega.{u}, setSucc x ∈ ZFSet.omega := by
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact (mem_omega _).mpr ⟨n+1,rfl⟩

theorem pair_mem_successorSet {x y : ZFSet.{u}} (hx : x ∈ ZFSet.omega) (hy : y ∈ ZFSet.omega) :
    ZFSet.pair x y ∈ successorSet ↔ y = setSucc x := by
  simp only [successorSet,ZFSet.mem_sep,ZFSet.pair_mem_prod,hx,hy,true_and,ZFSet.pair_inj]
  constructor
  · rintro ⟨a,ha,he,hs⟩
    exact he ▸ hs
  · intro h
    exact ⟨x,hx,rfl,h⟩

theorem successorSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : successorSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have hprod := product_mem M hM hP hU hPow hS hω hω
  have hs := sep_mem M hM hS successorFormula (fun _ => ZFSet.omega) (fun _ => hω) hprod
  have eq : ZFSet.sep (fun z => successorFormula.Eval (cons z (fun _ => ZFSet.omega)))
      (ZFSet.prod ZFSet.omega ZFSet.omega) = successorSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,successorFormula,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_successor,cons_zero,cons_succ,successorSet]
    apply and_congr Iff.rfl
    constructor
    · rintro ⟨x,hx,y,hy,hz,rfl⟩
      exact ⟨x,hx,hz⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,hx,setSucc x,setSucc_omega x hx,rfl,rfl⟩
  exact eq ▸ hs

theorem iterate_setSucc (n m : ℕ) : setSucc^[n] (natSet.{u} m) = natSet (m+n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    change natSet (m+n+1) = natSet (m+(n+1))
    rw [Nat.add_assoc]

theorem addition_code (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ additionSet ↔ k = n+m := by
  rw [additionSet,mem_iterationSet setSucc setSucc_omega]
  constructor
  · rintro ⟨i,x,hx,he⟩
    obtain ⟨hinput,hout⟩ := ZFSet.pair_inj.mp he
    obtain ⟨hi,rfl⟩ := ZFSet.pair_inj.mp hinput
    have hin := natSet_injective hi
    rw [←hin,iterate_setSucc] at hout
    exact (natSet_injective hout).trans (Nat.add_comm m n)
  · intro hk
    refine ⟨n,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,?_⟩
    rw [iterate_setSucc,hk,Nat.add_comm m n]

theorem additionSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : additionSet.{u} ∈ M :=
  iterationSet_mem M hM hP hU hPow hS hI (omega_mem M hM hS hI)
    (successorSet_mem M hM hP hU hPow hS hI) setSucc setSucc_omega
    (fun _ hx _ hy => pair_mem_successorSet hx hy)

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelMultiplicationStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem numberPair_injective : Function.Injective numberPair.{u} := by
  intro a b h
  obtain ⟨hl,hr⟩ := ZFSet.pair_inj.mp h
  exact Prod.ext (natSet_injective hl) (natSet_injective hr)

theorem mem_pairNumbers (x : ZFSet.{u}) : x ∈ pairNumbers ↔ ∃ q, x = numberPair q := by
  constructor
  · intro hx
    obtain ⟨a,ha,b,hb,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨m,rfl⟩ := (mem_omega b).mp hb
    exact ⟨(n,m),rfl⟩
  · rintro ⟨q,rfl⟩
    exact ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨q.1,rfl⟩,(mem_omega _).mpr ⟨q.2,rfl⟩⟩

@[simp] theorem addStep_numberPair (n m : ℕ) :
    addStep (numberPair.{u} (n,m)) = numberPair (n,n+m) := by
  have h := Function.leftInverse_invFun numberPair_injective (n,m)
  change Function.invFun numberPair.{u} (numberPair (n,m)) = (n,m) at h
  simp only [addStep,h]

theorem addStep_closed : ∀ x ∈ pairNumbers.{u}, addStep x ∈ pairNumbers := by
  intro x hx
  obtain ⟨⟨n,m⟩,rfl⟩ := (mem_pairNumbers x).mp hx
  rw [addStep_numberPair]
  exact (mem_pairNumbers _).mpr ⟨(n,n+m),rfl⟩

theorem pair_mem_addStepSet {x y : ZFSet.{u}} (hx : x ∈ pairNumbers) (hy : y ∈ pairNumbers) :
    ZFSet.pair x y ∈ addStepSet ↔ y = addStep x := by
  simp only [addStepSet,ZFSet.mem_sep,ZFSet.pair_mem_prod,hx,hy,true_and,ZFSet.pair_inj]
  constructor
  · rintro ⟨a,ha,he,hs⟩
    exact he ▸ hs
  · intro h
    exact ⟨x,hx,rfl,h⟩

theorem eval_addStepFormula (z : ZFSet.{u}) :
    addStepFormula.Eval (cons z (cons ZFSet.omega (cons pairNumbers (fun _ => additionSet)))) ↔
      ∃ x ∈ pairNumbers, z = ZFSet.pair x (addStep x) := by
  simp only [addStepFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ]
  constructor
  · rintro ⟨n,hn,m,hm,k,hk,x,hx,y,hy,hz,hxnm,hynk,hadd⟩
    obtain ⟨i,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨j,rfl⟩ := (mem_omega m).mp hm
    obtain ⟨l,rfl⟩ := (mem_omega k).mp hk
    rw [hxnm] at hadd
    have hl := (addition_code i j l).mp hadd
    refine ⟨x,hx,?_⟩
    rw [hz,hxnm,hynk,hl]
    exact congrArg (ZFSet.pair (numberPair (i,j))) (addStep_numberPair i j).symm
  · rintro ⟨x,hx,hz⟩
    obtain ⟨⟨i,j⟩,rfl⟩ := (mem_pairNumbers x).mp hx
    have hy : numberPair.{u} (i,i+j) ∈ pairNumbers := (mem_pairNumbers _).mpr ⟨_,rfl⟩
    refine ⟨natSet i,(mem_omega _).mpr ⟨i,rfl⟩,natSet j,(mem_omega _).mpr ⟨j,rfl⟩,
      natSet (i+j),(mem_omega _).mpr ⟨i+j,rfl⟩,numberPair (i,j),hx,numberPair (i,i+j),hy,
      ?_,rfl,rfl,(addition_code i j (i+j)).mpr rfl⟩
    simpa only [addStep_numberPair] using hz

theorem addStepSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : addStepSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have hp : pairNumbers.{u} ∈ M := product_mem M hM hP hU hPow hS hω hω
  have ha := additionSet_mem M hM hP hU hPow hS hI
  have hprod := product_mem M hM hP hU hPow hS hp hp
  let e := cons ZFSet.omega (cons pairNumbers (fun _ => additionSet))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i <;> simp [e,hω,hp,ha]
  have hs := sep_mem M hM hS addStepFormula e he hprod
  have eq : ZFSet.sep (fun z => addStepFormula.Eval (cons z e)) (ZFSet.prod pairNumbers pairNumbers) =
      addStepSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,show ∀ z, addStepFormula.Eval (cons z e) ↔ _ from eval_addStepFormula,
      addStepSet]
  exact eq ▸ hs

theorem iterate_addStep (n m : ℕ) :
    addStep^[n] (numberPair.{u} (m,0)) = numberPair (m,n*m) := by
  induction n with
  | zero => simp only [Function.iterate_zero,Function.id_def,Nat.zero_mul]
  | succ n ih => rw [Function.iterate_succ_apply',ih,addStep_numberPair,Nat.succ_mul,Nat.add_comm]

theorem multiplicationIteration_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : multiplicationIteration.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  exact iterationSet_mem M hM hP hU hPow hS hI
    (product_mem M hM hP hU hPow hS hω hω)
    (addStepSet_mem M hM hP hU hPow hS hI) addStep addStep_closed
    (fun _ hx _ hy => pair_mem_addStepSet hx hy)

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem eval_mulFormula (n m k i d D z : ℕ) (e : ℕ → ZFSet.{u}) (a b c : ℕ)
    (hn : e n = natSet a) (hm : e m = natSet b) (hk : e k = natSet c)
    (hi : e i = multiplicationIteration) (hd : e d = pairNumbers)
    (hD : e D = ZFSet.prod ZFSet.omega pairNumbers) (hz : e z = natSet 0) :
    (mulFormula n m k i d D z).Eval e ↔ c = a*b := by
  simp only [mulFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,hn,hm,hk,hi,hd,hD,hz]
  constructor
  · rintro ⟨s,hs,t,ht,w,hw,hsb,htbc,hwas,hwt⟩
    change ZFSet.pair w t ∈ iterationSet pairNumbers addStep at hwt
    obtain ⟨q,x,hx,he⟩ := (mem_iterationSet addStep addStep_closed _).mp hwt
    obtain ⟨hleft,hright⟩ := ZFSet.pair_inj.mp he
    rw [hwas] at hleft
    obtain ⟨hqa,hxs⟩ := ZFSet.pair_inj.mp hleft
    have hq := natSet_injective hqa
    rw [←hxs,hsb,←hq] at hright
    change t = addStep^[a] (numberPair (b,0)) at hright
    rw [iterate_addStep,htbc] at hright
    exact natSet_injective (ZFSet.pair_inj.mp hright).2
  · intro hc
    have hs : numberPair.{u} (b,0) ∈ pairNumbers := (mem_pairNumbers _).mpr ⟨_,rfl⟩
    have ht : numberPair.{u} (b,c) ∈ pairNumbers := (mem_pairNumbers _).mpr ⟨_,rfl⟩
    have hw : ZFSet.pair (natSet a) (numberPair.{u} (b,0)) ∈ ZFSet.prod ZFSet.omega pairNumbers :=
      ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨a,rfl⟩,hs⟩
    refine ⟨numberPair (b,0),hs,numberPair (b,c),ht,_,hw,rfl,rfl,rfl,?_⟩
    exact (mem_iterationSet addStep addStep_closed _).mpr
      ⟨a,numberPair (b,0),hs,by rw [iterate_addStep,hc]⟩

theorem multiplication_code (n m k : ℕ) :
    ZFSet.pair (numberPair.{u} (n,m)) (natSet k) ∈ multiplicationSet ↔ k = n*m := by
  simp only [multiplicationSet,ZFSet.mem_sep,ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨_,a,b,he⟩
    obtain ⟨hin,hout⟩ := ZFSet.pair_inj.mp he
    have hab := numberPair_injective hin
    have hn : n = a := congrArg Prod.fst hab
    have hm : m = b := congrArg Prod.snd hab
    simpa only [←hn,←hm] using natSet_injective hout
  · intro hk
    exact ⟨⟨(mem_pairNumbers _).mpr ⟨_,rfl⟩,(mem_omega _).mpr ⟨k,rfl⟩⟩,
      n,m,by rw [hk]⟩

theorem multiplicationSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : multiplicationSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have h0 : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  have hd : pairNumbers.{u} ∈ M := product_mem M hM hP hU hPow hS hω hω
  have hD := product_mem M hM hP hU hPow hS hω hd
  have hi := multiplicationIteration_mem M hM hP hU hPow hS hI
  have hprod := product_mem M hM hP hU hPow hS hd hω
  let e := cons ZFSet.omega (cons pairNumbers (cons multiplicationIteration
    (cons (ZFSet.prod ZFSet.omega pairNumbers) (fun _ => natSet 0))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hd
    · exact hi
    · exact hD
    · exact h0
  have hs := sep_mem M hM hS multiplicationFormula e he hprod
  have hφ (z : ZFSet.{u}) : multiplicationFormula.Eval (cons z e) ↔
      ∃ n m, z = ZFSet.pair (numberPair (n,m)) (natSet (n*m)) := by
    simp only [multiplicationFormula,Formula.Eval,Formula.eval_orderedPair,
      cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,m,hm,k,hk,t,ht,hz,htnm,hmu⟩
      obtain ⟨a,rfl⟩ := (mem_omega n).mp hn
      obtain ⟨b,rfl⟩ := (mem_omega m).mp hm
      obtain ⟨c,rfl⟩ := (mem_omega k).mp hk
      have hc := (eval_mulFormula 3 2 1 7 6 8 9
        (cons t (cons (natSet c) (cons (natSet b) (cons (natSet a) (cons z e)))))
        a b c rfl rfl rfl rfl rfl rfl rfl).mp hmu
      exact ⟨a,b,by simpa only [htnm,hc,numberPair] using hz⟩
    · rintro ⟨n,m,rfl⟩
      refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,
        natSet (n*m),(mem_omega _).mpr ⟨n*m,rfl⟩,numberPair (n,m),
        (mem_pairNumbers _).mpr ⟨_,rfl⟩,rfl,rfl,?_⟩
      exact (eval_mulFormula 3 2 1 7 6 8 9
        (cons (numberPair (n,m)) (cons (natSet (n*m)) (cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (numberPair (n,m)) (natSet (n*m))) e)))))
        n m (n*m) rfl rfl rfl rfl rfl rfl rfl).mpr rfl
  have eq : ZFSet.sep (fun z => multiplicationFormula.Eval (cons z e))
      (ZFSet.prod pairNumbers ZFSet.omega) = multiplicationSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,hφ,multiplicationSet]
  exact eq ▸ hs

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelSequences
universe u
noncomputable section

@[simp] theorem natPair_mem (n m : ℕ) :
    ZFSet.pair (natSet.{u} n) (natSet m) ∈ pairNumbers :=
  (mem_pairNumbers _).mpr ⟨(n,m),rfl⟩

theorem multiplication_code' (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ multiplicationSet ↔ k = n*m :=
  multiplication_code n m k

theorem eval_pairFormula (n m k a b d w : ℕ) (e : ℕ → ZFSet.{u}) (i j l : ℕ)
    (hn : e n = natSet i) (hm : e m = natSet j) (hk : e k = natSet l)
    (ha : e a = additionSet) (hb : e b = multiplicationSet)
    (hd : e d = pairNumbers) (hw : e w = ZFSet.omega) :
    (pairFormula n m k a b d w).Eval e ↔ l = Nat.pair i j := by
  simp only [pairFormula,Formula.eval_disj,Formula.Eval,eval_tripleFormula,
    cons_zero,cons_succ,hn,hm,hk,ha,hb,hd,hw,natSet_mem_natSet]
  simp_rw [omega_exists]
  simp only [natPair_mem,true_and,addition_code,multiplication_code']
  by_cases h : i < j <;> simp [h,Nat.pair]

theorem pairingSet_code : PairingCode pairingSet.{u} := by
  intro n m k
  simp only [pairingSet,ZFSet.mem_sep,ZFSet.pair_mem_prod,natPair_mem,true_and]
  constructor
  · rintro ⟨_,a,b,he⟩
    obtain ⟨hin,hout⟩ := ZFSet.pair_inj.mp he
    have hab : (n,m) = (a,b) := numberPair_injective hin
    have hn : n = a := congrArg Prod.fst hab
    have hm : m = b := congrArg Prod.snd hab
    simpa only [←hn,←hm] using natSet_injective hout
  · intro hk
    exact ⟨(mem_omega _).mpr ⟨k,rfl⟩,n,m,by simp only [hk,numberPair]⟩

theorem pairingSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : pairingSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have hd : pairNumbers.{u} ∈ M := product_mem M hM hP hU hPow hS hω hω
  have ha := additionSet_mem M hM hP hU hPow hS hI
  have hb := multiplicationSet_mem M hM hP hU hPow hS hI
  have hprod := product_mem M hM hP hU hPow hS hd hω
  let e := cons ZFSet.omega (cons pairNumbers (cons additionSet (fun _ => multiplicationSet)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hd
    · exact ha
    · exact hb
  have hs := sep_mem M hM hS pairingFormula e he hprod
  have hφ (z : ZFSet.{u}) : pairingFormula.Eval (cons z e) ↔
      ∃ n m, z = ZFSet.pair (numberPair (n,m)) (natSet (Nat.pair n m)) := by
    simp only [pairingFormula,Formula.Eval,Formula.eval_orderedPair,
      cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,m,hm,k,hk,t,ht,hz,htnm,hpr⟩
      obtain ⟨a,rfl⟩ := (mem_omega n).mp hn
      obtain ⟨b,rfl⟩ := (mem_omega m).mp hm
      obtain ⟨c,rfl⟩ := (mem_omega k).mp hk
      have hc := (eval_pairFormula 3 2 1 7 8 6 5
        (cons t (cons (natSet c) (cons (natSet b) (cons (natSet a) (cons z e)))))
        a b c rfl rfl rfl rfl rfl rfl rfl).mp hpr
      exact ⟨a,b,by simpa only [htnm,hc,numberPair] using hz⟩
    · rintro ⟨n,m,rfl⟩
      refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,
        natSet (Nat.pair n m),(mem_omega _).mpr ⟨Nat.pair n m,rfl⟩,numberPair (n,m),
        natPair_mem n m,rfl,rfl,?_⟩
      exact (eval_pairFormula 3 2 1 7 8 6 5
        (cons (numberPair (n,m)) (cons (natSet (Nat.pair n m)) (cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (numberPair (n,m)) (natSet (Nat.pair n m))) e)))))
        n m (Nat.pair n m) rfl rfl rfl rfl rfl rfl rfl).mpr rfl
  have eq : ZFSet.sep (fun z => pairingFormula.Eval (cons z e))
      (ZFSet.prod pairNumbers ZFSet.omega) = pairingSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,hφ,pairingSet]
  exact eq ▸ hs

end
end TuringRigidity.SetModelArithmetic

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

theorem Context.nat_mem (n : ℕ) : natSet.{u} n ∈ M :=
  C.transitive _ C.omega_mem _ ((mem_omega _).mpr ⟨n,rfl⟩)

theorem Context.prod_mem {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) :
    ZFSet.prod a b ∈ M :=
  product_mem M C.transitive C.pairing C.union C.power C.separation ha hb

theorem graph_of_formula (f : ℕ → ℕ) (p : Formula) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M)
    (hp : ∀ n m, p.Eval (cons (ZFSet.pair (natSet n) (natSet m)) e) ↔ m = f n) :
    HasGraph M f := by
  refine ⟨ZFSet.sep (fun z => p.Eval (cons z e)) pairNumbers,
    sep_mem M C.transitive C.separation p e he (C.prod_mem C.omega_mem C.omega_mem),?_⟩
  intro n m
  simp only [ZFSet.mem_sep,natPair_mem,true_and,hp]

theorem graph_of_relation (f : ℕ → ℕ) (p : Formula) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M)
    (hp : ∀ n m, p.Eval (cons (natSet m) (cons (natSet n) e)) ↔ m = f n) :
    HasGraph M f := by
  let r : ℕ → ℕ := fun i => if i < 2 then i else i+2
  let q : Formula := .existsMem 1 (.existsMem 2
    (.conj (.orderedPair 2 1 0) (p.rename r)))
  let d := cons ZFSet.omega e
  apply graph_of_formula C f q d
  · intro i
    cases i with
    | zero => exact C.omega_mem
    | succ i => exact he i
  · intro n m
    simp only [q,d,Formula.Eval,Formula.eval_orderedPair,Formula.eval_rename_comp,
      cons_zero,cons_succ]
    constructor
    · rintro ⟨x,hx,y,hy,hz,hp'⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hz
      have hh : cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (natSet n) (natSet m)) (cons ZFSet.omega e))) ∘ r =
          cons (natSet m) (cons (natSet n) e) := by
        funext i
        rcases i with _|_|i <;> simp [r,cons]
      rw [hh] at hp'
      exact (hp n m).mp hp'
    · intro h
      refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,natSet m,
        (mem_omega _).mpr ⟨m,rfl⟩,rfl,?_⟩
      have hh : cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (natSet n) (natSet m)) (cons ZFSet.omega e))) ∘ r =
          cons (natSet m) (cons (natSet n) e) := by
        funext i
        rcases i with _|_|i <;> simp [r,cons]
      rw [hh]
      exact (hp n m).mpr h

theorem const_graph (k : ℕ) : HasGraph M (fun _ => k) := by
  apply graph_of_relation C _ (.equal 0 2) (fun _ => natSet k) (fun _ => C.nat_mem k)
  intro n m
  exact ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩

theorem id_graph : HasGraph M id := by
  apply graph_of_relation C _ (.equal 0 1) (fun _ => ZFSet.omega) (fun _ => C.omega_mem)
  intro n m
  exact ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩

theorem succ_graph : HasGraph M Nat.succ := by
  refine ⟨successorSet,successorSet_mem M C.transitive C.pairing C.union C.power
    C.separation C.infinity,?_⟩
  intro n m
  rw [pair_mem_successorSet ((mem_omega _).mpr ⟨n,rfl⟩)
    ((mem_omega _).mpr ⟨m,rfl⟩),setSucc_nat]
  exact ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩

theorem HasGraph.comp {f g : ℕ → ℕ} (hf : HasGraph M f) (hg : HasGraph M g) :
    HasGraph M (fun n => f (g n)) := by
  obtain ⟨a,ha,hac⟩ := hf
  obtain ⟨b,hb,hbc⟩ := hg
  let e := cons ZFSet.omega (cons a (fun _ => b))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [e,C.omega_mem,ha,hb]
  apply graph_of_relation C _ (.existsMem 2 (.conj (.pairMem 2 0 5) (.pairMem 0 1 4))) e he
  intro n m
  simp only [Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e]
  rw [omega_exists]
  simp only [hac,hbc]
  constructor
  · rintro ⟨k,rfl,h⟩
    exact h
  · intro h
    exact ⟨g n,rfl,h⟩

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionPairing
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

theorem Context.pairing_mem : pairingSet.{u} ∈ M :=
  pairingSet_mem M C.transitive C.pairing C.union C.power C.separation C.infinity

theorem Context.pairNumbers_mem : pairNumbers.{u} ∈ M := C.prod_mem C.omega_mem C.omega_mem

omit C in
@[simp] theorem pairing_code (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ pairingSet ↔
      k = Nat.pair n m := pairingSet_code n m k

theorem left_graph : HasGraph M (fun n => (Nat.unpair n).1) := by
  let e := cons ZFSet.omega (cons pairNumbers (fun _ => pairingSet))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [e,C.omega_mem,C.pairNumbers_mem,C.pairing_mem]
  apply graph_of_relation C _ (.existsMem 2 (tripleFormula 1 0 2 5 4)) e he
  intro n m
  simp only [Formula.Eval,eval_tripleFormula,cons_zero,cons_succ,e]
  rw [omega_exists]
  simp only [natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨k,rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair n).2,by rw [h,Nat.pair_unpair]⟩

theorem right_graph : HasGraph M (fun n => (Nat.unpair n).2) := by
  let e := cons ZFSet.omega (cons pairNumbers (fun _ => pairingSet))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [e,C.omega_mem,C.pairNumbers_mem,C.pairing_mem]
  apply graph_of_relation C _ (.existsMem 2 (tripleFormula 0 1 2 5 4)) e he
  intro n m
  simp only [Formula.Eval,eval_tripleFormula,cons_zero,cons_succ,e]
  rw [omega_exists]
  simp only [natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨k,rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair n).1,by rw [h,Nat.pair_unpair]⟩

theorem HasGraph.pair {f g : ℕ → ℕ} (hf : HasGraph M f) (hg : HasGraph M g) :
    HasGraph M (fun n => Nat.pair (f n) (g n)) := by
  obtain ⟨a,ha,hac⟩ := hf
  obtain ⟨b,hb,hbc⟩ := hg
  let e := cons ZFSet.omega (cons a (cons b (cons pairNumbers (fun _ => pairingSet))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp [e,C.omega_mem,ha,hb,C.pairNumbers_mem,C.pairing_mem]
  apply graph_of_relation C _ (.existsMem 2 (.existsMem 3
    (.conj (.pairMem 3 1 5) (.conj (.pairMem 3 0 6) (tripleFormula 1 0 2 8 7))))) e he
  intro n m
  simp only [Formula.Eval,Formula.eval_pairMem,eval_tripleFormula,cons_zero,cons_succ,e]
  simp_rw [omega_exists]
  simp only [hac,hbc,natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨i,j,rfl,rfl,h⟩
    exact h
  · intro h
    exact ⟨f n,g n,rfl,rfl,h⟩

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionIteration
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

omit C in
theorem natLift_closed (f : ℕ → ℕ) : ∀ x ∈ ZFSet.omega.{u}, natLift f x ∈ ZFSet.omega := by
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact (mem_omega _).mpr ⟨f n,natLift_nat f n⟩

omit C in
theorem iterate_natLift (f : ℕ → ℕ) (n m : ℕ) :
    (natLift f)^[n] (natSet.{u} m) = natSet (f^[n] m) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,natLift_nat,Function.iterate_succ_apply']

omit C in
theorem natIteration_code (f : ℕ → ℕ) (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ natIteration f ↔
      k = f^[n] m := by
  rw [natIteration,mem_iterationSet _ (natLift_closed f)]
  constructor
  · rintro ⟨i,x,hx,he⟩
    obtain ⟨hi,hk⟩ := ZFSet.pair_inj.mp he
    obtain ⟨hnum,rfl⟩ := ZFSet.pair_inj.mp hi
    have hin := natSet_injective hnum
    rw [←hin,iterate_natLift] at hk
    exact natSet_injective hk
  · intro h
    refine ⟨n,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,?_⟩
    rw [iterate_natLift,h]

theorem natIteration_mem {f : ℕ → ℕ} (hf : HasGraph M f) : natIteration.{u} f ∈ M := by
  obtain ⟨g,hg,hgc⟩ := hf
  apply iterationSet_mem M C.transitive C.pairing C.union C.power C.separation C.infinity
    C.omega_mem hg (natLift f) (natLift_closed f)
  intro x hx y hy
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  obtain ⟨m,rfl⟩ := (mem_omega y).mp hy
  rw [hgc,natLift_nat]
  exact ⟨fun h => congrArg natSet h,fun h => natSet_injective h⟩

theorem HasGraph.iterate {f : ℕ → ℕ} (hf : HasGraph M f) :
    HasGraph M (fun v => f^[(Nat.unpair v).2] (Nat.unpair v).1) := by
  let e := cons ZFSet.omega (cons pairNumbers (cons pairingSet (fun _ => natIteration f)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|i <;>
      simp [e,C.omega_mem,C.pairNumbers_mem,C.pairing_mem,natIteration_mem C hf]
  apply graph_of_relation C _ (.existsMem 2 (.existsMem 3 (.existsMem 5
    (.conj (tripleFormula 2 1 4 7 6)
      (.conj (.orderedPair 0 1 2) (.pairMem 0 3 8)))))) e he
  intro n m
  simp only [Formula.Eval,eval_tripleFormula,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,e]
  simp_rw [omega_exists]
  simp only [natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨a,b,t,ht,hn,rfl,h⟩
    rw [natIteration_code] at h
    simpa only [hn,Nat.unpair_pair] using h
  · intro h
    refine ⟨(Nat.unpair n).1,(Nat.unpair n).2,
      ZFSet.pair (natSet (Nat.unpair n).2) (natSet (Nat.unpair n).1),
      natPair_mem _ _,(Nat.pair_unpair n).symm,rfl,?_⟩
    exact (natIteration_code _ _ _ _).mpr h

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPrimrec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section

variable {M : ZFSet.{u}}

theorem HasGraph.congr {f g : ℕ → ℕ} (hf : HasGraph M f) (h : ∀ n, f n = g n) :
    HasGraph M g := (funext h) ▸ hf

theorem iterate_recStep (f g : ℕ → ℕ) (z n : ℕ) :
    (recStep g)^[n] (recStart f z) = Nat.pair z (Nat.pair n (recValue f g z n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [recStep,Nat.unpair_pair,recValue]

theorem HasGraph.prec (C : Context M) {f g : ℕ → ℕ}
    (hf : HasGraph M f) (hg : HasGraph M g) :
    HasGraph M (Nat.unpaired (recValue f g)) := by
  have hs : HasGraph M (recStep g) :=
    HasGraph.pair C (left_graph C) (HasGraph.pair C
      (HasGraph.comp C (succ_graph C) (HasGraph.comp C (left_graph C) (right_graph C))) hg)
  have hz : HasGraph M (recStart f) :=
    HasGraph.pair C (id_graph C) (HasGraph.pair C (const_graph C 0) hf)
  have hp := HasGraph.pair C (HasGraph.comp C hz (left_graph C)) (right_graph C)
  have hi := HasGraph.comp C (HasGraph.iterate C hs) hp
  have h := HasGraph.comp C (HasGraph.comp C (right_graph C) (right_graph C)) hi
  apply h.congr
  intro v
  simp only [Nat.unpair_pair,iterate_recStep,Nat.unpaired]

theorem natPrimrec_graph (C : Context M) {f : ℕ → ℕ} (hf : Nat.Primrec f) : HasGraph M f := by
  induction hf with
  | zero => exact const_graph C 0
  | succ => exact succ_graph C
  | left => exact left_graph C
  | right => exact right_graph C
  | pair hf hg ihf ihg => exact HasGraph.pair C ihf ihg
  | comp hf hg ihf ihg => exact HasGraph.comp C ihf ihg
  | prec hf hg ihf ihg => exact HasGraph.prec C ihf ihg

theorem primrec_graph (C : Context M) {f : ℕ → ℕ} (hf : Primrec f) : HasGraph M f :=
  natPrimrec_graph C (Primrec.nat_iff.mp hf)

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

theorem Definable.existsParam (h : Definable M P) {a : ZFSet.{u}} (ha : a ∈ M) :
    Definable M (fun e => ∃ x ∈ a, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  let r := slotMap id Nat.succ
  refine ⟨.existsMem 1 ((p.rename r).rename bindSlots),cons a d,?_,?_⟩
  · intro i
    cases i with
    | zero => exact ha
    | succ i => exact hd i
  · intro e
    have hd' : cons a d ∘ Nat.succ = d := rfl
    simp only [r,Formula.Eval,Formula.eval_rename_comp,bind_mix,mix_slotMap,Function.comp_id,hd',hp,
      show mix e (cons a d) 1 = a from rfl]

theorem equal_definable (C : Context M) (i j : ℕ) : Definable M (fun e => e i = e j) :=
  ⟨.equal (2*i) (2*j),fun _ => ZFSet.omega,fun _ => C.omega_mem,fun e => by simp [Formula.Eval]⟩

theorem member_definable (C : Context M) (i j : ℕ) : Definable M (fun e => e i ∈ e j) :=
  ⟨.member (2*i) (2*j),fun _ => ZFSet.omega,fun _ => C.omega_mem,fun e => by simp [Formula.Eval]⟩

theorem equal_param {a : ZFSet.{u}} (ha : a ∈ M) (i : ℕ) :
    Definable M (fun e => e i = a) :=
  ⟨.equal (2*i) 1,fun _ => a,fun _ => ha,fun e => by simp [Formula.Eval,mix]⟩

theorem pairMem_param {a : ZFSet.{u}} (ha : a ∈ M) (i j : ℕ) :
    Definable M (fun e => ZFSet.pair (e i) (e j) ∈ a) :=
  ⟨.pairMem (2*i) (2*j) 1,fun _ => a,fun _ => ha,fun e => by simp [mix]⟩

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelArithmeticSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open BoundedDefinability UniformArithmetic Encodable
universe u
noncomputable section

variable {M : ZFSet.{u}}

theorem pairCode_definable (C : Context M) (i j k : ℕ) :
    Definable M (fun e => PairCode (e i) (e j) (e k)) := by
  refine ⟨tripleFormula (2*i) (2*j) (2*k) 1 3,
    cons pairingSet (fun _ => pairNumbers),?_,?_⟩
  · intro n
    cases n with
    | zero => exact C.pairing_mem
    | succ n => exact C.pairNumbers_mem
  · intro e
    simp only [eval_tripleFormula,mix_even,PairCode]
    rfl

@[simp] theorem pairCode_nat (i j k : ℕ) :
    PairCode (natSet.{u} i) (natSet j) (natSet k) ↔ k = Nat.pair i j := by
  simp only [PairCode,natPair_mem,true_and,pairing_code]

end
end TuringRigidity.SetModelSyntax

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

theorem defAllParam {P : (ℕ → ZFSet.{u}) → Prop} {a : ZFSet.{u}}
    (h : Definable M P) (ha : a ∈ M) : Definable M (fun e => ∀ x ∈ a, P (cons x e)) :=
  (h.neg.existsParam ha).neg.congr (fun _ => by simp)

theorem defMemberParam {a : ZFSet.{u}} (ha : a ∈ M) (i : ℕ) :
    Definable M (fun e => e i ∈ a) :=
  ⟨.member (2*i) 1,fun _ => a,fun _ => ha,fun e => by simp [Formula.Eval,mix]⟩

theorem defSubset (C : Context M) (i j : ℕ) : Definable M (fun e => e i ⊆ e j) :=
  defAllMem (member_definable C 0 (j+1)) i

theorem unaryGraph_definable (C : Context M) (f : ℕ → ℕ) (hf : Primrec f) (i j : ℕ) :
    Definable M (fun e => UnaryGraph f (e i) (e j)) := by
  obtain ⟨g,hg,hcode⟩ := primrec_graph C hf
  refine (((defMemberParam C.omega_mem i).and (defMemberParam C.omega_mem j)).and
    (pairMem_param hg i j)).congr ?_
  intro e
  simp only [UnaryGraph,mem_omega]
  constructor
  · rintro ⟨⟨⟨n,hn⟩,⟨m,hm⟩⟩,h⟩
    refine ⟨n,hn,?_⟩
    have hm' : m = f n := (hcode n m).mp (by rwa [hn,hm] at h)
    rw [← hm',hm]
  · rintro ⟨n,hn,hm⟩
    exact ⟨⟨⟨n,hn⟩,⟨f n,hm⟩⟩,by rw [hn,hm]; exact (hcode n (f n)).mpr rfl⟩

theorem binaryGraph_definable (C : Context M) (f : ℕ → ℕ → ℕ)
    (hf : Primrec₂ f) (i j k : ℕ) :
    Definable M (fun e => BinaryGraph f (e i) (e j) (e k)) := by
  have hu : Primrec (Nat.unpaired f) := hf.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  have hd := ((pairCode_definable C (i+1) (j+1) 0).and
    (unaryGraph_definable C (Nat.unpaired f) hu 0 (k+1))).existsParam C.omega_mem
  refine hd.congr ?_
  intro e
  simp only [cons_zero,cons_succ,UnaryGraph,BinaryGraph]
  constructor
  · rintro ⟨z,_,hz,n,hn,hk⟩
    have hxy := hz.1
    obtain ⟨a,ha,b,hb,he⟩ := ZFSet.mem_prod.mp hxy
    obtain ⟨hi,hj⟩ := ZFSet.pair_inj.mp he
    obtain ⟨a,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨b,rfl⟩ := (mem_omega b).mp hb
    have heq : n = Nat.pair a b := (pairCode_nat a b n).mp (by rwa [hi,hj,hn] at hz)
    exact ⟨a,b,hi,hj,by rw [heq] at hk; simpa [Nat.unpaired,Nat.unpair_pair] using hk⟩
  · rintro ⟨a,b,hi,hj,hk⟩
    refine ⟨natSet (Nat.pair a b),(mem_omega _).mpr ⟨_,rfl⟩,?_,Nat.pair a b,rfl,?_⟩
    · rw [hi,hj]; exact (pairCode_nat a b _).mpr rfl
    · simpa [Nat.unpaired,Nat.unpair_pair] using hk

theorem atom_primrec : Primrec atom := Primrec₂.natPair.comp (Primrec.const 0) Primrec.id

theorem cell_primrec : Primrec₂ cell :=
  Primrec₂.natPair.comp (Primrec.succ.comp Primrec.fst) Primrec.snd

theorem binary_primrec (t : ℕ) : Primrec₂ (binary t) :=
  cell_primrec.comp (Primrec.const (atom t))
    (cell_primrec.comp Primrec.fst (cell_primrec.comp Primrec.snd (Primrec.const (atom 0))))

theorem unary_primrec (t : ℕ) : Primrec (unary t) :=
  cell_primrec.comp (Primrec.const (atom t))
    (cell_primrec.comp Primrec.id (Primrec.const (atom 0)))

theorem atomic_primrec (t : ℕ) : Primrec₂ (fun i j => binary t (atom i) (atom j)) :=
  (binary_primrec t).comp (atom_primrec.comp Primrec.fst) (atom_primrec.comp Primrec.snd)

end TuringRigidity.SentenceCoding

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_FiniteGraphSatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem prependValues_tail (w : ℕ → ZFSet.{u}) (n : ℕ) (e : ℕ → ZFSet.{u}) (i : ℕ) :
    prependValues w n e (n+i) = e i := by
  induction n generalizing e i with
  | zero => simp [prependValues]
  | succ n ih =>
    change prependValues w n (cons (w n) e) (n+1+i) = e i
    rw [show n+1+i = n+(i+1) by omega,ih]
    rfl

theorem prependValues_lt (w : ℕ → ZFSet.{u}) (n : ℕ) (e : ℕ → ZFSet.{u})
    (i : ℕ) (hi : i < n) : prependValues w n e i = w i := by
  induction n generalizing e with
  | zero => omega
  | succ n ih =>
    by_cases hin : i < n
    · exact ih _ hin
    · have he : i = n := by omega
      subst i
      exact prependValues_tail w n (cons (w n) e) 0

theorem readGraph_eval (n a g : ℕ) (idx : ℕ → ℕ) (ψ : Formula)
    (e w : ℕ → ZFSet.{u}) (hw : ∀ i, i < n → w i ∈ e a)
    (hg : ∀ i, i < n → ∀ y ∈ e a,
      (ZFSet.pair (e (idx i)) y ∈ e g ↔ y = w i)) :
    (readGraph n a g idx ψ).Eval e ↔ ψ.Eval (prependValues w n e) := by
  induction n generalizing a g idx e with
  | zero => rfl
  | succ n ih =>
    simp only [readGraph,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ]
    constructor
    · rintro ⟨x,hx,hpair,hbody⟩
      have he : x = w n := (hg n (by omega) x hx).mp hpair
      subst x
      exact (ih (a+1) (g+1) (fun i => idx i+1) (cons (w n) e)
        (fun i hi => hw i (by omega)) (fun i hi => hg i (by omega))).mp hbody
    · intro h
      refine ⟨w n,hw n (by omega),(hg n (by omega) _ (hw n (by omega))).mpr rfl,?_⟩
      exact (ih (a+1) (g+1) (fun i => idx i+1) (cons (w n) e)
        (fun i hi => hw i (by omega)) (fun i hi => hg i (by omega))).mpr h

theorem graphTruth_spec (p : SentenceForm) (a g : ℕ) (idx : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ e a) (hb : p.bound ≤ n) (hg : e g = tupleGraph v)
    (hi : ∀ i, i < p.bound → e (idx i) = natSet i) :
    (graphTruth p a g idx).Eval e ↔ p.Sat (e a : Set ZFSet) (tupleEnv v) := by
  have hw (i : ℕ) (h : i < p.bound) : tupleEnv v i ∈ e a := by
    simpa [tupleEnv,show i < n by omega] using hv ⟨i,by omega⟩
  have hlookup (i : ℕ) (h : i < p.bound) (y : ZFSet.{u}) (_hy : y ∈ e a) :
      ZFSet.pair (e (idx i)) y ∈ e g ↔ y = tupleEnv v i := by
    rw [hg,hi i h]
    simpa [tupleEnv,show i < n by omega] using tupleGraph_pair v ⟨i,by omega⟩ y
  rw [graphTruth,readGraph_eval p.bound a g idx _ e (tupleEnv v) hw hlookup,setBounded_eval,
    prependValues_tail]
  exact p.finite_support _ _ _ (fun i h => prependValues_lt _ _ _ i h)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSatisfactionSlice
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
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

theorem tupleTruth_spec (p : SentenceForm) (o A Q b t : ℕ) (idx : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega) (hb : e b = natSet p.bound)
    (hi : ∀ i, i < p.bound → e (idx i) = natSet i)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ e A)
    (ht : e t = tupleCode v) (hQ : tupleGraph v ∈ e Q) :
    (tupleTruth p o A Q b t idx).Eval e ↔
      p.bound ≤ n ∧ p.Sat (e A : Set ZFSet) (tupleEnv v) := by
  simp only [tupleTruth,Formula.Eval,Formula.eval_orderedPair,Formula.eval_subset,
    cons_zero,cons_succ]
  constructor
  · rintro ⟨m,_,g,_,hp,hsub,htruth⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp (ht.symm.trans hp)
    have hbn : p.bound ≤ n := natSet_subset_iff p.bound n |>.mp (hb ▸ hsub)
    exact ⟨hbn,(graphTruth_spec p (A+2) 0 (fun i => idx i+2)
      (cons (tupleGraph v) (cons (natSet n) e)) v hv hbn rfl hi).mp htruth⟩
  · rintro ⟨hbn,htruth⟩
    refine ⟨natSet n,ho ▸ (mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hQ,ht,?_,?_⟩
    · rw [hb]; exact (natSet_subset_iff p.bound n).mpr hbn
    · exact (graphTruth_spec p (A+2) 0 (fun i => idx i+2)
        (cons (tupleGraph v) (cons (natSet n) e)) v hv hbn rfl hi).mpr htruth

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

theorem finiteSatisfaction_subset (A : ZFSet.{u}) (ps : List SentenceForm) :
    finiteSatisfaction A ps ⊆ satisfactionSet A := by
  intro z hz
  obtain ⟨p,_,t,ht,rfl⟩ := (mem_finiteSatisfaction A z ps).mp hz
  exact (ZFSet.mem_sep.mp ht).2

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

theorem family_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M) (p : SentenceForm) :
    family p ∈ M := by
  have hn (k : ℕ) : natSet.{u} k ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨k,rfl⟩)
  exact finite_range_mem M hM hP hU (hn 0) _ _ (fun _ => hn _)

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

theorem internal_family_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hω : ZFSet.omega.{u} ∈ M) :
    ∃ Q ∈ M, (∀ S, S ∈ Q ↔ S ∈ M ∧ S ⊆ ZFSet.omega) ∧
      ∀ p : SentenceForm, family p ∈ Q := by
  obtain ⟨Q,hQ,hdef⟩ := internal_power M hM hPow hω
  exact ⟨Q,hQ,hdef,fun p => (hdef _).mpr
    ⟨family_mem M hM hP hU hω p,family_subset_omega p⟩⟩

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceFamilyFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

theorem setStep_nat (S : ZFSet.{u}) (n : ℕ) :
    SetStep S (natSet n) ↔ Step (fun k => natSet k ∈ S) n := by
  simp only [SetStep,Step,BinaryGraph,UnaryGraph]
  have hn (a b : ℕ) : natSet.{u} a = natSet b ↔ a = b := natSet_injective.eq_iff
  simp only [hn]
  constructor
  · intro h
    rcases h with h|h|h|h|h
    · obtain ⟨x,_,y,_,i,j,_,_,he⟩ := h; exact Or.inl ⟨i,j,he⟩
    · obtain ⟨x,_,y,_,i,j,_,_,he⟩ := h; exact Or.inr (Or.inl ⟨i,j,he⟩)
    · obtain ⟨x,hx,y,hy,i,j,rfl,rfl,he⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨i,j,he,hx,hy⟩))
    · obtain ⟨x,hx,i,rfl,he⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i,he,hx⟩)))
    · obtain ⟨x,hx,i,rfl,he⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i,he,hx⟩)))
  · intro h
    have hw (k : ℕ) : natSet.{u} k ∈ ZFSet.omega := (mem_omega _).mpr ⟨k,rfl⟩
    rcases h with h|h|h|h|h
    · obtain ⟨i,j,he⟩ := h
      exact Or.inl ⟨_,hw i,_,hw j,i,j,rfl,rfl,he⟩
    · obtain ⟨i,j,he⟩ := h
      exact Or.inr (Or.inl ⟨_,hw i,_,hw j,i,j,rfl,rfl,he⟩)
    · obtain ⟨i,j,he,hi,hj⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨_,hi,_,hj,i,j,rfl,rfl,he⟩))
    · obtain ⟨i,he,hi⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_,hi,i,rfl,he⟩)))
    · obtain ⟨i,he,hi⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_,hi,i,rfl,he⟩)))

theorem setStep_definable (C : Context M) (s c : ℕ) :
    Definable M (fun e => SetStep (e s) (e c)) := by
  have he := ((binaryGraph_definable C _ (atomic_primrec 0) 1 0 (c+2)).existsParam
    C.omega_mem).existsParam C.omega_mem
  have hm := ((binaryGraph_definable C _ (atomic_primrec 1) 1 0 (c+2)).existsParam
    C.omega_mem).existsParam C.omega_mem
  have ha := ((binaryGraph_definable C _ (binary_primrec 2) 1 0 (c+2)).existsMem (s+1)).existsMem s
  have hn := (unaryGraph_definable C _ (unary_primrec 3) 0 (c+1)).existsMem s
  have hx := (unaryGraph_definable C _ (unary_primrec 4) 0 (c+1)).existsMem s
  exact defOr he (defOr hm (defOr ha (defOr hn hx)))

theorem setClosed_spec (S : ZFSet.{u}) :
    SetClosed S ↔ S ⊆ ZFSet.omega ∧ ∀ c ∈ S, SetStep S c := by
  constructor
  · rintro ⟨hs,hc⟩
    refine ⟨hs,fun c hm => ?_⟩
    obtain ⟨n,rfl⟩ := (mem_omega c).mp (hs hm)
    exact (setStep_nat S n).mpr (hc n hm)
  · rintro ⟨hs,hc⟩
    exact ⟨hs,fun n hn => (setStep_nat S n).mp (hc _ hn)⟩

theorem setClosed_definable (C : Context M) (s : ℕ) :
    Definable M (fun e => SetClosed (e s)) := by
  have hs := defAllMem (defMemberParam C.omega_mem 0) s
  have hc := defAllMem (setStep_definable C (s+1) 0) s
  exact (hs.and hc).congr (fun e => (setClosed_spec (e s)).symm)

theorem leastFamily_definable (C : Context M) (q c s : ℕ) :
    Definable M (fun e => LeastFamily (e q) (e c) (e s)) := by
  have hm := defAllMem (defImp (member_definable C (c+1) 0)
    (defImp (setClosed_definable C 0) (defSubset C (s+1) 0))) q
  exact (member_definable C c s).and ((setClosed_definable C s).and hm)

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

theorem supportGraph_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M) (p : SentenceForm) :
    supportGraph p ∈ M := by
  have hn (k : ℕ) : natSet.{u} k ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨k,rfl⟩)
  exact finite_range_mem M hM hP hU (hn 0) _ _
    (fun _ => orderedPair_mem M hM hP (hn _) (hn _))

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

theorem defOrderedPair (C : Context M) (z i j : ℕ) :
    Definable M (fun e => e z = ZFSet.pair (e i) (e j)) :=
  ⟨.orderedPair (2*z) (2*i) (2*j),fun _ => ZFSet.omega,fun _ => C.omega_mem,
    fun e => by simp only [Formula.eval_orderedPair,mix_even]⟩

theorem defIff {P Q : (ℕ → ZFSet.{u}) → Prop}
    (hp : Definable M P) (hq : Definable M Q) : Definable M (fun e => P e ↔ Q e) :=
  ((defImp hp hq).and (defImp hq hp)).congr (fun _ => iff_def.symm)

theorem setSupportStep_definable (C : Context M) (g c b : ℕ) :
    Definable M (fun e => SetSupportStep (e g) (e c) (e b)) := by
  have hm : Primrec₂ (fun i j : ℕ => max i j + 1) := Primrec.succ.comp Primrec.nat_max
  have ha (t : ℕ) := (((binaryGraph_definable C _ (atomic_primrec t) 1 0 (c+2)).and
    (binaryGraph_definable C _ hm 1 0 (b+2))).existsParam C.omega_mem).existsParam C.omega_mem
  have hc := (((((binaryGraph_definable C _ (binary_primrec 2) 3 2 (c+4)).and
    ((defPairMem C 3 1 (g+4)).and ((defPairMem C 2 0 (g+4)).and
      (binaryGraph_definable C max Primrec.nat_max 1 0 (b+4))))).existsParam C.omega_mem).existsParam
        C.omega_mem).existsParam C.omega_mem).existsParam C.omega_mem
  have hn := ((unaryGraph_definable C _ (unary_primrec 3) 0 (c+1)).and
    (defPairMem C 0 (b+1) (g+1))).existsParam C.omega_mem
  have hp : Primrec (fun n : ℕ => n-1) := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  have hx := (((unaryGraph_definable C _ (unary_primrec 4) 1 (c+2)).and
    ((defPairMem C 1 0 (g+2)).and (unaryGraph_definable C _ hp 0 (b+2)))).existsParam
      C.omega_mem).existsParam C.omega_mem
  exact defOr (ha 0) (defOr (ha 1) (defOr hc (defOr hn hx)))

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

theorem setSupportRecursion_definable (C : Context M) (f g : ℕ) :
    Definable M (fun e => SetSupportRecursion (e f) (e g)) := by
  have hn := defAllMem (((defOrderedPair C 2 1 0).existsParam C.omega_mem).existsMem (f+1)) g
  have hr := defAllMem (defAllParam (defIff (defPairMem C 1 0 (g+2))
    (setSupportStep_definable C (g+2) 1 0)) C.omega_mem) f
  exact hn.and hr

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

theorem leastFamily_param (C : Context M) {Q : ZFSet.{u}} (hQ : Q ∈ M) (c s : ℕ) :
    Definable M (fun e => LeastFamily Q (e c) (e s)) := by
  have hs : ({Q} : ZFSet.{u}) ∈ M := singleton_mem M C.transitive C.pairing hQ
  exact (((equal_param hQ 0).and (leastFamily_definable C 0 (c+1) (s+1))).existsParam hs).congr
    (fun e => by simp only [ZFSet.mem_singleton,cons_zero,cons_succ]; simp)

theorem boundWitness_definable (C : Context M) {Q B : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (c b : ℕ) :
    Definable M (fun e => BoundWitness Q B (e c) (e b)) :=
  (((leastFamily_param C hQ (c+2) 1).and ((setSupportRecursion_definable C 1 0).and
    (defPairMem C (c+2) (b+2) 0))).existsParam hB).existsParam hQ

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

theorem internal_support_bound (C : Context M) :
    ∃ B ∈ M, ∀ p : SentenceForm, supportGraph p ∈ B := by
  obtain ⟨B,hB,hdef⟩ := internal_power M C.transitive C.power (C.prod_mem C.omega_mem C.omega_mem)
  exact ⟨B,hB,fun p => (hdef _).mpr
    ⟨supportGraph_mem M C.transitive C.pairing C.union C.omega_mem p,supportGraph_subset p⟩⟩

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

theorem internal_tuple_graph_bound (C : Context M) {A : ZFSet.{u}} (hA : A ∈ M) :
    ∃ G ∈ M, ∀ (n : ℕ) (v : Fin n → ZFSet.{u}),
      (∀ i, v i ∈ A) → tupleGraph v ∈ G := by
  obtain ⟨G,hG,hdef⟩ := internal_power M C.transitive C.power (C.prod_mem C.omega_mem hA)
  refine ⟨G,hG,fun n v hv => (hdef _).mpr ⟨?_,?_⟩⟩
  · exact tupleGraph_mem M C.transitive C.pairing C.union C.omega_mem v
      (fun i => C.transitive A hA _ (hv i))
  · intro z hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i.val,rfl⟩,_,hv i,rfl⟩

theorem tupleLookup_definable (C : Context M) {G : ZFSet.{u}} (hG : G ∈ M) (t i x : ℕ) :
    Definable M (fun e => TupleLookup G (e t) (e i) (e x)) :=
  (((defOrderedPair C (t+2) 1 0).and (defPairMem C (i+2) (x+2) 0)).existsParam hG).existsParam C.omega_mem

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

theorem tupleAdequate_definable (C : Context M) {Q B G : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (hG : G ∈ M) (c t : ℕ) :
    Definable M (fun e => TupleAdequate Q B G (e c) (e t)) :=
  ((((defOrderedPair C (t+3) 2 1).and ((boundWitness_definable C hQ hB (c+3) 0).and
    (defSubset C 0 2))).existsParam C.omega_mem).existsParam hG).existsParam C.omega_mem

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

theorem tuplePrefix_definable (C : Context M) {G : ZFSet.{u}} (hG : G ∈ M) (a t x s : ℕ) :
    Definable M (fun e => TuplePrefix (e a) G (e t) (e x) (e s)) := by
  let d := cons ZFSet.omega (cons G (fun _ => natSet 0))
  let r : ℕ → ℕ := fun i => match i with
    | 0 => 2*a | 1 => 1 | 2 => 3 | 3 => 2*t | 4 => 2*x | 5 => 2*s | _ => 5
  refine ⟨(tuplePrefixFormula 0 1 2 3 4 5 6).rename r,d,?_,?_⟩
  · intro i
    rcases i with _|_|i
    · exact C.omega_mem
    · exact hG
    · exact C.transitive _ C.omega_mem _ ((mem_omega _).mpr ⟨0,rfl⟩)
  · intro e
    rw [Formula.eval_rename_comp]
    have he : mix e d ∘ r = cons (e a) (cons ZFSet.omega (cons G
        (cons (e t) (cons (e x) (cons (e s) (fun _ => natSet 0)))))) := by
      funext i
      rcases i with _|_|_|_|_|_|i <;> simp only [r,d,Function.comp_apply,mix_even,cons_zero,cons_succ] <;> rfl
    rw [he]
    rfl

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

theorem setTruthStep_definable (C : Context M) {G : ZFSet.{u}}
    (hG : G ∈ M) (a T S c t : ℕ) :
    Definable M (fun e => SetTruthStep (e a) G (e T) (e S) (e c) (e t)) := by
  have ha (tag : ℕ) (hr : Definable M (fun e => e 1 = e 0)) :=
    (((((binaryGraph_definable C _ (atomic_primrec tag) 3 2 (c+4)).and
      ((tupleLookup_definable C hG (t+4) 3 1).and
        ((tupleLookup_definable C hG (t+4) 2 0).and hr))).existsMem (a+3)).existsMem (a+2)).existsParam
          C.omega_mem).existsParam C.omega_mem
  have he := ha 0 (equal_definable C 1 0)
  have hm := (((((binaryGraph_definable C _ (atomic_primrec 1) 3 2 (c+4)).and
    ((tupleLookup_definable C hG (t+4) 3 1).and
      ((tupleLookup_definable C hG (t+4) 2 0).and (member_definable C 1 0)))).existsMem (a+3)).existsMem
        (a+2)).existsParam C.omega_mem).existsParam C.omega_mem
  have hc := (((binaryGraph_definable C _ (binary_primrec 2) 1 0 (c+2)).and
    ((defPairMem C 1 (t+2) (S+2)).and (defPairMem C 0 (t+2) (S+2)))).existsParam
      C.omega_mem).existsParam C.omega_mem
  have hn := ((unaryGraph_definable C _ (unary_primrec 3) 0 (c+1)).and
    (defPairMem C 0 (t+1) (S+1)).neg).existsParam C.omega_mem
  have hbody := (((tuplePrefix_definable C hG (a+3) (t+3) 1 0).and
    (defPairMem C 2 0 (S+3))).existsMem (T+2)).existsMem (a+1)
  have hx := ((unaryGraph_definable C _ (unary_primrec 4) 0 (c+1)).and hbody).existsParam C.omega_mem
  exact defOr he (defOr hm (defOr hc (defOr hn hx)))

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

theorem setTruthRecursion_definable (C : Context M) {Q B G : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (hG : G ∈ M) (a T f s : ℕ) :
    Definable M (fun e => SetTruthRecursion Q B G (e a) (e T) (e f) (e s)) := by
  have hn := defAllMem ((((tupleAdequate_definable C hQ hB hG 1 0).and
    (defOrderedPair C 2 1 0)).existsMem (T+2)).existsMem (f+1)) s
  have hr := defAllMem (defAllMem (defImp (tupleAdequate_definable C hQ hB hG 1 0)
    (defIff (defPairMem C 1 0 (s+2))
      (setTruthStep_definable C hG (a+2) (T+2) (s+2) 1 0))) (T+1)) f
  exact hn.and hr

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

theorem truthWitness_definable (C : Context M) {Q B G : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (hG : G ∈ M) (a T c s : ℕ) :
    Definable M (fun e => TruthWitness Q B G (e a) (e T) (e c) (e s)) :=
  ((leastFamily_param C hQ (c+1) 0).and
    (setTruthRecursion_definable C hQ hB hG (a+1) (T+1) 0 (s+1))).existsParam hQ

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SatisfactionCertificateBound
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem satisfactionSet_subset_product (A : ZFSet.{u}) :
    satisfactionSet A ⊆ ZFSet.prod ZFSet.omega (tupleSpace A) := by
  intro z hz
  obtain ⟨⟨⟨n,p,v⟩,_,_⟩,rfl⟩ := ZFSet.mem_range.mp hz
  exact ZFSet.mem_prod.mpr ⟨natSet (Encodable.encode p),(mem_omega _).mpr ⟨_,rfl⟩,
    tupleCode (fun i => label A (v i)),
    (mem_tupleSpace A _).mpr ⟨n,_,fun i => label_mem A (v i),rfl⟩,rfl⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformInternalSatisfaction
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
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

theorem satisfactionWitness_definable (C : Context M) {Q B G H : ZFSet.{u}}
    (hQ : Q ∈ M) (hB : B ∈ M) (hG : G ∈ M) (hH : H ∈ M) (a T z : ℕ) :
    Definable M (fun e => SatisfactionWitness Q B G H (e a) (e T) (e z)) :=
  ((((truthWitness_definable C hQ hB hG (a+3) (T+3) 2 0).and
    ((defPairMem C 2 1 0).and (defOrderedPair C (z+3) 2 1))).existsParam hH).existsMem
      (T+1)).existsParam C.omega_mem

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

theorem tupleSystem_canonical (A G : ZFSet.{u})
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G) :
    TupleSystem A G (tupleSpace A) := by
  refine ⟨?_,?_,?_⟩
  · intro t ht
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    exact ⟨_,(mem_omega _).mpr ⟨n,rfl⟩,_,hG n v hv,rfl,tupleGraph_function A v hv⟩
  · let v : Fin 0 → ZFSet.{u} := Fin.elim0
    have hg : tupleGraph v = (∅ : ZFSet.{u}) := by
      apply ZFSet.ext; intro z; simp [tupleGraph]
    have ht := (mem_tupleSpace A _).mpr ⟨0,v,fun i => Fin.elim0 i,rfl⟩
    change ZFSet.pair (natSet 0) (tupleGraph v) ∈ tupleSpace A at ht
    rwa [hg] at ht
  · intro t ht x hx
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    let w : Fin (n+1) → ZFSet.{u} := Fin.cases x v
    exact ⟨tupleCode w,(mem_tupleSpace A _).mpr ⟨n+1,w,fun i => Fin.cases hx hv i,rfl⟩,
      (tuplePrefix_spec A G hG v hv x _ hx).mpr rfl⟩

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

theorem satisfactionSystem_canonical (Q B A G H : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (hH : ∀ p : SentenceForm, finiteSatisfaction A (subformulas p) ∈ H) :
    SatisfactionSystem Q B A G (tupleSpace A) H (satisfactionSet A) := by
  refine ⟨tupleSystem_canonical A G hG,?_,?_,?_⟩
  · intro c _ F _ hf
    obtain ⟨p,rfl⟩ := setClosed_valid F hf.2.1 c hf.1
    have he := (leastFamily_spec Q F p (hQ p)).mp hf
    subst F
    exact ⟨_,hH p,(setTruthRecursion_spec Q B G A _ hQ hB hG p).mpr
      (finiteSatisfaction_recursion A p)⟩
  · intro z hz
    exact (satisfactionWitness_spec Q B G H A z hQ hB hG hH).mpr hz
  · intro c hc t ht S hS hs hct
    exact (satisfactionWitness_spec Q B G H A _ hQ hB hG hH).mp
      ⟨c,hc,t,ht,S,hS,hs,hct,rfl⟩

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

theorem defSystem_canonical (Q B A G H : ZFSet.{u})
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hG : ∀ (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) → tupleGraph v ∈ G)
    (hH : ∀ p : SentenceForm, finiteSatisfaction A (subformulas p) ∈ H) :
    DefSystem Q B A G (tupleSpace A) H (satisfactionSet A) (definablePower A) := by
  refine ⟨satisfactionSystem_canonical Q B A G H hQ hB hG hH,?_,?_⟩
  · intro S hS
    exact (definitionWitness_spec Q B G A S hQ hB hG).mpr ((mem_definablePower A S).mp hS)
  · intro c _ t ht ha
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    obtain ⟨p,rfl,hp⟩ := (parameterAdequate_spec Q B G c hQ hB v (hG n v hv)).mp ha
    exact ⟨definedSubset A p v,(mem_definablePower A _).mpr ⟨n,p,v,hp,hv,rfl⟩,
      (definesSubset_spec A G _ hG p v hv hp).mpr rfl⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ContextDefinablePower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem tupleSpace_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) : tupleSpace A ∈ M := by
  have hS := C.separation
  have hω := C.omega_mem
  obtain ⟨Q,hQM,hQdef⟩ := internal_power M C.transitive C.power
    (product_mem M C.transitive C.pairing C.union C.power hS hω hA)
  have hQ (n : ℕ) (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) : tupleGraph v ∈ Q := by
    apply (hQdef _).mpr
    refine ⟨tupleGraph_mem M C.transitive C.pairing C.union hω v (fun i => C.transitive A hA _ (hv i)),?_⟩
    intro z hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i.val,rfl⟩,_,hv i,rfl⟩
  let e := cons ZFSet.omega (cons A (fun _ => Q))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i; exact hω; exact hA; exact hQM
  have hs := sep_mem M C.transitive hS (tupleFormula 1 2 3 0) e he
    (product_mem M C.transitive C.pairing C.union C.power hS hω hQM)
  have heq : (ZFSet.prod ZFSet.omega Q).sep
      (fun t => (tupleFormula 1 2 3 0).Eval (cons t e)) = tupleSpace A := by
    apply ZFSet.ext; intro t
    rw [ZFSet.mem_sep,tupleFormula_spec 1 2 3 0 (cons t e) rfl hQ]
    change (t ∈ ZFSet.prod ZFSet.omega Q ∧ t ∈ tupleSpace A) ↔ t ∈ tupleSpace A
    refine ⟨And.right,fun ht => ⟨?_,ht⟩⟩
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    exact ZFSet.mem_prod.mpr ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,tupleGraph v,hQ n v hv,rfl⟩
  exact heq ▸ hs

theorem truthSlice_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) (p : SentenceForm) : truthSlice A p ∈ M := by
  have hS := C.separation
  have hω := C.omega_mem
  have hn (n : ℕ) : natSet.{u} n ∈ M := C.transitive _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  obtain ⟨Q,hQM,hQdef⟩ := internal_power M C.transitive C.power
    (product_mem M C.transitive C.pairing C.union C.power hS hω hA)
  have hQ {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) : tupleGraph v ∈ Q := by
    apply (hQdef _).mpr
    refine ⟨tupleGraph_mem M C.transitive C.pairing C.union hω v (fun i => C.transitive A hA _ (hv i)),?_⟩
    intro z hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i.val,rfl⟩,_,hv i,rfl⟩
  let e := cons ZFSet.omega (cons A (cons Q (cons (natSet p.bound) natSet)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact hω; exact hA; exact hQM; exact hn _; exact hn _
  let φ := tupleTruth p 1 2 3 4 0 (fun i => i+5)
  have hs := sep_mem M C.transitive hS φ e he (tupleSpace_mem_of_context M A C hA)
  have heq : (tupleSpace A).sep (fun t => φ.Eval (cons t e)) = truthSlice A p := by
    apply ZFSet.ext; intro t
    rw [truthSlice,ZFSet.mem_sep,ZFSet.mem_sep]
    apply and_congr_right; intro ht
    obtain ⟨n,v,hv,rfl⟩ := (mem_tupleSpace A t).mp ht
    exact (tupleTruth_spec p 1 2 3 4 0 (fun i => i+5) (cons (tupleCode v) e)
      rfl rfl (fun _ _ => rfl) v hv rfl (hQ v hv)).trans (satisfactionSet_record A p v hv).symm
  exact heq ▸ hs

theorem finiteSatisfaction_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) (ps : List SentenceForm) : finiteSatisfaction A ps ∈ M := by
  have hω := C.omega_mem
  have hn (n : ℕ) : natSet.{u} n ∈ M := C.transitive _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  apply union_mem M C.transitive C.union
  apply finite_range_mem M C.transitive C.pairing C.union (hn 0)
  intro i
  exact product_mem M C.transitive C.pairing C.union C.power C.separation
    (singleton_mem M C.transitive C.pairing (hn _)) (truthSlice_mem_of_context M A C hA ps[i])

theorem internal_certificate_bound_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) :
    ∃ Q ∈ M,
      (∀ S, S ∈ Q ↔ S ∈ M ∧ S ⊆ ZFSet.prod ZFSet.omega (tupleSpace A)) ∧
      ∀ ps : List SentenceForm, finiteSatisfaction A ps ∈ Q := by
  obtain ⟨Q,hQ,hdef⟩ := internal_power M C.transitive C.power
    (product_mem M C.transitive C.pairing C.union C.power C.separation
      (C.omega_mem) (tupleSpace_mem_of_context M A C hA))
  refine ⟨Q,hQ,hdef,fun ps => (hdef _).mpr ⟨finiteSatisfaction_mem_of_context M A C hA ps,?_⟩⟩
  exact fun z hz => satisfactionSet_subset_product A (finiteSatisfaction_subset A ps hz)

theorem satisfactionSet_mem_of_context (M A : ZFSet.{u}) (C : Context M) (hA : A ∈ M) : satisfactionSet A ∈ M := by
  obtain ⟨Q,hQ,_,hf⟩ := internal_family_bound M C.transitive C.pairing C.union C.power C.omega_mem
  obtain ⟨B,hB,hb⟩ := internal_support_bound C
  obtain ⟨G,hG,hg⟩ := internal_tuple_graph_bound C hA
  obtain ⟨H,hH,_,hh⟩ := internal_certificate_bound_of_context M A C hA
  have ht := tupleSpace_mem_of_context M A C hA
  let e := cons A (cons (tupleSpace A) (fun _ => ZFSet.omega))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hA
    · exact ht
    · exact C.omega_mem
  have hd := satisfactionWitness_definable C hQ hB hG hH 1 2 0
  have hs := hd.sep_mem C e he (C.prod_mem C.omega_mem ht)
  have heq : (ZFSet.prod ZFSet.omega (tupleSpace A)).sep
      (fun z => SatisfactionWitness Q B G H A (tupleSpace A) z) = satisfactionSet A := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,satisfactionWitness_spec Q B G H A z hf hb hg (fun p => hh (subformulas p))]
    exact ⟨And.right,fun hz => ⟨satisfactionSet_subset_product A hz,hz⟩⟩
  exact heq ▸ hs

theorem internal_defSystem_of_context_oai (M : ZFSet.{u}) (C : Context M)
    (Q B A : ZFSet.{u}) (hA : A ∈ M)
    (hQ : ∀ p : SentenceForm, family p ∈ Q)
    (hB : ∀ p : SentenceForm, supportGraph p ∈ B) :
    ∃ G ∈ M, ∃ T ∈ M, ∃ H ∈ M, ∃ Z ∈ M,
      DefSystem Q B A G T H Z (definablePower A) := by
  obtain ⟨G,hG,hg⟩ := internal_tuple_graph_bound C hA
  obtain ⟨H,hH,_,hh⟩ := internal_certificate_bound_of_context M A C hA
  exact ⟨G,hG,tupleSpace A,tupleSpace_mem_of_context M A C hA,H,hH,
    satisfactionSet A,satisfactionSet_mem_of_context M A C hA,
    defSystem_canonical Q B A G H hQ hB hg (fun p => hh (subformulas p))⟩

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution.{u} : type_of% @OAI.TuringRigidity.RelativeConstructible.internal_defSystem_of_context_oai.{u} := @OAI.TuringRigidity.RelativeConstructible.internal_defSystem_of_context_oai.{u}

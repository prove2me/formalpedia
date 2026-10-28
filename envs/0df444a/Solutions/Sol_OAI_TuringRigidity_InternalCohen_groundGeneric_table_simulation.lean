-- Prove2me | solution 1 for OAI.TuringRigidity.InternalCohen.groundGeneric_table_simulation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:03:46.339453+00:00
-- url     : https://prove2.me/submissions/8336c4eb-1a71-46a1-8fb8-9fa173739970

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectiveCohen
open Encodable UniformOracle ArithmeticHierarchy OracleJump

theorem sigma1_enumeration {Y : Oracle} {P : ℕ → Prop} (h : Sigma Y 1 P) :
    ∃ e, ∀ n, P n ↔ Halts Y e n := by
  classical
  obtain ⟨Q,hQ,he⟩ := h
  have hf := Nat.RecursiveIn.rfind (recursive_not hQ)
  obtain ⟨e,hd⟩ := partial_table hf
  refine ⟨e,fun n => (he n).trans ?_⟩
  rw [hd n]
  erw [Nat.rfind_dom]
  simp [Quant]

theorem OneGeneric.decides {Y G : Oracle} (hG : OneGeneric Y G)
    {P : ℕ → Prop} (hP : Sigma Y 1 P) : ∃ p : List Bool,
      (∀ n < p.length, G n = p.getD n false) ∧
        (P (encode p) ∨ ∀ q : List Bool, p <+: q → ¬ P (encode q)) := by
  obtain ⟨e,he⟩ := sigma1_enumeration hP
  obtain ⟨p,hp,hd⟩ := hG e
  refine ⟨p,hp,?_⟩
  simpa only [he] using hd

end TuringRigidity.EffectiveCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformPrograms
open Encodable

variable {X : Type*} {O : X → ℕ →. ℕ}

theorem oracle_free {f : ℕ →. ℕ} (hf : Nat.RecursiveIn ∅ f) :
    ∃ p : OracleCode, ∀ g, OracleCode.eval g p = f := by
  induction hf with
  | zero => exact ⟨.zero,fun _ => rfl⟩
  | succ => exact ⟨.succ,fun _ => rfl⟩
  | left => exact ⟨.left,fun _ => rfl⟩
  | right => exact ⟨.right,fun _ => rfl⟩
  | oracle f hf => simp at hf
  | pair _ _ hc hd =>
    obtain ⟨c,hc⟩ := hc; obtain ⟨d,hd⟩ := hd
    exact ⟨.pair c d,fun g => by simp only [OracleCode.eval,hc g,hd g]; rfl⟩
  | comp _ _ hc hd =>
    obtain ⟨c,hc⟩ := hc; obtain ⟨d,hd⟩ := hd
    exact ⟨.comp c d,fun g => by simp only [OracleCode.eval,hc g,hd g]; rfl⟩
  | prec _ _ hc hd =>
    obtain ⟨c,hc⟩ := hc; obtain ⟨d,hd⟩ := hd
    exact ⟨.prec c d,fun g => by simp only [OracleCode.eval,hc g,hd g]; rfl⟩
  | rfind _ hc =>
    obtain ⟨c,hc⟩ := hc
    exact ⟨.find c,fun g => by simp only [OracleCode.eval,hc g]; rfl⟩

theorem primrec {f : ℕ → ℕ} (hf : Primrec f) : Runs O (fun _ n => Part.some (f n)) := by
  obtain ⟨p,hp⟩ := oracle_free (RecursiveIn.iff_nat.mp (hf.computableIn (O := ∅)))
  exact ⟨p,fun x => hp (O x)⟩

theorem query : Runs O O := ⟨.query,fun _ => rfl⟩

theorem Runs.of_eq {f g : X → ℕ →. ℕ} (hf : Runs O f) (h : ∀ x n, f x n = g x n) : Runs O g := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun x => (hp x).trans (funext (h x))⟩

theorem Runs.pair {f g : X → ℕ →. ℕ} (hf : Runs O f) (hg : Runs O g) :
    Runs O (fun x n => Nat.pair <$> f x n <*> g x n) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨.pair p q,fun x => by simp only [OracleCode.eval,hp x,hq x]; rfl⟩

theorem Runs.comp {f g : X → ℕ →. ℕ} (hf : Runs O f) (hg : Runs O g) :
    Runs O (fun x n => g x n >>= f x) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨.comp p q,fun x => by simp only [OracleCode.eval,hp x,hq x]; rfl⟩

theorem Runs.prec {f g : X → ℕ →. ℕ} (hf : Runs O f) (hg : Runs O g) :
    Runs O (fun x p => ((Nat.unpair p).2).rec (f x (Nat.unpair p).1)
      (fun y ih => ih.bind (fun i => g x (Nat.pair (Nat.unpair p).1 (Nat.pair y i))))) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨.prec p q,fun x => by simp only [OracleCode.eval,hp x,hq x]; rfl⟩

theorem Runs.find {f : X → ℕ →. ℕ} (hf : Runs O f) :
    Runs O (fun x a => Nat.rfind (fun n => (fun m => decide (m=0)) <$> f x (Nat.pair a n))) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨.find p,fun x => by simp only [OracleCode.eval,hp x]; rfl⟩

theorem total_comp {f g : X → ℕ → ℕ}
    (hf : Runs O (fun x n => Part.some (f x n)))
    (hg : Runs O (fun x n => Part.some (g x n))) :
    Runs O (fun x n => Part.some (f x (g x n))) := by
  simpa using hf.comp hg

theorem total_pair {f g : X → ℕ → ℕ}
    (hf : Runs O (fun x n => Part.some (f x n)))
    (hg : Runs O (fun x n => Part.some (g x n))) :
    Runs O (fun x n => Part.some (Nat.pair (f x n) (g x n))) := by
  simpa [Seq.seq] using hf.pair hg

theorem initial_program (g : X → ℕ → ℕ)
    (hquery : Runs O (fun x n => Part.some (g x n))) :
    Runs O (fun x m => Part.some (encode (UniformOracle.oraclePrefix (g x) m))) := by
  have hy := (primrec (O := O)) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := (primrec (O := O)) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp ((primrec (O := O)) (UniformOracle.appendEncoded_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hquery hy))
  have hp := Runs.prec ((primrec (O := O)) (Primrec.const (encode ([] : List ℕ)))) hs
  have hh := Runs.comp hp (total_pair ((primrec (O := O)) (Primrec.const 0))
    ((primrec (O := O)) Primrec.id))
  apply hh.of_eq
  intro x n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [UniformOracle.appendEncoded,UniformOracle.oraclePrefix,List.range_succ]

private theorem flag_primrec : Primrec flag := by
  apply (Primrec.cond (Primrec.option_isSome.comp (Primrec.option_getD_default.comp (Primrec.decode (α := Option ℕ))))
    (Primrec.const 0) (Primrec.const 1)).of_eq
  intro n
  change (cond ((decode (α := Option ℕ) n).getD none).isSome 0 1) = _
  cases hh : ((decode (α := Option ℕ) n).getD none).isSome <;> simp only [flag,hh] <;> rfl
private theorem answer_primrec : Primrec answer :=
  Primrec.option_getD_default.comp (Primrec.option_getD_default.comp Primrec.decode)

theorem total_search {E : X → ℕ → ℕ → Option ℕ}
    (hE : Runs O (fun x z => Part.some (encode (E x (Nat.unpair z).1 (Nat.unpair z).2))))
    (f : X → ℕ → ℕ) (hsound : ∀ x n m a, a ∈ E x n m → a = f x n)
    (hcomplete : ∀ x n, ∃ m a, a ∈ E x n m) :
    Runs O (fun x n => Part.some (f x n)) := by
  have hflag := total_comp (primrec flag_primrec) hE
  have hfind := Runs.find hflag
  have hpair := Runs.pair (primrec Primrec.id) hfind
  have hrun := Runs.comp (primrec answer_primrec) (Runs.comp hE hpair)
  apply hrun.of_eq
  intro x n
  apply Part.eq_some_iff.mpr
  have hex : ∃ m, (E x n m).isSome = true := by
    obtain ⟨m,a,ha⟩ := hcomplete x n
    exact ⟨m,Option.isSome_iff_exists.mpr ⟨a,ha⟩⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp hm
  have hval : a = f x n := hsound x n m a ha
  have hmem : m ∈ Nat.rfind (fun k =>
      (fun v : ℕ => decide (v=0)) <$> Part.some (flag (encode (E x n k)))) := by
    apply Nat.mem_rfind.mpr
    constructor
    · simp [flag,m,hm]
    · intro k hk
      have hk' : (E x n k).isSome = false := Bool.eq_false_iff.mpr (Nat.find_min hex hk)
      simp [flag,hk']
  apply Part.mem_bind_iff.mpr
  refine ⟨encode (E x n m),?_,?_⟩
  · apply Part.mem_bind_iff.mpr
    refine ⟨Nat.pair n m,?_,?_⟩
    · simp only [Seq.seq]
      apply Part.mem_bind_iff.mpr
      refine ⟨Nat.pair n,(Part.mem_map_iff _).mpr ⟨n,Part.mem_some _,rfl⟩,?_⟩
      exact (Part.mem_map_iff _).mpr ⟨m,by simpa only [Nat.unpair_pair] using hmem,rfl⟩
    · simp
  · have hea : E x n m = some a := Option.mem_def.mp ha
    apply Part.mem_some_iff.mpr
    rw [hea]
    simpa only [answer,Encodable.encodek,Option.getD_some] using hval.symm

end TuringRigidity.UniformPrograms

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenConditions
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing

theorem conditions_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) : conditions ∈ M := by
  obtain ⟨c,hc,hdef⟩ := conditions_exist_absolute_without_choice M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT)
    (alphabet_mem M hM hT)
  have he : c = conditions := ZFSet.ext (fun p => (hdef p).trans (mem_conditions p).symm)
  exact he ▸ hc

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

end TuringRigidity.InternalCohen

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticOracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable UniformOracle CommonIdeal IndexMatrix TableIndices OracleJump EncodedForcing
noncomputable section

theorem halts_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {c e n : ℕ → ℕ} (hc : Primrec c) (he : Primrec e) (hn : Primrec n) :
    Arith (fun O v => Halts (B O (c v)) (e v) (n v)) := by
  have h := (run_arith hB (hc.comp (left_primrec.comp left_primrec))
    (he.comp (left_primrec.comp left_primrec))
    (hn.comp (left_primrec.comp left_primrec)) (right_primrec.comp left_primrec)
    right_primrec).ex.ex
  exact h.congr (fun _ _ => by simp only [Halts,left,right,Nat.unpair_pair,Option.mem_def])

theorem jump_arith {B : OracleFamily} (hB : ArithmeticOracle B) :
    ArithmeticOracle (fun O v => jump (B O v)) :=
  (halts_arith hB left_primrec (left_primrec.comp right_primrec)
    (right_primrec.comp right_primrec)).congr (fun _ _ => by simp [jump])

end
end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenHalting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenHalting
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing IndexMatrix

theorem table_primrec : Primrec table := Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem agrees_recursive (Y : Oracle) : RecursivePred Y (fun v =>
    Agrees Y (word (Nat.unpair v).1) (table (Nat.unpair v).2)) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let p := word_primrec.comp (f.comp f)
  let L := table_primrec.comp (r.comp f)
  let i := r
  let half := Primrec.nat_div.comp i (Primrec.const 2)
  let val := (Primrec.list_getD 0).comp L i
  have ho := recursive_primrecPred Y (Primrec.eq.comp (Primrec.nat_bodd.comp i) (Primrec.const true))
  have hb := recursive_primrecPred Y (Primrec.nat_lt.comp half (Primrec.list_length.comp p))
  have hp := recursive_primrecPred Y (Primrec.eq.comp val
    (bit_primrec.comp ((Primrec.list_getD false).comp p half)))
  have hquery : Nat.RecursiveIn {oracleFunction Y} (oracleFunction Y) := .oracle _ (Set.mem_singleton _)
  have hq : Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some (bit (Y ((Nat.unpair v).2/2)))) := by
    exact _root_.OAI.TuringRigidity.UniformOracle.total_comp (f := fun input => bit (Y input)) hquery (_root_.OAI.TuringRigidity.UniformOracle.total_primrec half)
  have hv := _root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec val) hq
  have heq : Primrec (fun v : ℕ => if (Nat.unpair v).1 = (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp f r) (Primrec.const 1) (Primrec.const 0)
  have hy : RecursivePred Y (fun v => (table (Nat.unpair (Nat.unpair v).1).2).getD (Nat.unpair v).2 0 =
      bit (Y ((Nat.unpair v).2/2))) := by
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec heq) hv).of_eq (fun v => by simp [bit])
  have hi := Form.or (n := 0) (s := true) (recursive_and ho (recursive_and hb hp))
    (recursive_and (recursive_not ho) hy)
  apply Form.congr (n := 0) (s := true) (recursive_bounded_all hi (Primrec.list_length.comp (table_primrec.comp r)))
  intro v
  simp only [Agrees,Nat.unpair_pair]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  cases i.bodd <;> simp

theorem certificate_recursive (Y : Oracle) : RecursivePred Y (Certificate Y) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have ha := recursive_comp (agrees_recursive Y) (Primrec₂.natPair.comp (r.comp f) (f.comp r))
  have he := Nat.Partrec.Code.primrec_evaln.comp
    (((r.comp r).pair (machine_primrec.comp (f.comp (f.comp f)))).pair
      (Primrec₂.natPair.comp (Primrec.encode.comp (table_primrec.comp (f.comp r))) (r.comp (f.comp f))))
  unfold Certificate
  simpa only [Nat.unpair_pair] using recursive_and ha (recursive_primrecPred Y
    (Primrec.eq.comp (Primrec.option_isSome.comp he) (Primrec.const true)))

theorem openHalts_sigma (Y : Oracle) : Sigma Y 1 (fun v => OpenHalts Y (Nat.unpair v).1 (Nat.unpair v).2) := by
  simpa only [OpenHalts,Nat.pair_unpair] using exists_form (n := 0) (certificate_recursive Y)

theorem initial_getD (G : Oracle) {m i : ℕ} (hi : i < m) : (initial G m).getD i false = G i := by
  simp [initial,List.getD_eq_getElem?_getD,List.getElem?_range hi]

theorem prefix_initial {G : Oracle} {p : List Bool} (hp : Prefix G p) : p = initial G p.length := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h := hp i hi
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi, initial, hi] using h.symm

theorem initial_mono (G : Oracle) {m n : ℕ} (h : m ≤ n) : initial G m <+: initial G n := by
  exact (List.prefix_iff_eq_take.mpr (by simp [initial,← List.map_take,List.take_range,min_eq_left h]))

theorem agrees_table {Y G : Oracle} {p : List Bool} {L : List ℕ}
    (hp : Prefix G p) (h : Agrees Y p L) : L = oraclePrefix (fun i => bit (join Y G i)) L.length := by
  apply List.ext_getElem
  · simp [oraclePrefix]
  · intro i hi hj
    have hh := h i hi
    have he : L.getD i 0 = bit (join Y G i) := by
      cases hb : i.bodd with
      | false => simpa [hb,join] using hh
      | true =>
        simp only [hb,↓reduceIte] at hh
        simpa [join,hb,hp (i/2) hh.1] using hh.2
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,oraclePrefix,hi] using he

theorem openHalts_sound {Y G : Oracle} {x : ℕ} {p : List Bool}
    (hp : Prefix G p) (h : OpenHalts Y x (encode p)) : Halts (join Y G) (Nat.unpair x).1 (Nat.unpair x).2 := by
  obtain ⟨z,ha,hh⟩ := h
  simp only [Nat.unpair_pair,word,encodek,Option.getD_some] at ha hh
  obtain ⟨a,ha'⟩ := Option.isSome_iff_exists.mp hh
  refine ⟨Nat.pair (table (Nat.unpair z).1).length (Nat.unpair z).2,a,?_⟩
  have ht := agrees_table hp ha
  simpa only [TableIndices.run,trial,Nat.unpair_pair,← ht] using Option.mem_def.mpr ha'

theorem openHalts_complete {Y G : Oracle} {x : ℕ}
    (h : Halts (join Y G) (Nat.unpair x).1 (Nat.unpair x).2) :
    ∃ m, OpenHalts Y x (encode (initial G m)) := by
  obtain ⟨z,a,ha⟩ := h
  let m := (Nat.unpair z).1
  let L := oraclePrefix (fun i => bit (join Y G i)) m
  refine ⟨m,Nat.pair (encode L) (Nat.unpair z).2,?_,?_⟩
  · simp only [Nat.unpair_pair,word,table,encodek,Option.getD_some]
    intro i hi
    have him : i < m := by simpa [L,oraclePrefix] using hi
    have hh : i/2 < m := (Nat.div_le_self i 2).trans_lt him
    have hv : L.getD i 0 = bit (join Y G i) := by
      simp [L,oraclePrefix,List.getD_eq_getElem?_getD,List.getElem?_range him]
    cases hb : i.bodd with
    | false => simpa only [hb,Bool.false_eq_true,↓reduceIte,join] using hv
    | true =>
      simp only [↓reduceIte]
      exact ⟨by simpa using hh, by rw [hv,join,ite_eq_left hb,initial_getD G hh]⟩
  · simp only [Nat.unpair_pair,table,encodek,Option.getD_some]
    exact Option.isSome_iff_exists.mpr ⟨a,ha⟩

theorem openHalts_mono {Y : Oracle} {x : ℕ} {p q : List Bool}
    (hpq : p <+: q) (h : OpenHalts Y x (encode p)) : OpenHalts Y x (encode q) := by
  obtain ⟨z,ha,hh⟩ := h
  refine ⟨z,?_,by simpa only [Nat.unpair_pair] using hh⟩
  simp only [Nat.unpair_pair,word,encodek,Option.getD_some] at ha ⊢
  intro i hi
  have hv := ha i hi
  cases hb : i.bodd with
  | false => simpa only [hb,Bool.false_eq_true,↓reduceIte] using hv
  | true =>
    simp only [hb,↓reduceIte] at hv ⊢
    exact ⟨hv.1.trans_le hpq.length_le,hv.2.trans (congrArg bit
      (CodingForcing.getD_of_prefix hpq hv.1).symm)⟩

end TuringRigidity.CohenHalting

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenLowness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenLowness
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing
open CohenHalting EffectiveCohen EffectiveWitness

theorem extension_sigma (Y : Oracle) : Sigma Y 1 (fun v => Extension Y (Nat.unpair v).1 (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := EncodedForcing.prefix_recursive Y (word_primrec.comp (r.comp f)) (word_primrec.comp r)
  have hh := (openHalts_sigma Y).comp (Primrec₂.natPair.comp (f.comp f)
    (Primrec.encode.comp (word_primrec.comp r)))
  simpa only [Extension,Nat.unpair_pair] using ((Form.raise (n := 0) (s := true) hp).and hh).ex

theorem deciding_total {Y G : Oracle} (hG : OneGeneric Y G) : ∀ x, ∃ p, Deciding Y G (Nat.pair x p) := by
  intro x
  have hh := (openHalts_sigma Y).comp (Primrec₂.natPair.comp (Primrec.const x) Primrec.id)
  obtain ⟨p,hp,hd⟩ := hG.decides hh
  refine ⟨encode p,?_,?_⟩
  · simpa only [Prefix,Nat.unpair_pair,word,encodek,Option.getD_some] using hp
  · simp only [Nat.unpair_pair] at hd
    simp only [Nat.unpair_pair,word,encodek,Option.getD_some]
    rcases hd with hd | hd
    · exact Or.inl hd
    · refine Or.inr ?_
      rintro ⟨q,hpq,hq⟩
      exact hd (word q) (by simpa [word] using hpq) hq

theorem deciding_correct {Y G : Oracle} {x p : ℕ} (h : Deciding Y G (Nat.pair x p)) :
    OpenHalts Y x (encode (word p)) ↔ Halts (join Y G) (Nat.unpair x).1 (Nat.unpair x).2 := by
  obtain ⟨hp,hd⟩ := h
  simp only [Nat.unpair_pair] at hp hd
  refine ⟨openHalts_sound hp,fun hh => ?_⟩
  rcases hd with hd | hd
  · exact hd
  · exfalso
    apply hd
    obtain ⟨m,hm⟩ := openHalts_complete hh
    let n := max m (word p).length
    have hpm : word p <+: initial G n := by
      rw [prefix_initial hp]
      exact initial_mono G (le_max_right _ _)
    exact ⟨encode (initial G n),by simpa [word] using hpm,
      by simpa [word] using openHalts_mono (initial_mono G (le_max_left _ _)) hm⟩

end TuringRigidity.CohenLowness

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

@[simp] theorem pairCode_nat (i j k : ℕ) :
    PairCode (natSet.{u} i) (natSet j) (natSet k) ↔ k = Nat.pair i j := by
  simp only [PairCode,natPair_mem,true_and,pairing_code]

end
end TuringRigidity.SetModelSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenWordCodeGraph
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory SetModelFunctions SetModelArithmetic SetModelReals
open Encodable EncodedForcing

theorem wordBit_primrec : Primrec wordBit :=
  CommonIdeal.bit_primrec.comp ((Primrec.list_getD false).comp
    (word_primrec.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair))

theorem wordGraphFormula_spec (gl gb : ZFSet.{0})
    (hl : GraphCode gl (fun n => (word n).length)) (hb : GraphCode gb wordBit)
    (n : ℕ) (q : ZFSet.{0}) :
    wordGraphFormula.Eval (wordGraphEnv q (natSet n) gl gb) ↔
      q = wordCode (word n) := by
  simp only [wordGraphFormula,wordGraphEnv,Formula.Eval,Formula.eval_pairMem,
    Formula.eval_functionGraph,Formula.eval_allMem,eval_tripleFormula,
    cons_zero,cons_succ]
  simp_rw [omega_exists]
  simp only [hl]
  constructor
  · rintro ⟨l,rfl,hq,hi⟩
    have hq' : FunctionGraph (natSet (word n).length) alphabet q := hq
    have hbits (i : ℕ) (h : i < (word n).length) :
        ZFSet.pair (natSet i) (bitSet (word n)[i]) ∈ q := by
      obtain ⟨k,b,⟨_,hk⟩,hb',hi'⟩ := hi (natSet i) ((natSet_mem_natSet _ _).mpr h)
      have hk' : k = Nat.pair n i := (pairing_code n i k).mp hk
      have hb'' := (hb k b).mp hb'
      subst k
      subst b
      simpa [wordBit,List.getD,h,bitSet] using hi'
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨x,hx,y,_,rfl⟩ := hq'.1 z hz
      obtain ⟨i,hi,rfl⟩ := (mem_natSet _ _).mp hx
      have hy := hq'.functional ((natSet_mem_natSet _ _).mpr hi) hz (hbits i hi)
      rw [hy]
      exact (mem_wordCode _ _).mpr ⟨⟨i,hi⟩,rfl⟩
    · intro hz
      obtain ⟨i,rfl⟩ := (mem_wordCode _ _).mp hz
      exact hbits i.val i.isLt
  · rintro rfl
    refine ⟨(word n).length,rfl,wordCode_function _,?_⟩
    intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet _ _).mp hx
    refine ⟨Nat.pair n i,wordBit (Nat.pair n i),⟨natPair_mem _ _,
      (pairing_code _ _ _).mpr rfl⟩,(hb _ _).mpr rfl,?_⟩
    simp only [wordBit,Nat.unpair_pair]
    exact (pair_mem_wordCode _ _ _).mpr ⟨hi,by simp [List.getD,hi]⟩

theorem mem_wordCodeGraph (z : ZFSet.{0}) : z ∈ wordCodeGraph ↔
    ∃ n : ℕ, z = ZFSet.pair (natSet n) (wordCode (word n)) := by
  simp only [wordCodeGraph,ZFSet.mem_range,eq_comm]

theorem pair_mem_wordCodeGraph (n : ℕ) (q : ZFSet.{0}) :
    ZFSet.pair (natSet n) q ∈ wordCodeGraph ↔ q = wordCode (word n) := by
  rw [mem_wordCodeGraph]
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨hn,hq⟩ := ZFSet.pair_inj.mp hk
    have hn' := natSet_injective hn
    simpa only [← hn'] using hq
  · intro h
    exact ⟨n,by rw [h]⟩

theorem wordCodeGraph_function : FunctionGraph ZFSet.omega conditions wordCodeGraph := by
  constructor
  · intro z hz
    obtain ⟨n,rfl⟩ := (mem_wordCodeGraph z).mp hz
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,wordCode (word n),
      (mem_conditions _).mpr ⟨_,wordCode_function _⟩,rfl⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨wordCode (word n),(mem_conditions _).mpr ⟨_,wordCode_function _⟩,
      (pair_mem_wordCodeGraph _ _).mpr rfl,
      fun y _ hy => (pair_mem_wordCodeGraph n y).mp hy⟩

theorem wordCodeGraph_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    wordCodeGraph ∈ M := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  obtain ⟨gl,hgl,hl⟩ := primrec_graph C (Primrec.list_length.comp word_primrec)
  obtain ⟨gb,hgb,hb⟩ := primrec_graph C wordBit_primrec
  let r : ℕ → ℕ := fun i => if i < 2 then i else i+3
  let φ : Formula := .existsMem 1 (.existsMem 3
    (.conj (.orderedPair 2 1 0) (wordGraphFormula.rename r)))
  let e := cons ZFSet.omega (cons conditions (cons gl (cons gb
    (cons ZFSet.omega (cons alphabet (cons pairNumbers (fun _ => pairingSet)))))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|_|_|i
    · exact C.omega_mem
    · exact conditions_mem M hM hT
    · exact hgl
    · exact hgb
    · exact C.omega_mem
    · exact alphabet_mem M hM hT
    · exact C.pairNumbers_mem
    · exact C.pairing_mem
  have hs := sep_mem M hM C.separation φ e he
    (C.prod_mem C.omega_mem (conditions_mem M hM hT))
  have hspec (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ wordCodeGraph := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_rename_comp,
      cons_zero,cons_succ,e]
    rw [omega_exists,mem_wordCodeGraph]
    have hh (n : ℕ) (q : ZFSet.{0}) :
        cons q (cons (natSet n) (cons z e)) ∘ r = wordGraphEnv q (natSet n) gl gb := by
      funext i
      rcases i with _|_|i <;> simp [r,e,wordGraphEnv,cons]
    simp_rw [show ∀ n q, (cons q (cons (natSet n) (cons z
      (cons ZFSet.omega (cons conditions (cons gl (cons gb (cons ZFSet.omega
      (cons alphabet (cons pairNumbers (fun _ => pairingSet))))))))))) ∘ r =
      wordGraphEnv q (natSet n) gl gb from hh]
    simp_rw [wordGraphFormula_spec gl gb hl hb]
    constructor
    · rintro ⟨n,q,_,hz,rfl⟩
      exact ⟨n,hz⟩
    · rintro ⟨n,rfl⟩
      exact ⟨n,wordCode (word n),(mem_conditions _).mpr ⟨_,wordCode_function _⟩,rfl,rfl⟩
  have heq : ZFSet.sep (fun z => φ.Eval (cons z e))
      (ZFSet.prod ZFSet.omega conditions) = wordCodeGraph := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,hspec]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr (wordCodeGraph_function.1 z hz),hz⟩⟩
  exact heq ▸ hs

theorem canonical_wordCodeGraph (p : List Bool) (q : ZFSet.{0}) :
    ZFSet.pair (natSet (encode p)) q ∈ wordCodeGraph ↔ q = wordCode p := by
  simp only [pair_mem_wordCodeGraph,word,encodek,Option.getD_some]

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenFilters
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem filter_ext {P : Type*} [Preorder P] (F H : GenericFilter P)
    (h : F.carrier = H.carrier) : F = H := by
  cases F; cases H; cases h; rfl

theorem pull_push (G : GenericFilter Condition) : pullFilter (pushFilter G) = G := by
  have he : (pullFilter (pushFilter G)).carrier = G.carrier := by
    ext p; simp [pullFilter,pushFilter]
  exact filter_ext _ _ he

theorem dense_pull_iff (D : Set (Conditions conditions)) :
    Dense {p : Condition | conditionEquiv p ∈ D} ↔ Dense D := by
  constructor
  · intro h q
    obtain ⟨p,hp,hpD⟩ := h (conditionEquiv.symm q)
    exact ⟨conditionEquiv p,by simpa using conditionEquiv.monotone hp,hpD⟩
  · intro h q
    obtain ⟨p,hp,hpD⟩ := h (conditionEquiv q)
    exact ⟨conditionEquiv.symm p,by simpa using conditionEquiv.symm.monotone hp,
      by simpa using hpD⟩

theorem groundGeneric_iff (M : ZFSet.{0}) (G : GenericFilter (Conditions conditions)) :
    AtomicForcing.GroundGeneric M G ↔
      ∀ D ∈ M, Dense {p : Condition | wordCode p.word ∈ D} →
        ∃ p ∈ (pullFilter G).carrier, wordCode p.word ∈ D := by
  have hl (p : Condition) : label conditions (conditionEquiv p) = wordCode p.word :=
    label_encodeCondition p
  constructor
  · intro h D hD hd
    have hd' := (dense_pull_iff {p | label conditions p ∈ D}).mp (by simpa only [Set.mem_ofPred_eq,hl] using hd)
    obtain ⟨q,hq,hqD⟩ := h D hD hd'
    refine ⟨conditionEquiv.symm q,by simpa [pullFilter] using hq,?_⟩
    simpa only [←hl,OrderIso.apply_symm_apply] using hqD
  · intro h D hD hd
    have hd' := (dense_pull_iff {p | label conditions p ∈ D}).mpr hd
    obtain ⟨q,hq,hqD⟩ := h D hD (by simpa only [Set.mem_ofPred_eq,hl] using hd')
    exact ⟨conditionEquiv q,hq,by simpa only [hl] using hqD⟩

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenEffectiveGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory Encodable OracleJump
open UniformArithmetic CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem wordDecision_arith (e : ℕ) :
    Arith (fun O n => WordDecision (O 0) e (EncodedForcing.word n)) := by
  let w := EncodedForcing.word
  have hw : Primrec w := EncodedForcing.word_primrec
  have hp : Arith (fun (_ : Oracles) v => w (left v) <+: w (right v)) := by
    have h := Arith.pure _ (Primrec.eq.comp (hw.comp left_primrec)
      (Primrec.list_take.comp (Primrec.list_length.comp (hw.comp left_primrec))
        (hw.comp right_primrec)))
    exact h.congr (fun _ _ => List.prefix_iff_eq_take.symm)
  have hhalt := halts_arith (parameter_arith 0) (Primrec.const 0)
    (Primrec.const e) (Primrec.encode.comp hw)
  have hno := (hp.imp (hhalt.comp _ right_primrec).neg).all
  apply (hhalt.or hno).congr
  intro O n
  simp only [left,right,Nat.unpair_pair]
  constructor
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (fun q hq => by
        have hq' : w n <+: w (encode q) := by simpa [w,EncodedForcing.word] using hq
        simpa [w,EncodedForcing.word] using h (encode q) hq')
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (fun k hk => h (w k) hk)

theorem decisionCodes_true (Y : Oracle) (e n : ℕ) :
    decisionCodes Y e n = true ↔ WordDecision Y e (EncodedForcing.word n) :=
  arithmeticReal_true _ _ n

theorem decisionCodes_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (Y : Oracle) (hY : realCode Y ∈ M) (e : ℕ) : realCode (decisionCodes Y e) ∈ M :=
  sourceT_arithmetic_comprehension M hM hT (wordDecision_arith e) (fun _ => Y) (fun _ => hY)

theorem decisionSet_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (Y : Oracle) (hY : realCode Y ∈ M) (e : ℕ) : decisionSet Y e ∈ M := by
  let d := cons (realCode (decisionCodes Y e)) (fun _ => wordCodeGraph)
  have hd : ∀ i, d i ∈ M := by
    intro i
    cases i with
    | zero => exact decisionCodes_mem M hM hT Y hY e
    | succ i => exact wordCodeGraph_mem M hM hT
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 0 1 3)) d hd (conditions_mem M hM hT)
  simpa only [Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,d,decisionSet] using hs

theorem wordCode_mem_decisionSet (Y : Oracle) (e : ℕ) (p : List Bool) :
    wordCode p ∈ decisionSet Y e ↔ WordDecision Y e p := by
  rw [decisionSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x,hx,hq⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp (realCode_subset _ hx)
    have hp := wordCode_injective ((pair_mem_wordCodeGraph _ _).mp hq)
    rw [hp]
    exact (decisionCodes_true Y e n).mp ((natSet_mem_realCode _ _).mp hx)
  · intro h
    refine ⟨(mem_conditions _).mpr ⟨_,wordCode_function _⟩,natSet (encode p),?_,
      (canonical_wordCodeGraph p _).mpr rfl⟩
    apply (natSet_mem_realCode _ _).mpr
    apply (decisionCodes_true Y e (encode p)).mpr
    simpa [EncodedForcing.word] using h

theorem decisionSet_dense (Y : Oracle) (e : ℕ) :
    Dense {p : Condition | wordCode p.word ∈ decisionSet Y e} := by
  classical
  intro p
  by_cases h : ∃ q : List Bool, p.word <+: q ∧ Halts Y e (encode q)
  · obtain ⟨q,hpq,hq⟩ := h
    exact ⟨⟨q⟩,hpq,(wordCode_mem_decisionSet _ _ _).mpr (Or.inl hq)⟩
  · exact ⟨p,le_refl p,(wordCode_mem_decisionSet _ _ _).mpr
      (Or.inr (fun q hpq hq => h ⟨q,hpq,hq⟩))⟩

theorem groundGeneric_oneGeneric (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A Y : Oracle) (hY : realCode Y ∈ M)
    (hA : AtomicForcing.GroundGeneric M (pushFilter (realFilter A))) :
    EffectiveCohen.OneGeneric Y A := by
  intro e
  obtain ⟨p,hp,hd⟩ := (groundGeneric_iff M _).mp hA (decisionSet Y e)
    (decisionSet_mem M hM hT Y hY e) (decisionSet_dense Y e)
  rw [pull_push] at hp
  exact ⟨p.word,fun n hn => (hp n hn).symm,(wordCode_mem_decisionSet Y e p.word).mp hd⟩

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelRealOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic Encodable TableIndices OracleJump IndexMatrix
universe u

theorem sourceT_real_jump (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A : Oracle} (hA : A ∈ modelReals M) : jump A ∈ modelReals M :=
  sourceT_arithmetic_oracle M hM hT (jump_arith (parameter_arith 0))
    (fun _ => A) (fun _ => hA) 0

theorem sourceT_real_iterate (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A : Oracle} (hA : A ∈ modelReals M) (n : ℕ) : iterate A n ∈ modelReals M := by
  induction n with
  | zero => exact hA
  | succ n ih => exact sourceT_real_jump M hM hT ih

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenGroundJump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CountableForcing OracleJump
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem groundGeneric_iterate_oneGeneric (M : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (A R : Oracle) (hR : realCode R ∈ M)
    (hA : AtomicForcing.GroundGeneric M (pushFilter (CohenBorelForcing.realFilter A)))
    (j : ℕ) : EffectiveCohen.OneGeneric (iterate R j) A :=
  groundGeneric_oneGeneric M hM hT A (iterate R j)
    (sourceT_real_iterate M hM hT hR j) hA

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformOracleSimulation
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.UniformPrograms
variable {X Z : Type*} {O F H : X → ℕ →. ℕ}

theorem Runs.reindex (h : Runs O F) (g : Z → X) :
    Runs (O ∘ g) (F ∘ g) := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p,fun z => hp (g z)⟩

theorem Runs.simulate (h : Runs O F) (p : OracleCode) :
    Runs O (fun x => OracleCode.eval (F x) p) := by
  induction p with
  | zero => exact primrec (Primrec.const 0)
  | succ => exact primrec Primrec.succ
  | left => exact primrec (Primrec.fst.comp Primrec.unpair)
  | right => exact primrec (Primrec.snd.comp Primrec.unpair)
  | query => exact h
  | pair p q hp hq => exact hp.pair hq
  | comp p q hp hq => exact hp.comp hq
  | prec p q hp hq => exact hp.prec hq
  | find p hp => exact hp.find

theorem Runs.trans (h : Runs O F) (h' : Runs F H) : Runs O H := by
  obtain ⟨p,hp⟩ := h'
  exact (h.simulate p).of_eq (fun x n => congrFun (hp x) n)

theorem fixed_recursive {g f : ℕ →. ℕ} (hf : Nat.RecursiveIn {g} f)
    (hg : Runs O (fun _ => g)) : Runs O (fun _ => f) := by
  obtain ⟨p,hp⟩ := OracleCode.exists_code hf
  exact (hg.simulate p).of_eq (fun _ n => congrFun hp n)

theorem join_left_program (A B : X → Oracle) :
    Runs (fun x => oracleFunction (join (A x) (B x))) (fun x => oracleFunction (A x)) := by
  have hq := @query X (fun x => oracleFunction (join (A x) (B x)))
  exact (hq.comp (primrec (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))).of_eq
    (fun x n => by
      change (Part.some (2*n)).bind (fun input => oracleFunction (join (A x) (B x)) input) = _
      rw [Part.bind_some]
      simp [oracleFunction,join])

theorem join_right_program (A B : X → Oracle) :
    Runs (fun x => oracleFunction (join (A x) (B x))) (fun x => oracleFunction (B x)) := by
  have hq := @query X (fun x => oracleFunction (join (A x) (B x)))
  exact (hq.comp (primrec (Primrec.succ.comp
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))).of_eq
    (fun x n => by
      change (Part.some (2*n+1)).bind (fun input => oracleFunction (join (A x) (B x)) input) = _
      rw [Part.bind_some]
      simp [oracleFunction,join,Nat.add_div])

end TuringRigidity.UniformPrograms

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformCohenPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.UniformCohenPrefix
open Encodable UniformPrograms UniformOracle CommonIdeal EncodedForcing CohenHalting
noncomputable section
attribute [local instance] Classical.propDecidable

theorem bit_eq_iff (a b : Bool) : bit a = bit b ↔ a = b := by
  cases a <;> cases b <;> simp [bit]

theorem numericPrefix_iff (G : Oracle) (p : ℕ) :
    oraclePrefix (fun i => bit (G i)) (word p).length = (word p).map bit ↔
      Prefix G (word p) := by
  constructor
  · intro h i hi
    have he := congrArg (fun l : List ℕ => l.getD i 0) h
    have hbit : bit (G i) = bit ((word p).getD i false) := by
      simpa [oraclePrefix,List.getD,hi] using he
    exact (bit_eq_iff _ _).mp hbit
  · intro h
    apply List.ext_getElem
    · simp [oraclePrefix]
    · intro i hi hj
      have hi' : i < (word p).length := by simpa [oraclePrefix] using hi
      simpa [oraclePrefix,List.getD,hi'] using congrArg bit (h i hi')

theorem prefix_program {X : Type*} {O : X → ℕ →. ℕ} (G : X → Oracle)
    (hG : Runs O (fun x => oracleFunction (G x))) :
    Runs O (fun x p => Part.some (if Prefix (G x) (word p) then 1 else 0)) := by
  classical
  have hq : Runs O (fun x i => Part.some (bit (G x i))) := hG
  have hi := _root_.OAI.TuringRigidity.UniformPrograms.total_comp (initial_program (fun x i => bit (G x i)) hq)
    (primrec (Primrec.list_length.comp word_primrec))
  have hw := primrec (O := O) (Primrec.encode.comp
    (Primrec.list_map word_primrec (bit_primrec.comp Primrec.snd).to₂))
  have hc := _root_.OAI.TuringRigidity.UniformPrograms.total_comp (primrec (O := O) (Primrec.ite
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
    (Primrec.const 1) (Primrec.const 0))) (_root_.OAI.TuringRigidity.UniformPrograms.total_pair hi hw)
  exact hc.of_eq (fun x n => by
    simp only [Nat.unpair_pair,encode_injective.eq_iff,numericPrefix_iff])

end
end TuringRigidity.UniformCohenPrefix

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformCohenJump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.UniformCohenJump
open Encodable UniformPrograms CommonIdeal EncodedForcing OracleJump
open ArithmeticHierarchy CohenHalting CohenLowness EffectiveCohen
noncomputable section
attribute [local instance] Classical.propDecidable

theorem trialAnswer_primrec : Primrec trialAnswer := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  exact Primrec.ite ((Primrec.eq.comp f (Primrec.const 1)).and
    ((Primrec.eq.comp (f.comp r) (Primrec.const 1)).or
      (Primrec.eq.comp (r.comp r) (Primrec.const 0))))
    (Primrec.option_some.comp (f.comp r)) (Primrec.const none)

theorem searchTrial_program (Y : Oracle) :
    Runs (fun G => oracleFunction (join (jump Y) G))
      (fun G v => Part.some (encode (searchTrial Y G (Nat.unpair v).1 (Nat.unpair v).2))) := by
  let O := fun G => oracleFunction (join (jump Y) G)
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hground : Runs O (fun _ => oracleFunction (jump Y)) := join_left_program (fun _ => jump Y) id
  have hG : Runs O oracleFunction := join_right_program (fun _ => jump Y) id
  have hp := _root_.OAI.TuringRigidity.UniformPrograms.total_comp (UniformCohenPrefix.prefix_program id hG) (primrec r)
  have hhalt := fixed_recursive (form_recursive (openHalts_sigma Y)) hground
  have hh := _root_.OAI.TuringRigidity.UniformPrograms.total_comp hhalt (primrec
    (Primrec₂.natPair.comp f (Primrec.encode.comp (word_primrec.comp r))))
  have he := fixed_recursive (form_recursive (extension_sigma Y)) hground
  have ht := _root_.OAI.TuringRigidity.UniformPrograms.total_comp (primrec (Primrec.encode.comp trialAnswer_primrec))
    (_root_.OAI.TuringRigidity.UniformPrograms.total_pair hp (_root_.OAI.TuringRigidity.UniformPrograms.total_pair hh he))
  apply ht.of_eq
  intro G v
  simp only [Nat.unpair_pair]
  by_cases hp : Prefix G (word (Nat.unpair v).2) <;>
    by_cases hh : OpenHalts Y (Nat.unpair v).1 (encode (word (Nat.unpair v).2)) <;>
    by_cases he : Extension Y (Nat.unpair v).1 (Nat.unpair v).2 <;>
    simp [trialAnswer,searchTrial,Deciding,hp,hh,he]

theorem oneGeneric_jump_program (Y : Oracle) :
    ∃ p : OracleCode, ∀ G : Oracle, OneGeneric Y G →
      OracleCode.eval (oracleFunction (join (jump Y) G)) p =
        oracleFunction (jump (join Y G)) := by
  let X := {G : Oracle // OneGeneric Y G}
  let O := fun G : X => oracleFunction (join (jump Y) G.val)
  let f := fun (G : X) x => if Halts (join Y G.val) (Nat.unpair x).1 (Nat.unpair x).2 then 1 else 0
  have ht : Runs O (fun G v => Part.some
      (encode (searchTrial Y G.val (Nat.unpair v).1 (Nat.unpair v).2))) :=
    (searchTrial_program Y).reindex (fun G : X => G.val)
  have hs (G : X) (x p a : ℕ) (ha : a ∈ searchTrial Y G.val x p) : a = f G x := by
    by_cases hd : Deciding Y G.val (Nat.pair x p)
    · have ha' : a = (if OpenHalts Y x (encode (word p)) then 1 else 0) := by
        exact (by simpa only [searchTrial,ite_eq_left hd,Option.mem_some_iff] using ha :
          (if OpenHalts Y x (encode (word p)) then 1 else 0) = a).symm
      rw [ha',deciding_correct hd]
    · simp [searchTrial,hd] at ha
  have hc (G : X) (x : ℕ) : ∃ p a, a ∈ searchTrial Y G.val x p := by
    obtain ⟨p,hp⟩ := deciding_total G.property x
    exact ⟨p,(if OpenHalts Y x (encode (word p)) then 1 else 0),by
      simp only [searchTrial,ite_eq_left hp,Option.mem_some_iff]⟩
  obtain ⟨p,hp⟩ := total_search ht f hs hc
  refine ⟨p,fun G hG => ?_⟩
  have h := hp (⟨G,hG⟩ : X)
  funext n
  exact (congrFun h n).trans (by simp [f,oracleFunction,jump])

end
end TuringRigidity.UniformCohenJump

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformJumpSimulation
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.UniformPrograms
open Encodable CommonIdeal TableIndices IndexMatrix OracleJump
noncomputable section
variable {X : Type*}

theorem run_program (Y : X → Oracle) :
    Runs (fun x => oracleFunction (Y x)) (fun x v => Part.some
      (encode (run (Y x) (machine (Nat.unpair v).1)
        (Nat.unpair (Nat.unpair v).2).1 (Nat.unpair (Nat.unpair v).2).2))) := by
  let O := fun x => oracleFunction (Y x)
  let e := Primrec.fst.comp Primrec.unpair
  let rest := Primrec.snd.comp Primrec.unpair
  let n := Primrec.fst.comp (Primrec.unpair.comp rest)
  let z := Primrec.snd.comp (Primrec.unpair.comp rest)
  have he := primrec (O := O) e
  have hn := primrec (O := O) n
  have hm := primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp z))
  have ht := primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp z))
  have hL := total_comp (initial_program (fun x k => bit (Y x k)) query) hm
  let r := Primrec.snd.comp Primrec.unpair
  have hdecode := primrec (O := O) (Primrec.encode.comp (Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.fst.comp Primrec.unpair).pair
      (machine_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp r)))).pair
      (Primrec.snd.comp (Primrec.unpair.comp r)))))
  exact (total_comp hdecode (total_pair ht (total_pair he (total_pair hL hn)))).of_eq
    (fun x v => by simp [TableIndices.run,UniformOracle.trial])

theorem haltFlag_primrec : Primrec haltFlag := by
  apply (Primrec.cond (Primrec.option_isSome.comp
    (Primrec.option_getD_default.comp (Primrec.decode (α := Option ℕ))))
    (Primrec.const 0) (Primrec.const 1)).of_eq
  intro n
  change (cond ((decode (α := Option ℕ) n).getD none).isSome 0 1) = _
  cases h : ((decode (α := Option ℕ) n).getD none).isSome <;>
    simp only [haltFlag,h] <;> rfl

theorem haltingSearch_program (Y : X → Oracle) :
    Runs (fun x => oracleFunction (Y x)) (fun x => haltingSearch (Y x)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hr := total_comp (run_program Y) (primrec
    (Primrec₂.natPair.comp (f.comp f) (Primrec₂.natPair.comp (r.comp f) r)))
  have hh := (total_comp (primrec haltFlag_primrec) hr).find
  apply hh.of_eq
  intro x n
  unfold haltingSearch
  congr 1
  funext z
  simp only [Nat.unpair_pair,haltFlag,encodek,Option.getD_some]
  cases run (Y x) (machine (Nat.unpair n).1) (Nat.unpair n).2 z <;> rfl

theorem haltingSearch_dom (Y : Oracle) (v : ℕ) :
    (haltingSearch Y v).Dom ↔ Halts Y (Nat.unpair v).1 (Nat.unpair v).2 := by
  erw [haltingSearch,Nat.rfind_dom]
  simp [Halts,Option.isSome_iff_exists]

theorem uniform_partial_table (c : OracleCode) :
    ∃ e, ∀ Y : Oracle, ∀ n, Halts Y e n ↔ (OracleCode.eval (oracleFunction Y) c n).Dom := by
  have hh : Partrec₂ (fun L : List ℕ => fun n => OracleCode.eval (BranchMachine.lookup L) c n) :=
    OracleCode.eval_partrec BranchMachine.lookup_partrec c
  obtain ⟨d,hd⟩ := partrec_code hh
  have hd' : ∀ L n, d.eval (Nat.pair (encode L) n) = OracleCode.eval (BranchMachine.lookup L) c n :=
    fun L n => hd (L,n)
  refine ⟨encode d,fun Y n => ?_⟩
  let f := OracleCode.eval (oracleFunction Y) c
  have ha : Approximates (f n) (fun m => d.eval
      (Nat.pair (encode (UniformOracle.oraclePrefix (fun k => bit (Y k)) m)) n)) := by
    simp only [hd']
    exact OracleCode.eval_approximates (UniformOracle.prefix_approximates (fun k => bit (Y k))) c n
  constructor
  · rintro ⟨z,a,hz⟩
    simp only [machine_encode] at hz
    exact (ha.1 (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound hz)).1
  · intro hf
    obtain ⟨m,hm⟩ := ha.2 ((f n).get hf) ⟨hf,rfl⟩
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hm m le_rfl)
    exact ⟨Nat.pair m t,(f n).get hf,by simpa [TableIndices.run,UniformOracle.trial] using ht⟩

theorem Runs.jump {Y Z : X → Oracle}
    (h : Runs (fun x => oracleFunction (Z x)) (fun x => oracleFunction (Y x))) :
    Runs (fun x => oracleFunction (jump (Z x))) (fun x => oracleFunction (jump (Y x))) := by
  classical
  obtain ⟨c,hc⟩ := h.trans (haltingSearch_program Y)
  obtain ⟨e,he⟩ := uniform_partial_table c
  have hhalts (x : X) (v : ℕ) : Halts (Z x) e v ↔
      Halts (Y x) (Nat.unpair v).1 (Nat.unpair v).2 := by
    rw [he,hc x,haltingSearch_dom]
  have hq := @query X (fun x => oracleFunction (OracleJump.jump (Z x)))
  exact (hq.comp (primrec (Primrec₂.natPair.comp (Primrec.const e) Primrec.id))).of_eq
    (fun x n => by
      change (Part.some (Nat.pair e n)).bind
        (fun input => Part.some (if OracleJump.jump (Z x) input then 1 else 0)) = _
      rw [Part.bind_some]
      simp [oracleFunction,OracleJump.jump,hhalts])

theorem Runs.iterate_jump {Y Z : X → Oracle}
    (h : Runs (fun x => oracleFunction (Z x)) (fun x => oracleFunction (Y x))) (k : ℕ) :
    Runs (fun x => oracleFunction (iterate (Z x) k))
      (fun x => oracleFunction (iterate (Y x) k)) := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.jump

end
end TuringRigidity.UniformPrograms

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformCohenIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.UniformCohenJump
open UniformPrograms OracleJump EffectiveCohen

theorem iterate_join_program (Y : Oracle) (k : ℕ) :
    ∃ p : OracleCode, ∀ G : Oracle, (∀ j < k, OneGeneric (iterate Y j) G) →
      OracleCode.eval (oracleFunction (join (iterate Y k) G)) p =
        oracleFunction (iterate (join Y G) k) := by
  induction k with
  | zero => exact ⟨.query,fun _ _ => rfl⟩
  | succ k ih =>
    let X := {G : Oracle // ∀ j < k+1, OneGeneric (iterate Y j) G}
    obtain ⟨p,hp⟩ := ih
    have hprev : Runs (fun G : X => oracleFunction (join (iterate Y k) G.val))
        (fun G => oracleFunction (iterate (join Y G.val) k)) :=
      ⟨p,fun G => hp G.val (fun j hj => G.property j (Nat.lt_succ_of_lt hj))⟩
    obtain ⟨q,hq⟩ := oneGeneric_jump_program (iterate Y k)
    have hstep : Runs (fun G : X => oracleFunction (join (iterate Y (k+1)) G.val))
        (fun G => oracleFunction (jump (join (iterate Y k) G.val))) :=
      ⟨q,fun G => hq G.val (G.property k (Nat.lt_succ_self k))⟩
    obtain ⟨r,hr⟩ := hstep.trans hprev.jump
    exact ⟨r,fun G hG => hr ⟨G,hG⟩⟩

theorem swap_program {X : Type*} (A B : X → Oracle) :
    Runs (fun x => oracleFunction (join (A x) (B x)))
      (fun x => oracleFunction (join (B x) (A x))) := by
  have hq := @query X (fun x => oracleFunction (join (A x) (B x)))
  have hs := primrec (O := fun x => oracleFunction (join (A x) (B x)))
    (Primrec.ite (Primrec.eq.comp Primrec.nat_bodd (Primrec.const true))
      (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)) Primrec.succ)
  apply (hq.comp hs).of_eq
  intro x n
  change (Part.some (if n.bodd = true then n - 1 else n.succ)).bind
    (fun index => oracleFunction (join (A x) (B x)) index) = _
  rw [Part.bind_some]
  rcases Nat.mod_two_eq_zero_or_one n with hn|hn
  · have hform : n = 2*(n/2) := by omega
    conv_lhs => rw [hform]
    conv_rhs => rw [hform]
    simp [oracleFunction,join,Nat.add_div]
  · have hform : n = 2*(n/2)+1 := by omega
    conv_lhs => rw [hform]
    conv_rhs => rw [hform]
    simp [oracleFunction,join,Nat.add_div]

theorem iterate_generic_join_program (Y : Oracle) (k : ℕ) :
    ∃ p : OracleCode, ∀ G : Oracle, (∀ j < k, OneGeneric (iterate Y j) G) →
      OracleCode.eval (oracleFunction (join G (iterate Y k))) p =
        oracleFunction (iterate (join G Y) k) := by
  let X := {G : Oracle // ∀ j < k, OneGeneric (iterate Y j) G}
  obtain ⟨p,hp⟩ := iterate_join_program Y k
  have hi : Runs (fun G : X => oracleFunction (join (iterate Y k) G.val))
      (fun G => oracleFunction (iterate (join Y G.val) k)) :=
    ⟨p,fun G => hp G.val G.property⟩
  have hfirst := swap_program (fun G : X => G.val) (fun _ => iterate Y k)
  have hlast := (swap_program (fun _ : X => Y) (fun G => G.val)).iterate_jump k
  obtain ⟨q,hq⟩ := (hfirst.trans hi).trans hlast
  exact ⟨q,fun G hG => hq ⟨G,hG⟩⟩

end TuringRigidity.UniformCohenJump

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformTableSimulation
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.UniformPrograms
open Encodable CommonIdeal TableIndices IndexMatrix

theorem table_program (d : ℕ) :
    ∃ p : OracleCode, ∀ Y A : Oracle, Represents Y (machine d) A →
      OracleCode.eval (oracleFunction Y) p = oracleFunction A := by
  let X := {s : Oracle × Oracle // Represents s.1 (machine d) s.2}
  let Y := fun s : X => s.val.1
  have hr := total_comp (run_program Y) (primrec
    (Primrec₂.natPair.comp (Primrec.const d) Primrec.id))
  have hr' : Runs (fun s : X => oracleFunction (Y s)) (fun s v =>
      Part.some (encode (TableIndices.run s.val.1 (machine d) (Nat.unpair v).1 (Nat.unpair v).2))) := by
    simpa only [Nat.unpair_pair,Y,id_eq] using hr
  have hs : Runs (fun s => oracleFunction (Y s)) (fun s n => Part.some (bit (s.val.2 n))) :=
    UniformPrograms.total_search hr' (fun (s : X) n => bit (s.val.2 n))
      (fun (s : X) => s.property.1) (fun (s : X) => s.property.2)
  obtain ⟨p,hp⟩ := hs
  exact ⟨p,fun B A h => hp ⟨(B,A),h⟩⟩

theorem program_table (p : OracleCode) :
    ∃ d : ℕ, ∀ Y A : Oracle, OracleCode.eval (oracleFunction Y) p = oracleFunction A →
      Represents Y (machine d) A := by
  have hf : Partrec₂ (fun L : List ℕ => fun n => OracleCode.eval (BranchMachine.lookup L) p n) :=
    OracleCode.eval_partrec BranchMachine.lookup_partrec p
  obtain ⟨d,hd⟩ := partrec_code hf
  have hd' : ∀ L n, d.eval (Nat.pair (encode L) n) = OracleCode.eval (BranchMachine.lookup L) p n :=
    fun L n => hd (L,n)
  refine ⟨encode d,fun Y A he => ?_⟩
  have ha (n : ℕ) : Approximates (oracleFunction A n)
      (fun m => d.eval (Nat.pair (encode (UniformOracle.oraclePrefix (fun k => bit (Y k)) m)) n)) := by
    simp only [hd']
    rw [← he]
    exact OracleCode.eval_approximates (UniformOracle.prefix_approximates (fun k => bit (Y k))) p n
  rw [machine_encode]
  constructor
  · intro n z a hz
    exact Part.mem_some_iff.mp ((ha n).1 (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound hz))
  · intro n
    obtain ⟨m,hm⟩ := (ha n).2 (bit (A n)) (Part.mem_some _)
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hm m le_rfl)
    exact ⟨Nat.pair m t,bit (A n),by simpa [TableIndices.run,UniformOracle.trial] using ht⟩

theorem Runs.table_simulation {X : Type*} {Y Z : X → Oracle}
    (h : Runs (fun x => oracleFunction (Z x)) (fun x => oracleFunction (Y x))) (d : ℕ) :
    ∃ e : ℕ, ∀ x : X, ∀ A : Oracle, Represents (Y x) (machine d) A →
      Represents (Z x) (machine e) A := by
  obtain ⟨p,hp⟩ := table_program d
  obtain ⟨q,hq⟩ := h.simulate p
  obtain ⟨e,he⟩ := program_table q
  exact ⟨e,fun x A hA => he (Z x) A ((hq x).trans (hp (Y x) A hA))⟩

end TuringRigidity.UniformPrograms

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenGroundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CountableForcing OracleJump
open TableIndices IndexMatrix UniformPrograms
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem groundGeneric_iterate_program (M : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (R : Oracle) (hR : realCode R ∈ M) (k : ℕ) :
    ∃ p : OracleCode, ∀ A : Oracle,
      AtomicForcing.GroundGeneric M (pushFilter (CohenBorelForcing.realFilter A)) →
      OracleCode.eval (oracleFunction (join A (iterate R k))) p =
        oracleFunction (iterate (join A R) k) := by
  obtain ⟨p,hp⟩ := UniformCohenJump.iterate_generic_join_program R k
  exact ⟨p,fun A hA => hp A (fun j _ => groundGeneric_iterate_oneGeneric M hM hT A R hR hA j)⟩

theorem groundGeneric_table_simulation_oai (M : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (R : Oracle) (hR : realCode R ∈ M) (k d : ℕ) :
    ∃ e : ℕ, ∀ A : Oracle,
      AtomicForcing.GroundGeneric M (pushFilter (CohenBorelForcing.realFilter A)) →
      ∀ X : Oracle, Represents (iterate (join A R) k) (machine d) X →
        Represents (join A (iterate R k)) (machine e) X := by
  let S := {A : Oracle //
    AtomicForcing.GroundGeneric M (pushFilter (CohenBorelForcing.realFilter A))}
  obtain ⟨p,hp⟩ := groundGeneric_iterate_program M hM hT R hR k
  have h : Runs (fun A : S => oracleFunction (join A.val (iterate R k)))
      (fun A => oracleFunction (iterate (join A.val R) k)) := ⟨p,fun A => hp A.val A.property⟩
  obtain ⟨e,he⟩ := h.table_simulation d
  exact ⟨e,fun A hA => he ⟨A,hA⟩⟩

end TuringRigidity.InternalCohen

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.InternalCohen.groundGeneric_table_simulation_oai := @OAI.TuringRigidity.InternalCohen.groundGeneric_table_simulation_oai

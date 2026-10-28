-- Prove2me | solution 1 for OAI.TuringRigidity.ArithmeticTree.sourceT_piOneOne_matrix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:55:06.976917+00:00
-- url     : https://prove2.me/submissions/6840687a-b30d-4b34-9238-d4b73c8b85c2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticFiniteTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic

namespace Term

theorem eval_subst (t inputTerm : Term) (query : Term → Term)
    (f g : ℕ → ℕ) (v : ℕ)
    (hq : ∀ t, (query t).eval f v = g (t.eval f v)) :
    (t.subst inputTerm query).eval f v = t.eval g (inputTerm.eval f v) := by
  induction t with
  | input => rfl
  | const n => rfl
  | prim f hf t ih => simp only [subst,eval,ih]
  | pair t s ih ik => simp only [subst,eval,ih,ik]
  | witness t ih => simp only [subst,eval,hq,ih]
end Term

namespace Test

theorem eval_subst (t : Test) (inputTerm : Term) (query : Term → Term)
    (O : Oracles) (f g : ℕ → ℕ) (v : ℕ)
    (hq : ∀ t, (query t).eval f v = g (t.eval f v)) :
    (t.subst inputTerm query).eval O f v ↔ t.eval O g (inputTerm.eval f v) := by
  induction t with
  | pure P hP t => simp only [subst,eval,Term.eval_subst t inputTerm query f g v hq]
  | query i t => simp only [subst,eval,Term.eval_subst t inputTerm query f g v hq]
  | neg t ih => exact not_congr ih
  | and t s ih ik => exact and_congr ih ik

end Test

end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticSkolem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic
noncomputable section

namespace HasTest

private theorem col_eval (k : ℕ) (t : Test) (O : Oracles) (f : ℕ → ℕ) (v : ℕ) :
    (col k t).eval O f v ↔ t.eval O (fun n => f (Nat.pair k n)) v :=
  t.eval_subst _ _ O f _ v (fun _ => rfl)

theorem pure (P : ℕ → Prop) (hP : PrimrecPred P) : HasTest (fun _ v => P v) := by
  refine ⟨.pure P hP (.left .input),fun O v => ?_⟩
  simp only [Test.eval,Term.eval,Term.left,UniformArithmetic.left,Nat.unpair_pair]
  exact ⟨fun h => ⟨fun _ => 0,fun _ => h⟩,fun ⟨_,h⟩ => h 0⟩

theorem query (i : ℕ) : HasTest (fun O v => O i v = true) := by
  refine ⟨.query i (.left .input),fun O v => ?_⟩
  simp only [Test.eval,Term.eval,Term.left,UniformArithmetic.left,Nat.unpair_pair]
  exact ⟨fun h => ⟨fun _ => 0,fun _ => h⟩,fun ⟨_,h⟩ => h 0⟩

theorem not_pure (P : ℕ → Prop) (hP : PrimrecPred P) : HasTest (fun _ v => ¬ P v) := by
  refine ⟨.neg (.pure P hP (.left .input)),fun O v => ?_⟩
  simp only [Test.eval,Term.eval,Term.left,UniformArithmetic.left,Nat.unpair_pair]
  exact ⟨fun h => ⟨fun _ => 0,fun _ => h⟩,fun ⟨_,h⟩ => h 0⟩

theorem not_query (i : ℕ) : HasTest (fun O v => ¬ O i v = true) := by
  refine ⟨.neg (.query i (.left .input)),fun O v => ?_⟩
  simp only [Test.eval,Term.eval,Term.left,UniformArithmetic.left,Nat.unpair_pair]
  exact ⟨fun h => ⟨fun _ => 0,fun _ => h⟩,fun ⟨_,h⟩ => h 0⟩

theorem and {P Q} (hP : HasTest P) (hQ : HasTest Q) :
    HasTest (fun O v => P O v ∧ Q O v) := by
  classical
  obtain ⟨t,ht⟩ := hP
  obtain ⟨s,hs⟩ := hQ
  refine ⟨.and (col 0 t) (col 1 s),fun O v => ?_⟩
  simp only [Test.eval,col_eval]
  constructor
  · rintro ⟨hp,hq⟩
    obtain ⟨f,hf⟩ := (ht O v).mp hp
    obtain ⟨g,hg⟩ := (hs O v).mp hq
    refine ⟨fun k => if (Nat.unpair k).1 = 0 then f (Nat.unpair k).2 else g (Nat.unpair k).2,?_⟩
    intro n
    constructor
    · simpa only [Nat.unpair_pair,ite_eq_left rfl,ite_true] using hf n
    · simpa only [Nat.unpair_pair,ite_eq_right (Nat.one_ne_zero)] using hg n
  · rintro ⟨f,hf⟩
    exact ⟨(ht O v).mpr ⟨_,fun n => (hf n).1⟩,
      (hs O v).mpr ⟨_,fun n => (hf n).2⟩⟩

private theorem tail_eval (t : Test) (O : Oracles) (f : ℕ → ℕ) (v : ℕ) :
    (tailTest t).eval O f v ↔ t.eval O (fun n => f (n+1)) v :=
  t.eval_subst _ _ O f _ v (fun _ => rfl)

theorem or {P Q} (hP : HasTest P) (hQ : HasTest Q) :
    HasTest (fun O v => P O v ∨ Q O v) := by
  classical
  obtain ⟨t,ht⟩ := hP
  obtain ⟨s,hs⟩ := hQ
  refine ⟨(Test.and zeroTag (tailTest t)).or (.and (.neg zeroTag) (tailTest s)),fun O v => ?_⟩
  simp only [Test.eval_or,Test.eval,tail_eval,zeroTag,Term.eval]
  constructor
  · intro h
    rcases h with hp | hq
    · obtain ⟨f,hf⟩ := (ht O v).mp hp
      exact ⟨(fun n => Nat.casesOn n 0 f),fun n => Or.inl ⟨rfl,hf n⟩⟩
    · obtain ⟨g,hg⟩ := (hs O v).mp hq
      exact ⟨(fun n => Nat.casesOn n 1 g),fun n => Or.inr ⟨by simp,hg n⟩⟩
  · rintro ⟨f,hf⟩
    by_cases hz : f 0 = 0
    · exact Or.inl ((ht O v).mpr ⟨_,fun n => ((hf n).resolve_right (fun h => h.1 hz)).2⟩)
    · exact Or.inr ((hs O v).mpr ⟨_,fun n => ((hf n).resolve_left (fun h => hz h.1)).2⟩)

theorem comp {P} (hP : HasTest P) (g : ℕ → ℕ) (hg : Primrec g) :
    HasTest (fun O v => P O (g v)) := by
  obtain ⟨t,ht⟩ := hP
  let inputTerm : Term := .pair (.prim g hg (.left .input)) (.right .input)
  refine ⟨t.subst inputTerm Term.witness,fun O v => ?_⟩
  dsimp only
  rw [ht]
  apply exists_congr
  intro f
  apply forall_congr'
  intro n
  simpa only [inputTerm,Term.eval,Term.left,Term.right,UniformArithmetic.left,
    UniformArithmetic.right,Nat.unpair_pair] using
    (t.eval_subst inputTerm Term.witness O f f (Nat.pair v n) (fun _ => rfl)).symm

theorem ex {P} (hP : HasTest P) : HasTest (fun O v => ∃ k, P O (Nat.pair v k)) := by
  obtain ⟨t,ht⟩ := hP
  let inputTerm : Term := .pair (.pair (.left .input) (.witness (.const 0))) (.right .input)
  let q : Term → Term := fun s => .witness (.prim Nat.succ Primrec.succ s)
  have he O f v n : (t.subst inputTerm q).eval O f (Nat.pair v n) ↔
      t.eval O (fun k => f (k+1)) (Nat.pair (Nat.pair v (f 0)) n) := by
    simpa only [inputTerm,Term.eval,Term.left,Term.right,UniformArithmetic.left,
      UniformArithmetic.right,Nat.unpair_pair] using
      t.eval_subst inputTerm q O f (fun k => f (k+1)) (Nat.pair v n) (fun _ => rfl)
  refine ⟨t.subst inputTerm q,fun O v => ?_⟩
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨f,hf⟩ := (ht O (Nat.pair v k)).mp hk
    exact ⟨(fun n => Nat.casesOn n k f),fun n => (he _ _ _ _).mpr (hf n)⟩
  · rintro ⟨f,hf⟩
    exact ⟨f 0,(ht O _).mpr ⟨_,fun n => (he _ _ _ _).mp (hf n)⟩⟩

theorem all {P} (hP : HasTest P) : HasTest (fun O v => ∀ k, P O (Nat.pair v k)) := by
  classical
  obtain ⟨t,ht⟩ := hP
  let inputTerm : Term := .pair (.pair (.left .input) (.left (.right .input))) (.right (.right .input))
  let q : Term → Term := fun s => .witness (.pair (.left (.right .input)) s)
  have he O f v n : (t.subst inputTerm q).eval O f (Nat.pair v n) ↔
      t.eval O (fun k => f (Nat.pair (Nat.unpair n).1 k))
        (Nat.pair (Nat.pair v (Nat.unpair n).1) (Nat.unpair n).2) := by
    simpa only [inputTerm,Term.eval,Term.left,Term.right,UniformArithmetic.left,
      UniformArithmetic.right,Nat.unpair_pair] using
      t.eval_subst inputTerm q O f (fun k => f (Nat.pair (Nat.unpair n).1 k))
        (Nat.pair v n) (fun _ => by simp [q,Term.eval,Term.left,Term.right,
          UniformArithmetic.left,UniformArithmetic.right])
  refine ⟨t.subst inputTerm q,fun O v => ?_⟩
  constructor
  · intro h
    have hh : ∀ k, ∃ f, ∀ n, t.eval O f (Nat.pair (Nat.pair v k) n) :=
      fun k => (ht O _).mp (h k)
    choose f hf using hh
    refine ⟨fun n => f (Nat.unpair n).1 (Nat.unpair n).2,fun n => (he _ _ _ _).mpr ?_⟩
    simpa only [Nat.unpair_pair] using hf (Nat.unpair n).1 (Nat.unpair n).2
  · rintro ⟨f,hf⟩ k
    refine (ht O _).mpr ⟨fun n => f (Nat.pair k n),fun n => ?_⟩
    simpa only [Nat.unpair_pair] using (he _ _ _ _).mp (hf (Nat.pair k n))

theorem congr {P Q} (hP : HasTest P) (he : ∀ O v, P O v ↔ Q O v) : HasTest Q := by
  obtain ⟨t,ht⟩ := hP
  exact ⟨t,fun O v => (he O v).symm.trans (ht O v)⟩
end HasTest

theorem arithmetic_tests {P} (h : Arith P) : HasTest P ∧ HasTest (fun O v => ¬ P O v) := by
  induction h with
  | pure P hP => exact ⟨HasTest.pure P hP,HasTest.not_pure P hP⟩
  | query i => exact ⟨HasTest.query i,HasTest.not_query i⟩
  | neg h ih => exact ⟨ih.2,ih.1.congr (fun _ _ => not_not.symm)⟩
  | and h k ih ik =>
    exact ⟨ih.1.and ik.1,(ih.2.or ik.2).congr (fun _ _ => not_and_or.symm)⟩
  | ex h ih => exact ⟨ih.1.ex,ih.2.all.congr (fun _ _ => not_exists.symm)⟩
  | comp f h hf ih => exact ⟨ih.1.comp f hf,ih.2.comp f hf⟩

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticTestApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable

theorem Captures.mono {s f N K} (h : Captures s f N) (hK : K ≤ N) : Captures s f K :=
  fun i hi => h i (lt_of_lt_of_le hi hK)

namespace Term

theorem approx_complete (t : Term) (f : ℕ → ℕ) (v : ℕ) :
    ∃ N, ∀ s : Approx, Captures s f N → t.approx s v = some (t.eval f v) := by
  induction t with
  | input => exact ⟨0,fun _ _ => rfl⟩
  | const n => exact ⟨0,fun _ _ => rfl⟩
  | prim g hg t ih =>
    obtain ⟨N,hN⟩ := ih
    exact ⟨N,fun s hs => by simp [approx,eval,hN s hs]⟩
  | pair t u ih ik =>
    obtain ⟨N,hN⟩ := ih
    obtain ⟨K,hK⟩ := ik
    exact ⟨max N K,fun s hs => by
      simp [approx,eval,hN s (hs.mono (le_max_left _ _)),hK s (hs.mono (le_max_right _ _))]⟩
  | witness t ih =>
    obtain ⟨N,hN⟩ := ih
    refine ⟨max N (t.eval f v + 1),fun s hs => ?_⟩
    simp only [approx,hN s (hs.mono (le_max_left _ _)),Option.bind_some,eval]
    exact hs _ (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
end Term

namespace Test

theorem approx_sound (t : Test) (O : Oracles) {s : Approx} {f : ℕ → ℕ}
    (h : Extends s (fun i => some (f i))) (v : ℕ) (a : Bool)
    (ha : t.approx O s v = some a) : t.eval O f v ↔ a = true := by
  have he : decide (t.eval O f v) = a := by
    simpa only [approx_full,Option.some.injEq] using t.approx_mono O h v a ha
  rw [← he]
  simp

theorem approx_complete (t : Test) (O : Oracles) (f : ℕ → ℕ) (v : ℕ) :
    ∃ N, ∀ s : Approx, Captures s f N →
      t.approx O s v = some (decide (t.eval O f v)) := by
  induction t with
  | pure P hP t =>
    obtain ⟨N,hN⟩ := t.approx_complete f v
    refine ⟨N,fun s hs => ?_⟩
    rw [← approx_full]
    simp only [approx,hN s hs,Term.approx_full]
  | query i t =>
    obtain ⟨N,hN⟩ := t.approx_complete f v
    refine ⟨N,fun s hs => ?_⟩
    rw [← approx_full]
    simp only [approx,hN s hs,Term.approx_full]
  | neg t ih =>
    obtain ⟨N,hN⟩ := ih
    refine ⟨N,fun s hs => ?_⟩
    rw [← approx_full]
    simp only [approx,hN s hs,approx_full]
  | and t u ih ik =>
    obtain ⟨N,hN⟩ := ih
    obtain ⟨K,hK⟩ := ik
    refine ⟨max N K,fun s hs => ?_⟩
    rw [← approx_full]
    simp only [approx,hN s (hs.mono (le_max_left _ _)),hK s (hs.mono (le_max_right _ _)),approx_full]

end Test

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticWitnessTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable

theorem prefix_succ (f : ℕ → ℕ) (n : ℕ) : initialSegment f (n+1) = initialSegment f n ++ [f n] := by
  unfold initialSegment
  rw [List.ofFn_succ_last]
  rfl

theorem prefix_captures (f : ℕ → ℕ) (n : ℕ) : Captures (listApprox (initialSegment f n)) f n := by
  intro i hi
  simp [listApprox,initialSegment,hi]

theorem prefix_extends (f : ℕ → ℕ) (n : ℕ) :
    Extends (listApprox (initialSegment f n)) (fun i => some (f i)) := by
  intro i a ha
  obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp ha
  simp only [prefix_length] at hi
  have hb := prefix_captures f n i hi
  exact hb.symm.trans ha

namespace Test

theorem branch_iff (t : Test) (O : Oracles) (v : ℕ) (f : ℕ → ℕ) :
    (∀ N, initialSegment f N ∈ t.tree O v) ↔ ∀ n, t.eval O f (Nat.pair v n) := by
  constructor
  · intro h n
    obtain ⟨N,hN⟩ := t.approx_complete O f (Nat.pair v n)
    let K := max N (n+1)
    have he := hN (listApprox (initialSegment f K)) ((prefix_captures f K).mono (le_max_left _ _))
    have hn : n < (initialSegment f K).length := by simp [K]
    have hh := h K n hn
    by_contra hp
    exact hh (he.trans (by simp [hp]))
  · intro h N n hn he
    have ha := (t.approx_sound O (prefix_extends f N) _ false he).mp (h n)
    exact Bool.false_ne_true ha

end Test

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticTreeDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic Encodable
noncomputable section
attribute [local instance] Classical.propDecidable

theorem Term.approx_primrec (t : Term) :
    Primrec (fun p : List ℕ × ℕ => t.approx (listApprox p.1) p.2) := by
  induction t with
  | input => exact Primrec.option_some.comp Primrec.snd
  | const n => exact Primrec.const (some n)
  | prim g hg t ih =>
    exact Primrec.option_bind ih (Primrec.option_some.comp (hg.comp Primrec.snd))
  | pair t u ih ik =>
    exact Primrec.option_bind ih (Primrec.option_bind (ik.comp Primrec.fst)
      (Primrec.option_some.comp (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)))
  | witness t ih =>
    exact Primrec.option_bind ih
      (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

private theorem option_neg_iff (a : Option Bool) (b : Bool) :
    (a.bind (fun c => some (!c)) = some b) ↔ a = some (!b) := by
  cases a with
  | none => simp
  | some a => cases a <;> cases b <;> decide

private theorem option_and_true (a b : Option Bool) :
    (a.bind (fun c => b.bind (fun d => some (c && d))) = some true) ↔
      a = some true ∧ b = some true := by
  cases a with
  | none => simp
  | some a => cases b with
    | none => simp
    | some b => cases a <;> cases b <;> decide

private theorem option_and_false (a b : Option Bool) :
    (a.bind (fun c => b.bind (fun d => some (c && d))) = some false) ↔
      (a = some false ∧ b = some false) ∨
      (a = some false ∧ b = some true) ∨ (a = some true ∧ b = some false) := by
  cases a with
  | none => simp
  | some a => cases b with
    | none => simp
    | some b => cases a <;> cases b <;> decide

theorem Test.approx_arith (t : Test) {s : ℕ → List ℕ} (hs : Primrec s)
    {v : ℕ → ℕ} (hv : Primrec v) (b : Bool) :
    Arith (fun O k => t.approx O (listApprox (s k)) (v k) = some b) := by
  induction t generalizing s v b with
  | pure P hP t =>
    have hp : Primrec (fun k : ℕ => (t.approx (listApprox (s k)) (v k)).bind
        (fun a => some (decide (P a)))) := Primrec.option_bind ((t.approx_primrec).comp (hs.pair hv))
      (Primrec.option_some.comp (hP.decide.comp Primrec.snd))
    exact .pure _ (Primrec.eq.comp hp (Primrec.const (some b)))
  | query i t =>
    have ht := (t.approx_primrec).comp ((hs.comp left_primrec).pair (hv.comp left_primrec))
    have hh : Arith (fun _ k => t.approx (listApprox (s (left k))) (v (left k)) = some (right k)) :=
      .pure _ (Primrec.eq.comp ht (Primrec.option_some.comp right_primrec))
    have hq : Arith (fun O k => O i (right k) = b) := by
      cases b with
      | true => exact (Arith.query i).comp _ right_primrec
      | false =>
        exact ((Arith.query i).comp _ right_primrec).neg.congr
          (fun O k => by cases O i (right k) <;> simp)
    exact (hh.and hq).ex.congr (fun O k => by
      simp only [left,right,Nat.unpair_pair,Test.approx,Option.bind_eq_some_iff,Option.some.injEq])
  | neg t ih =>
    exact (ih hs hv (!b)).congr (fun O k => (option_neg_iff _ b).symm)
  | and t u ih ik =>
    cases b with
    | true =>
      exact ((ih hs hv true).and (ik hs hv true)).congr
        (fun O k => (option_and_true _ _).symm)
    | false =>
      exact (((ih hs hv false).and (ik hs hv false)).or
        (((ih hs hv false).and (ik hs hv true)).or ((ih hs hv true).and (ik hs hv false)))).congr
        (fun O k => (option_and_false _ _).symm)

theorem Test.accepts_arith (t : Test) {s : ℕ → List ℕ} (hs : Primrec s)
    {v : ℕ → ℕ} (hv : Primrec v) : Arith (fun O k => t.accepts O (v k) (s k)) := by
  have hlen : Arith (fun _ k => right k < (s (left k)).length) :=
    .pure _ (Primrec.nat_lt.comp right_primrec (Primrec.list_length.comp (hs.comp left_primrec)))
  have ht := t.approx_arith (hs.comp left_primrec)
    (Primrec₂.natPair.comp (hv.comp left_primrec) right_primrec) false
  exact (hlen.imp ht.neg).all.congr (fun O k => by
    simp only [Test.accepts,left,right,Nat.unpair_pair])

theorem decodeNode_primrec : Primrec decodeNode :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistenceWitnessTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Test

theorem eval_bindOracle (t : Test) (q : ℕ → Term → Test)
    (O U : Oracles) (f : ℕ → ℕ) (v : ℕ)
    (hq : ∀ i s, (q i s).eval O f v ↔ U i (s.eval f v) = true) :
    (t.bindOracle q).eval O f v ↔ t.eval U f v := by
  induction t with
  | pure P hP t => rfl
  | query i t => exact hq i t
  | neg t ih => exact not_congr ih
  | and t s ih ik => exact and_congr ih ik

theorem mergeReal_eval (t : Test) (A R : Oracle) (f : ℕ → ℕ) (v : ℕ) :
    t.mergeReal.eval (parameters A R (fun _ => false)) f v ↔
      t.eval (parameters A R (realPart f)) (witnessPart f) v := by
  unfold mergeReal
  apply Iff.trans (t.subst _ _ |>.eval_bindOracle realQuery _
    (parameters A R (realPart f)) f v ?_)
  · exact t.eval_subst _ _ _ f _ v (fun _ => rfl)
  · intro i s
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i => simp [realQuery,eval,Term.eval,parameters,realPart]

private theorem realPart_join (H : Oracle) (f : ℕ → ℕ) :
    realPart (joinWitness H f) = H := by
  funext n
  cases hn : H n <;> simp [realPart,joinWitness,hn]

private theorem witnessPart_join (H : Oracle) (f : ℕ → ℕ) :
    witnessPart (joinWitness H f) = f := by
  funext n
  simp [witnessPart,joinWitness]

theorem exists_mergeReal (t : Test) (A R : Oracle) (v : ℕ) :
    (∃ H : Oracle, ∃ f : ℕ → ℕ, ∀ n, t.eval (parameters A R H) f (Nat.pair v n)) ↔
      ∃ f : ℕ → ℕ, ∀ n, t.mergeReal.eval (parameters A R (fun _ => false)) f (Nat.pair v n) := by
  constructor
  · rintro ⟨H,f,hf⟩
    refine ⟨joinWitness H f,fun n => (t.mergeReal_eval _ _ _ _).mpr ?_⟩
    simpa only [realPart_join,witnessPart_join] using hf n
  · rintro ⟨f,hf⟩
    exact ⟨realPart f,witnessPart f,fun n => (t.mergeReal_eval _ _ _ _).mp (hf n)⟩
end Test

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelReals
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelReals
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding
universe u
noncomputable section

theorem realSet_subset (A : Oracle) : realSet.{u} A ⊆ ZFSet.omega :=
  fun _ h => (ZFSet.mem_sep.mp h).1

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

theorem Definable.subst (h : Definable M P) (r : ℕ → ℕ) :
    Definable M (fun e => P (e ∘ r)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨p.rename (slotMap r id),d,hd,?_⟩
  intro e
  simpa only [Formula.eval_rename_comp,mix_slotMap,Function.comp_id] using hp (e ∘ r)

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

theorem pure_definition (C : Context M) (P : ℕ → Prop) (hP : PrimrecPred P) :
    ArithmeticDefinition M (fun _ n => P n) := by
  obtain ⟨d,hd⟩ := hP
  let : DecidablePred P := d
  obtain ⟨g,hg,hgc⟩ := primrec_graph C (Primrec.encode.comp hd)
  let Q := fun e : ℕ → ZFSet.{u} => ∃ x ∈ ZFSet.omega,
    x = natSet 1 ∧ ZFSet.pair (e 0) x ∈ g
  have hQ : Definable M Q :=
    ((equal_param (C.nat_mem 1) 0).and (pairMem_param hg 1 0)).existsParam C.omega_mem
  refine ⟨Q,hQ,?_⟩
  intro e n hn
  simp only [Q,hn,omega_exists]
  constructor
  · rintro ⟨k,hk,hgk⟩
    have hk' : k=1 := natSet_injective hk
    have hh := (hgc n k).mp hgk
    rw [hk'] at hh
    by_contra h
    simp [h] at hh
  · intro h
    exact ⟨1,rfl,(hgc n 1).mpr (by simp [h])⟩

theorem query_definition (C : Context M) (i : ℕ) :
    ArithmeticDefinition M (fun O n => O i n = true) := by
  refine ⟨fun e => e 0 ∈ e (i+1),member_definable C 0 (i+1),?_⟩
  intro e n hn
  simp [hn,oracleOf]

theorem ArithmeticDefinition.neg {P : Predicate} (h : ArithmeticDefinition M P) :
    ArithmeticDefinition M (fun O n => ¬ P O n) := by
  obtain ⟨Q,hQ,hc⟩ := h
  exact ⟨fun e => ¬ Q e,hQ.neg,fun e n hn => not_congr (hc e n hn)⟩

theorem ArithmeticDefinition.and {P R : Predicate}
    (hP : ArithmeticDefinition M P) (hR : ArithmeticDefinition M R) :
    ArithmeticDefinition M (fun O n => P O n ∧ R O n) := by
  obtain ⟨Q,hQ,hc⟩ := hP
  obtain ⟨S,hS,hs⟩ := hR
  exact ⟨fun e => Q e ∧ S e,hQ.and hS,fun e n hn => and_congr (hc e n hn) (hs e n hn)⟩

theorem ArithmeticDefinition.comp (C : Context M) {P : Predicate}
    (h : ArithmeticDefinition M P) {f : ℕ → ℕ} (hf : Primrec f) :
    ArithmeticDefinition M (fun O n => P O (f n)) := by
  obtain ⟨Q,hQ,hc⟩ := h
  obtain ⟨g,hg,hgc⟩ := primrec_graph C hf
  let R := fun e : ℕ → ZFSet.{u} => ∃ x ∈ ZFSet.omega,
    ZFSet.pair (e 0) x ∈ g ∧ Q (cons x e ∘ skipInput 1)
  have hR : Definable M R :=
    ((pairMem_param hg 1 0).and (hQ.subst (skipInput 1))).existsParam C.omega_mem
  refine ⟨R,hR,?_⟩
  intro e n hn
  simp only [R,omega_exists,hn,hgc]
  constructor
  · rintro ⟨k,rfl,hk⟩
    exact (hc (cons (natSet (f n)) e ∘ skipInput 1) (f n) rfl).mp hk
  · intro hh
    exact ⟨f n,rfl,(hc (cons (natSet (f n)) e ∘ skipInput 1) (f n) rfl).mpr hh⟩

theorem ArithmeticDefinition.ex (C : Context M) {P : Predicate}
    (h : ArithmeticDefinition M P) :
    ArithmeticDefinition M (fun O n => ∃ k, P O (Nat.pair n k)) := by
  obtain ⟨Q,hQ,hc⟩ := h
  let R := fun e : ℕ → ZFSet.{u} => ∃ x ∈ ZFSet.omega, ∃ y ∈ ZFSet.omega,
    PairCode (e 0) x y ∧ Q (cons y (cons x e) ∘ skipInput 2)
  have hR : Definable M R :=
    (((pairCode_definable C 2 1 0).and (hQ.subst (skipInput 2))).existsParam
      C.omega_mem).existsParam C.omega_mem
  refine ⟨R,hR,?_⟩
  intro e n hn
  simp only [R,hn]
  simp_rw [omega_exists]
  simp only [pairCode_nat]
  constructor
  · rintro ⟨k,l,rfl,hl⟩
    exact ⟨k,(hc (cons (natSet (Nat.pair n k)) (cons (natSet k) e) ∘ skipInput 2) (Nat.pair n k) rfl).mp hl⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,Nat.pair n k,rfl,(hc (cons (natSet (Nat.pair n k)) (cons (natSet k) e) ∘ skipInput 2) (Nat.pair n k) rfl).mpr hk⟩

theorem arith_definition (C : Context M) {P : Predicate} (h : Arith P) :
    ArithmeticDefinition M P := by
  induction h with
  | pure P hP => exact pure_definition C P hP
  | query i => exact query_definition C i
  | neg h ih => exact ih.neg
  | and h k ih ik => exact ih.and ik
  | ex h ih => exact ih.ex C
  | comp f h hf ih => exact ih.comp C hf

end
end TuringRigidity.SetModelSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelArithmeticClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open BoundedDefinability UniformArithmetic Encodable TableIndices IndexMatrix
universe u
noncomputable section

variable {M : ZFSet.{u}}

theorem arithmetic_comprehension (C : Context M) {P : Predicate} (hP : Arith P)
    (O : Oracles) (hO : ∀ i, O i ∈ reals M) (A : Oracle)
    (hA : ∀ n, P O n ↔ A n = true) : A ∈ reals M := by
  obtain ⟨Q,hQ,hc⟩ := arith_definition C hP
  let e : ℕ → ZFSet.{u} := fun i => realSet (O i)
  have he : ∀ i, e i ∈ M := hO
  have hs := hQ.sep_mem C e he C.omega_mem
  have hspec (n : ℕ) : Q (cons (natSet n) e) ↔ A n = true := by
    have hh := hc (cons (natSet n) e) n rfl
    have ho : (fun i => oracleOf (cons (natSet n) e (i+1))) = O := by
      funext i
      exact oracleOf_realSet (O i)
    rw [ho] at hh
    exact hh.trans (hA n)
  have eq : ZFSet.sep (fun x => Q (cons x e)) ZFSet.omega = realSet A := by
    apply ZFSet.ext
    intro x
    by_cases hx : x ∈ ZFSet.omega
    · obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      simp only [ZFSet.mem_sep,hspec,nat_mem_realSet]
      exact and_iff_right ((mem_omega _).mpr ⟨n,rfl⟩)
    · constructor
      · intro h
        exact (hx (ZFSet.mem_sep.mp h).1).elim
      · intro h
        exact (hx (realSet_subset A h)).elim
  change realSet A ∈ M
  exact eq ▸ hs

end
end TuringRigidity.SetModelSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelTreeRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic BoundedSetTheory TransitiveNameModel SetModelReals SetModelSyntax
open SetModelArithmetic SetModelFunctions SetModelSequences Encodable
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

theorem Test.canonical_arith (t : Test) (v : ℕ) : Arith (fun O n => t.canonicalNode O v n) :=
  (Arith.pure _ (Primrec.eq.comp (Primrec.encode.comp decodeNode_primrec) Primrec.id)).and
    (t.accepts_arith decodeNode_primrec (Primrec.const v))

theorem Test.edge_arith (t : Test) (v : ℕ) :
    Arith (fun O n => t.edgePredicate O v (left n) (right n)) := by
  have hc := ((t.canonical_arith v).comp _ left_primrec).and
    ((t.canonical_arith v).comp _ right_primrec)
  have he : Arith (fun _ n =>
      decodeNode (left (left n)) = decodeNode (right (left n)) ++ [right n]) :=
    .pure _ (Primrec.eq.comp (decodeNode_primrec.comp (left_primrec.comp left_primrec))
      (Primrec.list_concat.comp (decodeNode_primrec.comp (right_primrec.comp left_primrec)) right_primrec))
  exact (hc.and he.ex).congr (fun _ _ => by simp only [Test.edgePredicate,left,right,Nat.unpair_pair,and_assoc])

theorem relationSet_pair (A : Oracle) (n m : ℕ) :
    ZFSet.pair (natSet.{u} n) (natSet m) ∈ relationSet A ↔ A (Nat.pair n m) = true := by
  simp only [relationSet,ZFSet.mem_sep,natPair_mem,true_and]
  constructor
  · rintro ⟨x,hx,hp⟩
    obtain ⟨k,rfl⟩ := (mem_omega _).mp (realSet_subset A hx)
    have hk := (pairingSet_code n m k).mp hp
    simpa only [hk,nat_mem_realSet] using hx
  · intro hA
    exact ⟨natSet (Nat.pair n m),(nat_mem_realSet _ _).mpr hA,
      (pairingSet_code n m _).mpr rfl⟩

theorem relationSet_mem {M : ZFSet.{u}} (C : Context M) {A : Oracle} (hA : A ∈ reals M) :
    relationSet A ∈ M := by
  let φ : Formula := .existsMem 1 (.pairMem 1 0 3)
  let e := cons (realSet A) (fun _ => pairingSet.{u})
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i with
    | zero => exact hA
    | succ i => exact C.pairing_mem
  have h := sep_mem M C.transitive C.separation φ e he C.pairNumbers_mem
  have heq : ZFSet.sep (fun z => φ.Eval (cons z e)) pairNumbers = relationSet A := by
    apply ZFSet.ext
    intro z
    simp only [relationSet,ZFSet.mem_sep,φ,e,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ]
  exact heq ▸ h

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticTreeDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic SetModelReals SetModelSyntax SetModelFunctions
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem length_chain (c : ℕ → ℕ)
    (hs : ∀ n, ∃ a, decodeNode (c (n+1)) = decodeNode (c n) ++ [a]) (n : ℕ) :
    n ≤ (decodeNode (c n)).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨a,ha⟩ := hs n
    simp only [ha,List.length_append,List.length_singleton]
    omega

private theorem extends_chain (c : ℕ → ℕ)
    (hs : ∀ n, ∃ a, decodeNode (c (n+1)) = decodeNode (c n) ++ [a])
    {i j : ℕ} (hij : i ≤ j) : Extends (listApprox (decodeNode (c i))) (listApprox (decodeNode (c j))) := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ h => h
  | succ j hj ih =>
    obtain ⟨a,ha⟩ := hs j
    intro k b hb
    rw [ha]
    exact listApprox_append _ _ k b (ih k b hb)

theorem unionRead_captures (c : ℕ → ℕ)
    (hs : ∀ n, ∃ a, decodeNode (c (n+1)) = decodeNode (c n) ++ [a]) (n : ℕ) :
    Captures (listApprox (decodeNode (c n))) (unionRead c) n := by
  intro i hi
  have hil : i < (decodeNode (c (i+1))).length :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (length_chain c hs _)
  have he : (decodeNode (c (i+1)))[i]? = some ((decodeNode (c (i+1)))[i]) :=
    List.getElem?_eq_some_iff.mpr ⟨hil,rfl⟩
  have hv : unionRead c i = (decodeNode (c (i+1)))[i] := by simp [unionRead,he]
  rw [hv]
  exact extends_chain c hs (Nat.succ_le_of_lt hi) i _ he

theorem Test.eval_of_descent (t : Test) (O : Oracles) (v : ℕ) (c : ℕ → ℕ)
    (hc : ∀ n, t.edgePredicate O v (c (n+1)) (c n)) :
    ∀ n, t.eval O (unionRead c) (Nat.pair v n) := by
  have hs : ∀ n, ∃ a, decodeNode (c (n+1)) = decodeNode (c n) ++ [a] := fun n => (hc n).2.2
  intro n
  obtain ⟨N,hN⟩ := t.approx_complete O (unionRead c) (Nat.pair v n)
  let K := max N (n+1)
  have he := hN (listApprox (decodeNode (c K))) ((unionRead_captures c hs K).mono (le_max_left _ _))
  have hnK : n < (decodeNode (c K)).length :=
    lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)) (length_chain c hs K)
  have hh := (hc K).2.1.2 n hnK
  by_contra hp
  exact hh (he.trans (by simp [hp]))

private theorem read_primrec : Primrec (fun p : ℕ × ℕ => (decodeNode p.1)[p.2]?.getD 0) :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp (decodeNode_primrec.comp Primrec.fst) Primrec.snd)
    (Primrec.const 0)

theorem union_real_mem {M : ZFSet.{u}} (C : Context M) (G : Oracle) (hG : G ∈ reals M)
    (c : ℕ → ℕ) (hc : ∀ n k, G (Nat.pair n k) = true ↔ k = c n) :
    Test.realPart (unionRead c) ∈ reals M := by
  let idx : ℕ → ℕ := fun n => Nat.pair 0 n
  have hi : Primrec idx := Primrec₂.natPair.comp (Primrec.const 0) Primrec.id
  have hq := (Arith.query 0).comp
    (fun n => Nat.pair (idx (left n)+1) (right n))
    (Primrec₂.natPair.comp (Primrec.succ.comp (hi.comp left_primrec)) right_primrec)
  have hr : Arith (fun _ n => (decodeNode (right n))[idx (left n)]?.getD 0 = 1) :=
    .pure _ (Primrec.eq.comp (read_primrec.comp (right_primrec.pair (hi.comp left_primrec))) (Primrec.const 1))
  apply arithmetic_comprehension C (hq.and hr).ex (fun _ => G) (fun _ => hG) _
  intro n
  simp only [left,right,Nat.unpair_pair]
  change (∃ k, G (Nat.pair (idx n + 1) k) = true ∧ (decodeNode k)[idx n]?.getD 0 = 1) ↔ _
  simp only [hc,exists_eq_left,Test.realPart,unionRead,idx]
  exact ⟨decide_eq_true,of_decide_eq_true⟩

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalMinimalSelector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace InternalWellOrder

theorem leastMinimal_exists {δ d F r a : ZFSet.{u}} (hδ : δ.IsOrdinal)
    (honto : ∀ x ∈ d, ∃ i ∈ δ, ZFSet.pair i x ∈ F) (ha : a ⊆ d)
    (hm : ∃ x, MinimalIn r a x) : ∃ x, LeastMinimal δ F r a x := by
  classical
  have find (i : ZFSet.{u}) : i ∈ δ → (∃ x, MinimalIn r a x ∧ ZFSet.pair i x ∈ F) →
      ∃ x, LeastMinimal δ F r a x := by
    induction i using ZFSet.inductionOn with
    | h i ih =>
      intro hi hx
      by_cases he : ∃ j ∈ i, ∃ y, MinimalIn r a y ∧ ZFSet.pair j y ∈ F
      · obtain ⟨j,hji,hy⟩ := he
        exact ih j hji (hδ.subset_of_mem hi hji) hy
      · obtain ⟨x,hx,hix⟩ := hx
        exact ⟨x,hx,i,hi,hix,fun j hj y _ hjy hmy => he ⟨j,hj,y,hmy,hjy⟩⟩
  obtain ⟨x,hx⟩ := hm
  obtain ⟨i,hi,hix⟩ := honto x (ha hx.1)
  exact find i hi ⟨x,hx,hix⟩

theorem LeastMinimal.unique {δ d F r a x y : ZFSet.{u}} (hδ : δ.IsOrdinal)
    (hF : TransitiveNameModel.FunctionGraph δ d F)
    (hx : LeastMinimal δ F r a x) (hy : LeastMinimal δ F r a y) : x = y := by
  obtain ⟨hx,i,hi,hix,hleast⟩ := hx
  obtain ⟨hy,j,hj,hjy,hleast'⟩ := hy
  rcases (hδ.mem hi).mem_trichotomous (hδ.mem hj) with hij|he|hji
  · exact False.elim (hleast' i hij x hx.1 hix hx)
  · subst j; exact hF.functional hi hix hjy
  · exact False.elim (hleast j hji y hy.1 hjy hy)

open Formula

theorem eval_minimalInFormula (r a x : ℕ) (e : ℕ → ZFSet.{u}) :
    (minimalInFormula r a x).Eval e ↔ MinimalIn (e r) (e a) (e x) := by
  simp only [minimalInFormula,MinimalIn,Formula.Eval,eval_allMem,eval_pairMem,cons_zero,cons_succ]

theorem eval_leastMinimalFormula (δ F r a x : ℕ) (e : ℕ → ZFSet.{u}) :
    (leastMinimalFormula δ F r a x).Eval e ↔ LeastMinimal (e δ) (e F) (e r) (e a) (e x) := by
  simp only [leastMinimalFormula,LeastMinimal,Formula.Eval,eval_minimalInFormula,
    eval_pairMem,eval_allMem,eval_imp,cons_zero,cons_succ]

theorem internal_minimal_selector (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hw : InternallyWellFounded M d r) :
    ∃ q ∈ M, ∃ s ∈ M, ChoiceGraph q s ∧
      (∀ a, a ∈ q ↔ a ∈ M ∧ a ⊆ d ∧ ∃ x, x ∈ a) ∧
      ∀ a x, ZFSet.pair a x ∈ s → MinimalIn r a x := by
  have hS := hT.separation.finitePrefix
  obtain ⟨q,hq,_,_,_,hqdef⟩ := internal_selector M hM hT.powerSet hS.bounded hT.choice hd
  obtain ⟨δ,hδM,hδ,F,hFM,hF,honto,_⟩ := internal_ordinal_enumeration M hM
    hT.pairing hT.union hT.powerSet hS hT.replacement.finitePrefix hT.infinity hT.choice hd
  let e := cons q (cons d (cons δ (cons F (fun _ => r))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hq
    rcases i with _|i; exact hd
    rcases i with _|i; exact hδM
    rcases i with _|i; exact hFM
    exact hr
  let s := ZFSet.sep (fun z => minimalSelectorFormula.Eval (cons z e)) (ZFSet.prod q d)
  have hs : s ∈ M := sep_mem M hM hS.bounded _ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS.bounded hq hd)
  have hmem (z : ZFSet.{u}) : z ∈ s ↔
      ∃ a ∈ q, ∃ x ∈ a, z = ZFSet.pair a x ∧ LeastMinimal δ F r a x := by
    simp only [s,ZFSet.mem_sep,minimalSelectorFormula,Formula.Eval,eval_orderedPair,
      eval_leastMinimalFormula,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,a,ha,x,_,hz,hm⟩; exact ⟨a,ha,x,hm.1.1,hz,hm⟩
    · rintro ⟨a,ha,x,hx,rfl,hm⟩
      have hxd := ((hqdef a).mp ha).2.1 hx
      exact ⟨ZFSet.mem_prod.mpr ⟨a,ha,x,hxd,rfl⟩,a,ha,x,hxd,rfl,hm⟩
  refine ⟨q,hq,s,hs,⟨?_,?_⟩,hqdef,?_⟩
  · intro z hz
    obtain ⟨a,ha,x,hx,hz,_⟩ := (hmem z).mp hz
    exact ⟨a,ha,x,hx,hz⟩
  · intro a ha
    obtain ⟨haM,had,hane⟩ := (hqdef a).mp ha
    obtain ⟨x,hx⟩ := leastMinimal_exists hδ honto had (hw a haM had hane)
    refine ⟨x,hx.1.1,(hmem _).mpr ⟨a,ha,x,hx.1.1,rfl,hx⟩,?_⟩
    intro y _ hy
    obtain ⟨a',_,y',_,heq,hy'⟩ := (hmem _).mp hy
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact hy'.unique hδ hF hx
  · intro a x hax
    obtain ⟨a',_,x',_,heq,hx⟩ := (hmem _).mp hax
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact hx.1

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_SelectorOrdinalEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace InternalWellOrder

theorem internal_enumeration_from_selector (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {a q s : ZFSet.{u}} (ha : a ∈ M) (hq : q ∈ M) (hsM : s ∈ M)
    (hs : ChoiceGraph q s) (hqdef : ∀ x, x ∈ q ↔ x ∈ M ∧ x ⊆ a ∧ ∃ y, y ∈ x) :
    ∃ δ ∈ M, δ.IsOrdinal ∧ ∃ F ∈ M, TransitiveNameModel.FunctionGraph δ a F ∧
      (∀ x ∈ a, ∃ i ∈ δ, ZFSet.pair i x ∈ F) ∧
      (∀ i ∈ δ, ∀ j ∈ δ, ∀ x, ZFSet.pair i x ∈ F → ZFSet.pair j x ∈ F → i = j) ∧
      (∀ i ∈ δ, ∀ x ∈ a, ZFSet.pair i x ∈ F →
        ∃ b ∈ q, Remaining a F i b ∧ ZFSet.pair b x ∈ s) := by
  classical
  obtain ⟨α,hαM,hα,hHartogs⟩ := internal_hartogs M a hM hP hU hPow hS hR hI ha
  have hαT : Transitive α := fun i hi j hj => hα.subset_of_mem hi hj
  obtain ⟨F,hF,htrace,hmax⟩ := internal_maximal_trace M hM hP hU hPow hS.bounded hαM ha hq hsM hαT hs
  have hfun := htrace.functional hαT hs
  have hmissing : ∃ i ∈ α, ¬ ∃ x ∈ a, ZFSet.pair i x ∈ F := by
    by_contra hn
    have htotal : ∀ i ∈ α, ∃ x ∈ a, ZFSet.pair i x ∈ F := by
      intro i hi; exact Classical.byContradiction (fun h => hn ⟨i,hi,h⟩)
    have hfg : TransitiveNameModel.FunctionGraph α a F := by
      refine ⟨htrace.shape,?_⟩
      intro i hi
      obtain ⟨x,hx,hix⟩ := htotal i hi
      exact ⟨x,hx,hix,fun y _ hiy => hfun i y x hiy hix⟩
    obtain ⟨v,hv,hva⟩ := FunctionGraph.exists_presentation hfg
    apply hHartogs F hF v hv hva
    intro i hi j hj he
    have hip := (hv.pair_iff i (v i)).mpr ⟨hi,rfl⟩
    have hjp := (hv.pair_iff j (v j)).mpr ⟨hj,rfl⟩
    rw [← he] at hjp
    exact htrace.injective hα hs i j (v i) hip hjp
  have minimal (i : ZFSet.{u}) : i ∈ α → (¬ ∃ x ∈ a, ZFSet.pair i x ∈ F) →
      ∃ j ∈ α, (¬ ∃ x ∈ a, ZFSet.pair j x ∈ F) ∧
        ∀ k ∈ j, ∃ x ∈ a, ZFSet.pair k x ∈ F := by
    induction i using ZFSet.inductionOn with
    | h i ih =>
      intro hi hmiss
      by_cases hex : ∃ j ∈ i, ¬ ∃ x ∈ a, ZFSet.pair j x ∈ F
      · obtain ⟨j,hji,hjmiss⟩ := hex
        exact ih j hji (hα.subset_of_mem hi hji) hjmiss
      · refine ⟨i,hi,hmiss,?_⟩
        intro j hji
        exact Classical.byContradiction (fun h => hex ⟨j,hji,h⟩)
  obtain ⟨i,hi,hmiss⟩ := hmissing
  obtain ⟨i,hi,hmiss,hprev⟩ := minimal i hi hmiss
  have hiM := hM α hαM i hi
  have hiT : Transitive i := fun j hj k hk => (hα.mem hi).subset_of_mem hj hk
  have hdom : ∀ j y, ZFSet.pair j y ∈ F → j ∈ i := htrace.domain_before hα hi hmiss
  have hres := residual_mem M hM hS.bounded ha hF hiM
  have hrem := residual_remaining a F i
  have hempty : ¬ ∃ x, x ∈ residual a F i := by
    intro hex
    have hrq : residual a F i ∈ q := (hqdef _).mpr ⟨hres,hrem.1,hex⟩
    obtain ⟨x,hxr,hrx,_⟩ := hs.2 _ hrq
    have hxa := hrem.1 hxr
    have hpair := orderedPair_mem M hM hP hiM (hM a ha x hxa)
    have hnew := binary_union_mem M hM hP hU hF (singleton_mem M hM hP hpair)
    have hnewtrace := htrace.adjoin hi hiT hxa hrq hrem hrx hprev hdom
    have hnewsub := hmax _ hnew hnewtrace
    exact hmiss ⟨x,hxa,hnewsub (ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl)))⟩
  refine ⟨i,hiM,hα.mem hi,F,hF,?_,?_,?_,?_⟩
  · refine ⟨?_,?_⟩
    · intro z hz
      obtain ⟨j,_,x,hx,rfl⟩ := htrace.shape z hz
      exact ⟨j,hdom j x hz,x,hx,rfl⟩
    · intro j hj
      obtain ⟨x,hx,hjx⟩ := hprev j hj
      exact ⟨x,hx,hjx,fun y _ hjy => hfun j y x hjy hjx⟩
  · intro x hx
    exact Classical.byContradiction (fun hn => hempty ⟨x,(hrem.2 x hx).mpr hn⟩)
  · intro j _ k _ x hjx hkx
    exact htrace.injective hα hs j k x hjx hkx

  · intro j hj x hx hjx
    exact htrace.choice j (hα.subset_of_mem hi hj) x hx hjx

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTWellFounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace InternalWellOrder

theorem sourceT_internal_ordinal_ranking (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hw : InternallyWellFounded M d r) :
    ∃ δ ∈ M, δ.IsOrdinal ∧ ∃ F ∈ M, TransitiveNameModel.FunctionGraph δ d F ∧
      (∀ x ∈ d, ∃ i ∈ δ, ZFSet.pair i x ∈ F) ∧
      (∀ i ∈ δ, ∀ j ∈ δ, ∀ x y, ZFSet.pair i x ∈ F → ZFSet.pair j y ∈ F →
        ZFSet.pair y x ∈ r → j ∈ i) := by
  obtain ⟨q,hq,s,hsM,hs,hqdef,hmin⟩ := internal_minimal_selector M hM hT hd hr hw
  obtain ⟨δ,hδM,hδ,F,hFM,hF,honto,hinj,hchoice⟩ := internal_enumeration_from_selector M hM
    hT.pairing hT.union hT.powerSet hT.separation.finitePrefix hT.replacement.finitePrefix
    hT.infinity hd hq hsM hs hqdef
  refine ⟨δ,hδM,hδ,F,hFM,hF,honto,?_⟩
  intro i hi j hj x y hix hjy hyx
  have hx := hF.value_mem hix
  have hy := hF.value_mem hjy
  obtain ⟨a,_,hrem,hax⟩ := hchoice i hi x hx hix
  by_contra hji
  have hya : y ∈ a := (hrem.2 y hy).mpr (by
    rintro ⟨k,hki,hky⟩
    have hkj := hinj k (hδ.subset_of_mem hi hki) j hj y hky hjy
    exact hji (hkj ▸ hki))
  exact (hmin a x hax).2 y hya hyx

theorem sourceT_wellFounded (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hon : On d r)
    (hw : InternallyWellFounded M d r) : WellFounded (Rel d r) := by
  classical
  obtain ⟨δ,_,_,F,_,_,honto,hrank⟩ := sourceT_internal_ordinal_ranking M hM hT hd hr hw
  let index (x : ZFSet.{u}) : ZFSet.{u} := if hx : x ∈ d then (honto x hx).choose else ∅
  have hi (x : ZFSet.{u}) (hx : x ∈ d) : index x ∈ δ ∧ ZFSet.pair (index x) x ∈ F := by
    simp only [index,dite_eq_left hx]
    exact (honto x hx).choose_spec
  apply (show WellFounded (fun y x => index y ∈ index x) from InvImage.wf index ZFSet.mem_wf).mono
  intro y x hyx
  have hx : x ∈ d := by
    obtain ⟨y',_,x',hx,he⟩ := ZFSet.mem_prod.mp (hon hyx.2)
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact hx
  exact hrank _ (hi x hx).1 _ (hi y hyx.1).1 x y (hi x hx).2 (hi y hyx.1).2 hyx.2

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_FiniteModelGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem finiteModelGraph_pair (f : ℕ → ZFSet.{u}) (n i : ℕ) (y : ZFSet.{u}) :
    ZFSet.pair (natSet i) y ∈ finiteModelGraph f n ↔ i ≤ n ∧ y = f i := by
  rw [mem_finiteModelGraph]
  constructor
  · rintro ⟨j,hj,he⟩
    obtain ⟨hij,hy⟩ := ZFSet.pair_inj.mp he
    have heq := natSet_injective hij
    subst j
    exact ⟨hj,hy⟩
  · rintro ⟨hi,rfl⟩
    exact ⟨i,hi,rfl⟩

theorem finiteModelGraph_function (R : ZFSet.{u}) (f : ℕ → ZFSet.{u}) (hf : ∀ i, f i ∈ R) (n : ℕ) :
    TransitiveNameModel.FunctionGraph (natSet (n+1)) R (finiteModelGraph.{u} f n) := by
  constructor
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := (mem_finiteModelGraph f n z).mp hz
    exact ⟨natSet i,(natSet_mem_natSet i (n+1)).mpr (by omega),f i,
      hf i,rfl⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet (n+1) x).mp hx
    have hin : i ≤ n := by omega
    refine ⟨f i,hf i,
      (finiteModelGraph_pair f n i _).mpr ⟨hin,rfl⟩,?_⟩
    intro y _ hy
    exact ((finiteModelGraph_pair f n i y).mp hy).2

theorem internal_finite_model_graph_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M) (R : ZFSet.{u}) (hR : R ∈ M) :
    ∃ Q ∈ M, (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ ZFSet.prod ZFSet.omega R) ∧
      ∀ f : ℕ → ZFSet.{u}, (∀ i, f i ∈ R) → ∀ n, finiteModelGraph f n ∈ Q := by
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hPow (product_mem M hM hP hU hPow hS hω hR)
  refine ⟨Q,hQ,hQdef,?_⟩
  intro f hf n
  apply (hQdef _).mpr
  refine ⟨finiteModelGraph_mem M hM hP hU hω f (fun i => hM _ hR _ (hf i)) n,?_⟩
  intro z hz
  obtain ⟨i,_,rfl⟩ := (mem_finiteModelGraph f n z).mp hz
  exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i,rfl⟩,_,hf i,rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelIterationTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem modelIterationTrace_exists (R : ZFSet.{u}) (a : ℕ → ZFSet.{u})
    (ha : ∀ i, a i ∈ R) (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i, S (natSet i) (a i) (a (i+1))) (n : ℕ) :
    ModelIterationTrace ZFSet.omega R (natSet 0) (natSet (n+1)) (natSet n) (a 0)
      (finiteModelGraph a n) S := by
  refine ⟨finiteModelGraph_function R a ha n,rfl,rfl,?_,?_⟩
  · exact (finiteModelGraph_pair a n 0 _).mpr ⟨Nat.zero_le _,rfl⟩
  · intro i hi j _ hj v _ w _ hiv hjw
    obtain ⟨i,_,rfl⟩ := (mem_natSet n i).mp hi
    have hj' : j = natSet (i+1) := hj
    subst j
    rw [((finiteModelGraph_pair a n i v).mp hiv).2,
      ((finiteModelGraph_pair a n (i+1) w).mp hjw).2]
    exact hS i

theorem ModelIterationTrace.correct {R z k f : ZFSet.{u}} (a : ℕ → ZFSet.{u})
    (ha : ∀ i, a i ∈ R) (n : ℕ)
    (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i w, w ∈ R → S (natSet i) (a i) w → w = a (i+1))
    (hf : ModelIterationTrace ZFSet.omega R z k (natSet n) (a 0) f S)
    {y : ZFSet.{u}} (hy : ZFSet.pair (natSet n) y ∈ f) : y = a n := by
  obtain ⟨hfun,hk,rfl,hzero,hstep⟩ := hf
  have hk' : k = natSet (n+1) := hk
  subst k
  have computes (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (a i) ∈ f := by
    induction i with
    | zero => exact hzero
    | succ i ih =>
      have hin : i ≤ n := by omega
      have hj : natSet.{u} (i+1) ∈ natSet (n+1) := (natSet_mem_natSet _ _).mpr (by omega)
      obtain ⟨w,hw,hjw,_⟩ := hfun.2 _ hj
      have hs := hstep (natSet i) ((natSet_mem_natSet _ _).mpr (by omega)) (natSet (i+1))
        ((mem_omega _).mpr ⟨i+1,rfl⟩) rfl (a i) (ha i) w hw (ih hin) hjw
      have he : w = a (i+1) := hS i w hw hs
      exact he ▸ hjw
  exact hfun.functional ((natSet_mem_natSet n (n+1)).mpr (Nat.lt_succ_self n)) hy (computes n le_rfl)

namespace Formula

theorem eval_modelIterationTrace (o R z k n b f : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (modelIterationTrace o R z k n b f θ).Eval e ↔ ModelIterationTrace (e o) (e R) (e z) (e k) (e n) (e b) (e f)
      (fun i v w => θ.Eval (cons w (cons v (cons i e)))) := by
  simp only [modelIterationTrace,ModelIterationTrace,TransitiveNameModel.FunctionGraph,Formula.Eval,
    eval_functionGraph,eval_successor,eval_empty,eval_pairMem,eval_allMem,eval_imp,eval_rename,cons_zero,cons_succ]
  have eq (i j v w : ZFSet.{u}) :
      (fun n => cons w (cons v (cons j (cons i e))) (modelIterationVars n)) = cons w (cons v (cons i e)) := by
    funext n
    rcases n with _|n; rfl
    rcases n with _|n; rfl
    rcases n with _|n <;> rfl
  simp only [eq]
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelIterationFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace Formula

theorem eval_modelIteration (o R Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (modelIteration o R Q n b y θ).Eval e ↔ ∃ k ∈ e o, ∃ z ∈ e o, ∃ f ∈ e Q,
      ModelIterationTrace (e o) (e R) z k (e n) (e b) f
        (fun i v w => θ.Eval (cons w (cons v (cons i e)))) ∧ ZFSet.pair (e n) (e y) ∈ f := by
  simp only [modelIteration,Formula.Eval,eval_modelIterationTrace,eval_pairMem,eval_rename,cons_zero,cons_succ]
  have eq (k z f i v w : ZFSet.{u}) :
      (fun n => cons w (cons v (cons i (cons f (cons z (cons k e))))) (modelIterationOuterVars n)) =
        cons w (cons v (cons i e)) := by
    funext n
    rcases n with _|n; rfl
    rcases n with _|n; rfl
    rcases n with _|n <;> rfl
  simp only [eq]

theorem modelIteration_spec (o R Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega)
    (hQ : ∀ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ e R) → ∀ k, finiteModelGraph a k ∈ e Q)
    (N : ℕ) (hn : e n = natSet N) (a : ℕ → ZFSet.{u}) (ha : ∀ i, a i ∈ e R)
    (hb : e b = a 0)
    (hθ : ∀ i w, w ∈ e R →
      (θ.Eval (cons w (cons (a i) (cons (natSet i) e))) ↔ w = a (i+1))) :
    (modelIteration o R Q n b y θ).Eval e ↔ e y = a N := by
  rw [eval_modelIteration,ho,hn,hb]
  constructor
  · rintro ⟨k,_,z,_,f,_,hf,hy⟩
    exact hf.correct a ha N _ (fun i w hw h => (hθ i w hw).mp h) hy
  · intro hy
    refine ⟨natSet (N+1),(mem_omega _).mpr ⟨N+1,rfl⟩,natSet 0,(mem_omega _).mpr ⟨0,rfl⟩,
      finiteModelGraph a N,hQ a ha N,?_,?_⟩
    · exact modelIterationTrace_exists (e R) a ha _ (fun i => (hθ i _ (ha (i+1))).mpr rfl) N
    · exact (finiteModelGraph_pair a N N _).mpr ⟨le_rfl,hy⟩

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFunctionOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem mem_orbitGraph (a : ℕ → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ orbitGraph a ↔ ∃ n, z = ZFSet.pair (natSet n) (a n) := by
  rw [orbitGraph,ZFSet.mem_range]
  exact ⟨fun ⟨n,hn⟩ => ⟨n,hn.symm⟩,fun ⟨n,hn⟩ => ⟨n,hn.symm⟩⟩

theorem orbitGraph_pair (a : ℕ → ZFSet.{u}) (n : ℕ) (x : ZFSet.{u}) :
    ZFSet.pair (natSet n) x ∈ orbitGraph a ↔ x = a n := by
  rw [mem_orbitGraph]
  constructor
  · rintro ⟨m,he⟩
    obtain ⟨hn,hx⟩ := ZFSet.pair_inj.mp he
    have hnm := natSet_injective hn
    exact hnm.symm ▸ hx
  · intro h; exact ⟨n,congrArg (ZFSet.pair (natSet n)) h⟩

theorem orbitGraph_function (d : ZFSet.{u}) (a : ℕ → ZFSet.{u}) (ha : ∀ n, a n ∈ d) :
    TransitiveNameModel.FunctionGraph ZFSet.omega d (orbitGraph a) := by
  constructor
  · intro z hz
    obtain ⟨n,rfl⟩ := (mem_orbitGraph a z).mp hz
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,a n,ha n,rfl⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨a n,ha n,(orbitGraph_pair a n _).mpr rfl,fun y _ hy => (orbitGraph_pair a n y).mp hy⟩

namespace Formula

theorem orbitMember_spec (o d Q b F z : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ e d) → ∀ k, finiteModelGraph a k ∈ e Q)
    (hF : TransitiveNameModel.FunctionGraph (e d) (e d) (e F))
    (a : ℕ → ZFSet.{u}) (ha : ∀ i, a i ∈ e d) (hb : e b = a 0)
    (hstep : ∀ i, ZFSet.pair (a i) (a (i+1)) ∈ e F) :
    (orbitMember o d Q b F z).Eval e ↔ e z ∈ orbitGraph a := by
  simp only [orbitMember,Formula.Eval,eval_orderedPair,cons_zero,cons_succ]
  rw [ho,mem_orbitGraph]
  have hs (n : ℕ) (w : ZFSet.{u}) :
      (modelIteration (o+2) (d+2) (Q+2) 1 (b+2) 0 (.pairMem 1 0 (F+5))).Eval
        (cons w (cons (natSet n) e)) ↔ w = a n := by
    apply modelIteration_spec (o+2) (d+2) (Q+2) 1 (b+2) 0 (.pairMem 1 0 (F+5))
      (cons w (cons (natSet n) e)) ho hQ n rfl a ha hb
    intro i v _
    simp only [eval_pairMem,cons_zero,cons_succ]
    exact ⟨fun hv => hF.functional (ha i) hv (hstep i),fun hv => hv.symm ▸ hstep i⟩
  constructor
  · rintro ⟨n,hn,w,_,hz,hw⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    rw [(hs n w).mp hw] at hz
    exact ⟨n,hz⟩
  · rintro ⟨n,hz⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,a n,ha n,hz,(hs n _).mpr rfl⟩
end Formula

theorem internal_orbitGraph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d F : ZFSet.{u}} (hd : d ∈ M) (hFM : F ∈ M)
    (hF : TransitiveNameModel.FunctionGraph d d F) (a : ℕ → ZFSet.{u})
    (ha : ∀ i, a i ∈ d) (hstep : ∀ i, ZFSet.pair (a i) (a (i+1)) ∈ F) : orbitGraph a ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_model_graph_bound M hM hT.pairing hT.union hT.powerSet hS hω d hd
  let e := cons ZFSet.omega (cons d (cons Q (cons (a 0) (fun _ => F))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hω
    rcases i with _|i; exact hd
    rcases i with _|i; exact hQM
    rcases i with _|i; exact hM _ hd _ (ha 0)
    exact hFM
  have hs := sep_mem M hM hS (Formula.orbitMember 1 2 3 4 5 0) e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hd)
  have hEq : ZFSet.sep (fun z => (Formula.orbitMember 1 2 3 4 5 0).Eval (cons z e))
      (ZFSet.prod ZFSet.omega d) = orbitGraph a := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,Formula.orbitMember_spec 1 2 3 4 5 0 (cons z e) rfl hQ hF a ha rfl hstep]
    exact ⟨And.right,fun h => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function d a ha).1 z h),h⟩⟩
  exact hEq ▸ hs

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSerialSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationHull
universe u
namespace Formula

theorem eval_predecessorSet (d r x a : ℕ) (e : ℕ → ZFSet.{u}) :
    (predecessorSet d r x a).Eval e ↔ e a = predecessors (e d) (e r) (e x) := by
  simp only [predecessorSet,Formula.Eval,eval_subset,eval_allMem,eval_iff,eval_pairMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro y
    rw [mem_predecessors]
    exact ⟨fun hy => ⟨hsub hy,(h y (hsub hy)).mp hy⟩,fun hy => (h y hy.1).mpr hy.2⟩
  · intro he
    rw [he]
    exact ⟨fun _ h => (mem_predecessors _ _ _ _).mp h |>.1,
      fun y hy => (mem_predecessors _ _ _ _).trans (and_iff_right hy)⟩

end Formula

theorem internal_serial_function (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M)
    (hser : ∀ x ∈ d, ∃ y ∈ d, ZFSet.pair y x ∈ r) :
    ∃ F ∈ M, TransitiveNameModel.FunctionGraph d d F ∧
      ∀ x y, ZFSet.pair x y ∈ F → ZFSet.pair y x ∈ r := by
  have hS := hT.separation.finitePrefix.bounded
  obtain ⟨q,hq,s,hsM,hs,hqdef⟩ := internal_selector M hM hT.powerSet hS hT.choice hd
  have hp (x : ZFSet.{u}) (hx : x ∈ d) : predecessors d r x ∈ q := by
    apply (hqdef _).mpr
    refine ⟨predecessors_mem M hM hS hd hr (hM _ hd _ hx),
      fun _ h => (mem_predecessors _ _ _ _).mp h |>.1,?_⟩
    obtain ⟨y,hy,hyx⟩ := hser x hx
    exact ⟨y,(mem_predecessors _ _ _ _).mpr ⟨hy,hyx⟩⟩
  let e := cons d (cons r (cons q (fun _ => s)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hd
    rcases i with _|i; exact hr
    rcases i with _|i; exact hq
    exact hsM
  let F := ZFSet.sep (fun z => (Formula.serialSelector 1 2 3 4 0).Eval (cons z e)) (ZFSet.prod d d)
  have hFM : F ∈ M := sep_mem M hM hS _ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hd hd)
  have hmem (z : ZFSet.{u}) : z ∈ F ↔
      ∃ x ∈ d, ∃ y ∈ d, z = ZFSet.pair x y ∧ ZFSet.pair (predecessors d r x) y ∈ s := by
    simp only [F,ZFSet.mem_sep,Formula.serialSelector,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_predecessorSet,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,x,hx,y,hy,hz,a,_,rfl,hay⟩; exact ⟨x,hx,y,hy,hz,hay⟩
    · rintro ⟨x,hx,y,hy,rfl,hxy⟩
      exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,predecessors d r x,hp x hx,rfl,hxy⟩
  refine ⟨F,hFM,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,y,hy,hz,_⟩ := (hmem z).mp hz
    exact ⟨x,hx,y,hy,hz⟩
  · intro x hx
    obtain ⟨y,hy,hxy,_⟩ := hs.2 _ (hp x hx)
    have hyd := ((mem_predecessors _ _ _ _).mp hy).1
    refine ⟨y,hyd,(hmem _).mpr ⟨x,hx,y,hyd,rfl,hxy⟩,?_⟩
    intro z _ hxz
    obtain ⟨x',_,z',_,heq,hxz'⟩ := (hmem _).mp hxz
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact hs.functional hxz' hxy
  · intro x y hxy
    obtain ⟨x',_,y',_,heq,hsy⟩ := (hmem _).mp hxy
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact ((mem_predecessors _ _ _ _).mp (InternalWellOrder.choice_value_mem hs hsy)).2

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTDependentChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse InternalWellOrder
universe u

theorem sourceT_dependent_choice (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r x : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hx : x ∈ d)
    (hser : ∀ x ∈ d, ∃ y ∈ d, ZFSet.pair y x ∈ r) :
    ∃ a : ℕ → ZFSet.{u}, a 0 = x ∧ (∀ n, a n ∈ d) ∧ orbitGraph a ∈ M ∧
      ∀ n, ZFSet.pair (a (n+1)) (a n) ∈ r := by
  classical
  obtain ⟨F,hFM,hF,hrel⟩ := internal_serial_function M hM hT hd hr hser
  let next (y : ZFSet.{u}) : ZFSet.{u} := if hy : y ∈ d then (hF.2 y hy).choose else y
  have hn (y : ZFSet.{u}) (hy : y ∈ d) : next y ∈ d ∧ ZFSet.pair y (next y) ∈ F := by
    simp only [next,dite_eq_left hy]
    exact ⟨(hF.2 y hy).choose_spec.1,(hF.2 y hy).choose_spec.2.1⟩
  let a : ℕ → ZFSet.{u} := Nat.rec x (fun _ y => next y)
  have ha : ∀ n, a n ∈ d := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => exact (hn (a n) ih).1
  have hstep : ∀ n, ZFSet.pair (a n) (a (n+1)) ∈ F := fun n => (hn (a n) (ha n)).2
  exact ⟨a,rfl,ha,internal_orbitGraph M hM hT hd hFM hF a ha hstep,
    fun n => hrel _ _ (hstep n)⟩

theorem sourceT_internal_descent (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hon : On d r)
    (hw : ¬ WellFounded (Rel d r)) :
    ∃ a : ℕ → ZFSet.{u}, (∀ n, a n ∈ d) ∧ orbitGraph a ∈ M ∧
      ∀ n, ZFSet.pair (a (n+1)) (a n) ∈ r := by
  classical
  have hn : ¬ InternallyWellFounded M d r := fun h => hw (sourceT_wellFounded M hM hT hd hr hon h)
  change ¬ (∀ b ∈ M, b ⊆ d → (∃ x, x ∈ b) → ∃ x, MinimalIn r b x) at hn
  simp only [not_forall] at hn
  obtain ⟨b,hb,hbd,hne,hbad⟩ := hn
  obtain ⟨x,hx⟩ := hne
  have hser : ∀ x ∈ b, ∃ y ∈ b, ZFSet.pair y x ∈ r := by
    intro y hy
    by_contra hn
    exact hbad ⟨y,hy,fun z hz hzy => hn ⟨z,hz,hzy⟩⟩
  obtain ⟨a,_,ha,hAM,hstep⟩ := sourceT_dependent_choice M hM hT hb hr hx hser
  exact ⟨a,fun n => hbd (ha n),hAM,hstep⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNaturalRelationReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u

theorem naturalRelationReal_pair (G : ZFSet.{u}) (n k : ℕ) :
    naturalRelationReal G (Nat.pair n k) = true ↔ ZFSet.pair (natSet n) (natSet k) ∈ G := by
  classical
  simp [naturalRelationReal]

namespace Formula

theorem naturalRelationBit_spec (o Q G v : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (N K : ℕ) (hv : e v = natSet (Nat.pair N K)) :
    (naturalRelationBit o Q G v).Eval e ↔ ZFSet.pair (natSet N) (natSet K) ∈ e G := by
  simp only [naturalRelationBit,Formula.Eval,eval_pairMem,cons_succ,cons_zero]
  rw [ho]
  constructor
  · rintro ⟨n,hn,k,hk,hp,hg⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨k,rfl⟩ := (mem_omega k).mp hk
    have hp' := (naturalPair_spec (o+2) (Q+2) 1 0 (v+2)
      (cons (natSet k) (cons (natSet n) e)) ho hQ n k rfl rfl).mp hp
    have hnk : Nat.pair N K = Nat.pair n k := natSet_injective (hv.symm.trans hp')
    have he := congrArg Nat.unpair hnk
    simp only [Nat.unpair_pair,Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    exact hg
  · intro h
    exact ⟨natSet N,(mem_omega _).mpr ⟨N,rfl⟩,natSet K,(mem_omega _).mpr ⟨K,rfl⟩,
      (naturalPair_spec (o+2) (Q+2) 1 0 (v+2)
        (cons (natSet K) (cons (natSet N) e)) ho hQ N K rfl rfl).mpr hv,h⟩
end Formula

theorem sourceT_naturalRelationReal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {G : ZFSet.{u}} (hG : G ∈ M) : naturalRelationReal G ∈ modelReals M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet hS hω
  let e := cons ZFSet.omega (cons Q (fun _ => G))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hω
    rcases i with _|i; exact hQM
    exact hG
  let B := ZFSet.sep (fun v => (Formula.naturalRelationBit 1 2 3 0).Eval (cons v e)) ZFSet.omega
  have hBM : B ∈ M := sep_mem M hM hS _ e he hω
  have hb (v : ℕ) : natSet.{u} v ∈ B ↔ naturalRelationReal G v = true := by
    obtain ⟨⟨n,k⟩,rfl⟩ := Nat.pairEquiv.surjective v
    change natSet (Nat.pair n k) ∈ B ↔ naturalRelationReal G (Nat.pair n k) = true
    rw [naturalRelationReal_pair]
    change natSet (Nat.pair n k) ∈ ZFSet.sep _ ZFSet.omega ↔ _
    rw [ZFSet.mem_sep,Formula.naturalRelationBit_spec 1 2 3 0
      (cons (natSet (Nat.pair n k)) e) rfl hQ n k rfl]
    exact and_iff_right ((mem_omega _).mpr ⟨Nat.pair n k,rfl⟩)
  have hEq : realCode (naturalRelationReal G) = B := by
    apply ZFSet.ext; intro x
    by_cases hx : x ∈ ZFSet.omega.{u}
    · obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      rw [natSet_mem_realCode,hb]
    · exact ⟨fun h => False.elim (hx (realCode_subset _ h)),fun h => False.elim (hx (ZFSet.mem_sep.mp h).1)⟩
  change realCode _ ∈ M
  rw [hEq]; exact hBM

theorem sourceT_natural_descent_real (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {r : ZFSet.{u}} (hr : r ∈ M) (hon : On ZFSet.omega r)
    (hw : ¬ WellFounded (Rel ZFSet.omega r)) :
    ∃ f : ℕ → ℕ, ∃ A ∈ modelReals M,
      (∀ n k, A (Nat.pair n k) = true ↔ k = f n) ∧
      ∀ n, ZFSet.pair (natSet (f (n+1))) (natSet (f n)) ∈ r := by
  classical
  obtain ⟨a,ha,hAM,hstep⟩ := sourceT_internal_descent M hM hT (sourceT_omega_mem M hM hT) hr hon hw
  have hn (n : ℕ) : ∃ k, a n = natSet k := (mem_omega _).mp (ha n)
  let f (n : ℕ) := (hn n).choose
  have hf (n : ℕ) : a n = natSet (f n) := (hn n).choose_spec
  refine ⟨f,naturalRelationReal (orbitGraph a),sourceT_naturalRelationReal M hM hT hAM,?_,?_⟩
  · intro n k
    rw [naturalRelationReal_pair,orbitGraph_pair,hf n]
    exact ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩
  · intro n
    rw [←hf (n+1),←hf n]
    exact hstep n

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTTreeAbsoluteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelFunctions SetModelReals SetModelSyntax RelationCollapse
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

theorem sourceContext (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) : Context M :=
  ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩

theorem modelReals_eq (M : ZFSet.{u}) : modelReals M = reals M := rfl

private theorem zero_real_mem {M : ZFSet.{u}} (C : Context M) : (fun _ => false) ∈ reals M := by
  have he : realSet.{u} (fun _ => false) = ∅ := by
    apply ZFSet.ext
    intro x
    simp [realSet]
  change realSet _ ∈ M
  rw [he]
  exact C.nat_mem 0

private theorem relationSet_on (B : Oracle) : On ZFSet.omega.{u} (relationSet B) :=
  fun _ hz => (ZFSet.mem_sep.mp hz).1

theorem Test.illFounded_edges (t : Test) (O : Oracles) (v : ℕ)
    (r : ZFSet.{u}) (hr : ∀ n m, ZFSet.pair (natSet n) (natSet m) ∈ r ↔ t.edgePredicate O v n m)
    (hw : ∃ f : ℕ → ℕ, ∀ n, t.eval O f (Nat.pair v n)) :
    ¬ WellFounded (Rel ZFSet.omega r) := by
  rintro hf
  obtain ⟨f,hf'⟩ := hw
  let nodes : ℕ → ZFSet.{u} := fun n => natSet (Encodable.encode (initialSegment f n))
  have hc : ∀ n, Rel ZFSet.omega r (nodes (n+1)) (nodes n) := by
    intro n
    refine ⟨(mem_omega _).mpr ⟨_,rfl⟩,(hr _ _).mpr ?_⟩
    refine ⟨⟨by simp,?_⟩,⟨by simp,?_⟩,f n,?_⟩
    · simpa only [decodeNode_encode] using
        (show t.accepts O v (initialSegment f (n+1)) from (t.branch_iff O v f).mpr hf' (n+1))
    · simpa only [decodeNode_encode] using
        (show t.accepts O v (initialSegment f n) from (t.branch_iff O v f).mpr hf' n)
    · simp only [decodeNode_encode,prefix_succ]
  exact (wellFounded_iff_isEmpty_descending_chain.mp hf).false ⟨nodes,hc⟩

theorem sourceT_merge_witness (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (t : Test) (A R : Oracle) (hA : A ∈ reals M) (hR : R ∈ reals M) (v : ℕ)
    (hw : ∃ H : Oracle, ∃ f : ℕ → ℕ, ∀ n, t.eval (parameters A R H) f (Nat.pair v n)) :
    ∃ H ∈ reals M, ∃ f : ℕ → ℕ, ∀ n, t.eval (parameters A R H) f (Nat.pair v n) := by
  let C := sourceContext M hM hT
  let O := parameters A R (fun _ => false)
  have hO : ∀ i, O i ∈ reals M := by
    intro i
    rcases i with _|_|i
    · exact hA
    · exact hR
    · exact zero_real_mem C
  let B : Oracle := fun n => decide (t.mergeReal.edgePredicate O v (left n) (right n))
  have hB : B ∈ reals M := arithmetic_comprehension C (t.mergeReal.edge_arith v) O hO B
    (fun n => by simp [B])
  let r := relationSet.{u} B
  have hr : ∀ n m, ZFSet.pair (natSet n) (natSet m) ∈ r ↔ t.mergeReal.edgePredicate O v n m := by
    intro n m
    simp [r,relationSet_pair,B,left,right]
  have hwf : ¬ WellFounded (Rel ZFSet.omega r) :=
    t.mergeReal.illFounded_edges O v r hr ((t.exists_mergeReal A R v).mp hw)
  obtain ⟨c,G,hG,hGc,hc⟩ := sourceT_natural_descent_real M hM hT
    (relationSet_mem C hB) (relationSet_on B) hwf
  have hGcM : G ∈ reals M := by simpa only [modelReals_eq] using hG
  have he : ∀ n, t.mergeReal.edgePredicate O v (c (n+1)) (c n) := fun n => (hr _ _).mp (hc n)
  refine ⟨Test.realPart (unionRead c),union_real_mem C G hGcM c hGc,Test.witnessPart (unionRead c),?_⟩
  intro n
  exact (t.mergeReal_eval A R (unionRead c) (Nat.pair v n)).mp (t.mergeReal.eval_of_descent O v c he n)

theorem sourceT_piOneOne_matrix_oai (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {Q : Predicate} (hQ : Arith Q) (A R : Oracle) (hA : A ∈ reals M) (hR : R ∈ reals M) (v : ℕ) :
    (∀ H ∈ reals M, Q (parameters A R H) v) ↔ ∀ H : Oracle, Q (parameters A R H) v := by
  constructor
  · intro h H
    by_contra hnot
    obtain ⟨t,ht⟩ := (arithmetic_tests hQ).2
    obtain ⟨f,hf⟩ := (ht (parameters A R H) v).mp hnot
    obtain ⟨K,hKM,g,hg⟩ := sourceT_merge_witness M hM hT t A R hA hR v ⟨H,f,hf⟩
    exact ((ht (parameters A R K) v).mpr ⟨g,hg⟩) (h K hKM)
  · exact fun h H _ => h H

end
end TuringRigidity.ArithmeticTree

end OAI
end

theorem solution.{u} : type_of% @OAI.TuringRigidity.ArithmeticTree.sourceT_piOneOne_matrix_oai.{u} := @OAI.TuringRigidity.ArithmeticTree.sourceT_piOneOne_matrix_oai.{u}

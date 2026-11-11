-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:59:27.49071+00:00
-- url     : https://prove2.me/submissions/3dc16053-8803-4ca4-b48c-3aea8b0143db

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K037
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_draw_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_nextTable_pack_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake

namespace WordList

lemma cons_ne_nil (w ws : List Bool) : cons w ws≠[] := List.cons_ne_nil _ _

end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations
namespace WordList
lemma length_encode_append (xs ys : List (List Bool)) :
    (encode (xs++ys)).length=(encode xs).length+(encode ys).length := by
  induction xs with
  | nil => simp only [List.nil_append,encode,List.length_nil,Nat.zero_add]
  | cons x xs ih => simp only [List.cons_append,encode,length_cons,ih]; omega
lemma length_encode_drop (xs : List (List Bool)) (n : ℕ) :
    (encode (xs.drop n)).length ≤ (encode xs).length := by
  have h := length_encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  omega
namespace Fold

lemma length_pack (ws ctx a : List Bool) : (pack ws ctx a).length=2*ws.length+2*ctx.length+a.length+2 := by
  simp only [pack,pairBits_length]; omega
lemma step_nil (f : List Bool → List Bool) (ctx a : List Bool) :
    step f (pack (encode []) ctx a)=pack (encode []) ctx a := by
  simp only [step,items_pack,encode,ite_true, if_true]
lemma step_cons (f : List Bool → List Bool) (ctx a w : List Bool) (ws : List (List Bool)) :
    step f (pack (encode (w::ws)) ctx a)=pack (encode ws) ctx (operation f ctx a w) := by
  simp only [step,items_pack,encode,cons_ne_nil,ite_false, if_false,context_pack,head_cons,tail_cons,accum_pack,operation]
lemma iterate_pack (f : List Bool → List Bool) (ctx a : List Bool) (ws : List (List Bool)) (n : ℕ) :
    (step f)^[n] (pack (encode ws) ctx a)=
      pack (encode (ws.drop n)) ctx ((ws.take n).foldl (operation f ctx) a) := by
  induction n generalizing ws a with
  | zero => simp only [Function.iterate_zero_apply,List.drop_zero,List.take_zero,List.foldl_nil]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases ws with
    | nil =>
      rw [step_nil,Function.iterate_fixed (step_nil f ctx a)]
      rfl
    | cons w ws =>
      rw [step_cons,ih]
      simp only [List.drop_succ_cons,List.take_succ_cons,List.foldl_cons]

lemma run_encode (f : List Bool → List Bool) (R : Polynomial ℕ) (ctx a : List Bool)
    (ws : List (List Bool)) (B : ℕ)
    (hB : ∀ n,((ws.take n).foldl (operation f ctx) a).length ≤ B)
    (hR : 2*(encode ws).length+2*ctx.length+B+2 ≤ R.eval (pack (encode ws) ctx a).length) :
    run f R (pack (encode ws) ctx a)=ws.foldl (operation f ctx) a := by
  have he := BoundedIteration.polynomialRun_eq (step f) Polynomial.X R (pack (encode ws) ctx a) (by
    intro j _
    rw [iterate_pack,length_pack]
    have hd := length_encode_drop ws j
    have hb := hB j
    omega)
  simp only [run,Function.comp_apply,he,Polynomial.eval_X,iterate_pack,accum_pack]
  rw [List.take_of_length_le]
  have hw := length_le_encode ws
  rw [length_pack]
  omega
end Fold
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace WordList
lemma encode_le_bound (ws : List (List Bool)) (B : ℕ) (hB : ∀ w∈ws,w.length ≤ B) :
    (encode ws).length ≤ ws.length*(2*B+2) := by
  induction ws with
  | nil => simp only [encode,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons w ws ih =>
    have hw := hB w (List.mem_cons_self ..)
    have ht := ih (fun x hx=>hB x (List.mem_cons_of_mem _ hx))
    simp only [encode,length_cons,List.length_cons]
    nlinarith
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma copies_encode (n : ℕ) (w : List Bool) :
    RepeatedAppend.copies n (encode [w])=encode (List.replicate n w) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RepeatedAppend.copies,ih,←encode_append,←List.replicate_succ']

lemma repeatWords_pair (u w : List Bool) : repeatWords (pairBits (u,w))=
    encode (List.replicate u.length w) := by
  simp only [repeatWords,extractPrefix_pairBits,discardPrefix_pairBits,copies_encode]
lemma repeatWords_ofFn (n : ℕ) (w : List Bool) : repeatWords (pairBits (List.replicate n true,w))=
    encode (List.ofFn (fun _ : Fin n=>w)) := by
  rw [repeatWords_pair,List.length_replicate,List.ofFn_const]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations
namespace WordList
namespace Count
lemma operation_eq (ctx a w : List Bool) : Fold.operation op ctx a w=true::a := by
  simp only [Fold.operation,op,Function.comp_apply,Fold.accum,discardPrefix_pairBits]
lemma fold_op (ws : List (List Bool)) (a : List Bool) (ctx : List Bool) :
    ws.foldl (Fold.operation op ctx) a=List.replicate ws.length true++a := by
  induction ws generalizing a with
  | nil => simp only [List.foldl_nil,List.length_nil,List.replicate_zero,List.nil_append]
  | cons w ws ih =>
    simp only [List.foldl_cons,operation_eq,ih,List.length_cons]
    rw [←List.singleton_append,←List.append_assoc,←List.replicate_succ',List.replicate_succ]
lemma run_encode (ws : List (List Bool)) : run (encode ws)=List.replicate ws.length true := by
  unfold run
  rw [Fold.run_encode op (4*Polynomial.X+4) [] [] ws (encode ws).length]
  · simp only [fold_op,List.append_nil]
  · intro n
    simp only [fold_op,List.append_nil,List.length_replicate]
    have ht : (ws.take n).length ≤ ws.length := by simp only [List.length_take]; omega
    exact ht.trans (length_le_encode ws)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
end Count
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {E : Type*} {a T : ℕ}
lemma omitted_end (r : Fin a→Fin T→Option E) : omitted r a=r := by
  funext j t
  exact ite_eq_right (Nat.ne_of_lt j.isLt)

attribute [local irreducible] Set.run mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CappedFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.CappedFold
open WordOperations
lemma run_pack (f : List Bool → List Bool) (cap ctx a : List Bool) (ws : List (List Bool))
    (hB : ∀ n, ((ws.take n).foldl (Fold.operation f ctx) a).length ≤ cap.length) :
    run f (pairBits (cap,Fold.pack (encode ws) ctx a))=ws.foldl (Fold.operation f ctx) a := by
  unfold run
  rw [discardPrefix_pairBits,Fold.items_pack,Count.run_encode,BoundedIteration.run_eq]
  · simp only [List.length_replicate,Fold.iterate_pack,Fold.accum_pack,List.take_length]
  · intro j _
    rw [Fold.iterate_pack,Fold.length_pack,RepeatedAppend.length_copies,pairBits_length,Fold.length_pack]
    dsimp only at *
    have hws:=length_encode_drop ws j
    have hb:=hB j
    omega

lemma fold_encode {S A : Type*} (encS : S → List Bool) (encA : A → List Bool)
    (g : S → A → S) (f : List Bool → List Bool) (ctx : List Bool)
    (hf : ∀ s a,f (pairBits (ctx,pairBits (encA a,encS s)))=encS (g s a))
    (s : S) (xs : List A) :
    (xs.map encA).foldl (Fold.operation f ctx) (encS s)=encS (xs.foldl g s) := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>
    simp only [List.map_cons,List.foldl_cons,Fold.operation,hf]
    exact ih (g s a)
lemma run_typed {S A : Type*} (encS : S → List Bool) (encA : A → List Bool)
    (g : S → A → S) (f : List Bool → List Bool) (ctx cap : List Bool)
    (hf : ∀ s a,f (pairBits (ctx,pairBits (encA a,encS s)))=encS (g s a))
    (s : S) (xs : List A) (hB : ∀ n,(encS ((xs.take n).foldl g s)).length ≤ cap.length) :
    run f (pairBits (cap,Fold.pack (encode (xs.map encA)) ctx (encS s)))=encS (xs.foldl g s) := by
  rw [run_pack]
  · exact fold_encode encS encA g f ctx hf s xs
  · intro n
    rw [←List.map_take,fold_encode encS encA g f ctx hf]
    exact hB n
end MetricKMedianRecovery.BitMachine.WordList.CappedFold

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
attribute [local irreducible] advance choices
lemma step_pack (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part) (s : Categorical.GreedyState (Fin q) a T)
    (seed : Categorical.OracleSeed (Fin q) a T L) :
    step g (pairBits (stepContext ctx part T,pairBits (oracleBits seed,stateBits s)))=
      stateBits (Categorical.Selected.greedyStep part (rule part hp) (fun S=>(G S:ℝ)) s seed) := by
  unfold step
  have hc : value (field 0 (Fold.accum (pairBits (stepContext ctx part T,pairBits (oracleBits seed,stateBits s)))))=s.1 := by
    simp only [Fold.accum,discardPrefix_pairBits,stateBits,
      field_encode,List.getElem?_cons_zero,Option.getD_some,value_bits]
  have hT : (field 2 (Find.context (pairBits (stepContext ctx part T,pairBits (oracleBits seed,stateBits s))))).length=T := by
    simp only [Find.context,extractPrefix_pairBits,stepContext,field_encode,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,List.length_replicate]
  rw [hc,hT]
  by_cases ht : s.1<T
  · rw [ite_eq_left ht,nextTable_pack_s238 g ctx G hg part hp s ht]
    simp only [Categorical.Selected.greedyStep,dite_eq_left ht,stateBits]
  · simp only [ite_eq_right ht,Categorical.Selected.greedyStep,dite_eq_right ht,Fold.accum,discardPrefix_pairBits]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
lemma member_length {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) : w.length≤(encode ws).length := by
  induction ws with
  | nil=>exact False.elim (List.not_mem_nil hw)
  | cons v vs ih=>
    rw [encode,length_cons]
    rcases List.mem_cons.mp hw with rfl|hw
    · omega
    · have h:=ih hw
      omega
end MetricKMedianRecovery.BitMachine.WordList

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
lemma optionBits_length (o : Option (Fin q)) : (optionBits elemBits o).length≤2*q+2 := by
  cases o with
  | none=>simp [optionBits,encode]
  | some e=>
    have he := (Indices.bits_length_le e.val).trans (Nat.le_of_lt e.isLt)
    simpa only [optionBits,Option.toList_some,List.map_cons,List.map_nil,encode,length_cons,List.length_nil,elemBits,Nat.add_zero] using
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 he) 2
lemma tableBits_length (r : Fin a→Fin T→Option (Fin q)) :
    (tableBits elemBits r).length≤a*(2*(T*(4*q+6))+2) := by
  unfold tableBits
  apply (encode_le_bound _ (T*(4*q+6)) ?_).trans
  · simp only [List.length_ofFn,Nat.le_refl]
  · intro w hw
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hw
    have h:=encode_le_bound (List.ofFn (fun t=>optionBits elemBits (r j t))) (2*q+2) (by
      intro w hw
      obtain ⟨t,rfl⟩:=List.mem_ofFn.mp hw
      exact optionBits_length (r j t))
    simp only [List.length_ofFn] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
lemma stateBits_length (s : Categorical.GreedyState (Fin q) a T) (ht : s.1≤T) :
    (stateBits s).length≤2*T+4+2*(a*(2*(T*(4*q+6))+2)) := by
  have hc := (Indices.bits_length_le s.1).trans ht
  have hb := tableBits_length s.2
  simp only [stateBits,encode,length_cons,List.length_nil]
  omega
lemma stateBits_length_bound (s : Categorical.GreedyState (Fin q) a T) (ht : s.1≤T)
    (N : ℕ) (hq : q≤N) (ha : a≤N) (hT : T≤N) : (stateBits s).length ≤ runCapPoly.eval N := by
  have hs := stateBits_length s ht
  have hb := Nat.mul_le_mul ha (Nat.add_le_add_right (Nat.mul_le_mul_left 2
    (Nat.mul_le_mul hT (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hq) 6))) 2)
  simp only [runCapPoly,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith [sq_nonneg (N:ℤ)]
lemma step_clock_le (part : Fin q→Fin a) (hp : Function.Surjective part) (G : Finset (Fin q)→ℚ)
    (s : Categorical.GreedyState (Fin q) a T) (ht : s.1≤T) (seed : Categorical.OracleSeed (Fin q) a T L) :
    (Categorical.Selected.greedyStep part (rule part hp) (fun S=>(G S:ℝ)) s seed).1≤T := by
  unfold Categorical.Selected.greedyStep
  split_ifs with h
  · exact Nat.succ_le_of_lt h
  · exact ht
lemma fold_clock_le (part : Fin q→Fin a) (hp : Function.Surjective part) (G : Finset (Fin q)→ℚ)
    (s : Categorical.GreedyState (Fin q) a T) (ht : s.1≤T) (seeds : List (Categorical.OracleSeed (Fin q) a T L)) :
    (seeds.foldl (Categorical.Selected.greedyStep part (rule part hp) (fun S=>(G S:ℝ))) s).1≤T := by
  induction seeds generalizing s with
  | nil=>exact ht
  | cons b bs ih=>exact ih _ (step_clock_le part hp G s ht b)
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.FiniteSampling
lemma adaptiveRun_list {S Ω : Type*} (f : S→Ω→S) (n : ℕ) (s : S) (seed : Fin n→Ω) :
    adaptiveRun f n s seed=(List.ofFn seed).foldl f s := by
  induction n generalizing s with
  | zero=>rfl
  | succ n ih=>simpa only [adaptiveRun,List.ofFn_succ,List.foldl_cons,Fin.tail_def] using ih (f s (seed 0)) (Fin.tail seed)
end MetricKMedianRecovery.FiniteSampling
namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
lemma initial_pack (ctx : List Bool) (part : Fin q→Fin a) (seeds : List (Categorical.OracleSeed (Fin q) a T L)) :
    initial (runPack ctx part T seeds)=stateBits (Categorical.initialState (Fin q) a T) := by
  simp only [initial,runPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,repeatWords_ofFn]
  rfl
lemma context_pack (ctx : List Bool) (part : Fin q→Fin a) (seeds : List (Categorical.OracleSeed (Fin q) a T L)) :
    context (runPack ctx part T seeds)=stepContext ctx part T := by
  simp only [context,runPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,stepContext]
lemma runPack_dimensions (ctx : List Bool) (part : Fin q→Fin a) (seeds : List (Categorical.OracleSeed (Fin q) a T L)) :
    q≤(runPack ctx part T seeds).length ∧ a≤(runPack ctx part T seeds).length ∧ T≤(runPack ctx part T seeds).length := by
  have hq : q≤(partBits part).length := by
    simpa only [partBits,List.length_ofFn] using length_le_encode (List.ofFn (fun e=>(part e).val.bits))
  have hp : (partBits part).length≤(runPack ctx part T seeds).length := member_length (by simp)
  have ha : (List.replicate a true).length≤(runPack ctx part T seeds).length := member_length (by simp)
  have hT : (List.replicate T true).length≤(runPack ctx part T seeds).length := member_length (by simp)
  exact ⟨hq.trans hp,by simpa only [List.length_replicate] using ha,by simpa only [List.length_replicate] using hT⟩
lemma run_pack (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part) (seeds : List (Categorical.OracleSeed (Fin q) a T L)) :
    run g (runPack ctx part T seeds)=stateBits (seeds.foldl
      (Categorical.Selected.greedyStep part (rule part hp) (fun S=>(G S:ℝ))) (Categorical.initialState (Fin q) a T)) := by
  unfold run
  rw [initial_pack,context_pack]
  have hf : field 4 (runPack ctx part T seeds)=encode (seeds.map oracleBits) := by
    simp only [runPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hf]
  apply CappedFold.run_typed stateBits oracleBits _ _ _ _ (step_pack g ctx G hg part hp)
  intro n
  rw [runCap.word_length]
  obtain ⟨hq,ha,hT⟩:=runPack_dimensions ctx part seeds
  exact stateBits_length_bound _ (fold_clock_le part hp G _ (Nat.zero_le _) _) _ hq ha hT
lemma run_ofFn (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part) (seed : Fin T→Categorical.OracleSeed (Fin q) a T L) :
    run g (runPack ctx part T (List.ofFn seed))=stateBits
      (Categorical.Selected.greedyRun part (rule part hp) (fun S=>(G S:ℝ)) seed) := by
  rw [run_pack g ctx G hg part hp,Categorical.Selected.greedyRun,FiniteSampling.adaptiveRun_list]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
lemma output_pack_s238_oai (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) :
    output g (outputPack ctx part seed)=encode ((drawn
      (Categorical.Selected.greedyRun part (rule part hp) (fun S=>(G S:ℝ)) seed.1).2 seed.2).map elemBits) := by
  unfold output outputPack
  rw [extractPrefix_pairBits,discardPrefix_pairBits,run_ofFn g ctx G hg part hp]
  simp only [stateBits,runPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,UnaryResources.lengthBits_eq,List.length_replicate]
  simpa only [drawPack,omitted_end] using draw_pack_s238 elemBits
    (Categorical.Selected.greedyRun part (rule part hp) (fun S=>(G S:ℝ)) seed.1).2 seed.2 a
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238_oai

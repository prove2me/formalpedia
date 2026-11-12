-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.loopInput_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:10:58.082008+00:00
-- url     : https://prove2.me/submissions/3ebe522f-b181-4f03-b682-cd8b0d3c4364

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitialQuery_count_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitialQuery_history_pack_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MulComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

lemma decode_encode (x : ℚ) : decode (encode x)=x := by
  simp only [decode,numerator,denominator,encode,pairBits,extractPrefix_pair,discardPrefix_pair,
    Signed.encode_decode,value_bits,Rat.mkRat_self]

end BinaryRational
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
namespace UnaryResources
lemma copies_replicate (a b : ℕ) (v : Bool) :
    RepeatedAppend.copies a (List.replicate b v)=List.replicate (a*b) v := by
  induction a with
  | zero => simp only [RepeatedAppend.copies,Nat.zero_mul,List.replicate_zero]
  | succ a ih => rw [RepeatedAppend.copies,ih,←List.replicate_add]; congr 1; ring

end UnaryResources
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DyadicGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.DyadicGrid
lemma point_double (a b : ℚ) (i d : ℕ) (hd : d≠0) : point a b (2*i) (2*d)=point a b i d := by
  have hz : (d:ℚ)≠0 := by exact_mod_cast hd
  unfold point
  push_cast
  field_simp
lemma point_mid (a b : ℚ) (i j d : ℕ) (hd : d≠0) :
    point a b (i+j) (2*d)=(point a b i d+point a b j d)/2 := by
  have hz : (d:ℚ)≠0 := by exact_mod_cast hd
  unfold point
  push_cast
  field_simp
  ring
lemma advance_interval (count : ℚ→ℕ) (k : ℕ) (a b : ℚ) (g : State) (hg : g.2.2≠0) :
    interval a b (advance count k a b g)=PriceBisection.refine count k (interval a b g) := by
  rcases g with ⟨i,j,d⟩
  simp only [advance,interval,PriceBisection.refine,point_mid a b i j d hg]
  split_ifs with h <;> simp only [point_mid a b i j d hg,point_double a b _ d hg,h,ite_true, if_true,ite_false, if_false]
lemma advance_bounds (count : ℚ→ℕ) (k : ℕ) (a b : ℚ) (g : State) (hg : g.1≤g.2.2 ∧ g.2.1≤g.2.2) :
    (advance count k a b g).1≤2*g.2.2 ∧ (advance count k a b g).2.1≤2*g.2.2 ∧
      (advance count k a b g).2.2=2*g.2.2 := by
  unfold advance
  split_ifs <;> dsimp <;> omega
lemma iterate_bounds (count : ℚ→ℕ) (k : ℕ) (a b : ℚ) (n : ℕ) :
    let g := (advance count k a b)^[n] start
    g.1≤2^n ∧ g.2.1≤2^n ∧ g.2.2=2^n := by
  induction n with
  | zero=>simp only [Function.iterate_zero_apply,start,pow_zero,Nat.zero_le,Nat.le_refl,and_self]
  | succ n ih=>
    have hh:=advance_bounds count k a b ((advance count k a b)^[n] start) ⟨by omega,by omega⟩
    rw [Function.iterate_succ_apply']
    simp only [pow_succ']
    omega
lemma search_iterate (count : ℚ→ℕ) (k n : ℕ) (I : ℚ×ℚ) :
    PriceBisection.search count k n I=(PriceBisection.refine count k)^[n] I := by
  induction n generalizing I with
  | zero=>rfl
  | succ n ih=>rw [PriceBisection.search,ih,Function.iterate_succ_apply]
lemma iterate_interval (count : ℚ→ℕ) (k : ℕ) (a b : ℚ) (n : ℕ) :
    interval a b ((advance count k a b)^[n] start)=PriceBisection.search count k n (a,b) := by
  rw [search_iterate]
  induction n with
  | zero=>simp only [Function.iterate_zero_apply,interval,start,point,Nat.cast_zero,Nat.cast_one,mul_zero,add_zero,mul_one,div_one,add_sub_cancel]
  | succ n ih=>
    have hd : ((advance count k a b)^[n] start).2.2≠0 := by
      rw [(iterate_bounds count k a b n).2.2]
      positivity
    rw [Function.iterate_succ_apply',advance_interval count k a b _ hd,ih,Function.iterate_succ_apply']
end MetricKMedianRecovery.DyadicGrid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_GridMachine
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGrid
open WordOperations WordList BinaryArithmetic DyadicGrid
open BinaryOpeningPayment (field field_computes field_encode)
lemma pointWords_pack (ctx : List Bool) (i d : ℕ) :
    pointWords (pairBits (ctx,pairBits (i.bits,d.bits)))=BinaryRational.encode
      (point (BinaryRational.decode (field 2 ctx)) (BinaryRational.decode (field 3 ctx)) i d) := by
  simp only [pointWords,cf,num,den,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,point]
lemma step_pack (query : List Bool→List Bool) (ctx : List Bool) (g : State) :
    step query (stateBits ctx g)=stateBits ctx (advance (count query ctx) (boundK ctx) (lower ctx) (upper ctx) g) := by
  rcases g with ⟨i,j,d⟩
  simp only [step,chooseLeft,queryInput,midpoint,summed,doubled,cf,gf,stateBits,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,value_bits,pointWords_pack,advance,count,boundK,lower,upper,decide_eq_true_eq]
  split_ifs with h <;> simp [upLeft,upRight,summed,doubled,gf,Function.comp_apply,
    discardPrefix_pairBits,field_encode,value_bits,h]
lemma iterate_pack (query : List Bool→List Bool) (ctx : List Bool) (n : ℕ) :
    (step query)^[n] (stateBits ctx start)=stateBits ctx
      ((advance (count query ctx) (boundK ctx) (lower ctx) (upper ctx))^[n] start) := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [Function.iterate_succ_apply',ih,step_pack,Function.iterate_succ_apply']
lemma bits_of_le_pow {i n : ℕ} (hi : i≤2^n) : i.bits.length≤n+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hp : 0<2^n := by positivity
  rw [pow_succ]
  omega
lemma iterate_length (query : List Bool→List Bool) (ctx : List Bool) (n : ℕ) :
    ((step query)^[n] (stateBits ctx start)).length≤2*ctx.length+6*n+13 := by
  rw [iterate_pack]
  obtain ⟨hl,hu,hd⟩:=iterate_bounds (count query ctx) (boundK ctx) (lower ctx) (upper ctx) n
  have h1:=bits_of_le_pow hl
  have h2:=bits_of_le_pow hu
  have h3:=bits_of_le_pow hd.le
  simp only [stateBits,pairBits_length,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil]
  omega
lemma stateRun_pack (query : List Bool→List Bool) (fuel ctx : List Bool) :
    stateRun query (pairBits (fuel,ctx))=(step query)^[fuel.length] (stateBits ctx start) := by
  simp only [stateRun,Function.comp_apply,runInput,initial,extractPrefix_pairBits,discardPrefix_pairBits]
  apply BoundedIteration.run_eq
  intro j hj
  have hh:=iterate_length query ctx j
  rw [capacity.word_length]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,pairBits_length]
  omega
lemma finish_pack (ctx : List Bool) (g : State) : finish (stateBits ctx g)=
    pairBits (BinaryRational.encode (interval (lower ctx) (upper ctx) g).1,
      BinaryRational.encode (interval (lower ctx) (upper ctx) g).2) := by
  rcases g with ⟨i,j,d⟩
  simp only [finish,endpoint,gf,Function.comp_apply,stateBits,extractPrefix_pairBits,discardPrefix_pairBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,pointWords_pack,interval,lower,upper]
lemma run_pack (query : List Bool→List Bool) (fuel ctx : List Bool) :
    run query (pairBits (fuel,ctx))=
      let I:=PriceBisection.search (count query ctx) (boundK ctx) fuel.length (lower ctx,upper ctx)
      pairBits (BinaryRational.encode I.1,BinaryRational.encode I.2) := by
  simp only [run,Function.comp_apply,stateRun_pack,iterate_pack,finish_pack,iterate_interval]
end MetricKMedianRecovery.BitMachine.BinaryGrid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_BisectionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBisection
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
lemma clog_two_eq_size_pred (n : ℕ) : Nat.clog 2 n=Nat.size (n-1) := by
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.clog_le_iff_le_pow (by decide : 1<2),Nat.size_le]
  have hp : 0<2^k := by positivity
  omega
lemma logWord_eq (x : List Bool) : logWord x=List.replicate (Nat.clog 2 (value x)) true := by
  unfold logWord predWords
  rw [show [true]=List.replicate 1 true from rfl,UnaryResources.copies_replicate,Nat.mul_one,
    Nat.size_eq_bits_len,clog_two_eq_size_pred]
lemma fuel_pack (N : ℕ) (ctx : List Bool) (k : ℕ) (a b : ℚ) :
    fuel (pack N ctx k a b)=List.replicate (PriceBisection.iterations a b N) true := by
  simp only [fuel,pack,widthCeil,width,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryRational.decode_encode,logWord_eq,value_bits,←List.replicate_add,PriceBisection.iterations]
lemma context_pack (N : ℕ) (ctx : List Bool) (k : ℕ) (a b : ℚ) :
    context (pack N ctx k a b)=encode [ctx,k.bits,BinaryRational.encode a,BinaryRational.encode b] := by
  simp only [context,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma run_pack (query : List Bool→List Bool) (N : ℕ) (ctx : List Bool) (k : ℕ) (a b : ℚ) :
    run query (pack N ctx k a b)=
      let f:=fun s=>value (query (pairBits (ctx,BinaryRational.encode s)))
      let I:=PriceBisection.search f k (PriceBisection.iterations a b N) (a,b)
      pairBits (BinaryRational.encode I.1,BinaryRational.encode I.2) := by
  have hc : BinaryGrid.count query (encode [ctx,k.bits,BinaryRational.encode a,BinaryRational.encode b])=
      (fun s=>value (query (pairBits (ctx,BinaryRational.encode s)))) := by
    funext s
    simp only [BinaryGrid.count,field_encode,List.getElem?_cons_zero,Option.getD_some]
  simp only [run,Function.comp_apply,input,fuel_pack,context_pack,BinaryGrid.run_pack,List.length_replicate,
    hc,BinaryGrid.boundK,BinaryGrid.lower,BinaryGrid.upper,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,BinaryRational.decode_encode]
end MetricKMedianRecovery.BitMachine.BinaryBisection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StartResources
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialQuery
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
attribute [local irreducible] BinaryFiniteMachine.continuation

lemma search_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v z lam a b : ℚ) (total precision k : ℕ) :
    BinaryBisection.run count (BinaryBisection.pack precision
      (ctx (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v z lam) total) k a b)=
      let I:=PriceBisection.search (fun t=>initialCount loc distance F v t total) k
        (PriceBisection.iterations a b precision) (a,b)
      pairBits (BinaryRational.encode I.1,BinaryRational.encode I.2) := by
  rw [BinaryBisection.run_pack]
  simp only [count_pack_s238r,value_bits]
end MetricKMedianRecovery.BitMachine.BinaryInitialQuery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialPack
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitial
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outputBits outcomeBits)
attribute [local irreducible] BinaryInitialQuery.count BinaryInitialQuery.history BinaryBisection.run
variable {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v lo M : ℚ) (N precision total k : ℕ)
local notation "xx" => pack distance loc F v lo M N precision total k
local notation "bb" => BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0
local notation "qq" => BinaryInitialQuery.ctx bb total
local notation "II" => PriceBisection.search (fun lam=>initialCount loc distance F v lam total) k
    (PriceBisection.iterations lo (8*(d:ℚ)*M) precision) (lo,8*(d:ℚ)*M)
lemma high_pack : high xx=BinaryRational.encode (8*(d:ℚ)*M) := by
  simp only [high,pack,BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,List.length_replicate,BinaryRational.decode_encode]
lemma far_pack : far xx=BinaryRational.encode (20*N*M) := by
  simp only [far,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,List.length_replicate,BinaryRational.decode_encode]
lemma ctx_pack : ctx xx=qq := by
  simp only [ctx,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryInitialQuery.ctx]
lemma bracketInput_pack : bracketInput xx=BinaryBisection.pack precision qq k lo (8*(d:ℚ)*M) := by
  unfold bracketInput
  rw [ctx_pack,high_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryBisection.pack]
lemma bracket_pack : bracket xx=pairBits (BinaryRational.encode II.1,BinaryRational.encode II.2) := by
  unfold bracket
  rw [bracketInput_pack,BinaryInitialQuery.search_pack]
lemma prices_pack : lower xx=BinaryRational.encode II.1 ∧ upper xx=BinaryRational.encode II.2 := by
  simp only [lower,upper,bracket_pack,extractPrefix_pairBits,discardPrefix_pairBits,and_self]
lemma inputs_pack : lowerInput xx=pairBits (qq,BinaryRational.encode II.1) ∧
    upperInput xx=pairBits (qq,BinaryRational.encode II.2) := by
  obtain ⟨hl,hu⟩:=prices_pack distance loc F v lo M N precision total k
  simp only [lowerInput,upperInput,ctx_pack,hl,hu,and_self]
lemma histories_pack : lowerHistory xx=historyBits (initialHistory loc distance F v II.1 total) ∧
    upperHistory xx=historyBits (initialHistory loc distance F v II.2 total) := by
  obtain ⟨hl,hu⟩:=inputs_pack distance loc F v lo M N precision total k
  simp only [lowerHistory,upperHistory,hl,hu,BinaryInitialQuery.history_pack_s238r,and_self]
lemma initialState_pack : initialState xx=stateBits (initial II.1 II.2 (initialHistory loc distance F v II.2 total)
    (initialHistory loc distance F v II.1 total)) := by
  obtain ⟨hl,hu⟩:=prices_pack distance loc F v lo M N precision total k
  obtain ⟨hL,hU⟩:=histories_pack distance loc F v lo M N precision total k
  simp only [initialState,hl,hu,hL,hU,stateBits,CanonicalCoupledMerge.initial,BinaryCorrection.encode,
    setBits,BinaryLabel.orderedSort,Finset.sort_empty,labels,List.map_nil,historyBits,encode]
lemma loopInput_pack_s238r_oai : loopInput xx=BinaryCoupledLoop.pack bb (20*N*M) precision k
    ⟨0,total,.inr (initial II.1 II.2 (initialHistory loc distance F v II.2 total) (initialHistory loc distance F v II.1 total))⟩ := by
  unfold loopInput initialOutcome
  rw [far_pack,initialState_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryCoupledLoop.pack,outcomeBits,List.replicate_zero]
end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.loopInput_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.loopInput_pack_s238r_oai

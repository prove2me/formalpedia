-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:13:22.75947+00:00
-- url     : https://prove2.me/submissions/d841d3a0-9973-4935-b40b-5526d7a3eec7

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_union_list_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLengthQuery_chosen_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLengthQuery_count_pack_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
lemma replaceOpen_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q R : Finset (Label (Fin m))) (v z lam : ℚ) :
    replaceOpen (pairBits (pack distance loc F Q v z lam,setBits R))=pack distance loc F R v z lam := by
  simp only [replaceOpen,extractPrefix_pairBits,discardPrefix_pairBits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_OrientedSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOrientedSearch
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
lemma reversed_pack (query : List Bool→List Bool) (ctx : List Bool) (b s : ℚ) :
    reversed query (pairBits (pairBits (ctx,BinaryRational.encode b),BinaryRational.encode s))=
      query (pairBits (ctx,BinaryRational.encode (b-s))) := by
  simp only [reversed,Function.comp_apply,reversedInput,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode]
lemma reverseInput_pack (N : ℕ) (ctx : List Bool) (k : ℕ) (b : ℚ) :
    reverseInput (BinaryBisection.pack N ctx k 0 b)=
      BinaryBisection.pack N (pairBits (ctx,BinaryRational.encode b)) k 0 b := by
  simp only [reverseInput,reverseContext,BinaryBisection.pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
lemma reflect_pack (b l u : ℚ) : reflect (pairBits (BinaryRational.encode b,
    pairBits (BinaryRational.encode l,BinaryRational.encode u)))=
    pairBits (BinaryRational.encode (b-u),BinaryRational.encode (b-l)) := by
  simp only [reflect,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode]
lemma reverseRun_pack (query : List Bool→List Bool) (N : ℕ) (ctx : List Bool) (k : ℕ) (b : ℚ) :
    reverseRun query (BinaryBisection.pack N ctx k 0 b)=
      let I:=PriceBisection.search (fun s=>value (query (pairBits (ctx,BinaryRational.encode (b-s))))) k
        (PriceBisection.iterations 0 b N) (0,b)
      pairBits (BinaryRational.encode (b-I.2),BinaryRational.encode (b-I.1)) := by
  unfold reverseRun
  rw [reverseInput_pack,BinaryBisection.run_pack]
  simp only [reversed_pack,BinaryBisection.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    reflect_pack]
lemma run_pack (query : List Bool→List Bool) (N : ℕ) (ctx : List Bool) (k : ℕ) (b : ℚ) :
    run query (BinaryBisection.pack N ctx k 0 b)=
      let I:=CanonicalLengthSearch.range (fun s=>value (query (pairBits (ctx,BinaryRational.encode s)))) k N b
      pairBits (BinaryRational.encode I.1,BinaryRational.encode I.2) := by
  unfold run
  rw [reverseRun_pack,BinaryBisection.run_pack]
  simp only [isReversed,BinaryBisection.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    value_bits,decide_eq_true_eq,CanonicalLengthSearch.range]
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryOrientedSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LengthQuery
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLengthSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
lemma finish_pack (N : ℕ) (ctx : List Bool) (k : ℕ) (b l u : ℚ) :
    finish (pairBits (BinaryBisection.pack N ctx k 0 b,pairBits (BinaryRational.encode l,BinaryRational.encode u)))=
    if value (BinaryLengthQuery.count (pairBits (ctx,BinaryRational.encode l)))=k then
      encode [(0:ℕ).bits,BinaryRational.encode l,[],BinaryLengthQuery.chosen (pairBits (ctx,BinaryRational.encode l)),[]]
    else if value (BinaryLengthQuery.count (pairBits (ctx,BinaryRational.encode u)))=k then
      encode [(0:ℕ).bits,BinaryRational.encode u,[],BinaryLengthQuery.chosen (pairBits (ctx,BinaryRational.encode u)),[]]
    else encode [(1:ℕ).bits,BinaryRational.encode l,BinaryRational.encode u,
      BinaryLengthQuery.chosen (pairBits (ctx,BinaryRational.encode l)),BinaryLengthQuery.chosen (pairBits (ctx,BinaryRational.encode u))] := by
  simp only [finish,leftEqual,rightEqual,leftSuccess,rightSuccess,bracket,leftHistory,rightHistory,
    leftInput,rightInput,context,boundK,lower,upper,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryBisection.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,decide_eq_true_eq]
lemma run_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b : ℚ)
    (T U : List (List (Label (Fin m)))) (k N : ℕ) :
    run (BinaryBisection.pack N (BinaryLengthQuery.ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U) k 0 b)=
      resultBits (CanonicalLengthSearch.run F Q (leaf key (parent i))
        (fun s=>FiniteLabelContinuation.continuation loc (rows distance) F v lam q n (insert (leaf key (parent i) s) Q)) T U b k N) := by
  unfold run input
  rw [Function.comp_apply,BinaryOrientedSearch.run_pack]
  simp only [BinaryLengthQuery.count_pack_s238r,value_bits]
  rw [finish_pack]
  simp only [BinaryLengthQuery.count_pack_s238r,value_bits,BinaryLengthQuery.chosen_pack_s238r,CanonicalLengthSearch.run]
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SensitiveMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySensitive
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalLengthView
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
lemma base_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) :
    base (pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J)=
      BinaryFiniteContext.pack distance loc F (Q∪(J.common H).toFinset) v z lam := by
  have hh:=(views_pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J).1
  unfold base opened
  rw [hh]
  simp only [pack,field_encode,List.getElem?_cons_zero,Option.getD_some]
  have hf : field 3 (BinaryFiniteContext.pack distance loc F Q v z lam)=setBits Q := by
    simp only [BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hf,BinaryFiniteContext.union_list_pack_s238r,BinaryFiniteContext.replaceOpen_pack]
lemma context_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) :
    context (pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J)=
      BinaryLengthQuery.ctxBits (BinaryFiniteContext.pack distance loc F (Q∪(J.common H).toFinset) v z lam)
        n (q+1) key J.root b (J.small T U) (J.large T U) := by
  obtain ⟨_,hs,hl,hr⟩:=views_pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J
  unfold context
  rw [base_pack,hs,hl,hr]
  simp only [nextQ,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryLengthQuery.ctxBits,List.replicate_succ]
lemma run_pack_s238r_oai {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q v z lam) n q key b k N H T U J)=
      BinaryLengthSearch.resultBits (CanonicalSensitiveEndpoint.run loc distance F Q v lam b q n k key N H T U J) := by
  let ctx:=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q v z lam
  have hctx:=context_pack distance (fun j=>original (loc j)) (F.image original) Q v z lam n q key b k N H T U J
  have hsmall:=(views_pack ctx n q key b k N H T U J).2.1
  change run (pack ctx n q key b k N H T U J)=_
  unfold run early earlyEqual atZero searchInput
  rw [show context (pack ctx n q key b k N H T U J)=_ from hctx,hsmall]
  have hf5 : field 5 (pack ctx n q key b k N H T U J)=k.bits := by simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have hf6 : field 6 (pack ctx n q key b k N H T U J)=List.replicate N true := by simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have hf4 : field 4 (pack ctx n q key b k N H T U J)=BinaryRational.encode b := by simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hf5,hf6,hf4,BinaryLengthQuery.count_pack_s238r]
  simp only [value_bits,CanonicalLengthSearch.count,CanonicalLengthSearch.chosen,ite_true, if_true,decide_eq_true_eq]
  rw [←BinaryBisection.pack,BinaryLengthSearch.run_pack]
  dsimp only [CanonicalSensitiveEndpoint.run]
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinarySensitive

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack_s238r_oai

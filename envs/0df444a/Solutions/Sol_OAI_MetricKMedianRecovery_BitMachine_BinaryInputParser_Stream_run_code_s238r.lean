-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:38:18.366891+00:00
-- url     : https://prove2.me/submissions/8c100e8d-90ec-48a1-b751-592f826611fd

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L025
import Definitions.Def_Q238L026

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

namespace ReverseMap

lemma next_nil (f : List Bool → List Bool) (d o : List Bool) :
    next f (pack true [] d o)=pack false [] d o := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,data_pack,output_pack]
lemma next_cons (f : List Bool → List Bool) (w ws d o : List Bool) :
    next f (pack true (cons w ws) d o)=pack true ws d (cons (f (pairBits (d,w))) o) := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,cons_ne_nil,ite_false, if_false,
    data_pack,output_pack,tail_cons,head_cons]
lemma loop_exact (f : List Bool → List Bool) (ws : List (List Bool)) (d : List Bool) (os : List (List Bool)) :
    (next f)^[ws.length+1] (pack true (encode ws) d (encode os))=
      pack false [] d (encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse++os)) := by
  induction ws generalizing os with
  | nil => simp only [encode,List.length_nil,Nat.zero_add,Function.iterate_one,next_nil,
      List.map_nil,List.reverse_nil,List.nil_append]
  | cons w ws ih =>
    rw [List.length_cons,Function.iterate_succ_apply,encode,next_cons]
    change (next f)^[ws.length+1] (pack true (encode ws) d (encode (f (pairBits (d,w))::os)))=_
    rw [ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
lemma loop_spec (f : List Bool → List Bool) (ws : List (List Bool)) (d : List Bool) :
    (next f)^[(encode ws).length+1] (pack true (encode ws) d [])=
      pack false [] d (encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse)) := by
  have hl := length_le_encode ws
  have hlen : (encode ws).length+1=((encode ws).length-ws.length)+(ws.length+1) := by omega
  rw [hlen,Function.iterate_add_apply]
  change (next f)^[_] ((next f)^[ws.length+1] (pack true (encode ws) d (encode [])))=_
  rw [loop_exact,List.append_nil]
  apply While.next_fixed
  exact (by decide : (some false:Option Bool)≠some true)

lemma run_encode (f : List Bool → List Bool) (d : List Bool) (ws : List (List Bool)) :
    run f (pairBits (d,encode ws))=encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse) := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits,rank,head_pack,ite_true, if_true,counter_pack,
    loop_spec,output_pack]
end ReverseMap

lemma reverse_encode (ws : List (List Bool)) : reverse (encode ws)=encode ws.reverse := by
  simp only [reverse,ReverseMap.run_encode,discardPrefix_pairBits,List.map_id']

end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed
lemma encode_length (z : ℤ) : (encode z).length=z.natAbs.size+1 := by
  simp only [encode,List.length_cons,Nat.size_eq_bits_len]
end Signed
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational
lemma encode_length (q : ℚ) : (encode q).length=2*(q.num.natAbs.size+1)+1+q.den.size := by
  simp only [encode,pairBits_length,Signed.encode_length,←Nat.size_eq_bits_len]
end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UnaryParser
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryParser
open WordOperations UnaryTake

lemma next_stop (c d : List Bool) : next (pack false c d [])=pack false c d [] := by
  simp only [next,While.next,head_pack,Option.some.injEq,Bool.false_eq_true,ite_false, if_false]
lemma next_false (c d : List Bool) : next (pack true c (false::d) [])=pack false c d [] := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,data_pack,counter_pack,List.head?_cons,
    Option.getD_some,Bool.false_eq_true,ite_false, if_false,List.tail_cons]
lemma next_true (c d : List Bool) : next (pack true c (true::d) [])=pack true (true::c) d [] := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,data_pack,counter_pack,List.head?_cons,
    Option.getD_some,List.tail_cons]
lemma exact_prefix (n : ℕ) (c d : List Bool) :
    next^[n+1] (pack true c (List.replicate n true++false::d) [])=
      pack false (List.replicate n true++c) d [] := by
  induction n generalizing c with
  | zero=>simp only [Nat.zero_add,List.replicate_zero,List.nil_append,Function.iterate_one,next_false]
  | succ n ih=>
    rw [List.replicate_succ,List.cons_append,Function.iterate_succ_apply,next_true,ih]
    rw [show List.replicate n true++true::c=(List.replicate (n+1) true)++c by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]]
    simp only [List.replicate_succ,List.cons_append]
lemma run_code (n : ℕ) (d : List Bool) :
    run (List.replicate n true++false::d)=pairBits (List.replicate n true,d) := by
  dsimp only [run,loop]
  have hl : n+1≤(pack true [] (List.replicate n true++false::d) []).length := by
    simp only [length_pack,List.length_nil,List.length_append,List.length_replicate,List.length_cons]; omega
  rw [show (pack true [] (List.replicate n true++false::d) []).length=
    (pack true [] (List.replicate n true++false::d) []).length-(n+1)+(n+1) by omega]
  rw [Function.iterate_add_apply,exact_prefix,List.append_nil,Function.iterate_fixed (next_stop _ _),
    counter_pack,data_pack]
end MetricKMedianRecovery.BitMachine.UnaryParser

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser
open WordOperations
attribute [local irreducible] UnaryParser.run UnaryTake.takeWords UnaryTake.dropWords
lemma nat_code (n : ℕ) (tail : List Bool) :
    nat (RationalMetricInput.natBits n++tail)=pairBits (n.bits,tail) := by
  simp only [RationalMetricInput.natBits,List.append_assoc,List.cons_append,List.nil_append,nat,
    UnaryParser.run_code,UnaryTake.takeWords,UnaryTake.dropWords,extractPrefix_pairBits,
    discardPrefix_pairBits,List.length_replicate,List.take_left,List.drop_left]
attribute [local irreducible] nat
attribute [local irreducible] numerator denominator
lemma rational_code (r : ℚ) (tail : List Bool) :
    rational (RationalMetricInput.rationalBits r++tail)=pairBits (BinaryRational.encode r,tail) := by
  have hs : decide (r<0)=decide (r.num<0) := by
    apply decide_eq_decide.mpr
    rw [lt_iff_not_ge,lt_iff_not_ge,Rat.num_nonneg]
  simp only [rational,numerator,denominator,RationalMetricInput.rationalBits,List.nil_append,
    List.cons_append,List.append_assoc,List.head?_cons,Option.getD_some,List.tail_cons,nat_code,
    extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.encode,Signed.encode,hs]
end MetricKMedianRecovery.BitMachine.BinaryInputParser

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalStream
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream
open WordOperations
attribute [local irreducible] rational
lemma raw_cons (r : ℚ) (rs : List ℚ) : raw (r::rs)=RationalMetricInput.rationalBits r++raw rs := rfl
lemma raw_length_pos (r : ℚ) : 0<(RationalMetricInput.rationalBits r).length := by
  simp only [RationalMetricInput.rationalBits,List.length_append,List.length_singleton]
  omega
lemma step_nil (acc : List ℚ) : step (pack [] acc)=pack [] acc := by
  unfold step pack
  rw [extractPrefix_pairBits,ite_eq_left (show raw []=[] from rfl)]
lemma step_cons (r : ℚ) (rs acc : List ℚ) : step (pack (r::rs) acc)=pack rs (r::acc) := by
  have hn : raw (r::rs)≠[] := by
    intro he
    have hh:=congrArg List.length he
    have hp:=raw_length_pos r
    simp only [raw_cons,List.length_append,List.length_nil] at hh
    omega
  rw [step,pack,extractPrefix_pairBits,ite_eq_right hn,raw_cons,rational_code,extractPrefix_pairBits,discardPrefix_pairBits,discardPrefix_pairBits]
  rfl
lemma code_length (r : ℚ) : (BinaryRational.encode r).length≤(RationalMetricInput.rationalBits r).length := by
  simp only [BinaryRational.encode_length,RationalMetricInput.rationalBits,RationalMetricInput.natBits,
    List.length_append,List.length_singleton,List.length_replicate,←Nat.size_eq_bits_len]
  omega
lemma codes_length (rs : List ℚ) : (codes rs).length≤3*(raw rs).length := by
  induction rs with
  | nil=>simp only [codes,raw,List.map_nil,List.flatten_nil,WordList.encode,List.length_nil,Nat.mul_zero,Nat.le_refl]
  | cons r rs ih=>
    have hc:=code_length r
    have hp : 2≤(RationalMetricInput.rationalBits r).length := by
      simp only [RationalMetricInput.rationalBits,RationalMetricInput.natBits,List.length_append,List.length_singleton,List.length_replicate]
      omega
    simp only [codes,List.map_cons,WordList.encode,WordList.length_cons,raw_cons,List.length_append] at *
    omega
lemma pack_length (rs acc : List ℚ) : (pack rs acc).length≤3*((raw rs).length+(raw acc).length)+1 := by
  have hc:=codes_length acc
  simp only [pack,pairBits_length]
  omega
lemma iterate_shape (rs acc : List ℚ) (n : ℕ) :
    ∃ rs' acc',step^[n] (pack rs acc)=pack rs' acc' ∧
      (raw rs').length+(raw acc').length=(raw rs).length+(raw acc).length := by
  induction n generalizing rs acc with
  | zero=>exact ⟨rs,acc,rfl,rfl⟩
  | succ n ih=>
    cases rs with
    | nil=>rw [Function.iterate_fixed (step_nil acc)]; exact ⟨[],acc,rfl,rfl⟩
    | cons r rs=>
      rw [Function.iterate_succ_apply,step_cons]
      obtain ⟨rs',acc',he,hl⟩:=ih rs (r::acc)
      refine ⟨rs',acc',he,?_⟩
      simp only [raw_cons,List.length_append] at hl ⊢
      omega
lemma iterate_done (rs acc : List ℚ) (n : ℕ) (hn : rs.length≤n) :
    step^[n] (pack rs acc)=pack [] (rs.reverse++acc) := by
  induction rs generalizing acc n with
  | nil=>rw [Function.iterate_fixed (step_nil acc)]; rfl
  | cons r rs ih=>
    cases n with
    | zero=>simp only [List.length_cons] at hn; omega
    | succ n=>
      rw [Function.iterate_succ_apply,step_cons,ih (r::acc) n (by simp only [List.length_cons] at hn; omega)]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
lemma count_le_raw (rs : List ℚ) : rs.length≤(raw rs).length := by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>have hh:=raw_length_pos r; simp only [List.length_cons,raw_cons,List.length_append]; omega
lemma run_code_s238r_oai (rs : List ℚ) : run (raw rs)=codes rs := by
  unfold run
  change WordList.reverse (discardPrefix (BoundedIteration.polynomialRun step Polynomial.X (3*Polynomial.X+1) (pack rs [])))=_
  rw [BoundedIteration.polynomialRun_eq step Polynomial.X (3*Polynomial.X+1) (pack rs []) ?_]
  · simp only [Polynomial.eval_X]
    rw [iterate_done rs [] (pack rs []).length (by
      have hh:=count_le_raw rs
      simp only [pack,pairBits_length]
      omega),pack,discardPrefix_pairBits,List.append_nil]
    change WordList.reverse (WordList.encode ((rs.reverse).map BinaryRational.encode))=_
    rw [WordList.reverse_encode,List.map_reverse,List.reverse_reverse]
  · intro j _
    obtain ⟨rs',acc',he,hl⟩:=iterate_shape rs [] j
    rw [he]
    have hb:=pack_length rs' acc'
    change (raw rs').length+(raw acc').length=(raw rs).length+0 at hl
    simp only [Nat.add_zero] at hl
    rw [hl] at hb
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    have hh : (raw rs).length≤(pack rs []).length := by simp only [pack,pairBits_length]; omega
    omega
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code_s238r_oai

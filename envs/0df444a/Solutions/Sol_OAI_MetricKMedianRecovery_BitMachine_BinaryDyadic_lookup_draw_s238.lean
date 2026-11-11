-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:00:39.643559+00:00
-- url     : https://prove2.me/submissions/aee80e14-a57a-41b1-871b-09d9fcc2c4dc

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K037
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInverseCDF_find_pack_s238

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
lemma mapWith_encode (f : List Bool → List Bool) (d : List Bool) (ws : List (List Bool)) :
    mapWith f (pairBits (d,encode ws))=encode (ws.map (fun w=>f (pairBits (d,w)))) := by
  simp only [mapWith,Function.comp_apply,ReverseMap.run_encode,reverse_encode,List.reverse_reverse]

end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UniformWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations BinaryArithmetic
lemma uniform_value (b : ℕ) (s : Fin b→Bool) :
    value (List.ofFn s).reverse=(Categorical.uniformBits b s).val := by
  induction b with
  | zero=>rfl
  | succ b ih=>
    rw [List.ofFn_succ,List.reverse_cons,value_append,List.length_reverse,List.length_ofFn,ih]
    simp only [value,Nat.mul_zero,Nat.add_zero]
    cases hs : s 0 <;> simp [Categorical.uniformBits,Equiv.trans_apply,Fin.consEquiv,finTwoEquiv,finProdFinEquiv,hs] <;> rfl
lemma normalizeBig_ofFn (b : ℕ) (s : Fin b→Bool) :
    normalizeBig (List.ofFn s)=(Categorical.uniformBits b s).val.bits := by rw [normalizeBig,normalize_eq_bits,uniform_value]
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_InverseCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInverseCDF
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Dyadic.Canonical

attribute [local irreducible] Take.run UnaryResources.inc
attribute [local irreducible] prefixCounts NaturalArray.sumWords
attribute [local irreducible] total
attribute [local irreducible] searched
lemma run_pack (d : ℕ) (ws : List ℕ) (b : ℕ) (s : Fin b→Bool) :
    run (pack d ws (List.ofFn s))=((rank ws (Categorical.uniformBits b s).val).getD d).bits := by
  simp only [run,searched,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinarySeed.normalizeBig_ofFn,find_pack_s238]
  cases rank ws (Categorical.uniformBits b s).val <;> simp [encodeOption]
end MetricKMedianRecovery.BitMachine.BinaryInverseCDF

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
lemma bits_two_pow (b : ℕ) : (2^b).bits=List.replicate b false++[true] := by
  induction b with
  | zero=>rfl
  | succ b ih=>rw [pow_succ,Nat.mul_comm,Nat.bit0_bits _ (by positivity),ih,List.replicate_succ,List.cons_append]
lemma power_replicate (b : ℕ) : power (List.replicate b true)=(2^b).bits := by
  rw [power,List.length_replicate,bits_two_pow]
lemma scale_replicate (b : ℕ) : scale (List.replicate b true)=(2:ℚ)^b := by
  rw [scale,power_replicate,value_bits,Nat.cast_pow,Nat.cast_ofNat]
lemma count_pack (p : ℚ) (b : ℕ) :
    count (pairBits (BinaryRational.encode ((2:ℚ)^b),BinaryRational.encode p))=(⌊p*(2:ℚ)^b⌋₊).bits := by
  simp only [count,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode]

lemma counts_pack (b d : ℕ) (ps : List ℚ) (raw : List Bool) :
    counts (pack b d ps raw)=NaturalArray.encode (ps.map (fun p=>⌊p*(2:ℚ)^b⌋₊)) := by
  simp only [counts,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    scale_replicate,RationalArray.encode,mapWith_encode,List.map_map,Function.comp_def,count_pack,NaturalArray.encode]
lemma run_pack (b d : ℕ) (ps : List ℚ) (s : Fin b→Bool) :
    run (pack b d ps (List.ofFn s))=
      ((Dyadic.Canonical.rank (ps.map (fun p=>⌊p*(2:ℚ)^b⌋₊)) (Categorical.uniformBits b s).val).getD d).bits := by
  rw [run,prepared,counts_pack]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  exact BinaryInverseCDF.run_pack d _ b s
lemma floor_cast (p : ℚ) : ⌊(p:ℝ)⌋₊=⌊p⌋₊ := by
  rw [←Int.floor_toNat,←Int.floor_toNat,Rat.floor_cast]
lemma rawCount_cast {A : Type*} (p : A→ℚ) (b : ℕ) (a : A) :
    Dyadic.rawCount (fun a=>(p a:ℝ)) b a=⌊p a*(2:ℚ)^b⌋₊ := by
  unfold Dyadic.rawCount
  have he : (2:ℝ)^b*(p a:ℝ)=((p a*(2:ℚ)^b:ℚ):ℝ) := by
    simp only [Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,mul_comm]
  rw [he,floor_cast]
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DyadicLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Dyadic.Canonical
lemma select_rank {A : Type*} (d : A) (ws : List (A×ℕ)) (v : ℕ) :
    select d ws v=((rank (ws.map Prod.snd) v).bind (fun j=>(ws[j]?).map Prod.fst)).getD d := by
  induction ws generalizing v with
  | nil=>rfl
  | cons w ws ih=>
    simp only [List.map_cons,select,rank]
    split_ifs with h
    · rfl
    · rw [ih]
      cases rank (ws.map Prod.snd) (v-w.2) <;>
        simp only [Option.map_none,Option.bind_none,Option.map_some,Option.bind_some,List.getElem?_cons_succ]
lemma select_rank_default {A : Type*} (d : A) (ws : List (A×ℕ)) (v : ℕ) (h : (ws[0]?).map Prod.fst=some d) :
    ((ws[(rank (ws.map Prod.snd) v).getD 0]?).map Prod.fst).getD d=select d ws v := by
  rw [select_rank]
  cases rank (ws.map Prod.snd) v <;> simp only [Option.getD_none,Option.getD_some,Option.bind_none,Option.bind_some,h]
lemma select_rank_map {A B : Type*} (code : A→B) (fallback : B) (d : A) (ws : List (A×ℕ)) (v : ℕ)
    (h : (ws[0]?).map Prod.fst=some d) :
    (((ws[(rank (ws.map Prod.snd) v).getD 0]?).map (fun z=>code z.1)).getD fallback)=code (select d ws v) := by
  have hl (xs : List ℕ) (u j : ℕ) (hh : rank xs u=some j) : j<xs.length := by
    induction xs generalizing u j with
    | nil=>simp [rank] at hh
    | cons x xs ih=>
      simp only [rank] at hh
      split_ifs at hh with hu
      · cases Option.some.inj hh; simp
      · obtain ⟨a,ha,hj⟩:=Option.map_eq_some_iff.mp hh
        rw [←hj]
        have hh2:=ih _ _ ha
        simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hh2
  have he : ∃ t,ws[(rank (ws.map Prod.snd) v).getD 0]?=some t := by
    cases hr : rank (ws.map Prod.snd) v with
    | none=>
      simp only [Option.getD_none]
      obtain ⟨t,ht,_⟩:=Option.map_eq_some_iff.mp h
      exact ⟨t,ht⟩
    | some j=>
      simp only [Option.getD_some]
      exact ⟨ws[j]'(by simpa only [List.length_map] using hl _ _ _ hr),by simp⟩
  obtain ⟨t,ht⟩:=he
  have hh:=select_rank_default d ws v h
  rw [ht,Option.map_some,Option.getD_some] at hh
  rw [ht,Option.map_some,Option.getD_some,←hh]
end MetricKMedianRecovery.Dyadic.Canonical
namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
lemma lookup_draw_s238_oai {A : Type*} (code : A→List Bool) (p : A→ℚ) (d : A) (as : List A)
    (ha : as[0]?=some d) (b : ℕ) (s : Fin b→Bool) :
    Lookup.run (pairBits (run (pack b 0 (as.map p) (List.ofFn s)),encode (as.map code)))=
      code (Dyadic.Canonical.draw (fun a=>(p a:ℝ)) b d as s) := by
  rw [run_pack,Lookup.run_encode]
  have hh:=Dyadic.Canonical.select_rank_map code [] d (as.map (fun a=>(a,⌊p a*(2:ℚ)^b⌋₊)))
    (Categorical.uniformBits b s).val (by simp only [List.getElem?_map,ha,Option.map_some])
  simpa only [List.map_map,Function.comp_def,List.getElem?_map,Option.map_map,
    Dyadic.Canonical.draw,Dyadic.Canonical.list,rawCount_cast] using hh
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238_oai.{u_1}

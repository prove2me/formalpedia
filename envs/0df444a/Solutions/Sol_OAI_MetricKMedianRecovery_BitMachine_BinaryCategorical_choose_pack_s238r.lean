-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choose_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:56:58.831208+00:00
-- url     : https://prove2.me/submissions/fd01cc66-422f-41ae-a228-bd63855bd1ca

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L026
import Definitions.Def_Q238L033
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_bagWords_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_marginal_pack_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RowEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

attribute [local irreducible] WordList.mapWith WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run IntegerArray.sumWords 
open WordOperations BinaryArithmetic
namespace WordList
lemma lookup_ofFn {n : ℕ} (i : Fin n) (f : Fin n → List Bool) :
    Lookup.run (pairBits (i.val.bits,encode (List.ofFn f)))=f i := by
  rw [Lookup.run_encode]
  simp only [List.getElem?_ofFn,i.isLt,dite_eq_left,Option.getD_some]
lemma mapWith_ofFn {n : ℕ} (f : List Bool → List Bool) (d : List Bool) (g : Fin n → List Bool) :
    mapWith f (pairBits (d,encode (List.ofFn g)))=encode (List.ofFn (fun i=>f (pairBits (d,g i)))) := by
  rw [mapWith_encode,List.map_ofFn]
  rfl
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
attribute [local irreducible] WordList.mapWith WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run IntegerArray.sumWords 
open WordOperations BinaryArithmetic
namespace WordList
lemma length_member_le_encode {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) :
    w.length≤(encode ws).length := by
  induction ws with
  | nil => simp only [List.not_mem_nil] at hw
  | cons v vs ih =>
    simp only [List.mem_cons] at hw
    rw [encode,length_cons]
    rcases hw with rfl|hv
    · omega
    · have hh := ih hv
      omega
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalHeight
open scoped BigOperators

lemma Height.mono {q : ℚ} {b c : ℕ} (h : Height q b) (hc : b ≤ c) : Height q c :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by norm_num) hc),h.2.trans (Nat.pow_le_pow_right (by norm_num) hc)⟩

lemma zero (b : ℕ) : Height 0 b := by
  constructor
  · simp
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^b)

lemma of_fraction (p : ℤ) (d b : ℕ) (hd : 0<d) (hp : p.natAbs≤2^b) (hdb : d≤2^b) :
    Height ((p:ℚ)/(d:ℚ)) b := by
  constructor
  · by_cases hz : p=0
    · simp [hz]
    · have hh := Rat.num_dvd p (by exact_mod_cast hd.ne' : (d:ℤ)≠0)
      rw [←Rat.intCast_div_eq_divInt] at hh
      simp only [Int.cast_natCast] at hh
      exact (Nat.le_of_dvd (by omega : 0<p.natAbs) (Int.natAbs_dvd_natAbs.mpr hh)).trans hp
  · have hh := Rat.den_dvd p (d:ℤ)
    rw [←Rat.intCast_div_eq_divInt] at hh
    simp only [Int.cast_natCast] at hh
    exact (Nat.le_of_dvd hd (Int.natCast_dvd_natCast.mp hh)).trans hdb

lemma Height.add {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q+r) (b+c+1) := by
  have hn : (q.num*(r.den:ℤ)+r.num*(q.den:ℤ)).natAbs≤2^(b+c+1) := by
    calc
      _ ≤ q.num.natAbs*r.den+r.num.natAbs*q.den := by
        simpa only [Int.natAbs_mul,Int.natAbs_natCast] using
          Int.natAbs_add_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ))
      _ ≤ 2^b*2^c+2^c*2^b := Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hr.1 hq.2)
      _ = _ := by rw [pow_succ,pow_add]; ring
  have hd : q.den*r.den≤2^(b+c+1) := by
    have hh := Nat.mul_le_mul hq.2 hr.2
    rw [←pow_add] at hh
    exact hh.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have he : q+r=((q.num*(r.den:ℤ)+r.num*(q.den:ℤ):ℤ):ℚ)/(q.den*r.den:ℕ) := by
    nth_rw 1 [←Rat.num_div_den q]
    nth_rw 1 [←Rat.num_div_den r]
    push_cast
    convert div_add_div (q.num:ℚ) (r.num:ℚ) (by exact_mod_cast q.den_nz : (q.den:ℚ)≠0) (by exact_mod_cast r.den_nz : (r.den:ℚ)≠0) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [he]
  exact of_fraction _ _ _ (Nat.mul_pos q.den_pos r.den_pos) hn hd

end MetricKMedianRecovery.RationalHeight

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Iterate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalHeight
lemma list_sum (xs : List ℚ) (b : ℕ) (hx : ∀ q∈xs,Height q b) :
    Height xs.sum (xs.length*(b+1)) := by
  induction xs with
  | nil => simpa using zero 0
  | cons x xs ih =>
    simp only [List.sum_cons,List.length_cons]
    have hh := (hx x (by simp)).add (ih (fun q hq=>hx q (by simp [hq])))
    convert hh using 1 <;> first | rfl | ring
end MetricKMedianRecovery.RationalHeight

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
lemma encode_height {q : ℚ} {b : ℕ} (hq : RationalHeight.Height q b) :
    (encode q).length≤3*b+6 := by
  have hn := Nat.size_le_size hq.1
  have hd := Nat.size_le_size hq.2
  rw [Nat.size_pow] at hn hd
  rw [encode_length]
  omega
lemma input_height (q : ℚ) : RationalHeight.Height q (encode q).length := by
  rw [encode_length]
  constructor
  · apply Nat.le_of_lt
    apply Nat.size_le.mp
    omega
  · apply Nat.le_of_lt
    apply Nat.size_le.mp
    omega
end BinaryRational
namespace RationalArray
open RationalHeight
lemma input_height (xs : List ℚ) (q : ℚ) (hq : q∈xs) : Height q (encode xs).length := by
  exact (BinaryRational.input_height q).mono
    (WordList.length_member_le_encode (List.mem_map.mpr ⟨q,hq,rfl⟩))
lemma fold_add (xs : List ℚ) (a : ℚ) (ctx : List Bool) :
    (xs.map BinaryRational.encode).foldl (WordList.Fold.operation addOp ctx) (BinaryRational.encode a)=
      BinaryRational.encode (a+xs.sum) := by
  induction xs generalizing a with
  | nil => simp only [List.map_nil,List.foldl_nil,List.sum_nil,add_zero]
  | cons x xs ih =>
    have hop : WordList.Fold.operation addOp ctx (BinaryRational.encode a) (BinaryRational.encode x)=
        BinaryRational.encode (a+x) := by
      simp only [WordList.Fold.operation,addOp,Function.comp_apply,discardPrefix_pairBits,BinaryRational.addWords_pair]
      rw [add_comm]
    rw [List.map_cons,List.foldl_cons,hop,ih,List.sum_cons,add_assoc]
lemma sumWords_encode (xs : List ℚ) : sumWords (encode xs)=BinaryRational.encode xs.sum := by
  let L := (encode xs).length
  have hn : xs.length≤L := by
    simpa only [List.length_map,L,encode] using WordList.length_le_encode (xs.map BinaryRational.encode)
  unfold sumWords
  simp only [Function.comp_apply,sumInput,encode]
  rw [WordList.Fold.run_encode addOp (20*(Polynomial.X+1)^2) [] (BinaryRational.encode 0)
    (xs.map BinaryRational.encode) (3*(L*(L+1))+6)]
  · simpa only [zero_add] using fold_add xs 0 []
  · intro n
    rw [←List.map_take,fold_add,zero_add]
    have hh := list_sum (xs.take n) L (fun q hq=>input_height xs q (List.mem_of_mem_take hq))
    have ht : (xs.take n).length≤L := by simp only [List.length_take]; omega
    exact (BinaryRational.encode_height hh).trans (by gcongr)
  · have hs : L≤(WordList.Fold.pack (WordList.encode (xs.map BinaryRational.encode)) []
        (BinaryRational.encode 0)).length := by
      rw [WordList.Fold.length_pack]
      change L≤2*L+2*[].length+(BinaryRational.encode 0).length+2
      omega
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,List.length_nil,Nat.mul_zero,Nat.add_zero]
    change 2*L+3*(L*(L+1))+6+2≤_
    nlinarith
end RationalArray
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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalScore
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
attribute [local irreducible] mapWith
lemma elementSamples_pack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) :
    elementSamples (pairBits (scorePack ctx part r seed,elemBits e))=encode (List.ofFn (fun l=>seedBits (seed e l))) := by
  simp only [elementSamples,scorePack,elemBits,oracleBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn]
lemma score_pack (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q)) (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) :
    score g (pairBits (scorePack ctx part r seed,elemBits e))=BinaryRational.encode (rationalScore G part r seed e) := by
  simp only [score,marginalValues,elementSamples_pack,mapWith_ofFn,marginal_pack_s238r g ctx G hg,
    Count.run_encode,List.length_ofFn,UnaryResources.lengthBits_eq,List.length_replicate,value_bits]
  rw [show encode (List.ofFn (fun l=>BinaryRational.encode (rationalMarginal G part r e (seed e l))))=
    RationalArray.encode (List.ofFn (fun l=>rationalMarginal G part r e (seed e l))) by
      simp only [RationalArray.encode,List.map_ofFn,Function.comp_def],RationalArray.sumWords_encode,
    BinaryRational.decode_encode,List.sum_ofFn]
  rfl
lemma rationalScore_cast (G : Finset (Fin q)→ℚ) (part : Fin q→Fin a)
    (r : Fin a→Fin T→Option (Fin q)) (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) :
    (rationalScore G part r seed e:ℝ)=Categorical.scores part (fun S=>(G S:ℝ)) r seed e := by
  simp only [rationalScore,rationalMarginal,Categorical.scores,FiniteSampling.sampleMean,
    Categorical.marginalSample,Categorical.marginal,Rat.cast_div,Rat.cast_sum,Rat.cast_sub,Rat.cast_natCast]
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_OrderedMaximum
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.OrderedMaximum
variable {E β : Type*} [LinearOrder β]
lemma fold (score : E→β) (s : E) (as : List E) :
    as.foldl (fun s a=>if score s < score a then a else s) s=run score s as := by
  induction as generalizing s with
  | nil=>rfl
  | cons a as ih=>exact ih _
lemma cast_run (score : E→ℚ) (s : E) (as : List E) :
    run (fun a=>(score a:ℝ)) s as=run score s as := by
  induction as generalizing s with
  | nil=>rfl
  | cons a as ih=>
    simp only [run,Rat.cast_lt,ih]
end MetricKMedianRecovery.OrderedMaximum

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalBest
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalBest
open WordOperations WordList BinaryArithmetic
lemma choose_pack {A : Type*} (enc : A→List Bool) (score : List Bool→List Bool) (ctx : List Bool)
    (r : A→ℚ) (hr : ∀ a,score (pairBits (ctx,enc a))=BinaryRational.encode (r a)) (a s : A) :
    choose score (pairBits (ctx,pairBits (enc a,enc s)))=enc (if r s < r a then a else s) := by
  simp only [choose,Find.context,Find.item,Fold.accum,Function.comp_apply,extractPrefix_pairBits,
    discardPrefix_pairBits,hr,BinaryRational.decode_encode]
  split_ifs <;> rfl
lemma run_pack {A : Type*} (enc : A→List Bool) (score : List Bool→List Bool) (ctx : List Bool)
    (r : A→ℚ) (hr : ∀ a,score (pairBits (ctx,enc a))=BinaryRational.encode (r a)) (s : A) (xs : List A) :
    run score (pack ctx (enc s) (xs.map enc))=enc (OrderedMaximum.run r s xs) := by
  unfold run
  simp only [pack,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [CappedFold.run_typed enc enc (fun s a=>if r s < r a then a else s) (choose score) ctx
    (pairBits (ctx,pairBits (enc s,encode (xs.map enc)))) (fun s a=>choose_pack enc score ctx r hr a s) s xs]
  · rw [OrderedMaximum.fold]
  · intro n
    rw [OrderedMaximum.fold]
    rcases OrderedMaximum.mem r s (xs.take n) with he|he
    · rw [he]
      simp only [pairBits_length]
      omega
    · have hh := WordList.length_member_le_encode (ws:=xs.map enc) (w:=enc (OrderedMaximum.run r s (xs.take n)))
        (List.mem_map.mpr ⟨_,List.mem_of_mem_take he,rfl⟩)
      simp only [pairBits_length]
      omega
lemma fromList_pack {A : Type*} (enc : A→List Bool) (score : List Bool→List Bool) (ctx : List Bool)
    (r : A→ℚ) (hr : ∀ a,score (pairBits (ctx,enc a))=BinaryRational.encode (r a)) (xs : List A) (hx : xs≠[]) :
    fromList score (pairBits (ctx,encode (xs.map enc)))=enc (OrderedMaximum.ofList r xs hx) := by
  cases xs with
  | nil=>exact False.elim (hx rfl)
  | cons a as=>
    simp only [fromList,extractPrefix_pairBits,discardPrefix_pairBits,List.map_cons,encode,head_cons,tail_cons]
    exact run_pack enc score ctx r hr a as
end MetricKMedianRecovery.BitMachine.BinaryRationalBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalChoice
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.OrderedMaximum
lemma cast_ofList {E : Type*} (score : E→ℚ) (as : List E) (h : as≠[]) :
    ofList (fun a=>(score a:ℝ)) as h=ofList score as h := cast_run score (as.head h) as.tail
end MetricKMedianRecovery.OrderedMaximum
namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
lemma choose_pack_s238r_oai (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (j : Fin a) :
    choose g (pairBits (scorePack ctx part r seed,j.val.bits))=
      elemBits ((rule part hp).choose (Categorical.scores part (fun S=>(G S:ℝ)) r seed) j) := by
  simp only [choose,extractPrefix_pairBits,bagWords_pack_s238r]
  rw [BinaryRationalBest.fromList_pack elemBits (score g) (scorePack ctx part r seed)
    (rationalScore G part r seed) (fun e=>score_pack g ctx G hg part r seed e)
    _ (Categorical.Selected.bag_ne_nil (elements q) mem_elements part hp j)]
  simp only [rule,Categorical.Selected.orderedRule]
  rw [show Categorical.scores part (fun S=>(G S:ℝ)) r seed=(fun e=>(rationalScore G part r seed e:ℝ)) from
    funext (fun e=>(rationalScore_cast G part r seed e).symm),OrderedMaximum.cast_ofList]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choose_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choose_pack_s238r_oai

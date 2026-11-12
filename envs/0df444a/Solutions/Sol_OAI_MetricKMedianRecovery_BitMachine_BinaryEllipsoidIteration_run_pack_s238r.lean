-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:46:35.615192+00:00
-- url     : https://prove2.me/submissions/e1abe6f2-f482-44ba-b4dd-5ec1884127a9

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L026
import Definitions.Def_Q238L028
import Definitions.Def_Q238L029
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidAdvance_found_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidCut_shapeWords_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidIteration_iterate_length_bound_s238r

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
namespace WordList
lemma length_encode_take (xs : List (List Bool)) (n : ℕ) :
    (encode (xs.take n)).length ≤ (encode xs).length := by
  have h := length_encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  omega
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

section
open WordOperations
namespace WordList
lemma length_encode_reverse (xs : List (List Bool)) : (encode xs.reverse).length=(encode xs).length := by
  simp only [length_encode,List.map_reverse,List.sum_reverse,List.length_reverse]
lemma length_encode_zip (xs ys : List (List Bool)) :
    (encode ((xs.zip ys).map pairBits)).length ≤ 2*(encode xs).length+(encode ys).length := by
  induction xs generalizing ys with
  | nil => simp only [List.zip_nil_left,List.map_nil,encode,List.length_nil,Nat.zero_le]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.zip_nil_right,List.map_nil,encode,List.length_nil,Nat.zero_le]
    | cons y ys =>
      simp only [List.zip_cons_cons,List.map_cons,encode,length_cons,pairBits_length]
      have h := ih ys
      omega
namespace Zip

lemma op_nil (w : List Bool) (os : List (List Bool)) :
    Fold.operation op [] (pairBits (encode [],encode os)) w=pairBits (encode [],encode os) := by
  simp only [Fold.operation,op,extractPrefix_pairBits,discardPrefix_pairBits,encode,ite_true, if_true]
lemma op_cons (w y : List Bool) (ys os : List (List Bool)) :
    Fold.operation op [] (pairBits (encode (y::ys),encode os)) w=
      pairBits (encode ys,encode (pairBits (w,y)::os)) := by
  simp only [Fold.operation,op,extractPrefix_pairBits,discardPrefix_pairBits,encode,cons_ne_nil,ite_false, if_false,
    tail_cons,head_cons]
lemma fold_eq (xs ys os : List (List Bool)) :
    xs.foldl (Fold.operation op []) (pairBits (encode ys,encode os))=
      pairBits (encode (ys.drop xs.length),encode (((xs.zip ys).map pairBits).reverse++os)) := by
  induction xs generalizing ys os with
  | nil => simp only [List.foldl_nil,List.length_nil,List.drop_zero,List.zip_nil_left,List.map_nil,
      List.reverse_nil,List.nil_append]
  | cons x xs ih =>
    rw [List.foldl_cons]
    cases ys with
    | nil =>
      rw [op_nil,ih]
      simp only [List.drop_nil,List.zip_nil_right,List.map_nil,List.reverse_nil,List.nil_append]
    | cons y ys =>
      rw [op_cons,ih]
      simp only [List.length_cons,List.drop_succ_cons,List.zip_cons_cons,List.map_cons,List.reverse_cons,
        List.append_assoc,List.singleton_append]

lemma run_encode (xs ys : List (List Bool)) :
    run (pairBits (encode xs,encode ys))=encode ((xs.zip ys).map pairBits) := by
  unfold run
  rw [extractPrefix_pairBits,discardPrefix_pairBits]
  change reverse (discardPrefix (Fold.run op _ (Fold.pack (encode xs) [] (pairBits (encode ys,encode [])))))=_
  rw [Fold.run_encode op (4*Polynomial.X+4) [] (pairBits (encode ys,encode [])) xs
    (2*(encode xs).length+3*(encode ys).length+1)]
  · rw [fold_eq,discardPrefix_pairBits,List.append_nil,reverse_encode,List.reverse_reverse]
  · intro n
    rw [fold_eq,List.append_nil,pairBits_length]
    dsimp only
    have hd := length_encode_drop ys (xs.take n).length
    have hz := length_encode_zip (xs.take n) ys
    have ht := length_encode_take xs n
    rw [length_encode_reverse]
    omega
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero,pairBits_length,encode]
    omega
end Zip
end WordList
end
open WordOperations BinaryArithmetic
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
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode
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
lemma dotWords_encode (xs : List (ℚ×ℚ)) :
    dotWords (encodePairs xs)=BinaryRational.encode (xs.map (fun p=>p.1*p.2)).sum := by
  simp only [dotWords,Function.comp_apply,encodePairs,WordList.mapWith_encode,List.map_map,
    Function.comp_def,mulOp,discardPrefix_pairBits,BinaryRational.mulWords_pair]
  simpa only [encode,List.map_map,Function.comp_def] using sumWords_encode (xs.map (fun p=>p.1*p.2))
lemma dotListsWords_encode (xs ys : List ℚ) :
    dotListsWords (pairBits (encode xs,encode ys))=BinaryRational.encode ((xs.zip ys).map (fun p=>p.1*p.2)).sum := by
  simp only [dotListsWords,Function.comp_apply,encode,WordList.Zip.run_encode,List.zip_map]
  simpa only [encodePairs,List.map_map,Function.comp_def,Prod.map] using dotWords_encode (xs.zip ys)
end RationalArray
namespace RationalMatrix
open WordList

lemma rowEncode_eq {n : ℕ} (v : Fin n → ℚ) :
    rowEncode v=WordList.encode (List.ofFn (fun i=>BinaryRational.encode (v i))) := by
  simp only [rowEncode,RationalArray.encode,List.map_ofFn,Function.comp_def]

lemma dotListsWords_ofFn {n : ℕ} (u v : Fin n → ℚ) :
    RationalArray.dotListsWords (pairBits (rowEncode u,rowEncode v))=BinaryRational.encode (∑ i,u i*v i) := by
  rw [rowEncode,rowEncode,RationalArray.dotListsWords_encode]
  congr 1
  have hz : ((List.ofFn u).zip (List.ofFn v)).map (fun p=>p.1*p.2)=List.ofFn (fun i=>u i*v i) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.getElem_map,List.getElem_zip,List.getElem_ofFn]
  rw [hz,List.sum_ofFn]
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NumAbs
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open WordOperations BinaryArithmetic
open scoped Matrix
namespace WordList
lemma zip_ofFn {n : ℕ} {α β : Type*} (u : Fin n → α) (v : Fin n → β) :
    (List.ofFn u).zip (List.ofFn v)=List.ofFn (fun i=>(u i,v i)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_zip,List.getElem_ofFn]
lemma pointwise_ofFn {n : ℕ} (f : List Bool → List Bool) (u v : Fin n → List Bool) :
    pointwise f (pairBits (encode (List.ofFn u),encode (List.ofFn v)))=
      encode (List.ofFn (fun i=>f (pairBits (u i,v i)))) := by
  simp only [pointwise,Zip.run_encode,zip_ofFn,List.map_ofFn,mapWith_ofFn,
    Function.comp_apply,discardPrefix_pairBits]
end WordList
namespace RationalMatrix
open WordList
lemma vectorSub_encode {n : ℕ} (u v : Fin n → ℚ) :
    vectorSub (pairBits (rowEncode u,rowEncode v))=rowEncode (u-v) := by
  simp only [vectorSub,rowEncode_eq,pointwise_ofFn,BinaryRational.subWords_pair,Pi.sub_apply]
lemma vectorScale_encode {n : ℕ} (r : ℚ) (u : Fin n → ℚ) :
    vectorScale (pairBits (BinaryRational.encode r,rowEncode u))=rowEncode (r • u) := by
  simp only [vectorScale,rowEncode_eq,mapWith_ofFn,BinaryRational.mulWords_pair,Pi.smul_apply,smul_eq_mul]
lemma mulVec_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) :
    mulVec (pairBits (encode A,rowEncode v))=rowEncode (A *ᵥ v) := by
  simp only [mulVec,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits,
    encode,mapWith_ofFn,dotRow,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits,
    dotListsWords_ofFn]
  simp only [rowEncode_eq]
  rfl
lemma quad_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) :
    quad (pairBits (encode A,rowEncode v))=BinaryRational.encode (v ⬝ᵥ (A *ᵥ v)) := by
  simp only [quad,Function.comp_apply,quadInput,discardPrefix_pairBits,mulVec_encode,dotListsWords_ofFn]
  rfl
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack5
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidCut
open RationalMatrix

lemma dim_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    dim (pack H a c D)=n.bits := by simp only [dim,pack,extractPrefix_pairBits]
lemma shape_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    shape (pack H a c D)=encode H := by
  simp only [shape,Function.comp_apply,rest,pack,extractPrefix_pairBits,discardPrefix_pairBits]
lemma direction_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    direction (pack H a c D)=rowEncode a := by
  simp only [direction,rest₂,Function.comp_apply,rest,pack,extractPrefix_pairBits,discardPrefix_pairBits]
lemma center_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    center (pack H a c D)=rowEncode c := by
  simp only [center,rest₃,rest₂,Function.comp_apply,rest,pack,extractPrefix_pairBits,discardPrefix_pairBits]
lemma haWords_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    haWords (pack H a c D)=rowEncode (H *ᵥ a) := by
  simp only [haWords,Function.comp_apply,haInput,shape_pack,direction_pack,mulVec_encode]
lemma quadWords_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    quadWords (pack H a c D)=BinaryRational.encode (Ellipsoid.rationalQuad H a) := by
  simp only [quadWords,Function.comp_apply,haInput,shape_pack,direction_pack,quad_encode,Ellipsoid.rationalQuad]

lemma centerWords_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    centerWords (pack H a c D)=rowEncode (Ellipsoid.rationalStepCenter H a c) := by
  simp only [centerWords,Function.comp_apply,centerInput,center_pack,scaledHa,scaledHaInput,
    coefCenter,dimension,dim_pack,value_bits,rootPrecision,qvalue,quadWords_pack,
    BinaryRational.decode_encode,haWords_pack,vectorScale_encode,vectorSub_encode,
    Ellipsoid.rationalStepCenter,Fintype.card_fin]

end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

lemma dim_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : dim (pack D rs S)=n.bits := by
  simp only [dim,pack,extractPrefix_pairBits]
lemma precision_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : precision (pack D rs S)=D.bits := by
  simp only [precision,rest,Function.comp_apply,pack,extractPrefix_pairBits,discardPrefix_pairBits]
lemma rows_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : rows (pack D rs S)=BinaryRow.rowsEncode rs := by
  simp only [rows,rest₂,rest,Function.comp_apply,pack,extractPrefix_pairBits,discardPrefix_pairBits]
lemma stored_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : stored (pack D rs S)=stateEncode S := by
  simp only [stored,rest₂,rest,Function.comp_apply,pack,discardPrefix_pairBits]
lemma shape_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : shape (pack D rs S)=encode S.shape := by
  simp only [shape,Function.comp_apply,stored_pack,stateEncode,extractPrefix_pairBits]
lemma center_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : center (pack D rs S)=rowEncode S.center := by
  simp only [center,Function.comp_apply,stored_pack,stateEncode,discardPrefix_pairBits]
lemma direction_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) (r : Row n)
    (h : badRow rs S.center=some r) : direction (pack D rs S)=rowEncode r.coeff := by
  simp only [direction,found_pack_s238r,h,Option.map_some,WordList.Find.optionEncode,List.tail_cons,
    BinaryRow.encode,extractPrefix_pairBits]

lemma normWords_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) (r : Row n)
    (h : badRow rs S.center=some r) :
    normWords (pack D rs S)=BinaryRational.encode (r.coeff ⬝ᵥ r.coeff) := by
  simp only [normWords,direction_pack D rs S r h,RationalMatrix.dotListsWords_ofFn]
  rfl
lemma zeroDirection_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) (r : Row n)
    (h : badRow rs S.center=some r) : zeroDirection (pack D rs S)=decide (r.coeff=0) := by
  rw [zeroDirection,normWords_pack D rs S r h,BinaryRational.decode_encode]
  congr 1
  have hn : (0:ℚ) ≤ r.coeff ⬝ᵥ r.coeff := by
    unfold dotProduct
    exact Finset.sum_nonneg (fun i _=>mul_self_nonneg (r.coeff i))
  exact propext ⟨fun hh=>dotProduct_self_eq_zero.mp (le_antisymm hh hn),
    fun hh=>by rw [hh,dotProduct_zero]⟩

lemma cutInput_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) (r : Row n)
    (h : badRow rs S.center=some r) : cutInput (pack D rs S)=BinaryEllipsoidCut.pack S.shape r.coeff S.center D := by
  simp only [cutInput,dim_pack,shape_pack,direction_pack D rs S r h,center_pack,precision_pack,BinaryEllipsoidCut.pack]
lemma nextState_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) :
    nextState (pack D rs S)=stateEncode (advance D rs S) := by
  unfold nextState advance
  rw [found_pack_s238r,stored_pack]
  cases h : badRow rs S.center with
  | none => simp only [Option.map_none,WordList.Find.optionEncode,ite_true, if_true]
  | some r =>
    simp only [Option.map_some,WordList.Find.optionEncode,reduceCtorEq,ite_false, if_false,
      zeroDirection_pack D rs S r h,decide_eq_true_eq]
    split_ifs with hz
    · rfl
    · simp only [updated,cutInput_pack D rs S r h,BinaryEllipsoidCut.shapeWords_pack_s238r,
        BinaryEllipsoidCut.centerWords_pack,stateEncode]
lemma run_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) :
    run (pack D rs S)=pack D rs (advance D rs S) := by
  simp only [run,dim_pack,precision_pack,rows_pack,nextState_pack]
  rfl
lemma iterate_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) (t : ℕ) :
    run^[t] (pack D rs S)=pack D rs (Ellipsoid.iterate D rs S t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,run_pack]; rfl
end BinaryEllipsoidAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight
namespace BinaryEllipsoidIteration
open RationalMatrix BinaryEllipsoidAdvance

lemma run_pack_s238r_oai (n T R : ℕ) (rs : List (Row n)) (hn : 2≤ n) (hR : 1≤ R) :
    run (pack n T R rs)=BinaryEllipsoidAdvance.pack (gridDenominator n T) rs
      (Ellipsoid.iterate (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ)) T) := by
  unfold run
  simp only [Function.comp_apply,prepared,pack,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [BoundedIteration.run_eq]
  · simp only [List.length_replicate,BinaryEllipsoidAdvance.iterate_pack]
  · intro j hj
    simp only [List.length_replicate] at hj
    rw [BinaryEllipsoidAdvance.iterate_pack,boundCounter.word_length]
    exact iterate_length_bound_s238r n T R rs hn hR j hj
end BinaryEllipsoidIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238r_oai

-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:01:36.927108+00:00
-- url     : https://prove2.me/submissions/9493b547-ac2b-4be9-9a1e-b4ccb3487fed

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K037
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRationalSort_sumBottom_pack_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace RationalMin
open WordList
lemma operation_pair (ctx a w : List Bool) :
    Fold.operation choose ctx a w=if BinaryRational.decode w≤BinaryRational.decode a then w else a := by
  simp only [Fold.operation,choose,Find.item,Fold.accum,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
lemma fold_encode (qs : List ℚ) (a : ℚ) (ctx : List Bool) :
    (qs.map BinaryRational.encode).foldl (Fold.operation choose ctx) (BinaryRational.encode a)=
      BinaryRational.encode (qs.foldl min a) := by
  induction qs generalizing a with
  | nil=>rfl
  | cons q qs ih=>
    simp only [List.map_cons,List.foldl_cons,operation_pair,BinaryRational.decode_encode]
    by_cases h : q≤a
    · simp only [h,ite_true, if_true,min_eq_right h,ih]
    · have ha : a≤q := le_of_lt (lt_of_not_ge h)
      simp only [h,ite_false, if_false,min_eq_left ha,ih]
lemma fold_length (ws : List (List Bool)) (a ctx : List Bool) :
    (ws.foldl (Fold.operation choose ctx) a).length≤a.length+(encode ws).length := by
  induction ws generalizing a with
  | nil=>simp only [List.foldl_nil,encode,List.length_nil,Nat.add_zero,Nat.le_refl]
  | cons w ws ih=>
    rw [List.foldl_cons,operation_pair]
    simp only [encode,length_cons]
    split_ifs
    · have hh := ih w; omega
    · have hh := ih a; omega

lemma seed_encode (qs : List ℚ) : seed (RationalArray.encode qs)=BinaryRational.encode (qs.head?.getD 0) := by
  cases qs with
  | nil=>rfl
  | cons q qs=>simp only [seed,RationalArray.encode,List.map_cons,encode,cons_ne_nil,
      ite_false, if_false,head_cons,List.head?_cons,Option.getD_some]
lemma run_encode (qs : List ℚ) : run (RationalArray.encode qs)=BinaryRational.encode (minimum qs) := by
  unfold run
  rw [show RationalArray.encode qs=encode (qs.map BinaryRational.encode) from rfl]
  rw [Fold.run_encode choose (3*Polynomial.X+3) [] (seed (encode (qs.map BinaryRational.encode)))
    (qs.map BinaryRational.encode)
    ((seed (encode (qs.map BinaryRational.encode))).length+(encode (qs.map BinaryRational.encode)).length)]
  · rw [show seed (encode (qs.map BinaryRational.encode))=BinaryRational.encode (qs.head?.getD 0) from seed_encode qs,
      fold_encode]
    rfl
  · intro j
    have hh := fold_length ((qs.map BinaryRational.encode).take j)
      (seed (encode (qs.map BinaryRational.encode))) []
    exact hh.trans (Nat.add_le_add_left (length_encode_take _ _) _)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil]
    omega

end RationalMin
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalCap
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)

lemma minimum_capped {E : Type*} [DecidableEq E] (b : ℚ) (d : E→ℚ) (xs : List E) :
    RationalMin.minimum (b::xs.map d)=capped b d xs.toFinset := by
  simp only [RationalMin.minimum,List.head?_cons,Option.getD_some,List.foldl_cons,min_self]
  rw [List.foldl_eq_foldr]
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.map_cons,List.foldr_cons,List.toFinset_cons,capped,Finset.fold_insert_idem] at *
    rw [ih]
attribute [local irreducible] mapWith
lemma offers_pack {q : ℕ} (b : ℚ) (d : Fin q→ℚ) (xs : List (Fin q)) :
    offers (pairBits (encode (xs.map BinaryCategorical.elemBits),rowBits b d))=
      encode (xs.map (fun e=>BinaryRational.encode (d e))) := by
  simp only [offers,rowBits,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,mapWith_encode,List.map_map,
    Function.comp_def,look,BinaryCategorical.elemBits,lookup_ofFn]
attribute [local irreducible] RationalMin.run
lemma cap_pack {q : ℕ} (b : ℚ) (d : Fin q→ℚ) (xs : List (Fin q)) :
    cap (pairBits (encode (xs.map BinaryCategorical.elemBits),rowBits b d))=
      BinaryRational.encode (capped b d xs.toFinset) := by
  unfold cap
  rw [offers_pack]
  simp only [discardPrefix_pairBits,rowBits,field_encode,List.getElem?_cons_zero,Option.getD_some]
  rw [show cons (BinaryRational.encode b) (encode (xs.map (fun e=>BinaryRational.encode (d e))))=
    RationalArray.encode (b::xs.map d) by
      simp only [RationalArray.encode,List.map_cons,List.map_map,Function.comp_def,encode]]
  rw [RationalMin.run_encode,minimum_capped]

lemma weightedCap_pack {q : ℕ} (w b : ℚ) (d : Fin q→ℚ) (xs : List (Fin q)) :
    weightedCap (pairBits (encode (xs.map BinaryCategorical.elemBits),weightedRowBits w b d))=
      BinaryRational.encode (w*capped b d xs.toFinset) := by
  simp only [weightedCap,weightedRowBits,extractPrefix_pairBits,discardPrefix_pairBits,cap_pack,
    BinaryRational.decode_encode]
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalSurrogate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q p r : ℕ}
lemma clientValues_pack (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) :
    clientValues (pairBits (contextBits k base distance weight redBase redDistance,encode (xs.map BinaryCategorical.elemBits)))=
      encode (List.ofFn (fun i=>BinaryRational.encode (capped (base i) (distance i) xs.toFinset))) := by
  simp only [clientValues,contextBits,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,mapWith_ofFn,cap_pack]
lemma redValues_pack (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) :
    redValues (pairBits (contextBits k base distance weight redBase redDistance,encode (xs.map BinaryCategorical.elemBits)))=
      encode (List.ofFn (fun i=>BinaryRational.encode (weight i*capped (redBase i) (redDistance i) xs.toFinset))) := by
  simp only [redValues,contextBits,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,mapWith_ofFn,weightedCap_pack]

lemma surrogate_pack (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) :
    surrogate (pairBits (contextBits k base distance weight redBase redDistance,encode (xs.map BinaryCategorical.elemBits)))=
      BinaryRational.encode (surrogateQ k base distance weight redBase redDistance xs.toFinset) := by
  unfold surrogate
  rw [clientValues_pack,redValues_pack]
  simp only [extractPrefix_pairBits,contextBits,field_encode,List.getElem?_cons_zero,Option.getD_some,
    BinaryRationalSort.sumBottom_pack_s238]
  rw [show encode (List.ofFn (fun i=>BinaryRational.encode (capped (base i) (distance i) xs.toFinset)))=
    RationalArray.encode (List.ofFn (fun i=>capped (base i) (distance i) xs.toFinset)) by
      simp only [RationalArray.encode,List.map_ofFn,Function.comp_def]]
  rw [RationalArray.sumWords_encode,BinaryRational.decode_encode,BinaryRational.decode_encode,List.sum_ofFn]
  rfl

lemma saving_pack_s238_oai (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) :
    saving (pairBits (contextBits k base distance weight redBase redDistance,encode (xs.map BinaryCategorical.elemBits)))=
      BinaryRational.encode (savingQ k base distance weight redBase redDistance xs.toFinset) := by
  unfold saving
  rw [extractPrefix_pairBits,surrogate_pack]
  rw [show ([]:List Bool)=encode (([]:List (Fin q)).map BinaryCategorical.elemBits) from rfl,surrogate_pack]
  simp only [BinaryRational.decode_encode,List.toFinset_nil,savingQ]
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238_oai

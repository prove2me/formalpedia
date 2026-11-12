-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:39:32.468531+00:00
-- url     : https://prove2.me/submissions/a3f2fef4-cc33-45bf-a8c7-6427686352a5

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L026
import Definitions.Def_Q238L028
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_RationalMatrix_determinantWords_encode_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Freeze
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdInteger
open Matrix Function
open scoped BigOperators

section Bridge
variable {R : Type*} [CommRing R] {n : ℕ}
lemma sumFrom_eq_sum_Ico {lo : ℕ} (f : ℕ → R) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [BirdDet.sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [BirdDet.sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

lemma sumFrom_fin_tail (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k ∈ Finset.Ioi i, f k.val := calc
  _ = ∑ k ∈ Finset.Ico (i.val + 1) n, f k := by rw [sumFrom_eq_sum_Ico]
  _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by congr; ext; aesop
  _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
  _ = ∑ k : Fin n, if i.val < k.val then f k else 0 := by rw [← Fin.sum_univ_eq_sum_range]
  _ = ∑ k ∈ Finset.Ioi i, f k.val := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

lemma iterate_get_eq_spec (A : Array R) (hA : A.size = n*n) (t : ℕ) (i j : Fin n) :
    ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (BirdDet.Spec.stepEntry (.ofArray A hA))^[t] (.ofArray A hA) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [BirdDet.get_eq]
  | succ t ih =>
    simp_rw [iterate_succ_apply',BirdDet.stepEntry_eq,BirdDet.Spec.stepEntry_eq,
      sumFrom_fin_tail,ih,Matrix.of_apply,BirdDet.get_eq]

lemma bird_eq_spec (A : Array R) (hA : A.size=n*n) :
    BirdDet.birdDet n A=BirdDet.Spec.birdDet (.ofArray A hA) := by
  cases n with
  | zero => rw [BirdDet.birdDet_zero,BirdDet.Spec.birdDetSpec_zero]
  | succ k => simp [BirdDet.birdDet_succ,BirdDet.Spec.birdDetSpec_succ,←iterate_get_eq_spec A hA k]

lemma spec_eq_det (A : Matrix (Fin n) (Fin n) R) : BirdDet.Spec.birdDet A=A.det := by
  let ar := Array.ofFn (fun k : Fin (n*n) => A k.divNat k.modNat)
  have har : ar.size=n*n := Array.size_ofFn
  have he : Matrix.ofArray ar har=A := Matrix.ofArray_ofFn A
  rw [←he,←bird_eq_spec ar har,←BirdDet.det_eq_birdDet ar har]
end Bridge

lemma iterate_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) :
    iterate A t=(BirdDet.Spec.stepEntry A)^[t] A := by
  induction t with
  | zero => simp [iterate]
  | succ t ih => simp only [iterate,freeze_eq,ih,iterate_succ_apply']

lemma determinant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : determinant A=A.det := by
  rw [←spec_eq_det]
  cases n with
  | zero => rfl
  | succ k => simp only [determinant,BirdDet.Spec.birdDetSpec_succ,iterate_eq]

end MetricKMedianRecovery.BirdInteger

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
end WordList
end
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
namespace Indices

lemma op_pair (w : List Bool) (a : ℕ) (os : List (List Bool)) :
    Fold.operation op [] (pairBits (a.bits,encode os)) w=
      pairBits ((a+1).bits,encode (a.bits::os)) := by
  simp only [Fold.operation,op,discardPrefix_pairBits,extractPrefix_pairBits,value_bits,encode]
lemma fold_eq (ws os : List (List Bool)) (a : ℕ) :
    ws.foldl (Fold.operation op []) (pairBits (a.bits,encode os))=
      pairBits ((a+ws.length).bits,encode ((List.range' a ws.length |>.map Nat.bits).reverse++os)) := by
  induction ws generalizing a os with
  | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero,List.range'_zero,List.map_nil,
      List.reverse_nil,List.nil_append]
  | cons w ws ih =>
    rw [List.foldl_cons,op_pair,ih]
    simp only [List.length_cons,List.range'_succ,List.map_cons,List.reverse_cons,List.append_assoc,
      List.singleton_append,Nat.add_assoc,Nat.add_comm 1]
lemma range_length (n : ℕ) : (encode ((List.range' 0 n).map Nat.bits)).length ≤ n*(2*n+2) := by
  have hh := encode_le_bound ((List.range' 0 n).map Nat.bits) n (by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have hh := (List.mem_range'_1.mp hi).2
    exact (bits_length_le i).trans (by omega))
  simpa only [List.length_map,List.length_range'] using hh

lemma run_encode (ws : List (List Bool)) : run (encode ws)=encode ((List.range ws.length).map Nat.bits) := by
  unfold run
  rw [Fold.run_encode op (20*(Polynomial.X+1)^2) [] (pairBits (Nat.bits 0,encode [])) ws
    (2*ws.length+1+ws.length*(2*ws.length+2))]
  · rw [fold_eq,discardPrefix_pairBits,List.append_nil,reverse_encode,List.reverse_reverse,List.range_eq_range']
  · intro n
    rw [fold_eq,Nat.zero_add,List.append_nil,pairBits_length]
    dsimp only
    rw [length_encode_reverse]
    have hb := bits_length_le (ws.take n).length
    have hr := range_length (ws.take n).length
    have hl : (ws.take n).length ≤ ws.length := by simp only [List.length_take]; omega
    nlinarith
  · simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    have hw := length_le_encode ws
    have hsq := Nat.mul_le_mul hw hw
    nlinarith [Nat.zero_le ((pairBits (Nat.bits 0, encode [])).length)]
end Indices
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
lemma indices_ofFn {n : ℕ} (f : Fin n → List Bool) :
    Indices.run (encode (List.ofFn f))=encode (List.ofFn (fun i : Fin n=>i.val.bits)) := by
  rw [Indices.run_encode,List.length_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonDen
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdRational
open Matrix RationalHeight
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma commonDen_pos (q : J → ℚ) : 0 < commonDen q := by
  exact Finset.prod_pos (fun i _ => by exact_mod_cast (q i).den_pos)

lemma scaled_cast (q : J → ℚ) (i : J) :
    (scaled q i:ℚ)=(commonDen q:ℚ)*q i := by
  have hh : commonDen q = (q i).den * ∏ j ∈ Finset.univ.erase i, ((q j).den:ℤ) :=
    (Finset.mul_prod_erase Finset.univ (fun j => ((q j).den:ℤ)) (Finset.mem_univ i)).symm
  have hn : ((q i).den:ℚ)≠0 := by exact_mod_cast (q i).den_nz
  calc
    _ = (commonDen q:ℚ)*((q i).num/(q i).den) := by
      rw [hh]
      unfold scaled
      push_cast
      field_simp
    _ = _ := by rw [Rat.num_div_den]

lemma integerMatrix_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    ((integerMatrix A b).map (Int.cast : ℤ → ℚ))=(commonDen (data A b):ℚ) • A := by
  ext i j
  change ((BirdInteger.freeze (Matrix.of (fun i j => scaled (data A b) (i,some j)))) i j:ℚ) = _
  rw [BirdInteger.freeze_eq]
  exact scaled_cast (data A b) (i,some j)
lemma integerVector_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    (fun i => (integerVector A b i:ℚ))=(commonDen (data A b):ℚ) • b := by
  ext i
  simp [integerVector,scaled_cast,Pi.smul_apply,smul_eq_mul,data]

lemma solve_as_cramer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    solve A b =
      (Matrix.det ((integerMatrix A b).map (Int.cast : ℤ → ℚ)))⁻¹ •
        (Matrix.cramer ((integerMatrix A b).map (Int.cast : ℤ → ℚ)) (fun i => (integerVector A b i:ℚ))) := by
  funext i
  simp [solve,BirdInteger.determinant_eq,Matrix.cramer_apply,Int.cast_det,
    Matrix.map_updateCol,div_eq_mul_inv,mul_comm]
  left
  rfl

end MetricKMedianRecovery.BirdRational

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
namespace RationalMatrix
open WordList

lemma rowEncode_eq {n : ℕ} (v : Fin n → ℚ) :
    rowEncode v=WordList.encode (List.ofFn (fun i=>BinaryRational.encode (v i))) := by
  simp only [rowEncode,RationalArray.encode,List.map_ofFn,Function.comp_def]

lemma columnOp_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (j : Fin n) :
    columnOp (pairBits (encode A,j.val.bits))=rowEncode (fun i=>A i j) := by
  simp only [columnOp,Function.comp_apply,swapWords,discardPrefix_pairBits,extractPrefix_pairBits,encode,mapWith_ofFn,rowEncode_eq,
    lookup_ofFn]

lemma transposeWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    transposeWords (encode A)=encode A.transpose := by
  simp only [transposeWords,Function.comp_apply,matrixIndices]
  have hi := indices_ofFn (fun i=>rowEncode (A i))
  change Indices.run (encode A)=_ at hi
  rw [hi,mapWith_ofFn]
  simp only [columnOp_encode]
  rfl

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack4
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList.Set

lemma op_ofFn {n : ℕ} (w : Fin n → List Bool) (i j : Fin n) (v : List Bool) :
    op (pairBits (pack (encode (List.ofFn w)) j.val.bits v,i.val.bits))=
      (if i=j then v else w i) := by
  simp only [op,pack,target,replacement,oldValue,oldInput,extractPrefix_pairBits,
    discardPrefix_pairBits,value_bits,lookup_ofFn]
  split_ifs <;> try rfl
  all_goals omega

lemma run_ofFn {n : ℕ} (w : Fin n → List Bool) (j : Fin n) (v : List Bool) :
    run (pack (encode (List.ofFn w)) j.val.bits v)=
      encode (List.ofFn (fun i=>if i=j then v else w i)) := by
  simp only [run,input,pack,extractPrefix_pairBits,indices_ofFn,mapWith_ofFn]
  have hh (i : Fin n) := op_ofFn w i j v
  simp only [pack] at hh
  simp only [hh]
end WordList.Set
open WordOperations BinaryArithmetic
open scoped Matrix
namespace RationalMatrix
open WordList

lemma updateColWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) (j : Fin n) :
    updateColWords (Set.pack (encode A) j.val.bits (rowEncode b))=encode (A.updateCol j b) := by
  have he : WordList.encode (List.ofFn (fun i=>if i=j then rowEncode b else rowEncode (A.transpose i)))=
      encode (A.updateCol j b).transpose := by
    rw [encode]
    congr 1
    apply congrArg List.ofFn
    funext i
    by_cases hi : i=j
    · subst i
      rw [ite_eq_left rfl]
      apply congrArg rowEncode
      funext k
      simp only [Matrix.transpose_apply,Matrix.updateCol_self]
    · rw [ite_eq_right hi]
      apply congrArg rowEncode
      funext k
      simp only [Matrix.transpose_apply,Matrix.updateCol_ne hi]
  unfold updateColWords updateInput
  simp only [Set.pack,extractPrefix_pairBits,discardPrefix_pairBits,transposeWords_encode]
  rw [encode,←Set.pack,Set.run_ofFn,he,transposeWords_encode,Matrix.transpose_transpose]

lemma cramerOp_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) (j : Fin n) :
    cramerOp (pairBits (pairBits (encode A,rowEncode b),j.val.bits))=
      BinaryRational.encode ((A.updateCol j b).det) := by
  simp only [cramerOp,cramerOpInput,extractPrefix_pairBits,discardPrefix_pairBits,
    updateColWords_encode,determinantWords_encode_s238r]
lemma cramerWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    cramerWords (pairBits (encode A,rowEncode b))=rowEncode (A.cramer b) := by
  have hi := indices_ofFn (fun i=>rowEncode (A i))
  change Indices.run (encode A)=_ at hi
  simp only [cramerWords,cramerInput,extractPrefix_pairBits,hi,mapWith_ofFn,cramerOp_encode]
  simp only [rowEncode_eq,Matrix.cramer_apply]

lemma solveWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    solveWords (pairBits (encode A,rowEncode b))=rowEncode (A.det⁻¹ • A.cramer b) := by
  simp only [solveWords,solveInput,inverseDet,firstDet,Function.comp_apply,extractPrefix_pairBits,determinantWords_encode_s238r,
    BinaryRational.invWords_encode,cramerWords_encode]
  simp only [rowEncode_eq,mapWith_ofFn,
    BinaryRational.mulWords_pair,Pi.smul_apply,smul_eq_mul]

lemma solveWords_bird_s238r_oai {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    solveWords (pairBits (encode A,rowEncode b))=rowEncode (MetricKMedianRecovery.BirdRational.solve A b) := by
  rw [solveWords_encode]
  congr 1
  symm
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    let D : ℚ := MetricKMedianRecovery.BirdRational.commonDen (MetricKMedianRecovery.BirdRational.data A b)
    have hD : D≠0 := by
      dsimp [D]
      exact_mod_cast (MetricKMedianRecovery.BirdRational.commonDen_pos (MetricKMedianRecovery.BirdRational.data A b)).ne'
    have hZ : (MetricKMedianRecovery.BirdRational.integerMatrix A b).map (Int.cast : ℤ → ℚ)=D • A :=
      MetricKMedianRecovery.BirdRational.integerMatrix_cast A b
    rw [MetricKMedianRecovery.BirdRational.solve_as_cramer,hZ,MetricKMedianRecovery.BirdRational.integerVector_cast,
      Matrix.det_smul,Matrix.cramer_smul,LinearMap.smul_apply,map_smul,
      smul_smul,smul_smul]
    simp only [Fintype.card_fin,Nat.add_sub_cancel]
    change ((D^(n+1)*A.det)⁻¹*D^n*D) • (A.cramer b)=_
    rw [mul_assoc,←pow_succ,mul_inv_rev,mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hD),mul_one]

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238r_oai

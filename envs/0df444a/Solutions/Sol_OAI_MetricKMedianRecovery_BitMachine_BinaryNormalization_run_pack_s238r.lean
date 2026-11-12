-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:51:05.906482+00:00
-- url     : https://prove2.me/submissions/d7eb5d18-a26e-49cb-860e-5164c87dbde7

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L028
import Definitions.Def_Q238L030
import Definitions.Def_Q238L031
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238r

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

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace MetricTable
open WordList

lemma get_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (f : Fin m) (j : Fin d) :
    get (pairBits (pairBits (Rectangular.encode distance,f.val.bits),j.val.bits))=
      BinaryRational.encode (distance f j) := by
  simp only [get,getRow,context,row,col,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,Rectangular.encode,lookup_ofFn,
    RationalMatrix.rowEncode_eq]
end MetricTable
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma map_encode (f : List Bool → List Bool) (ws : List (List Bool)) :
    map f (encode ws)=encode (ws.map f) := by
  simp only [map,mapWith_encode,Function.comp_apply,discardPrefix_pairBits]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_DuplicateMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix
open WordOperations WordList
variable {n : ℕ}
lemma row_double (f : Fin n→ℚ) :
    RationalMatrix.rowEncode (fun j : Fin (n+n)=>f (forget j))=
      RationalMatrix.rowEncode f++RationalMatrix.rowEncode f := by
  simp only [RationalMatrix.rowEncode_eq,List.ofFn_add,forget,Fin.append_left',Fin.append_right,id_eq,
    encode_append]
lemma forget_left (i : Fin n) : forget (Fin.castLE (Nat.le_add_right n n) i)=i := Fin.append_left' id id i
lemma forget_right (i : Fin n) : forget (Fin.natAdd n i)=i := Fin.append_right id id i
lemma run_encode (δ : Fin n→Fin n→ℚ) :
    run (RationalMatrix.encode δ)=RationalMatrix.encode (duplicate δ) := by
  change twice (map twice (encode (List.ofFn (fun i=>RationalMatrix.rowEncode (δ i)))))=
    encode (List.ofFn (fun i=>RationalMatrix.rowEncode (fun j=>δ (forget i) (forget j))))
  rw [map_encode,List.map_ofFn,List.ofFn_add]
  simp only [forget_left,forget_right,encode_append,row_double]
  rfl

end MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalConstants
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
lemma countRat_cast : (countRat:ℝ)=Anchoring.countConstant (1/100) := by
  simp only [countRat,Anchoring.countConstant,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one]
lemma gapRat_cast : (gapRat:ℝ)=strictnessGap (200*Anchoring.countConstant (1/100)) := by
  simp only [gapRat,strictnessGap,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,countRat_cast]
lemma gammaRat_cast : (gammaRat:ℝ)=gamma := by
  simp only [gammaRat,gamma,Rat.cast_min,Rat.cast_div,Rat.cast_ofNat,gapRat_cast]
lemma cap_rat (n : ℕ) : Rounding.cap n (gamma/16)=⌈20*(n:ℚ)^2/(gammaRat/16)⌉₊+1 := by
  unfold Rounding.cap
  congr 1
  rw [←gammaRat_cast]
  norm_cast
  rw [←Int.ceil_toNat,←Int.ceil_toNat,Rat.ceil_cast]
end MetricKMedianRecovery.IntegralAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingArithmetic
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRound
open WordList BinaryOpeningPayment

lemma positive_pack (q u : ℚ) (cap : ℕ) :
    positive (pack q u cap)=(min cap (max 1 ⌈q/u⌉₊)).bits := by
  simp only [positive,ceil,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryRational.decode_encode,value_bits]
lemma rational_pack (q u : ℚ) (cap : ℕ) :
    rational (pack q u cap)=BinaryRational.encode (min cap (max 1 ⌈q/u⌉₊):ℕ) := by
  rw [rational,positive_pack,value_bits]
end BinaryRound
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingMatrix
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
lemma entry_pack (δ : Fin n→Fin n→ℚ) (u : ℚ) (cap : ℕ) (i j : Fin n) :
    entry (pairBits (pairBits (pack δ u cap,i.val.bits),j.val.bits))=BinaryRational.encode (round δ u cap i j) := by
  simp only [entry,rowIndex,colIndex,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,value_bits]
  by_cases hij : i=j
  · simp only [hij,ite_true, if_true,round]
  · have hv : i.val≠j.val := fun he=>hij (Fin.ext he)
    rw [ite_eq_right hv,round,ite_eq_right hij]
    have he : entryInput (pairBits (pairBits (pack δ u cap,i.val.bits),j.val.bits))=BinaryRound.pack (δ i j) u cap := by
      simp only [entryInput,distance,ctx,rowIndex,colIndex,Function.comp_apply,extractPrefix_pairBits,
        discardPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
        Option.getD_some,BinaryRound.pack]
      rw [show MetricTable.get (pairBits (pairBits (RationalMatrix.encode δ,i.val.bits),j.val.bits))=BinaryRational.encode (δ i j) from MetricTable.get_pack δ i j]
    rw [he,BinaryRound.rational_pack]
lemma row_pack (δ : Fin n→Fin n→ℚ) (u : ℚ) (cap : ℕ) (i : Fin n) :
    row (pairBits (pack δ u cap,i.val.bits))=RationalMatrix.rowEncode (round δ u cap i) := by
  simp only [row,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,
    Option.getD_some,BinaryEllipsoidInitial.indices_replicate_s238r,mapWith_ofFn]
  change encode (List.ofFn (fun j : Fin n=>entry (pairBits (pairBits (pack δ u cap,i.val.bits),j.val.bits))))=_
  simp only [entry_pack,RationalMatrix.rowEncode_eq]
lemma run_pack (δ : Fin n→Fin n→ℚ) (u : ℚ) (cap : ℕ) :
    run (pack δ u cap)=RationalMatrix.encode (round δ u cap) := by
  simp only [run,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinaryEllipsoidInitial.indices_replicate_s238r,mapWith_ofFn]
  change encode (List.ofFn (fun i : Fin n=>row (pairBits (pack δ u cap,i.val.bits))))=_
  simp only [row_pack,RationalMatrix.encode]
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_NormalizationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalization
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
open IntegralAssembly (gammaRat)
lemma count_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) : count (pack δ d M)=d.bits := by
  simp only [count,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    UnaryResources.lengthBits_eq,List.length_replicate]
lemma mesh_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
    mesh (pack δ d M)=BinaryRational.encode ((gammaRat/16)*M/d) := by
  rw [mesh,count_pack,value_bits]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryRational.decode_encode]
lemma cap_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
    cap (pack δ d M)=(Rounding.cap d (IntegralAssembly.gamma/16)).bits := by
  simp only [cap,capArgument,count_pack,value_bits,BinaryRational.decode_encode,IntegralAssembly.cap_rat]
  congr 3
  ring
lemma roundingInput_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
    roundingInput (pack δ d M)=BinaryRoundingMatrix.pack (BinaryDuplicateMatrix.duplicate δ)
      ((gammaRat/16)*M/d) (Rounding.cap d (IntegralAssembly.gamma/16)) := by
  rw [roundingInput,mesh_pack,cap_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryDuplicateMatrix.run_encode,BinaryDuplicateMatrix.twice,←List.replicate_add,BinaryRoundingMatrix.pack]
lemma run_pack_s238r_oai {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
    run (pack δ d M)=RationalMatrix.encode
      (BinaryRoundingMatrix.round (BinaryDuplicateMatrix.duplicate δ) ((gammaRat/16)*M/d)
        (Rounding.cap d (IntegralAssembly.gamma/16))) := by
  rw [run,Function.comp_apply,roundingInput_pack,BinaryRoundingMatrix.run_pack]
end MetricKMedianRecovery.BitMachine.BinaryNormalization

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238r_oai

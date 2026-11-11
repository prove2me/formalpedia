-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:12:14.891209+00:00
-- url     : https://prove2.me/submissions/b503eaae-e1ba-4b6a-ad76-3d2f81e4b507

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitial_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitialAuto_context_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitialProject_extract_output_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalHeight
open scoped BigOperators

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

lemma natCast (n b : ℕ) (hn : n≤2^b) : Height (n:ℚ) b := by
  constructor
  · simpa using hn
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^b)

lemma Height.mul {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q*r) (b+c) := by
  have hn : (q.num*r.num).natAbs≤2^(b+c) := by
    rw [Int.natAbs_mul,pow_add]
    exact Nat.mul_le_mul hq.1 hr.1
  have hd : q.den*r.den≤2^(b+c) := by rw [pow_add]; exact Nat.mul_le_mul hq.2 hr.2
  have he : q*r=((q.num*r.num:ℤ):ℚ)/(q.den*r.den:ℕ) := by
    nth_rw 1 [←Rat.num_div_den q]
    nth_rw 1 [←Rat.num_div_den r]
    push_cast
    exact div_mul_div_comm _ _ _ _
  rw [he]
  exact of_fraction _ _ _ (Nat.mul_pos q.den_pos r.den_pos) hn hd

lemma Height.pow {q : ℚ} {b : ℕ} (hq : Height q b) (k : ℕ) : Height (q^k) (k*b) := by
  induction k with
  | zero => simpa using natCast 1 0 (by norm_num)
  | succ k ih =>
    rw [pow_succ,Nat.succ_mul]
    exact ih.mul hq

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
lemma values_sort (S : Finset (Fin n)) : (values S).sort (·≤·)=(S.sort (·≤·)).map Fin.val := by
  let f : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  have hh := Finset.map_sort f S (·≤·) (·≤·) (fun a _ b _=>show a≤b↔a.val≤b.val from Iff.rfl)
  simpa only [f,Finset.map_eq_image,values,Function.Embedding.coeFn_mk] using hh.symm
lemma encode_eq (S : Finset (Fin n)) : encode S=WordList.encode ((S.sort (·≤·)).map (fun i=>i.val.bits)) := by
  rw [encode,BinaryNatSet.encode,BinaryNatSet.pack,values_sort,List.map_map]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhaseFuel

lemma exponent_le_iff (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (n : ℕ) :
    exponent K Z ≤ n ↔ Z ≤ K^n := by
  have hk : (1:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hz : (0:ℝ) < (Z:ℝ) := by exact_mod_cast hZ
  rw [exponent,Nat.ceil_le,div_le_iff₀ (Real.log_pos hk)]
  rw [←Real.log_pow,Real.log_le_log_iff hz (pow_pos (lt_trans (by norm_num) hk) _)]
  exact_mod_cast Iff.rfl (a := Z ≤ K^n)

lemma to_limit (v Z : ℚ) : exponent (1+v^2) Z + 1 = HistoryPhaseBound.limit v Z := by
  simp only [exponent,HistoryPhaseBound.limit,Rat.cast_add,Rat.cast_one,Rat.cast_pow]

lemma exponent_bound (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (C N : ℕ)
    (hC : 2 ≤ K^C) (hN : Z ≤ 2^N) : exponent K Z ≤ C*N := by
  apply (exponent_le_iff K Z hK hZ _).mpr
  calc
    Z ≤ 2^N := hN
    _ ≤ (K^C)^N := pow_le_pow_left₀ (by norm_num) hC N
    _ = K^(C*N) := (pow_mul K C N).symm

lemma next_min (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (j : ℕ) :
    next K Z (min j (exponent K Z)) = min (j+1) (exponent K Z) := by
  unfold next
  simp only [←exponent_le_iff K Z hK hZ]
  split_ifs <;> omega

end MetricKMedianRecovery.RationalPhaseFuel

namespace MetricKMedianRecovery.RationalHeight
lemma Height.le_bound {q : ℚ} {b : ℕ} (h : Height q b) : q ≤ (2:ℚ)^b := by
  have hd : (1:ℚ) ≤ (q.den:ℚ) := by exact_mod_cast q.den_pos
  have hn : (q.num:ℚ) ≤ (2:ℚ)^b := by
    calc
      (q.num:ℚ) ≤ (q.num.natAbs:ℚ) := by
        calc
          (q.num:ℚ) ≤ |(q.num:ℚ)| := le_abs_self _
          _ = (q.num.natAbs:ℚ) := by simp
      _ ≤ (2:ℚ)^b := by exact_mod_cast h.1
  rw [←Rat.num_div_den q]
  exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℚ)<1) hd)).mpr
    (hn.trans (le_mul_of_one_le_right (by positivity) hd))
end MetricKMedianRecovery.RationalHeight

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFuel
open WordOperations BinaryArithmetic RationalPhaseFuel RationalHeight

lemma step_pack (K Z : ℚ) (q : ℕ) :
    step K (pack Z (K^q) q)=pack Z (K^(next K Z q)) (next K Z q) := by
  simp only [step,threshold,power,count,Function.comp_apply,pack,
    extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode,next]
  split_ifs <;> simp only [pow_succ,List.replicate_succ,mul_comm]

lemma iterate_pack (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (j : ℕ) :
    (step K)^[j] (pack Z 1 0)=
      pack Z (K^(min j (exponent K Z))) (min j (exponent K Z)) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply',ih,step_pack,next_min K Z hK hZ]

lemma pack_length (Z w : ℚ) (q : ℕ) :
    (pack Z w q).length=2*(BinaryRational.encode Z).length+2*(BinaryRational.encode w).length+q+2 := by
  simp only [pack,pairBits_length,List.length_replicate]
  omega

lemma iterate_length (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (C j : ℕ)
    (hj : j ≤ C*((BinaryRational.encode Z).length+1)) :
    ((step K)^[j] (pack Z 1 0)).length ≤
      coefficient K C*((BinaryRational.encode Z).length+1) := by
  rw [iterate_pack K Z hK hZ,pack_length]
  have hm : min j (exponent K Z) ≤ C*((BinaryRational.encode Z).length+1) :=
    (min_le_left _ _).trans hj
  have hp := BinaryRational.encode_height ((BinaryRational.input_height K).pow (min j (exponent K Z)))
  have ht := Nat.mul_le_mul_right (BinaryRational.encode K).length hm
  dsimp only [coefficient]
  nlinarith

lemma iterated_encode (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (C : ℕ) (hC : 2 ≤ K^C) :
    iterated K C (BinaryRational.encode Z)=pack Z (K^(exponent K Z)) (exponent K Z) := by
  have he := exponent_bound K Z hK hZ C (BinaryRational.encode Z).length hC
    (BinaryRational.input_height Z).le_bound
  have hinit : initial (BinaryRational.encode Z)=pack Z 1 0 := rfl
  simp only [iterated,hinit]
  rw [BoundedIteration.run_eq,iterate_pack K Z hK hZ,(fuel C).word_length]
  · simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    rw [Nat.min_eq_right (by nlinarith : exponent K Z ≤ C*((BinaryRational.encode Z).length+1))]
  · intro j hj
    rw [(cap K C).word_length]
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    apply iterate_length K Z hK hZ C j
    simpa only [(fuel C).word_length,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one] using hj

lemma run_encode (v Z : ℚ) (hv : 0 < v) (hZ : 0 < Z) (C : ℕ) (hC : 2 ≤ (1+v^2)^C) :
    run (1+v^2) C (BinaryRational.encode Z)=List.replicate (HistoryPhaseBound.limit v Z) true := by
  have hK : 1 < 1+v^2 := by nlinarith
  simp only [run,iterated_encode _ Z hK hZ C hC,count,Function.comp_apply,pack,discardPrefix_pairBits]
  rw [←to_limit,List.replicate_succ]

end MetricKMedianRecovery.BitMachine.BinaryPhaseFuel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialAuto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialAuto
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
lemma size_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (M : ℚ) (k : ℕ) :
    size (pack distance loc F M k)=List.replicate (d+F.card) true := by
  simp only [size,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.encode_eq,
    Count.run_encode,List.length_map,Finset.length_sort,←List.replicate_add]
lemma threshold_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (M : ℚ) (k : ℕ) :
    threshold (pack distance loc F M k)=BinaryRational.encode (M+8*(d:ℚ)*M) := by
  simp only [threshold,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRational.decode_encode,List.length_replicate]
lemma low_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (M : ℚ) (k : ℕ) :
    low (pack distance loc F M k)=BinaryRational.encode (2/((d+F.card:ℕ):ℚ)^2) := by
  rw [low,size_pack,List.length_replicate]
lemma total_pack (v M : ℚ) (hv : 0<v) (hM : 0<M) (C : ℕ) (hC : 2≤(1+v^2)^C)
    (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (k : ℕ) :
    total v C (pack distance loc F M k)=List.replicate (HistoryPhaseBound.limit v ((M:ℝ)+8*(d:ℝ)*M)+1) true := by
  rw [total,threshold_pack,BinaryPhaseFuel.run_encode v _ hv (by positivity) C hC]
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,List.replicate_succ]
lemma initialInput_pack (v M : ℚ) (hv : 0<v) (hM : 0<M) (C : ℕ) (hC : 2≤(1+v^2)^C)
    (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (k : ℕ) :
    initialInput v C (pack distance loc F M k)=BinaryInitial.pack distance loc F v
      (2/((d+F.card:ℕ):ℚ)^2) M (d+F.card) (d+F.card)
      (HistoryPhaseBound.limit v ((M:ℝ)+8*(d:ℝ)*M)+1) k := by
  rw [initialInput,context_pack_s238,size_pack,total_pack v M hv hM C hC,low_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryInitial.pack]
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialProject
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialProject
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
attribute [local irreducible] BinaryProjection.run BinaryFiniteMachine.after
lemma run_pack_s238_oai [PseudoMetricSpace (Fin m)] (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (v M : ℚ) (C k : ℕ) (hv : 0<v) (hC : 2≤(1+v^2)^C)
    (hd : 0<d) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤d+F.card)
    (hv1 : (v:ℝ)<1/6) (hlohi : 2/((d+F.card:ℕ):ℚ)^2≤8*(d:ℚ)*M)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    run v C (BinaryInitialAuto.pack distance loc F M k)=BinaryFinSet.encode
      (start loc distance F v (2/((d+F.card:ℕ):ℚ)^2) M (d+F.card) (d+F.card)
        (HistoryPhaseBound.limit v ((M:ℝ)+8*(d:ℝ)*M)+1) k).project := by
  rw [run,Function.comp_apply,BinaryInitialAuto.run,Function.comp_apply,
    BinaryInitialAuto.initialInput_pack v M hv hM C hC]
  rw [BinaryInitial.run_pack_s238 distance loc hmetric F v _ M ((1:ℝ)/2^(d+F.card)) _ _ _ k hd
    (Nat.le_add_right _ _) hk hF hM hN (by exact_mod_cast hv) hv1 (by positivity) (by positivity)
    hlohi (by simp only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,le_refl]) hfar hdiam,
    extract_output_s238]
end MetricKMedianRecovery.BitMachine.BinaryInitialProject

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack_s238_oai

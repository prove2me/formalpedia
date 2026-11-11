-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:51.362886+00:00
-- url     : https://prove2.me/submissions/507c51f8-d9d4-44c1-9bc0-ef4d0184c60e

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K029
import Definitions.Def_Q238K030
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFinSet_diff_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySamplingOracle_total_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySamplingOracle_weight_pair_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma copies_encode (n : ℕ) (w : List Bool) :
    RepeatedAppend.copies n (encode [w])=encode (List.replicate n w) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RepeatedAppend.copies,ih,←encode_append,←List.replicate_succ']

lemma repeatWords_pair (u w : List Bool) : repeatWords (pairBits (u,w))=
    encode (List.replicate u.length w) := by
  simp only [repeatWords,extractPrefix_pairBits,discardPrefix_pairBits,copies_encode]
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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalPower
open WordOperations WordList RationalHeight
lemma op_pack (q a : ℚ) (w : List Bool) :
    op (pairBits (BinaryRational.encode q,pairBits (w,BinaryRational.encode a)))=BinaryRational.encode (q*a) := by
  simp only [op,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode]
lemma fold_mul (q a : ℚ) (xs : List Unit) : xs.foldl (fun r _=>q*r) a=q^xs.length*a := by
  induction xs generalizing a with
  | nil=>simp
  | cons x xs ih=>rw [List.foldl_cons,ih,List.length_cons,pow_succ];ring
lemma run_pack (q : ℚ) (n : ℕ) : run (pack q n)=BinaryRational.encode (q^n) := by
  have hi : items (pack q n)=encode ((List.replicate n ()).map (fun _=>[])) := by
    simp only [items,pack,extractPrefix_pairBits,repeatWords_pair,List.length_replicate,List.map_replicate]
  have hd : discardPrefix (pack q n)=BinaryRational.encode q := discardPrefix_pairBits _ _
  unfold run prepared
  rw [hi,hd,CappedFold.run_typed BinaryRational.encode (fun _ : Unit=>[]) (fun a _=>q*a) op
    (BinaryRational.encode q) (cap.word (pack q n)) (fun a _=>op_pack q a [])]
  · simp only [fold_mul,List.length_replicate,mul_one]
  · intro j
    rw [fold_mul,mul_one,cap.word_length]
    have hn : (List.replicate n () |>.take j).length≤n := by simp
    have he := BinaryRational.encode_height ((BinaryRational.input_height q).pow (List.take j (List.replicate n ())).length)
    apply he.trans
    have hq : (BinaryRational.encode q).length≤(pack q n).length := by simp only [pack,pairBits_length,List.length_replicate];omega
    have hN : n≤(pack q n).length := by simp only [pack,pairBits_length,List.length_replicate];omega
    have hm := Nat.mul_le_mul (hn.trans hN) hq
    simp only [capPoly,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith
end MetricKMedianRecovery.BitMachine.BinaryRationalPower

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MenuMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMenu
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
lemma kind_pair (ctx : List Bool) (k j : ℕ) : kind (pairBits (ctx,code k j))=k := by
  simp only [kind,code,extractPrefix_pairBits,discardPrefix_pairBits,value_bits]
attribute [local irreducible] UnaryResources.lengthBits
lemma weight_pair (M E J k j : ℕ) : weight (pairBits (weights M E J,code k j))=
    if k=0 then 1/(3*(M:ℚ)) else if k=1 then 1/(3*((E:ℚ)+1))
    else (1/3)*((1/2:ℚ)^(j+1)/(1-(1/2:ℚ)^J)) := by
  have hp : exponent (pairBits (weights M E J,code k j))++[true]=List.replicate (j+1) true := by
    simp only [exponent,code,discardPrefix_pairBits,List.replicate_succ']
  simp only [weight,first,relative,kind_pair,decide_eq_true_eq,denominator,
    extractPrefix_pairBits,weights,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    UnaryResources.lengthBits_eq,List.length_replicate,value_bits,halfNumerator,halfNormalizer]
  dsimp only [weights] at hp
  rw [hp]
  rw [show pairBits (List.replicate (j+1) true,BinaryRational.encode (1/2))=BinaryRationalPower.pack (1/2) (j+1) from rfl,
    BinaryRationalPower.run_pack]
  rw [show pairBits (List.replicate J true,BinaryRational.encode (1/2))=BinaryRationalPower.pack (1/2) J from rfl,
    BinaryRationalPower.run_pack]
  simp only [BinaryRational.decode_encode]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMenu

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
lemma reference_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) :
    reference (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s))=BinarySamplingState.context Δ S s := by
  simp only [reference,c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    undeleted,deleted,BinarySamplingState.encode,discardPrefix_pairBits,BinaryFinSet.diff_pack_s238,leaves,BinarySamplingState.context]
lemma oracle_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) :
    oracle (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s))=BinarySamplingOracle.pack δ D S Δ s := by
  rw [oracle,reference_pair]
  simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinarySamplingOracle.pack]
end MetricKMedianRecovery.BitMachine.BinarySampler

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_RealizedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
lemma entry_weight (M E J : ℕ) (e : Entry M E J) :
    BinaryMenu.weight (pairBits (BinaryMenu.weights M E J,entryCode M E J e))=menuWeight M E J e := by
  rcases e with i | (i | i) <;> norm_num [entryCode,BinaryMenu.weight_pair,menuWeight]
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Weights
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
lemma stateInput_some (cfg : List Bool) (s : RationalSampling.State n) :
    stateInput (pairBits (cfg,BinarySamplingState.optionBits (some s)))=pairBits (cfg,BinarySamplingState.encode s) := by
  simp only [stateInput,BinarySamplingState.optionBits,Option.toList_some,List.map_cons,List.map_nil,
    extractPrefix_pairBits,discardPrefix_pairBits,encode,head_cons]
lemma state_none : BinarySamplingState.optionBits (n:=n) none=[] := rfl
lemma state_some_ne (s : RationalSampling.State n) : BinarySamplingState.optionBits (some s)≠[] := by
  simp [BinarySamplingState.optionBits,encode,WordList.cons]
lemma weight_pair_s238_oai (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (RationalSampling.State n)) (a : Sampling.Action D M E J) :
    weight (pairBits (context (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits s)),RationalSampling.actionCode D M E J a))=
      RationalSampling.transitionWeight δ D S Δ M E J s a := by
  cases s with
  | none=>
    rcases a with u | (w | ⟨w,e⟩) <;>
      simp only [context,weight,active,c,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,
        Option.getD_some,discardPrefix_pairBits,state_none,decide_true,
        Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false, if_false,kind,actionField,RationalSampling.actionCode,
        field_encode,value_bits,RationalSampling.transitionWeight,reduceCtorEq]
    all_goals norm_num
  | some s=>
    have hc : context (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)))=
        encode [BinarySamplingOracle.pack δ D S Δ s,BinaryRational.encode (RationalSampling.totalWeight δ D S Δ s),BinaryMenu.weights M E J,
          BinarySamplingState.optionBits (some s)] := by
      rw [context,stateInput_some,oracle_pair,BinarySamplingOracle.total_pack_s238]
      simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,discardPrefix_pairBits]
    rw [hc]
    rcases a with u | (w | ⟨w,e⟩) <;>
      simp only [weight,active,c,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
        BinaryRational.decode_encode,state_some_ne,decide_false,
        Bool.not_false,Bool.true_and,decide_eq_true_eq,kind,actionField,RationalSampling.actionCode,discardPrefix_pairBits,field_encode,
        value_bits,base,BinarySamplingOracle.weight_pair_s238,RationalSampling.transitionWeight,reduceCtorEq,RationalSampling.entry_weight]
    all_goals norm_num
end MetricKMedianRecovery.BitMachine.BinarySampler.Weights

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238_oai

-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:06:02.430203+00:00
-- url     : https://prove2.me/submissions/96eb1f80-9b34-4fe2-8a18-af9784c2a972

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K027
import Definitions.Def_Q238K037
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchRandomize_context_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchTape_Count_cut_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryZeroBranch_run_pack_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma lengthBits_encode (ws : List (List Bool)) : lengthBits (encode ws)=ws.length.bits := by
  simp only [lengthBits,Function.comp_apply,Count.run_encode,UnaryResources.lengthBits_eq,List.length_replicate]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawDrop
open WordOperations BinaryArithmetic

lemma step_zero (ws : List Bool) : step (pairBits (Nat.bits 0,ws))=pairBits (Nat.bits 0,ws) := by
  simp only [step,extractPrefix_pairBits,value_bits,ite_true, if_true]
lemma step_succ (i : ℕ) (ws : List Bool) :
    step (pairBits ((i+1).bits,ws))=pairBits (i.bits,ws.tail) := by
  simp only [step,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,Nat.add_sub_cancel,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false, if_false]
lemma drop_iterate (n i : ℕ) (ws : List Bool) (hn : ws.length≤n) :
    discardPrefix (step^[n] (pairBits (i.bits,ws)))=ws.drop i := by
  induction n generalizing i ws with
  | zero=>
    have hw : ws=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst ws
    simp only [Function.iterate_zero_apply,discardPrefix_pairBits,List.drop_nil]
  | succ n ih=>
    cases i with
    | zero=>rw [Function.iterate_fixed (step_zero ws),discardPrefix_pairBits,List.drop_zero]
    | succ i=>
      rw [Function.iterate_succ_apply,step_succ]
      have hl : ws.tail.length≤n := by simp only [List.length_tail]; omega
      rw [ih i ws.tail hl]
      cases ws with
      | nil=>simp only [List.tail_nil,List.drop_nil]
      | cons w ws=>rfl
lemma run_encode (i : ℕ) (ws : List Bool) :
    run (pairBits (i.bits,ws))=ws.drop i := by
  apply drop_iterate
  rw [pairBits_length]
  dsimp only
  omega
end MetricKMedianRecovery.BitMachine.RawDrop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SeedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] width RawTake.run RawDrop.run
lemma raw_length {ds : List ℕ} {b : ℕ} (s : Tensor ds b) : (raw s).length=(ds++[b]).prod := by
  induction ds with
  | nil=>change (List.ofFn (s:Fin b→Bool)).length = b*1
         rw [Nat.mul_one]
         exact List.length_ofFn
  | cons n ns ih=>
    change (List.ofFn (fun i:Fin n=>raw (s i))).flatten.length = ((n::ns)++[b]).prod
    simp only [List.length_flatten,List.map_ofFn,Function.comp_def,ih,List.cons_append,List.prod_cons]
    rw [List.sum_ofFn]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_TensorEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
lemma raw_tensorEquiv (ds : List ℕ) (b : ℕ) (s : Fin (count ds b)→Bool) :
    raw (tensorEquiv ds b s)=List.ofFn s := by
  induction ds with
  | nil=>rfl
  | cons n ns ih=>
    change Fin (n*count ns b)→Bool at s
    change (List.ofFn (fun i:Fin n=>raw (tensorEquiv ns b (fun j=>s (finProdFinEquiv (i,j)))))).flatten =
      List.ofFn (s:Fin (n*count ns b)→Bool)
    simp only [ih]
    conv_rhs => rw [List.ofFn_mul]
    congr 2
    funext i
    congr 1
    funext j
    congr 1
    apply Fin.ext
    change j.val+count ns b*i.val=i.val*count ns b+j.val
    ring
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape
open BinarySeed
variable (q a b L : ℕ)
lemma tensorPair_raw (s : Fin (M q a b L+K a b)→Bool) :
    BinarySeed.raw ((tensorPair q a b L s).1)++BinarySeed.raw ((tensorPair q a b L s).2)=List.ofFn s := by
  change BinarySeed.raw (tensorEquiv _ b _ )++BinarySeed.raw (tensorEquiv _ b _)=List.ofFn s
  rw [raw_tensorEquiv,raw_tensorEquiv]
  rw [List.ofFn_add]
  rfl
lemma raw_layout (s : Fin (M q a b L+K a b)→Bool) : raw q a b L (layout q a b L s)=List.ofFn s := by
  unfold raw layout
  rw [Equiv.trans_apply,Equiv.apply_symm_apply]
  exact tensorPair_raw q a b L s
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape

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
end MetricKMedianRecovery.BitMachine.BinaryBisection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
open BinarySeed BinaryObservableBranch
lemma colorTensor_colors (n : ℕ) (s : Fin (colorCount n)→Bool) :
    colorTensor (colors n s)=tensorEquiv [n] 2 s := by
  funext i
  exact Equiv.symm_apply_apply _ _
lemma raw_colors (n : ℕ) (s : Fin (colorCount n)→Bool) :
    BinarySeed.raw (colorTensor (colors n s))=List.ofFn s := by
  rw [colorTensor_colors]
  exact raw_tensorEquiv [n] 2 s
lemma split_raw (a b : ℕ) (s : Fin (a+b)→Bool) :
    List.ofFn ((split a b s).1)++List.ofFn ((split a b s).2)=List.ofFn s := by
  rw [List.ofFn_add]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRandomize
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Count.run BinaryBisection.logWord RawTake.run RawDrop.run BinaryColorLabel.colors BinaryColorLabel.labels
section Exact
variable {n m : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors0 : Fin n→Fin 3) (label0 : Fin n→Fin m) (q c : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors0 label0 q c extra
lemma nword_pack : nword data=List.replicate n true := by
  simp only [nword,pack,field_encode,List.getElem?_cons_zero,Option.getD_some,RationalMatrix.encode,Count.run_encode,List.length_ofFn]
lemma blog_pack : blog data=List.replicate (Nat.clog 2 m) true := by
  simp only [blog,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFinSet.table,lengthBits_encode,List.length_ofFn,BinaryBisection.logWord_eq,value_bits]
lemma csize_pack : csize data=(BinaryBranchTape.colorCount n).bits := by
  rw [csize,nword_pack,UnaryResources.lengthBits_eq,List.length_replicate,value_bits]
lemma lsize_pack : lsize data=(BinaryBranchTape.labelCount n m).bits := by
  rw [lsize,nword_pack,blog_pack]
  simp only [UnaryResources.lengthBits_eq,List.length_replicate,value_bits]
variable (seed : BinaryBranchTape.Seed n m s.leaves.length)
local notation "input" => pairBits (data,BinaryBranchTape.raw seed)
lemma rest_pack : rest input=BinarySeed.raw (BinaryBranchTape.labelTensor seed.1.2)++
    BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) seed.2 := by
  rw [rest,extractPrefix_pairBits,discardPrefix_pairBits,csize_pack,RawDrop.run_encode]
  have hc : (BinarySeed.raw (BinaryBranchTape.colorTensor seed.1.1)).length=BinaryBranchTape.colorCount n := by
    simp only [BinarySeed.raw_length,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Nat.mul_one]
  rw [BinaryBranchTape.raw,List.append_assoc,←hc,List.drop_left]
lemma tailBits_pack : tailBits input=
    BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) seed.2 := by
  rw [tailBits,extractPrefix_pairBits,lsize_pack,rest_pack,RawDrop.run_encode]
  have hl : (BinarySeed.raw (BinaryBranchTape.labelTensor seed.1.2)).length=BinaryBranchTape.labelCount n m := by
    simp only [BinarySeed.raw_length,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Nat.mul_one]
  rw [←hl,List.drop_left]
end Exact
end MetricKMedianRecovery.BitMachine.BinaryBranchRandomize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RandomizedZeroBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch
open WordOperations WordList BinaryBranchContext
variable {n : ℕ}
lemma run_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors0 : Fin n→Fin 3) (q : ℕ) (extra : List Bool) (seed : Seed n s.leaves.length) :
    run (pairBits (BinaryZeroBranch.pack δ D F S Δ s colors0 q extra,raw seed))=
      BinaryFinSet.encode (BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed.1 i)) q seed.2) := by
  rw [run,BinaryZeroBranch.pack,raw,
    BinaryBranchRandomize.context_pack_s238 δ D F S Δ s colors0 (fun _=>0 : Fin n→Fin 1) q 0 extra (embed seed) (by omega),
    BinaryBranchRandomize.tailBits_pack]
  have he : (fun i=>ColorLabel.label 1 (by omega) ((embed seed).1.2 i))=(fun _=>0 : Fin n→Fin 1) := by
    funext i
    exact Subsingleton.elim _ _
  simp only [he]
  exact BinaryZeroBranch.run_pack_s238 δ D F S Δ s (fun i=>ColorLabel.color (seed.1 i)) q extra seed.2
lemma raw_eq {n p : ℕ} (seed : Seed n p) : raw seed=
    BinarySeed.raw (BinaryBranchTape.colorTensor seed.1)++BinaryCategorical.Tape.raw (p*n) p
      (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p) seed.2 := by
  have hlabel : BinarySeed.raw (BinaryBranchTape.labelTensor (embed seed).1.2)=[] := by
    apply List.eq_nil_of_length_eq_zero
    rw [BinarySeed.raw_length]
    simp [Nat.clog]
  change (BinarySeed.raw (BinaryBranchTape.colorTensor seed.1)++BinarySeed.raw (BinaryBranchTape.labelTensor (embed seed).1.2))++_= _
  rw [hlabel,List.append_nil]
  rfl
lemma raw_layout (n p : ℕ) (seed : Fin (count n p)→Bool) : raw (layout n p seed)=List.ofFn seed := by
  rw [raw_eq]
  simp only [layout,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,
    BinaryBranchTape.raw_colors,BinaryCategorical.Tape.raw_layout]
  exact BinaryBranchTape.split_raw _ _ seed
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_FairPrefix
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
lemma take_ofFn_cast {n N : ℕ} (h : n≤N) (seed : Fin N→Bool) :
    (List.ofFn seed).take n=List.ofFn (fun i:Fin n=>seed (Fin.castLE h i)) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,min_eq_left h]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl
end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix
open WordOperations
lemma run_pack_s238_oai {n K : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors0 : Fin n→Fin 3) (q : ℕ) (extra : List Bool)
    (hK : BinaryRandomizedZeroBranch.count n s.leaves.length≤K) (seed : Fin K→Bool) :
    run (pairBits (BinaryZeroBranch.pack δ D F S Δ s colors0 q extra,List.ofFn seed))=
      let seed':=BinaryRandomizedZeroBranch.layout n s.leaves.length (fun i=>seed (Fin.castLE hK i))
      BinaryFinSet.encode (BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1 i)) q seed'.2) := by
  have hc : BinaryBranchTape.count n 1 s.leaves.length=BinaryRandomizedZeroBranch.count n s.leaves.length := by
    simp only [BinaryBranchTape.count,BinaryBranchTape.labelCount,Nat.clog_one_right,Nat.mul_zero,Nat.add_zero]
  rw [run,Function.comp_apply,BinaryZeroBranch.pack,BinaryBranchTape.Count.cut_pack_s238,hc,
    FiniteSampling.take_ofFn_cast hK,←BinaryRandomizedZeroBranch.raw_layout]
  exact BinaryRandomizedZeroBranch.run_pack δ D F S Δ s colors0 q extra _
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238_oai

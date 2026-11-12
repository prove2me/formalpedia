-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:06:15.138499+00:00
-- url     : https://prove2.me/submissions/85236b23-072a-4252-9d4b-9a3bfe1663e5

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L037
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchRandomize_context_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryObservableBranch_run_pack_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
lemma member_length {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) : w.length≤(encode ws).length := by
  induction ws with
  | nil=>exact False.elim (List.not_mem_nil hw)
  | cons v vs ih=>
    rw [encode,length_cons]
    rcases List.mem_cons.mp hw with rfl|hw
    · omega
    · have h:=ih hw
      omega
end MetricKMedianRecovery.BitMachine.WordList

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LogSubsetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LogPolynomial
lemma binary_exponential (A : ℝ) : ∃ d : ℕ, ∀ N b : ℕ,
    (b:ℝ)≤A*Real.log ((N:ℝ)+2) → 2^b≤(N+2)^d := by
  refine ⟨⌈A*Real.log 2⌉₊,?_⟩
  intro N b hb
  have hN : 0<(N:ℝ)+2 := by positivity
  have hlog : 0≤Real.log ((N:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have h2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hm : (b:ℝ)*Real.log 2 ≤ (⌈A*Real.log 2⌉₊:ℝ)*Real.log ((N:ℝ)+2) := by
    calc
      _ ≤ (A*Real.log ((N:ℝ)+2))*Real.log 2 := mul_le_mul_of_nonneg_right hb h2
      _ = (A*Real.log 2)*Real.log ((N:ℝ)+2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hlog
  have hh := Real.exp_le_exp.mpr hm
  simp only [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2),Real.exp_log hN] at hh
  exact_mod_cast hh
end MetricKMedianRecovery.LogPolynomial
namespace MetricKMedianRecovery.BitMachine.BinaryBlueStates
open WordOperations WordList
lemma source_capacity (A : ℝ) : ∃ d : ℕ, ∀ {n : ℕ} (ctx : List Bool) (U : Finset (Fin n)) (N : ℕ),
    N≤(pairBits (ctx,BinaryFinSet.encode U)).length →
    (U.card:ℝ)≤A*Real.log ((N:ℝ)+2) →
    2^U.card*(2*(BinaryFinSet.encode U).length+2)≤((pairBits (ctx,BinaryFinSet.encode U)).length+1)^d := by
  obtain ⟨e,he⟩:=LogPolynomial.binary_exponential A
  refine ⟨2*e+2,?_⟩
  intro n ctx U N hN hU
  let L:=(pairBits (ctx,BinaryFinSet.encode U)).length
  have hL : 1≤L := by dsimp [L];simp only [pairBits_length];omega
  have hk : (BinaryFinSet.encode U).length≤L := by dsimp [L];simp only [pairBits_length];omega
  have hd : N+2≤(L+1)^2 := by nlinarith
  have hp: 2^U.card≤(L+1)^(2*e) := by
    calc
      _ ≤ (N+2)^e := he N U.card hU
      _ ≤ ((L+1)^2)^e := Nat.pow_le_pow_left hd e
      _ = _ := by rw [pow_mul]
  have hx : 2*(BinaryFinSet.encode U).length+2≤(L+1)^2 := by nlinarith
  calc
    _ ≤ (L+1)^(2*e)*(L+1)^2 := Nat.mul_le_mul hp hx
    _ = _ := by rw [pow_add]
end MetricKMedianRecovery.BitMachine.BinaryBlueStates

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_ObservableCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram
lemma source_run (A : ℝ) : ∃ d : ℕ, ∀ {n m : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (label : Fin n→Fin m) (q c : ℕ) (extra : List Bool) (r0 y0 : Fin n) (N : ℕ),
    N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) →
    ∀ bits,
    run d (pairBits (pack δ D F S Δ s colors label q c extra,
      BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
        (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) bits))=
    BinaryFinSet.encode (output δ D F S Δ s colors label q c r0 y0 bits) := by
  obtain ⟨d,hd⟩:=BinaryBlueStates.source_capacity A
  refine ⟨d,?_⟩
  intro n m δ D F S Δ s colors label q c extra r0 y0 N hN hm bits
  apply run_pack_s238r δ D F S Δ s colors label q c extra d r0 y0 _ bits
  have hx:=hd (BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits)
    ((S\s.deleted).filter (fun i=>colors i=2)) F label (rationalScore δ D S Δ s) Finset.univ c)
      (Finset.univ : Finset (Fin m)) N
  apply (by simpa only [Finset.card_univ,Fintype.card_fin] using hx)
  · have he : extra.length≤(BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits)
        ((S\s.deleted).filter (fun i=>colors i=2)) F label (rationalScore δ D S Δ s) Finset.univ c).length :=
      member_length (by simp)
    simp only [pairBits_length]
    omega
  · exact hm
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch
open WordOperations WordList BinaryBranchContext BinaryObservableBranch
lemma source_run_s238r_oai (A : ℝ) : ∃ d : ℕ, ∀ {n b : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (colors0 : Fin n→Fin 3)
    (label0 : Fin n→Fin b) (q c : ℕ) (extra : List Bool) (r0 y0 : Fin n) (N : ℕ),
    N≤extra.length → (b:ℝ)≤A*Real.log ((N:ℝ)+2) → (hb0 : 0<b) →
    ∀ seed : BinaryBranchTape.Seed n b s.leaves.length,
    run d (pairBits (pack δ D F S Δ s colors0 label0 q c extra,BinaryBranchTape.raw seed))=
    BinaryFinSet.encode (output δ D F S Δ s (fun i=>ColorLabel.color (seed.1.1 i))
      (fun i=>ColorLabel.label b hb0 (seed.1.2 i)) q c r0 y0 seed.2) := by
  obtain ⟨d,hd⟩:=BinaryObservableBranch.source_run A
  refine ⟨d,?_⟩
  intro n b δ D F S Δ s colors0 label0 q c extra r0 y0 N hN hb hb0 seed
  rw [run,BinaryBranchRandomize.context_pack_s238r δ D F S Δ s colors0 label0 q c extra seed hb0,
    BinaryBranchRandomize.tailBits_pack]
  exact hd δ D F S Δ s _ _ q c extra r0 y0 N hN hb seed.2
end MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run_s238r_oai

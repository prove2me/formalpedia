-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:03:45.121524+00:00
-- url     : https://prove2.me/submissions/8bc7974f-a783-460c-9bb4-699e6b12b27b

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L037
import Theorems.Thm_OAI_MetricKMedianRecovery_IntegralAssembly_gamma_pos_s238r

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
namespace MetricKMedianRecovery.BitMachine.RawTake
open WordOperations BinaryArithmetic
attribute [local irreducible] number RawDrop.run
lemma run_pack (n : ℕ) (ws : List Bool) : run (pairBits (n.bits,ws))=ws.take n := by
  simp only [run,number,extractPrefix_pairBits,discardPrefix_pairBits,UnaryResources.lengthBits_eq,value_bits,
    RawDrop.run_encode,List.reverse_drop,List.reverse_reverse,List.length_reverse]
  rw [show ws.length-(ws.length-n)=min n ws.length by omega]
  exact List.take_eq_take_min.symm
end MetricKMedianRecovery.BitMachine.RawTake

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
open BinarySeed BinaryObservableBranch
lemma split_raw (a b : ℕ) (s : Fin (a+b)→Bool) :
    List.ofFn ((split a b s).1)++List.ofFn ((split a b s).2)=List.ofFn s := by
  rw [List.ofFn_add]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_BoundedNatWord
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BoundedNatWord
open WordOperations
attribute [local irreducible] RawTake.run RawUnary.run counter
lemma run_pack (P : Polynomial ℕ) (n : ℕ) (w : List Bool) :
    run P (pairBits (n.bits,w))=List.replicate (min n (P.eval w.length)) true := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits,RawTake.run_pack,RawUnary.run,
    List.length_take,(counter P).word_length]
lemma run_exact (P : Polynomial ℕ) (n : ℕ) (w : List Bool) (hn : n≤P.eval w.length) :
    run P (pairBits (n.bits,w))=List.replicate n true := by
  rw [run_pack,min_eq_left hn]
end MetricKMedianRecovery.BitMachine.BoundedNatWord

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PolynomialProduct
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.GlobalAssembly

open LocalSearch Sampling FiniteSampling IntegralAssembly IndexedCopies

lemma cap_polynomial (n N : ℕ) (h : n ≤ N) :
    Rounding.cap n (gamma/16) ≤ (⌈20/(gamma/16)⌉₊+2)*(N+2)^2 := by
  have he : 0 < gamma/16 := div_pos gamma_pos_s238r (by norm_num)
  have hn : (n:ℝ)^2 ≤ ((N:ℝ)+2)^2 := by
    have h' : (n:ℝ) ≤ N := by exact_mod_cast h
    nlinarith [Nat.cast_nonneg (α := ℝ) n,Nat.cast_nonneg (α := ℝ) N]
  have hc : ⌈20*(n:ℝ)^2/(gamma/16)⌉₊ ≤ ⌈20/(gamma/16)⌉₊*(N+2)^2 := by
    apply Nat.ceil_le.mpr
    push_cast
    calc
      _ = (20/(gamma/16))*(n:ℝ)^2 := by ring
      _ ≤ (20/(gamma/16))*((N:ℝ)+2)^2 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (sq_nonneg _)
  have hb : 1 ≤ (N+2)^2 := one_le_pow₀ (by omega)
  unfold Rounding.cap
  nlinarith

end MetricKMedianRecovery.GlobalAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Parameters
open WordOperations WordList BinaryArithmetic Polynomial RadiusMenus Sampling Sampling.Comparison
open BinaryOpeningPayment (field field_computes field_encode)
lemma thirdSize_eq (m : ℕ) : thirdSize mainKappa m=1+2000000*m := by
  unfold thirdSize mainKappa
  have he : 2*(m:ℝ)/(1/1000000)=(2000000*m:ℕ) := by push_cast <;> ring
  rw [he, Nat.ceil_natCast]
attribute [local irreducible] BoundedNatWord.run bound
variable {n : ℕ}
lemma pack_resources (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    m≤bound.eval (pack δ D F S Δ P m).length ∧ Δ≤bound.eval (pack δ D F S Δ P m).length := by
  let L := (pack δ D F S Δ P m).length
  have hn : n≤L := by
    have hh:=member_length (show List.replicate n true∈[RationalMatrix.encode δ,List.replicate n true,
      BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,Δ.bits,BinaryRational.encode P,m.bits] by simp)
    simpa only [L,pack,List.length_replicate] using hh
  have hd : D.card≤L := (Finset.card_le_univ D).trans (by simpa only [Finset.card_univ,Fintype.card_fin] using hn)
  have hc:=GlobalAssembly.cap_polynomial D.card L hd
  simp only [bound,eval_add,eval_X,eval_mul,eval_C,eval_pow,eval_ofNat]
  exact ⟨(hm.trans hn).trans (Nat.le_add_right _ _),(hΔ.trans hc).trans (Nat.le_add_left _ _)⟩
lemma unary_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    unary 7 (pack δ D F S Δ P m)=List.replicate m true ∧
    unary 5 (pack δ D F S Δ P m)=List.replicate Δ true := by
  obtain ⟨hm',hd'⟩:=pack_resources δ D F S Δ P m hm hΔ
  constructor
  · simpa only [unary,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      using BoundedNatWord.run_exact bound m (pack δ D F S Δ P m) hm'
  · simpa only [unary,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      using BoundedNatWord.run_exact bound Δ (pack δ D F S Δ P m) hd'
lemma Jword_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    Jword (pack δ D F S Δ P m)=List.replicate (thirdSize mainKappa m) true := by
  rw [Jword,(unary_pack δ D F S Δ P m hm hΔ).1,List.length_replicate,thirdSize_eq]
  have he (k : ℕ) : RepeatedAppend.copies k (List.replicate 2000000 true)=List.replicate (2000000*k) true := by
    induction k with
    | zero=>rfl
    | succ k ih=>simp only [RepeatedAppend.copies,ih,←List.replicate_add]; congr 1
  rw [he]
  exact (List.replicate_add 1 _ true).symm
lemma precision_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    precision (pack δ D F S Δ P m)=List.replicate (integralPrecision D (Δ:ℝ) m) true := by
  rw [precision,(unary_pack δ D F S Δ P m hm hΔ).2,Jword_pack δ D F S Δ P m hm hΔ]
  simp only [nword,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFinSet.encode_eq,Count.run_encode,List.length_map,Finset.length_sort,integralPrecision,
    Nat.ceil_natCast,precisionBits,M,E,←List.replicate_add]
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations WordList Sampling.Comparison BinaryArithmetic
attribute [local irreducible] mword precision sampleCount raw extra RawTake.run RawDrop.run
lemma layout_raw {n : ℕ} (D : Finset (Fin n)) (Δ m : ℕ) (bits : Fin (count D Δ m)→Bool) :
    BinarySeed.raw (ds:=[2*m]) (layout D Δ m bits).1++List.ofFn (layout D Δ m bits).2=List.ofFn bits := by
  change BinarySeed.raw (BinarySeed.tensorEquiv [2*m] (integralPrecision D (Δ:ℝ) m)
    ((BinaryBranchTape.split (2*m*integralPrecision D (Δ:ℝ) m) (BinaryRecovery.tapeSize (n+1)) bits).1)) ++
      List.ofFn (BinaryBranchTape.split (2*m*integralPrecision D (Δ:ℝ) m) (BinaryRecovery.tapeSize (n+1)) bits).2=_
  have hh := BinarySeed.raw_tensorEquiv [2*m] (integralPrecision D (Δ:ℝ) m)
    ((BinaryBranchTape.split (2*m*integralPrecision D (Δ:ℝ) m) (BinaryRecovery.tapeSize (n+1)) bits).1)
  exact (congrArg (fun xs=>xs++List.ofFn (BinaryBranchTape.split (2*m*integralPrecision D (Δ:ℝ) m)
    (BinaryRecovery.tapeSize (n+1)) bits).2) hh).trans (BinaryBranchTape.split_raw _ _ _)
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (g bits : List Bool) (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
include hm hΔ in
lemma sampleCount_pack : sampleCount (pack δ D F S Δ P m g bits)=(2*m*integralPrecision D (Δ:ℝ) m).bits := by
  have hp : params (pack δ D F S Δ P m g bits)=BinarySampler.Parameters.pack δ D F S Δ P m := by
    simp only [params,pack,extractPrefix_pairBits]
  simp only [sampleCount,mword,precision,Function.comp_apply,hp,
    (BinarySampler.Parameters.unary_pack δ D F S Δ P m hm hΔ).1,
    BinarySampler.Parameters.precision_pack δ D F S Δ P m hm hΔ,List.length_replicate]
include hm hΔ in
lemma repack_pack_s238r_oai (seed : Fin (count D Δ m)→Bool) :
    repack (pack δ D F S Δ P m g (List.ofFn seed))=
      BinaryIntegralRecovery.pack δ D F S Δ P m g (layout D Δ m seed).1 (List.ofFn (layout D Δ m seed).2) := by
  rw [repack,sampleCount_pack δ D F S Δ P m g _ hm hΔ]
  simp only [pack,raw,extra,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    RawTake.run_pack,RawDrop.run_encode]
  rw [←layout_raw D Δ m seed]
  have hl : (BinarySeed.raw (ds:=[2*m]) (layout D Δ m seed).1).length=2*m*integralPrecision D (Δ:ℝ) m := by
    simpa only [List.cons_append,List.nil_append,List.prod_cons,List.prod_singleton,List.prod_nil,Nat.mul_one] using BinarySeed.raw_length (ds:=[2*m]) (layout D Δ m seed).1
  rw [←hl,List.take_left,List.drop_left]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack_s238r_oai

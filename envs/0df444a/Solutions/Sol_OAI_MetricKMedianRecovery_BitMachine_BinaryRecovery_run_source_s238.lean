-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:09:15.317454+00:00
-- url     : https://prove2.me/submissions/479a9e46-1394-40da-be1f-592b71475f36

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K040
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMetricBest_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRandomizedZeroBranch_Prefix_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_atBranch_source_s238

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
lemma mapWith_ofFn {n : ℕ} (f : List Bool → List Bool) (d : List Bool) (g : Fin n → List Bool) :
    mapWith f (pairBits (d,encode (List.ofFn g)))=encode (List.ofFn (fun i=>f (pairBits (d,g i)))) := by
  rw [mapWith_encode,List.map_ofFn]
  rfl
end WordList
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
open WordOperations
namespace WordList
namespace Flatten

lemma operation_eq (ctx a w : List Bool) : Fold.operation op ctx a w=a++w := by
  simp only [Fold.operation,op,Fold.accum,Find.item,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits]
lemma fold_eq (ws : List (List Bool)) (ctx a : List Bool) :
    ws.foldl (Fold.operation op ctx) a=a++ws.flatten := by
  induction ws generalizing a with
  | nil=>simp only [List.foldl_nil,List.flatten_nil,List.append_nil]
  | cons w ws ih=>simp only [List.foldl_cons,operation_eq,ih,List.flatten_cons,List.append_assoc]
lemma length_flatten_le (ws : List (List Bool)) : ws.flatten.length≤(encode ws).length := by
  induction ws with
  | nil=>rfl
  | cons w ws ih=>simp only [List.flatten_cons,List.length_append,encode,length_cons]; omega
lemma run_encode (ws : List (List Bool)) : run (encode ws)=ws.flatten := by
  unfold run
  rw [Fold.run_encode op (3*Polynomial.X+3) [] [] ws (encode ws).length]
  · simp only [fold_eq,List.nil_append]
  · intro n
    simp only [fold_eq,List.nil_append]
    exact (length_flatten_le _).trans (length_encode_take ws n)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
lemma encode_flatMap {α : Type*} (ws : List α) (f : α → List (List Bool)) :
    encode (ws.flatMap f)=(ws.map (fun x=>encode (f x))).flatten := by
  induction ws with
  | nil=>rfl
  | cons a ws ih=>simp only [List.flatMap_cons,encode_append,List.map_cons,List.flatten_cons,ih]
end Flatten
lemma flatMapWith_encode (f : List Bool → List Bool) (ctx : List Bool) (ws : List (List Bool))
    (g : List Bool → List (List Bool)) (h : ∀ w∈ws, f (pairBits (ctx,w))=encode (g w)) :
    flatMapWith f (pairBits (ctx,encode ws))=encode (ws.flatMap g) := by
  simp only [flatMapWith,Function.comp_apply,mapWith_encode,Flatten.run_encode,Flatten.encode_flatMap]
  congr 1
  apply List.map_congr_left
  exact h
end WordList
end MetricKMedianRecovery.BitMachine
namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList
lemma crossWith_encode (f : List Bool → List Bool) (xs ys : List (List Bool)) :
    crossWith f (pairBits (encode xs,encode ys))=
      encode (xs.flatMap (fun x=>ys.map (fun y=>f (pairBits (x,y))))) := by
  unfold crossWith
  simp only [extractPrefix_pairBits,discardPrefix_pairBits]
  apply flatMapWith_encode
  intro w _
  simp only [extractPrefix_pairBits,discardPrefix_pairBits,mapWith_encode]
lemma cross_encode (xs ys : List (List Bool)) :
    cross (pairBits (encode xs,encode ys))=encode (xs.flatMap (fun x=>ys.map (fun y=>pairBits (x,y)))) :=
  crossWith_encode id xs ys
end WordList
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma flatMap_ofFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : α → List β) :
    (List.ofFn f).flatMap g=(List.ofFn (fun j=>g (f j))).flatten := by
  change ((List.ofFn f).map g).flatten=_
  rw [List.map_ofFn]
  rfl
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] RawTake.run BinaryEllipsoidInitial.indices
attribute [local irreducible] mapWith
attribute [local irreducible] src zeros labels qbits cword bword
section Exact
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool) (q c b : ℕ)
local notation "data" => pairBits (pack δ D F S Δ s m extra raw,choiceBits q c b)
lemma qbits_pack : qbits data=q.bits := by simp only [qbits,choiceBits,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
lemma zeros_pack (a : ℕ) [NeZero a] : zeros data=BinaryFinSet.table (fun _:Fin n=>(0:Fin a)) := by
  simp only [zeros,src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryEllipsoidInitial.indices_replicate_s238,mapWith_ofFn,BinaryFinSet.table]
  rfl
lemma zeroContext_pack : zeroContext data=BinaryZeroBranch.pack δ D F S Δ s (fun _=>0) q extra := by
  rw [zeroContext,zeros_pack δ D F S Δ s m extra raw q c b 3,qbits_pack]
  simp only [src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryZeroBranch.pack,BinaryBranchContext.pack]
  rfl
end Exact
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] context zeroContext BinaryRandomizedBranch.Prefix.run BinaryRandomizedZeroBranch.Prefix.run
attribute [local irreducible] mapWith
attribute [local irreducible] metricContext candidateWords
section Exact
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool)
local notation "data" => pack δ D F S Δ s m extra raw
lemma range_pack : range data=encode (List.ofFn (fun q:Fin (n+1)=>q.val.bits)) := by
  simp only [range,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    ←List.replicate_one (a:=true),←List.replicate_add,BinaryEllipsoidInitial.indices_replicate_s238]
lemma blueRange_pack : blueRange data=encode (List.ofFn (fun b:Fin m=>b.val.bits)) := by
  simp only [blueRange,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryEllipsoidInitial.indices_replicate_s238]
lemma choices_pack : choices data=encode ((List.ofFn (fun q:Fin (n+1)=>q)).flatMap (fun q=>
    (List.ofFn (fun c:Fin (n+1)=>c)).flatMap (fun c=>List.ofFn (fun b:Fin m=>choiceBits q.val c.val b.val)))) := by
  rw [choices,range_pack,blueRange_pack,cross_encode,cross_encode]
  simp only [flatMap_ofFn,List.map_flatten,List.map_ofFn,Function.comp_def,choiceBits]
lemma candidateWords_pack (d : ℕ) : candidateWords d data=encode
    ((List.ofFn (fun q:Fin (n+1)=>atZero (pairBits (data,q.val.bits))))++
      (List.ofFn (fun q:Fin (n+1)=>q)).flatMap (fun q=>(List.ofFn (fun c:Fin (n+1)=>c)).flatMap
        (fun c=>List.ofFn (fun b:Fin m=>atBranch d (pairBits (data,choiceBits q.val c.val b.val)))))) := by
  rw [candidateWords,range_pack,choices_pack,mapWith_ofFn,mapWith_encode,←encode_append]
  simp only [List.map_flatMap,List.map_ofFn,Function.comp_def]
lemma metricContext_pack : metricContext data=BinaryMetricBest.context δ D := by
  simp only [metricContext,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryMetricBest.context]
lemma run_of_candidates (d : ℕ) (xs : List (Finset (Fin n)))
    (hxs : candidateWords d data=encode (xs.map BinaryFinSet.encode)) :
    run d data=BinaryFinSet.encode (BinaryMetricBest.best δ D S xs) := by
  rw [run,metricContext_pack,hxs]
  have he : field 3 data=BinaryFinSet.encode S := by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [he]
  exact BinaryMetricBest.run_pack_s238 δ D S xs
end Exact
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RecoveryTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] atBranch atZero context zeroContext
  BinaryRandomizedBranch.Prefix.run BinaryRandomizedZeroBranch.Prefix.run
  BinaryObservableBranch.output BinaryZeroBranch.output ColorLabel.label ColorLabel.color
  BinaryBranchTape.layout BinaryRandomizedZeroBranch.layout

lemma atZero_context {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool) (q : ℕ) :
    atZero (pairBits (pack δ D F S Δ s m extra raw,q.bits))=
      BinaryRandomizedZeroBranch.Prefix.run (pairBits (BinaryZeroBranch.pack δ D F S Δ s (fun _=>0) q extra,raw)) := by
  rw [atZero]
  have hpro : promote (pairBits (pack δ D F S Δ s m extra raw,q.bits))=
      pairBits (pack δ D F S Δ s m extra raw,choiceBits q 0 0) := by
    simp only [promote,extractPrefix_pairBits,discardPrefix_pairBits,choiceBits,Nat.zero_bits]
  rw [hpro,zeroContext_pack]
  congr 1
  simp only [src,Function.comp_apply,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma atZero_pack {n H : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (m : ℕ) (extra : List Bool) (hn : n≤H) (hH : 1≤H)
    (hp : s.leaves.length≤H) (q : Fin (n+1)) (seed : Fin (tapeSize H)→Bool) :
    atZero (pairBits (pack δ D F S Δ s m extra (List.ofFn seed),q.val.bits))=
      let seed':=zeroSeed hn hH hp seed
      BinaryFinSet.encode (BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1 i)) q.val seed'.2) := by
  rw [atZero_context]
  simpa only [zeroSeed] using BinaryRandomizedZeroBranch.Prefix.run_pack_s238 δ D F S Δ s
    (fun _=>(0:Fin 3)) q.val extra (zeroCount_bound hn hH hp) seed
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape Completion FiniteSampling
variable {n m H : ℕ}
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s : RationalSampling.State n) (hn : n≤H) (hm : m≤H) (hH : 1≤H)
  (hp : s.leaves.length≤H) (r0 y0 : Fin n) (seed : Fin (tapeSize H)→Bool)
lemma run_source_s238_oai (A : ℝ) : ∃ d : ℕ, ∀ {n m H : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (extra : List Bool)
    (r0 y0 : Fin n) (N : ℕ), N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) →
    (hn : n≤H) → (hm : m≤H) → (hH : 1≤H) → (hp : s.leaves.length≤H) →
    ∀ (seed : Fin (tapeSize H)→Bool),
    run d (pack δ D F S Δ s m extra (List.ofFn seed))=
      BinaryFinSet.encode (result δ D F S Δ s hn hm hH hp r0 y0 seed) := by
  obtain ⟨d,hd⟩:=atBranch_source_s238 A
  refine ⟨d,?_⟩
  intro n m H δ D F S Δ s extra r0 y0 N hN hlog hn hm hH hp seed
  apply run_of_candidates
  rw [candidateWords_pack]
  unfold candidates
  simp only [List.map_append,List.map_flatMap,List.map_ofFn,Function.comp_def]
  congr 2
  · apply congrArg List.ofFn
    funext q
    exact atZero_pack δ D F S Δ s m extra hn hH hp q seed
  · apply List.flatMap_congr
    intro q _
    apply List.flatMap_congr
    intro c _
    congr 1
    funext b
    exact hd δ D F S Δ s extra r0 y0 N hN hlog hn hm hp q c b seed
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238_oai

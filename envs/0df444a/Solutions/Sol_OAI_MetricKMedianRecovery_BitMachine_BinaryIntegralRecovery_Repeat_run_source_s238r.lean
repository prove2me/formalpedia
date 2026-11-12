-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:09:42.205193+00:00
-- url     : https://prove2.me/submissions/ff913d6b-bb49-4da5-94c4-42a08c948563

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L040
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_demandWord_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_run_source_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMetricBest_run_pack_s238r

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
lemma mapWith_ofFn {n : ℕ} (f : List Bool → List Bool) (d : List Bool) (g : Fin n → List Bool) :
    mapWith f (pairBits (d,encode (List.ofFn g)))=encode (List.ofFn (fun i=>f (pairBits (d,g i)))) := by
  rw [mapWith_encode,List.map_ofFn]
  rfl
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_MatrixRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows
open WordOperations WordList BinaryArithmetic
lemma slice_flatten {α : Type*} (xs : List (List α)) (n : ℕ) (h : ∀ x∈xs,x.length=n) (i : ℕ) :
    (xs.flatten.drop (n*i)).take n=(xs[i]?).getD [] := by
  induction xs generalizing i with
  | nil=>simp only [List.flatten_nil,List.drop_nil,List.take_nil,List.getElem?_nil,Option.getD_none]
  | cons x xs ih=>
    have hx:=h x List.mem_cons_self
    have ht : ∀ y∈xs,y.length=n := fun y hy=>h y (List.mem_cons_of_mem _ hy)
    cases i with
    | zero=>simp only [Nat.mul_zero,List.drop_zero,List.flatten_cons,List.getElem?_cons_zero,Option.getD_some]; rw [←hx,List.take_left]
    | succ i=>
      rw [Nat.mul_succ,Nat.add_comm,←List.drop_drop,List.flatten_cons,←hx,List.drop_left]
      simpa only [hx,List.getElem?_cons_succ] using ih ht i
attribute [local irreducible] offset Drop.run Take.run
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows

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
lemma shape_tail (n : ℕ) (ns : List ℕ) : WordList.tail (shape (n::ns))=shape ns := by
  simp only [shape,List.map_cons,encode,tail_cons]
lemma product_shape (ds : List ℕ) : product ds.length (shape ds)=ds.prod.bits := by
  induction ds with
  | nil=>rfl
  | cons d ds ih=>simp only [List.length_cons,product,shape,List.map_cons,encode,head_cons,tail_cons,
      UnaryResources.lengthBits_eq,List.length_replicate,value_bits,List.prod_cons] at ih ⊢; rw [ih,value_bits]
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
lemma chunk_tensor (n : ℕ) (ns : List ℕ) (b : ℕ) (s : Tensor (n::ns) b) (i : Fin n) :
    chunk ns.length (pairBits (pairBits (shape (n::ns++[b]),raw s),i.val.bits))=raw (s i) := by
  have hw : width ns.length (pairBits (pairBits (shape (n::ns++[b]),raw s),i.val.bits))=(ns++[b]).prod.bits := by
    rw [width,extractPrefix_pairBits,extractPrefix_pairBits,List.cons_append,shape_tail]
    rw [show ns.length+1=(ns++[b]).length by simp,product_shape]
  rw [chunk,hw,discardPrefix_pairBits,value_bits,extractPrefix_pairBits,discardPrefix_pairBits,
    RawDrop.run_encode,RawTake.run_pack]
  rw [value_bits]
  change ((List.ofFn (fun j=>raw (s j))).flatten.drop ((ns++[b]).prod*i.val)).take (ns++[b]).prod=raw (s i)
  rw [BinaryInputParser.Rows.slice_flatten _ _ (by
    intro x hx; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hx; exact raw_length (s j)),List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList
attribute [local irreducible] WordList.mapWith
attribute [local irreducible] indices chunk
lemma rows_tensor {t b : ℕ} (s : Fin t→Fin b→Bool) :
    rows (pairBits (shape [t,b],raw (ds:=[t]) s))=encode (List.ofFn (fun i=>List.ofFn (s i))) := by
  have hi : indices (pairBits (shape [t,b],raw (ds:=[t]) s))=encode (List.ofFn (fun i:Fin t=>i.val.bits)) := by
    simp only [indices,extractPrefix_pairBits,shape,List.map_cons,List.map_nil,encode,head_cons]
    exact BinaryEllipsoidInitial.indices_replicate_s238r t
  rw [rows,hi,mapWith_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact chunk_tensor t [] b s i
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open WordOperations WordList Sampling.Comparison
attribute [local irreducible] extra Fair.raw Fair.demandWord Fair.run BinaryMetricBest.run RawUnary.run BinarySeed.rows
  BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
attribute [local irreducible] mapWith
lemma run_of_candidates (Q : Polynomial ℕ) (d : ℕ) (data : List Bool) {n : ℕ}
    (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n)))
    (hmetric : metricContext data=BinaryMetricBest.context δ D)
    (hS : src 4 data=BinaryFinSet.encode S)
    (hxs : candidates Q d data=encode (xs.map BinaryFinSet.encode)) :
    run Q d data=BinaryFinSet.encode (BinaryMetricBest.best δ D S xs) := by
  rw [run,hmetric,hS,hxs]
  exact BinaryMetricBest.run_pack_s238r δ D S xs
variable {n : ℕ}
lemma rows_pack (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) (g : List Bool)
    (seed : Fin (Q.eval g.length)→Fin (Fair.count D Δ m)→Bool) :
    rows Q (Fair.pack δ D F S Δ P m g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
      encode (List.ofFn (fun i=>List.ofFn (seed i))) := by
  have hr : rword Q (Fair.pack δ D F S Δ P m g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
      List.replicate (Q.eval g.length) true := by
    simp only [rword,RawUnary.run,PolynomialCounter.word_length,extra,Fair.pack,Function.comp_apply,
      extractPrefix_pairBits,discardPrefix_pairBits]
  have hb : bword (Fair.pack δ D F S Δ P m g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
      List.replicate (Fair.count D Δ m) true := by
    rw [bword,Function.comp_apply,RawUnary.run,Fair.demandWord_pack_s238r δ D F S Δ P m g _ hm hΔ]
  rw [rows,hr,hb]
  simp only [Fair.raw,Fair.pack,Function.comp_apply,discardPrefix_pairBits]
  exact BinarySeed.rows_tensor seed
lemma candidates_of_rows (Q : Polynomial ℕ) (d : ℕ) (data ctx : List Bool) {t b n : ℕ}
    (seed : Fin t→Fin b→Bool) (f : Fin t→Finset (Fin n))
    (hr : rows Q data=encode (List.ofFn (fun i=>List.ofFn (seed i))))
    (hx : context data=ctx)
    (hf : ∀ i,atSeed d (pairBits (ctx,List.ofFn (seed i)))=BinaryFinSet.encode (f i)) :
    candidates Q d data=encode ((List.ofFn f).map BinaryFinSet.encode) := by
  rw [candidates,hr,hx,mapWith_ofFn,List.map_ofFn]
  exact congrArg encode (congrArg List.ofFn (funext hf))
lemma atSeed_pack {n : ℕ} (d : ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (P : ℚ) (m : ℕ) (g bits : List Bool) :
    atSeed d (pairBits (pairBits (BinarySampler.Parameters.pack δ D F S Δ P m,g),bits))=
      Fair.run d (Fair.pack δ D F S Δ P m g bits) := by
  simp only [atSeed,Function.comp_apply,atSeedInput,extractPrefix_pairBits,discardPrefix_pairBits,Fair.pack]
lemma run_source_s238r_oai (A : ℝ) : ∃ d : ℕ, ∀ (Q : Polynomial ℕ) {n : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n),
    Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16) → ∀ (extra : List Bool) (N : ℕ),
    N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) → ∀ (r0 y0 : Fin n)
    (seed : Fin (Q.eval extra.length)→Fin (Fair.count D Δ m)→Bool),
    run Q d (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=
      BinaryFinSet.encode (output δ D F S Δ P m hm r0 y0 (Q.eval extra.length) seed) := by
  obtain ⟨d,hd⟩:=Fair.run_source_s238r A
  refine ⟨d,?_⟩
  intro Q n δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 seed
  have hx : context (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=
      pairBits (BinarySampler.Parameters.pack δ D F S Δ P m,extra) := by
    simp only [context,Fair.pack,BinaryIntegralRecovery.extra,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  have hc : candidates Q d (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=
      encode ((List.ofFn (fun i=>Fair.output δ D F S Δ P m hm r0 y0 (seed i))).map BinaryFinSet.encode) := by
    apply candidates_of_rows Q d _ _ seed _ (rows_pack Q δ D F S Δ P m hm hΔ extra seed) hx
    intro i
    rw [atSeed_pack]
    simpa only [Fair.output] using hd δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 (seed i)
  have hmtr : metricContext (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=BinaryMetricBest.context δ D := by
    simp only [metricContext,src,Fair.pack,Function.comp_apply,extractPrefix_pairBits,
      BinarySampler.Parameters.pack,BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,BinaryMetricBest.context]
  have hs : src 4 (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=BinaryFinSet.encode S := by
    simp only [src,Fair.pack,Function.comp_apply,extractPrefix_pairBits,BinarySampler.Parameters.pack,
      BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [output]
  exact run_of_candidates Q d _ δ D S (List.ofFn (fun i=>Fair.output δ D F S Δ P m hm r0 y0 (seed i))) hmtr hs hc
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238r_oai

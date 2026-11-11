-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:09:11.476121+00:00
-- url     : https://prove2.me/submissions/55242a3b-ab10-438e-b785-565d9177f4bd

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K040
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_repack_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_recoveryContext_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_sampleContext_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMetricBest_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_atOption_none_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_run_source_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Trace_run_pack_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RecoveryOptionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] run
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s0 s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool)
lemma replaceState_pack : replaceState (pairBits (pack δ D F S Δ s0 m extra raw,
    BinarySamplingState.optionBits (some s)))=pack δ D F S Δ s m extra raw := by
  simp only [replaceState,src,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    pack,BinarySamplingState.optionBits,Option.toList_some,List.map_cons,List.map_nil,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma atOption_some (d : ℕ) : atOption d (pairBits (pack δ D F S Δ s0 m extra raw,
    BinarySamplingState.optionBits (some s)))=run d (pack δ D F S Δ s m extra raw) := by
  have h : BinarySamplingState.optionBits (some s)≠[] := by
    simp [BinarySamplingState.optionBits,WordList.encode,WordList.cons,pairBits]
  rw [atOption,discardPrefix_pairBits]
  simp only [h,decide_false,Bool.false_eq_true,ite_false, if_false,replaceState_pack]
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open BitMachine RationalHeight
variable {n : ℕ}
lemma retain_bounded (m : ℕ) (s t : State n) (ht : retain m s=some t) : t.Bounded m := by
  unfold retain at ht
  split_ifs at ht with h
  cases Option.some.inj ht
  exact h
lemma update_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (State n)) (a : Sampling.Action D M E J) (t : State n)
    (ht : update δ D F S Δ P κ m M E J s a=some t) : t.Bounded m := by
  cases s with
  | none=>simp only [update] at ht;contradiction
  | some s=>
    simp only [update] at ht
    split_ifs at ht
    rcases a with u | (w | ⟨w,e⟩)
    · contradiction
    · dsimp only at ht
      split_ifs at ht
      exact retain_bounded m _ t ht
    · dsimp only at ht
      cases he : menuRadius δ D P κ m M E J s w e with
      | none=>simp only [he] at ht;contradiction
      | some R=>
        simp only [he] at ht
        split_ifs at ht
        exact retain_bounded m _ t ht
end MetricKMedianRecovery.RationalSampling

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
lemma fold_next_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ)
    (seeds : List (Fin b→Bool)) (s : Option (State n)) (hs : ∀ z,s=some z→z.Bounded m) (t : State n)
    (ht : seeds.foldl (next δ D F S Δ P κ m M E J b) s=some t) : t.Bounded m := by
  induction seeds generalizing s with
  | nil=>exact hs t ht
  | cons seed seeds ih=>exact ih _ (fun z hz=>update_bounded δ D F S Δ P κ m M E J s _ z hz) ht
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList Sampling.Comparison
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] params cfg mword precision sampleRaw completeRaw extra src
  BinarySampler.Parameters.run BinarySampler.Parameters.precision BinarySampler.Parameters.unary
variable {n b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
  (g : List Bool) (seed : Fin (2*m)→Fin b→Bool) (complete : List Bool)
lemma src_pack (j : ℕ) : src j (pack δ D F S Δ P m g seed complete)=
    field j (BinarySampler.Parameters.pack δ D F S Δ P m) := by
  simp only [src,pack,Function.comp_apply,extractPrefix_pairBits]
lemma metricContext_pack : metricContext (pack δ D F S Δ P m g seed complete)=BinaryMetricBest.context δ D := by
  simp only [metricContext,src_pack,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryMetricBest.context]
lemma start_pack : src 4 (pack δ D F S Δ P m g seed complete)=BinaryFinSet.encode S := by
  simp only [src_pack,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList Sampling.Comparison
variable {n : ℕ}
lemma stateAt_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (seed : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool) (i : Fin (2*m+1))
    (s : RationalSampling.State n) (hs : stateAt δ D F S Δ P m seed i=some s) : s.Bounded m := by
  apply RationalSampling.fold_next_bounded δ D F S Δ P (1/1000000) m BinarySampler.Parameters.M BinarySampler.Parameters.E
    (RadiusMenus.thirdSize mainKappa m) (integralPrecision D (Δ:ℝ) m) _ _ _ s hs
  intro z hz
  cases Option.some.inj hz
  simp [RationalSampling.State.Bounded,RationalSampling.State.initial]
lemma optionOutput_none (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (m : ℕ) (hm : m≤n)
    (r0 y0 : Fin n) (seed : Fin (BinaryRecovery.tapeSize (n+1))→Bool) :
    optionOutput δ D F S Δ m hm r0 y0 seed none=S := rfl
lemma optionOutput_some (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (m : ℕ) (hm : m≤n)
    (r0 y0 : Fin n) (seed : Fin (BinaryRecovery.tapeSize (n+1))→Bool) (s : RationalSampling.State n)
    (hp : s.leaves.length≤n+1) : optionOutput δ D F S Δ m hm r0 y0 seed (some s)=
      BinaryRecovery.result δ D F S Δ s (Nat.le_succ n) (hm.trans (Nat.le_succ n)) (by omega) hp r0 y0 seed := by
  simp only [optionOutput,Option.elim_some,dite_eq_left hp]
lemma run_source (A : ℝ) : ∃ d : ℕ, ∀ {n : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n),
    Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16) → ∀ (extra : List Bool) (N : ℕ),
    N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) → ∀ (r0 y0 : Fin n)
    (sample : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
    (complete : Fin (BinaryRecovery.tapeSize (n+1))→Bool),
    run d (pack δ D F S Δ P m extra sample (List.ofFn complete))=
      BinaryFinSet.encode (result δ D F S Δ P m hm r0 y0 sample complete) := by
  obtain ⟨d,hd⟩:=BinaryRecovery.run_source_s238 A
  refine ⟨d,?_⟩
  intro n δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 sample complete
  have hc : candidateWords d (pack δ D F S Δ P m extra sample (List.ofFn complete))=
      encode ((candidates δ D F S Δ P m hm r0 y0 sample complete).map BinaryFinSet.encode) := by
    rw [candidateWords,recoveryContext_pack_s238 δ D F S Δ P m extra sample _ hm hΔ,
      sampleContext_pack_s238 δ D F S Δ P m extra _ sample hm hΔ,BinarySampler.Trace.run_pack_s238,mapWith_ofFn]
    simp only [candidates,List.map_ofFn,Function.comp_def]
    apply congrArg encode
    apply congrArg List.ofFn
    funext i
    change BinaryRecovery.atOption d (pairBits (BinaryRecovery.pack δ D F S (Δ:ℚ) RationalSampling.State.initial m extra
      (List.ofFn complete),BinarySamplingState.optionBits (stateAt δ D F S Δ P m sample i)))=_
    cases hs : stateAt δ D F S Δ P m sample i with
    | none=>rw [BinaryRecovery.atOption_none_s238,optionOutput_none]
    | some s=>
      have hp : s.leaves.length≤n+1 := ((stateAt_bounded δ D F S Δ P m sample i s hs).1.trans hm).trans (Nat.le_succ n)
      rw [BinaryRecovery.atOption_some,optionOutput_some δ D F S Δ m hm r0 y0 complete s hp]
      exact hd δ D F S Δ s extra r0 y0 N hN hlog (Nat.le_succ n) (hm.trans (Nat.le_succ n)) (by omega) hp complete
  rw [run,metricContext_pack,start_pack,hc]
  exact BinaryMetricBest.run_pack_s238 δ D S _
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

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
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (g bits : List Bool) (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
lemma run_source_s238_oai (A : ℝ) : ∃ d : ℕ, ∀ {n : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n),
    Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16) → ∀ (extra : List Bool) (N : ℕ),
    N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) → ∀ (r0 y0 : Fin n) (seed : Fin (count D Δ m)→Bool),
    run d (pack δ D F S Δ P m extra (List.ofFn seed))=
      BinaryFinSet.encode (result δ D F S Δ P m hm r0 y0 (layout D Δ m seed).1 (layout D Δ m seed).2) := by
  obtain ⟨d,hd⟩:=BinaryIntegralRecovery.run_source A
  refine ⟨d,?_⟩
  intro n δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 seed
  rw [run,Function.comp_apply,repack_pack_s238 δ D F S Δ P m extra hm hΔ]
  exact hd δ D F S Δ P m hm hΔ extra N hN hlog r0 y0 _ _
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238_oai

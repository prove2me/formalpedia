-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallback_bits_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:07:28.448194+00:00
-- url     : https://prove2.me/submissions/9dc711e0-1e62-4aaf-957f-b00fd8070345

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K040
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFinSet_pad_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNormalizeInput_P_facilities_bits_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList LocalSearch Completion
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySanitizedBest.output
lemma fallback_bits_s238_oai (I : RationalMetricInput) : fallback I.bits=BinaryFinSet.encode (start I) := by
  rw [fallback,Function.comp_apply,fallbackInput,P.facilities,BinaryNormalizeInput.P.facilities_bits_s238]
  have he : BinaryFinSet.encode (∅:Finset (Fin I.pointCount))=[] := by simp only [BinaryFinSet.encode_eq,Finset.sort_empty,List.map_nil,encode]
  simpa only [he,start] using BinaryFinSet.pad_pack_s238 I.facilities ∅ 1
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallback_bits_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallback_bits_s238_oai

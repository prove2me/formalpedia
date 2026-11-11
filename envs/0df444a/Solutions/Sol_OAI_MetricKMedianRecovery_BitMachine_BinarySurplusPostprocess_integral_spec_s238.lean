-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:04:46.913231+00:00
-- url     : https://prove2.me/submissions/3fa0bd41-39b7-4bf6-8cc1-9a6b6858c806

import Mathlib
import Definitions.Def_Q238K027
import Definitions.Def_Q238K037
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLocalRefine_integral_spec_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryProjection_run_setBits_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySurplusPostprocess_localInput_pack_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BottomMath
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {α : Type*} [LinearOrder α]
lemma bottomSet_subset (U : Finset α) (k : ℕ) : bottomSet U k⊆U := by
  intro x hx
  exact (Finset.mem_sort _).mp (List.mem_of_mem_take (List.mem_toFinset.mp hx))
lemma bottomSet_card (U : Finset α) (k : ℕ) : (bottomSet U k).card=min k U.card := by
  rw [bottomSet,List.toFinset_card_of_nodup ((U.sort_nodup (·≤·)).sublist (List.take_sublist _ _)),List.length_take,Finset.length_sort]
end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFillMath
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.Canonical
variable {V : Type*} [LinearOrder V]
lemma subset_pad (F U : Finset V) (n : ℕ) : U⊆pad F U n := Finset.subset_union_left
lemma pad_subset (F U : Finset V) (n : ℕ) (hUF : U⊆F) : pad F U n⊆F :=
  Finset.union_subset hUF ((bottomSet_subset _ _).trans Finset.sdiff_subset)
lemma pad_card (F U : Finset V) (n : ℕ) (hUF : U⊆F) (hUn : U.card≤n) (hnF : n≤F.card) :
    (pad F U n).card=n := by
  have hd : Disjoint U (bottomSet (F\U) (n-U.card)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    exact (Finset.mem_sdiff.mp (bottomSet_subset _ _ hb)).2 hx
  rw [pad,Finset.card_union_of_disjoint hd,bottomSet_card,Finset.card_sdiff_of_subset hUF,
    min_eq_left (Nat.sub_le_sub_right hnF _)]
  omega
end MetricKMedianRecovery.Completion.Canonical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassSlotsMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

lemma connection_mono {S T : Finset V} (hS : S.Nonempty) (hST : S ⊆ T) (p : V) :
    connection T p ≤ connection S p := by
  simp only [connection,dite_eq_left hS,dite_eq_left (hS.mono hST)]
  exact Finset.le_inf' hS _ (fun _ hs => Finset.inf'_le _ (hST hs))
lemma cost_mono (D : Finset V) {S T : Finset V} (hS : S.Nonempty) (hST : S ⊆ T) :
    cost D T ≤ cost D S := Finset.sum_le_sum (fun p _ => connection_mono hS hST p)

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_SurplusPostprocess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
lemma integral_spec_s238_oai [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (F S : Finset (Fin m)) (k : ℕ) (hSF : S⊆F) (hS : S.Nonempty)
    (hkF : k≤F.card) (hδ : ∀ j,∀ i∈F,(δ (loc j) i:ℝ)=dist (loc j) i)
    (hM : ∀ j,∀ i∈F,δ (loc j) i≤Rounding.cap d (IntegralAssembly.gamma/16)) :
    ∃ T : Finset (Fin m),run (pack (fun i j=>(δ (loc j) i:ℚ)) F S k)=BinaryFinSet.encode T ∧
      T⊆F ∧ T.Nonempty ∧ T.card=max k S.card ∧
      LocalSearch.cost (Finset.univ.image loc) T≤LocalSearch.cost (Finset.univ.image loc) S ∧
      LocalSearch.WidthLocalMin F (Finset.univ.image loc) T 5 := by
  let U:=Completion.Canonical.pad F S (max k S.card)
  have hUF : U⊆F := Completion.Canonical.pad_subset F S _ hSF
  have hSU : S⊆U := Completion.Canonical.subset_pad F S _
  have hU : U.Nonempty := hS.mono hSU
  have hcard : U.card=max k S.card :=
    Completion.Canonical.pad_card F S _ hSF (le_max_right _ _) (max_le hkF (Finset.card_le_card hSF))
  obtain ⟨T,he,hTF,hT,hTc,hcost,hmin⟩:=BinaryLocalRefine.integral_spec_s238 δ loc hloc (F.sort (·≤·)) U
    (by simpa only [Finset.sort_toFinset] using hUF) hU
    (by simpa only [Finset.sort_toFinset] using hδ) (by simpa only [Finset.sort_toFinset] using hM)
  refine ⟨T,?_,by simpa only [Finset.sort_toFinset] using hTF,hT,hTc.trans hcard,
    hcost.trans (LocalSearch.cost_mono _ hS hSU),by simpa only [Finset.sort_toFinset] using hmin⟩
  rw [run,Function.comp_apply,Function.comp_apply,localInput_pack_s238,he,BinaryProjection.run_setBits_s238]
  congr 1
  simp only [RationalLeaves.project,Finset.image_image]
  change T.image id=T
  exact Finset.image_id
end MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238_oai

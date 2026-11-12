-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:17:17.226219+00:00
-- url     : https://prove2.me/submissions/f7e2f245-3676-4780-8461-78a86400ba47

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L031
import Definitions.Def_Q238L049
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRefine_cutOp_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRegular_run_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_WordList_Slices_run_items_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_WordList_flatMapWith_typed_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

lemma base_F {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    field 2 (BinaryFiniteContext.pack distance loc F Q v z lam)=setBits F := by
  simp only [BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
end MetricKMedianRecovery.BitMachine.BinaryRegular

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RefineMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeRefinement
variable {X Y : Type*}
lemma cuts_adjacent (f : X → X → List Y) (U : List X) :
    (cuts U).flatMap (fun p=>match p.2.2 with | []=>[] | b::_=>f p.2.1 b)=adjacent f U := by
  induction U with
  | nil=>rfl
  | cons a U ih=>
    simp only [cuts,List.flatMap_cons,List.flatMap_map,ih]
    cases U with
    | nil=>rfl
    | cons b U=>rfl
variable [DecidableEq X]
lemma refinePath_adjacent (F : Finset X) (R : List X) (copy spare : X → X) (H : List X) (T : List (List X)) :
    refinePath F R copy spare H T=adjacent (refinedEdge F R copy spare) (H::T) := by
  induction T generalizing H with
  | nil=>rfl
  | cons G T ih=>
    change refinePath F R copy spare H (G::T)=refinedEdge F R copy spare H G ++ adjacent (refinedEdge F R copy spare) (G::T)
    simp only [refinePath]
    cases he : view F R copy H G <;> simp only [he,refinedEdge,ih,List.singleton_append]
end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RefineMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRefine
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
lemma run_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key spare : ℕ)
    (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
    run (pairBits (ctxBits F R key spare,historyBits (H::T)))=
      historyBits (refinePath F R (copy key) (copy spare) H T) := by
  have hs : Slices.run (historyBits (H::T))=Slices.outBits labels (cuts (H::T)) := Slices.run_items_s238r labels (H::T)
  simp only [run,Function.comp_apply,runInput,extractPrefix_pairBits,discardPrefix_pairBits,hs,Slices.outBits]
  rw [flatMapWith_typed_s238r (Slices.cutBits labels) labels cutOp (ctxBits F R key spare)
    (fun p=>match p.2.2 with | []=>[] | G::_=>refinedEdge F R (copy key) (copy spare) p.2.1 G)
    (cuts (H::T)) (fun p _=>cutOp_pack_s238r F R key spare p)]
  apply congrArg historyBits
  convert (cuts_adjacent (refinedEdge F R (copy key) (copy spare)) (H::T)).trans
    (refinePath_adjacent F R (copy key) (copy spare) H T).symm using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext p
  cases p.2.2 <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegularChain
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryRegular.run BinaryRefine.run
lemma regularInput_pack {m : ℕ} (base : List Bool) (key spare : ℕ) (R H G : List (Label (Fin m))) :
    regularInput (pack base key spare R H G)=BinaryRegular.pack base key G H := by
  simp only [regularInput,pack,BinaryRegular.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma context_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key spare : ℕ) (R H G : List (Label (Fin m))) :
    context (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare R H G)=BinaryRefine.ctxBits F R key spare := by
  simp only [context,pack,BinaryRefine.ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRegular.base_F]
lemma run_pack_s238r_oai {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v z lam : ℚ) (eta : ℝ) (key spare : ℕ) (R : List (Label (Fin m)))
    (hc : CorrectCompletion loc F (v:ℝ) z lam (FiniteLabelContinuation.complete loc (rows distance) F v z lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hz : (0:ℝ)<z) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) z Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (H G : List (Label (Fin m))) (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
    (hH : Valid loc F B Q v z lam eta H) (hG : Valid loc F B Q v z lam eta G) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare R H G)=
      historyBits (CanonicalMergeRefinement.regularChain F R
        (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) (copy spare) H G) := by
  rw [run,context_pack]
  unfold vertices
  rw [regularInput_pack,BinaryRegular.run_pack_s238r distance loc F B Q v z lam eta key hc hv hvsmall hz hlam heta
    hQ hdis hrow hfresh hco G H hGr hHr hG hH]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  change BinaryRefine.run (pairBits (BinaryRefine.ctxBits F R key spare,
    historyBits (H::CanonicalMergePath.regularPath (FiniteLabelContinuation.complete loc (rows distance) F v z lam)
      Q (copy key) G H)))=_
  exact BinaryRefine.run_pack F R key spare H _
end MetricKMedianRecovery.BitMachine.BinaryRegularChain

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238r_oai

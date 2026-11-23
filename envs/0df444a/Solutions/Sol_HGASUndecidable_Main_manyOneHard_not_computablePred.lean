-- Prove2me | solution 1 for HGASUndecidable.Main.manyOneHard_not_computablePred
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:41:15.922639+00:00
-- url     : https://prove2.me/submissions/094ce7ed-2761-40ce-a0f5-98c03125f2b3

import Definitions.Def_HGASUndecidable_Main_Codes
import Mathlib.Computability.Halting

open Filter Topology MeasureTheory
open scoped BigOperators
open HGASUndecidable.Main

theorem solution (S : ℕ → Prop) : ManyOneHard S → ¬ ComputablePred S := by
  intro hard computable
  have re : REPred haltingSet := by
    unfold haltingSet
    rw [← Nat.Partrec.Code.ofNatCode_eq]
    exact Partrec.dom_re (Partrec₂.comp Nat.Partrec.Code.eval_part
      ((Computable.ofNat Nat.Partrec.Code).comp (Computable.fst.comp Computable.unpair))
      (Computable.snd.comp Computable.unpair))
  have reduction : ManyOneReducible haltingSet S := hard haltingSet re
  have haltingComputable : ComputablePred haltingSet :=
    ComputablePred.computable_of_manyOneReducible reduction computable
  apply ComputablePred.halting_problem 0
  apply ComputablePred.computable_of_manyOneReducible (q := haltingSet) ?_ haltingComputable
  refine ⟨fun c => Nat.pair (Encodable.encode c) 0, ?_, ?_⟩
  · exact Primrec.to_comp (Primrec₂.natPair.comp Primrec.encode (Primrec.const 0))
  · intro c
    simp [haltingSet, ← Nat.Partrec.Code.ofNatCode_eq]

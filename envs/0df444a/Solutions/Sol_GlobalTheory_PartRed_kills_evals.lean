-- Prove2me | solution 1 for GlobalTheory.PartRed.kills_evals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:27:05.701956+00:00
-- url     : https://prove2.me/submissions/4ec96ca8-1ee6-4380-89f5-93b7f0ed8e52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMulAddCharLinearFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqFlatMapFourierJacobiRowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiRowAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapLawsFactorFourierJacobiSource
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_partialReduction_evaluate_entry_of_mul_law
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.PartRed
open GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] {M : Type} [AddCommGroup M]
  [Module ℂ M]
namespace GlobalTheory.PartRed
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hν : ν.IsAddHaarMeasure) (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (I : Finset (R × Q)) (S : Finset (R × Q)) : ∀ E : Finset (R × Q), Disjoint S I → Kills L ψ ν w β E I →
    (∀ e ∈ S, ∀ E' : Finset (R × Q), E ⊆ E' → E' ⊆ E ∪ S → e ∉ E' → EvalLaw L ψ ν w β E' I e) →
    Kills L ψ ν w β (E ∪ S) I := by
  induction S using Finset.induction_on with
  | empty => intro E _ hK _; simpa using hK
  | insert a S ha ih =>
    intro E hdisj hK hlaw
    have hdisj' : Disjoint S I := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdisj
    have h1 : Kills L ψ ν w β (E ∪ S) I := ih E hdisj' hK fun e he E' h1 h2 h3 =>
      hlaw e (Finset.mem_insert_of_mem he) E' h1
        (h2.trans (Finset.union_subset_union_right (Finset.subset_insert _ _))) h3
    have haI : a ∉ I := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self _ _)
    have heq : E ∪ insert a S = insert a (E ∪ S) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [heq]
    by_cases haE : a ∈ E ∪ S
    · rwa [Finset.insert_eq_of_mem haE]
    · refine GlobalTheory.T.partialReduction_evaluate_entry_of_mul_law k ψ ν hψ hψ1 hν R Q M L w β (E ∪ S) I a haI h1 ?_
      refine hlaw a (Finset.mem_insert_self _ _) (E ∪ S) Finset.subset_union_left ?_ haE
      exact Finset.union_subset_union_right (Finset.subset_insert _ _)
end GlobalTheory.PartRed

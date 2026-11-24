-- Prove2me | solution 1 for GlobalTheory.PartRed.kills_ints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:27:17.059555+00:00
-- url     : https://prove2.me/submissions/d5a5f93e-54da-4660-b745-9de2ed1f3b81

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
import Theorems.Thm_GlobalTheory_T_partialReduction_integrate_entry_of_translation
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
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ)
    (hν : ν.IsAddHaarMeasure) (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E : Finset (R × Q)) (S : Finset (R × Q)) : ∀ I : Finset (R × Q), Disjoint S E → Kills L ψ ν w β E I →
    (∀ e ∈ S, ∀ I' : Finset (R × Q), I ⊆ I' → I' ⊆ I ∪ S → e ∉ I' → IntLaw L ψ ν w β E I' e) →
    Kills L ψ ν w β E (I ∪ S) := by
  induction S using Finset.induction_on with
  | empty => intro I _ hK _; simpa using hK
  | insert a S ha ih =>
    intro I hdisj hK hlaw
    have hdisj' : Disjoint S E := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdisj
    have h1 : Kills L ψ ν w β E (I ∪ S) := ih I hdisj' hK fun e he I' h1 h2 h3 =>
      hlaw e (Finset.mem_insert_of_mem he) I' h1
        (h2.trans (Finset.union_subset_union_right (Finset.subset_insert _ _))) h3
    have haE : a ∉ E := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self _ _)
    have heq : I ∪ insert a S = insert a (I ∪ S) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [heq]
    by_cases haI : a ∈ I ∪ S
    · rwa [Finset.insert_eq_of_mem haI]
    · refine GlobalTheory.T.partialReduction_integrate_entry_of_translation k ψ ν hψ hν R Q M L w β E (I ∪ S) a haE h1 ?_
      refine hlaw a (Finset.mem_insert_self _ _) (I ∪ S) Finset.subset_union_left ?_ haI
      exact Finset.union_subset_union_right (Finset.subset_insert _ _)
end GlobalTheory.PartRed

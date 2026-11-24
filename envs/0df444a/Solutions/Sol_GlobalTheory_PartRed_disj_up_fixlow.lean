-- Prove2me | solution 1 for GlobalTheory.PartRed.disj_up_fixlow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:24:30.410452+00:00
-- url     : https://prove2.me/submissions/82beb30e-7d3b-4cf3-a86d-7565b4a47007

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
import Theorems.Thm_GlobalTheory_PartRed_mem_fixSet
import Theorems.Thm_GlobalTheory_PartRed_mem_lowSet
import Theorems.Thm_GlobalTheory_PartRed_mem_upSet
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.PartRed
theorem _root_.solution (ρ : ℕ) :
    Disjoint (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (fixSet ρ ∪ lowSet ρ) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨l, i, rfl, hli, hiρ⟩ := mem_upSet.mp h1
  rcases Finset.mem_union.mp h2 with h | h
  · rcases mem_fixSet.mp h with ⟨i', hq, -, hnf⟩ | ⟨l', s, -, -, hq⟩
    · exact hnf (by simp only [Free]; exact hli)
    · simp at hq
  · obtain ⟨l', i', he, -, hil⟩ := mem_lowSet.mp h
    simp only [Prod.mk.injEq, Sum.inr.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    omega
end GlobalTheory.PartRed

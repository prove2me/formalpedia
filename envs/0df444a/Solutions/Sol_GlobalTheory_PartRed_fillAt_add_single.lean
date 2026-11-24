-- Prove2me | solution 1 for GlobalTheory.PartRed.fillAt_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:48.777918+00:00
-- url     : https://prove2.me/submissions/22e4ce80-18a3-4c25-83f5-beda5da63e49

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
theorem _root_.solution (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) (a : k) :
    fillAt β E I x y + Matrix.single e.1 e.2 a = fillAt β E I (x + Matrix.single e.1 e.2 a) y := by
  obtain ⟨r₀, q₀⟩ := e
  ext r q
  by_cases h1 : (r, q) ∈ I
  · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hI h1
    simp [fillAt, h1, Matrix.single_apply, this]
  · by_cases h2 : (r, q) ∈ E
    · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hE h2
      simp [fillAt, h1, h2, Matrix.single_apply, this]
    · simp [fillAt, h1, h2]
end GlobalTheory.PartRed

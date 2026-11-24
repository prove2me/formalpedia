-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.fill_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:58.849861+00:00
-- url     : https://prove2.me/submissions/b88b9805-0ea0-434a-a43a-9b63b1b78765

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.IntEntry
namespace GlobalTheory.PartRed.IntEntry
theorem _root_.solution {k : Type} [Field k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
    (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) (a : k) :
    fillAt β E I (x + Matrix.single e.1 e.2 a) y = fillAt β E I x y + Matrix.single e.1 e.2 a := by
  obtain ⟨r₀, q₀⟩ := e
  ext r q
  by_cases h1 : (r, q) ∈ I
  · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hI h1
    simp [fillAt, h1, Matrix.single_apply, this]
  · by_cases h2 : (r, q) ∈ E
    · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hE h2
      simp [fillAt, h1, h2, Matrix.single_apply, this]
    · simp [fillAt, h1, h2]
end GlobalTheory.PartRed.IntEntry

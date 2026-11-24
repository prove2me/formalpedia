-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.fill_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:12.712269+00:00
-- url     : https://prove2.me/submissions/70f42741-96cf-4e07-a4c4-364dd0dfd0db

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
    (hI : e ∉ I) (hE : e ∉ E) : fillAt β E I x y e.1 e.2 = x e.1 e.2 := by
  obtain ⟨r, q⟩ := e
  simp [fillAt, hI, hE]
end GlobalTheory.PartRed.IntEntry

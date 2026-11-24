-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.isPat_colGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:50:28.382844+00:00
-- url     : https://prove2.me/submissions/8c4268b7-92bb-44f0-9020-b5912c5d7305

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep
namespace GlobalTheory.CompanionTheory.TyFin.ColStep
theorem _root_.solution (d j : ℕ) : IsPat (colGe d j) := by
  refine ⟨fun i h => lt_irrefl _ h.1, ?_⟩
  intro a b c hab hbc
  exact ⟨hab.1.trans hbc.1, hbc.2⟩
end GlobalTheory.CompanionTheory.TyFin.ColStep

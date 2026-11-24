-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.isPat_colGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:47:35.03966+00:00
-- url     : https://prove2.me/submissions/b2dd44ef-8429-4510-aa28-1f1a1f2f6efa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSums

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
theorem _root_.solution (d j : ℕ) : IsPat (colGe d j) :=
  ⟨fun i h => lt_irrefl _ h.1, fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2⟩⟩
end GlobalTheory.CompanionTheory.TyFin.ColStep.Avg

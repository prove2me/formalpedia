-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.natCard_colGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:06:52.849835+00:00
-- url     : https://prove2.me/submissions/4edddc71-f6cc-459a-a6cd-66391b52801d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStep
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_colGeSplit_bijective

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
theorem _root_.solution (d j : ℕ) (hj : j < d) :
    Nat.card {p : Fin d × Fin d // colGe d j p.1 p.2} =
      j + Nat.card {p : Fin d × Fin d // colGe d (j + 1) p.1 p.2} := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (colGeSplit_bijective d j hj)), Nat.card_sum,
    Nat.card_eq_fintype_card, Fintype.card_fin]
end GlobalTheory.CompanionTheory.TyFin.ColStep

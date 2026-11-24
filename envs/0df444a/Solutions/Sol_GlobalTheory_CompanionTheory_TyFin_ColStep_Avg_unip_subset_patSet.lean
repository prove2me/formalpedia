-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.unip_subset_patSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:53:19.98091+00:00
-- url     : https://prove2.me/submissions/c6ccf391-d844-4f0e-b3e4-f86123096e2b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSums
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_unip_entry

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
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {d j : ℕ}
namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
theorem _root_.solution {v : GL (Fin d) K}
    (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) :
    v ∈ patSet K (colGe d j) := by
  intro i l
  constructor
  · rintro rfl
    have := hv.2 i i rfl
    simpa using this
  · intro e hn
    by_cases hi : (i : ℕ) < j
    · by_cases hl : (l : ℕ) < j
      · have := hv.2 i l (by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock, hi, hl])
        simpa [e] using this
      · exact absurd ⟨Fin.lt_def.2 (by
          have := not_lt.1 hl
          omega), not_lt.1 hl⟩ hn
    · by_cases hl : (l : ℕ) < j
      · refine hv.1.1 i l ?_
        simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock, hi, hl]
      · have := unip_entry hv (not_lt.1 hi) (not_lt.1 hl)
        simpa [e] using this
end GlobalTheory.CompanionTheory.TyFin.ColStep.Avg

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:15.204806+00:00
-- url     : https://prove2.me/submissions/33d7d27c-518a-4b3b-b529-20de6a4c0335

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_cnt_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_cnt_diff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BruhatInv
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.BruhatInv
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.BruhatUniq := by
  intro K _ _ _ ι _ _ s s' b b' σ τ h c c'
  have h1 := cnt_diff b b' σ c c'
  have h2 := cnt_diff b b' τ c c'
  simp only [cnt_eq (K := K) b b' σ τ h] at h2
  omega
end GlobalTheory.CompanionTheory.BruhatInv

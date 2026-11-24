-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGLChar.hcChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:39:57.052311+00:00
-- url     : https://prove2.me/submissions/cd422826-8d98-4989-8f5f-498d4f88050f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGLChar_character_hcRep
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGLChar_isClassOn_hcFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGLChar
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
namespace GlobalTheory.CompanionTheory.FinGLChar
theorem _root_.solution : St.HCChar := by
  intro K _ _ _ ι _ _ s b lam
  exact ⟨character_hcRep b lam, isClassOn_hcFun b lam⟩
end GlobalTheory.CompanionTheory.FinGLChar

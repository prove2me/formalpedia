-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PatGrp.patChar_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:55:27.829144+00:00
-- url     : https://prove2.me/submissions/fcdb86e7-eb3e-4e64-8b2c-bdd168cc2782

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_pair_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PatGrp
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}
namespace GlobalTheory.CompanionTheory.PatGrp
theorem _root_.solution (h : IsPat Φ) {E : ι → ι → K} (hE : IsPatChar Φ E) (ψ₀ : AddChar K ℂ) :
    patChar E ψ₀ (1 : GL ι K) = 1 := by
  show ψ₀ (pair E ((1 : GL ι K) : Matrix ι ι K)) = 1
  rw [Units.val_one, pair_one h hE, AddChar.map_zero_eq_one]
end GlobalTheory.CompanionTheory.PatGrp

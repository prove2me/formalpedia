-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.generic_block_matrix_isBlockDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:59:53.012278+00:00
-- url     : https://prove2.me/submissions/bcc6f1d1-8ba0-4f1d-8fa0-549dd7d467df

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {R : Type} [CommRing R] {N : ℕ} {Ψ : Type}
variable {j : ℕ} {S : Type} [CommRing S]
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution (τ : Ψ) : IsBlockDiag j (genericBlockMatrix R N j τ) := fun _ _ h => dif_neg h
end GlobalTheory.CompanionTheory.Ar.PB

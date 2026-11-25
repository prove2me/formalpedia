-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.generic_block_matrix_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:03.10809+00:00
-- url     : https://prove2.me/submissions/b41699aa-322c-474c-bfa7-00b84a792baa

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
theorem _root_.solution (f : MvPolynomial (inertBlockIndex Ψ N j) R →+* S) {H : Ψ → Matrix (Fin N) (Fin N) S}
    (hH : ∀ τ, IsBlockDiag j (H τ)) (hf : ∀ q, f (X q) = H q.1.1 q.1.2.1 q.1.2.2) (τ : Ψ) :
    (genericBlockMatrix R N j τ).map f = H τ := by
  ext a b
  rw [Matrix.map_apply, genericBlockMatrix]
  split_ifs with h
  · exact hf _
  · rw [map_zero, hH τ a b h]
end GlobalTheory.CompanionTheory.Ar.PB
